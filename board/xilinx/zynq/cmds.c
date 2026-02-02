// SPDX-License-Identifier: GPL-2.0+
/*
 * Copyright (C) 2018 Xilinx, Inc.
 */

#include <command.h>
#include <log.h>
#include <asm/global_data.h>
#include <asm/io.h>
#include <asm/arch/hardware.h>
#include <asm/arch/sys_proto.h>
#include <malloc.h>
#include <linux/bitops.h>
#include <u-boot/md5.h>
#include <u-boot/rsa.h>
#include <u-boot/rsa-mod-exp.h>
#include <u-boot/sha256.h>
#include <zynqpl.h>
#include <fpga.h>
#include <zynq_bootimg.h>

DECLARE_GLOBAL_DATA_PTR;

#ifdef CONFIG_CMD_ZYNQ_RSA

#define ZYNQ_EFUSE_RSA_ENABLE_MASK	0x400
#define ZYNQ_ATTRIBUTE_PL_IMAGE_MASK		0x20
#define ZYNQ_ATTRIBUTE_CHECKSUM_TYPE_MASK	0x7000
#define ZYNQ_ATTRIBUTE_RSA_PRESENT_MASK		0x8000
#define ZYNQ_ATTRIBUTE_RSA_PART_OWNER_MASK	0x30000

#define ZYNQ_RSA_MODULAR_SIZE			256
#define ZYNQ_RSA_MODULAR_EXT_SIZE		256
#define ZYNQ_RSA_EXPO_SIZE			64
#define ZYNQ_RSA_SPK_SIGNATURE_SIZE		256
#define ZYNQ_RSA_PARTITION_SIGNATURE_SIZE	256
#define ZYNQ_RSA_SIGNATURE_SIZE			0x6C0
#define ZYNQ_RSA_HEADER_SIZE			4
#define ZYNQ_RSA_MAGIC_WORD_SIZE		60
#define ZYNQ_RSA_PART_OWNER_UBOOT		1
#define ZYNQ_RSA_ALIGN_PPK_START		64
#define ZYNQ_PARTITION_CHECKSUM_MASK		0x7000

#define WORD_LENGTH_SHIFT	2

static u8 *ppkmodular;
static u8 *ppkmodularex;

struct zynq_rsa_public_key {
	uint len;		/* Length of modulus[] in number of u32 */
	u32 n0inv;		/* -1 / modulus[0] mod 2^32 */
	u32 *modulus;	/* modulus as little endian array */
	u32 *rr;		/* R^2 as little endian array */
};

static struct zynq_rsa_public_key public_key;

static struct partition_hdr part_hdr[ZYNQ_MAX_PARTITION_NUMBER];

/* Global variable to store selected flash address for bootimg command */
static u32 bootimg_selected_flash_addr = 0;

/*
 * Extract the primary public key components from already autheticated FSBL
 */
static void zynq_extract_ppk(u32 fsbl_len)
{
	u32 padsize;
	u8 *ppkptr;

	debug("%s\n", __func__);

	/*
	 * Extract the authenticated PPK from OCM i.e at end of the FSBL
	 */
	ppkptr = (u8 *)(fsbl_len + ZYNQ_OCM_BASEADDR);
	padsize = ((u32)ppkptr % ZYNQ_RSA_ALIGN_PPK_START);
	if (padsize)
		ppkptr += (ZYNQ_RSA_ALIGN_PPK_START - padsize);

	ppkptr += ZYNQ_RSA_HEADER_SIZE;

	ppkptr += ZYNQ_RSA_MAGIC_WORD_SIZE;

	ppkmodular = (u8 *)ppkptr;
	ppkptr += ZYNQ_RSA_MODULAR_SIZE;
	ppkmodularex = (u8 *)ppkptr;
	ppkptr += ZYNQ_RSA_MODULAR_EXT_SIZE;
}

/*
 * Calculate the inverse(-1 / modulus[0] mod 2^32 ) for the PPK
 */
static u32 zynq_calc_inv(void)
{
	u32 modulus = public_key.modulus[0];
	u32 tmp = BIT(1);
	u32 inverse;

	inverse = modulus & BIT(0);

	while (tmp) {
		inverse *= 2 - modulus * inverse;
		tmp *= tmp;
	}

	return ~(inverse - 1);
}

/*
 * Recreate the signature by padding the bytes and verify with hash value
 */
static int zynq_pad_and_check(u8 *signature, u8 *hash)
{
	u8 padding[] = {0x30, 0x31, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48,
			0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04,
			0x20};
	u8 *pad_ptr = signature + 256;
	u32 pad = 202;
	u32 ii;

	/*
	 * Re-Create PKCS#1v1.5 Padding
	 * MSB  ----------------------------------------------------LSB
	 * 0x0 || 0x1 || 0xFF(for 202 bytes) || 0x0 || T_padding || SHA256 Hash
	 */
	if (*--pad_ptr != 0 || *--pad_ptr != 1)
		return -1;

	for (ii = 0; ii < pad; ii++) {
		if (*--pad_ptr != 0xFF)
			return -1;
	}

	if (*--pad_ptr != 0)
		return -1;

	for (ii = 0; ii < sizeof(padding); ii++) {
		if (*--pad_ptr != padding[ii])
			return -1;
	}

	for (ii = 0; ii < 32; ii++) {
		if (*--pad_ptr != hash[ii])
			return -1;
	}
	return 0;
}

/*
 * Verify and extract the hash value from signature using the public key
 * and compare it with calculated hash value.
 */
static int zynq_rsa_verify_key(const struct zynq_rsa_public_key *key,
			       const u8 *sig, const u32 sig_len, const u8 *hash)
{
	int status;
	void *buf;

	if (!key || !sig || !hash)
		return -1;

	if (sig_len != (key->len * sizeof(u32))) {
		printf("Signature is of incorrect length %d\n", sig_len);
		return -1;
	}

	/* Sanity check for stack size */
	if (sig_len > ZYNQ_RSA_SPK_SIGNATURE_SIZE) {
		printf("Signature length %u exceeds maximum %d\n", sig_len,
		       ZYNQ_RSA_SPK_SIGNATURE_SIZE);
		return -1;
	}

	buf = malloc(sig_len);
	if (!buf)
		return -1;

	memcpy(buf, sig, sig_len);

	status = zynq_pow_mod((u32 *)key, (u32 *)buf);
	if (status == -1) {
		free(buf);
		return status;
	}

	status = zynq_pad_and_check((u8 *)buf, (u8 *)hash);

	free(buf);
	return status;
}

/*
 * Authenticate the partition
 */
static int zynq_authenticate_part(u8 *buffer, u32 size)
{
	u8 hash_signature[32];
	u8 *spk_modular;
	u8 *spk_modular_ex;
	u8 *signature_ptr;
	u32 status;

	debug("%s\n", __func__);

	signature_ptr = (u8 *)(buffer + size - ZYNQ_RSA_SIGNATURE_SIZE);

	signature_ptr += ZYNQ_RSA_HEADER_SIZE;

	signature_ptr += ZYNQ_RSA_MAGIC_WORD_SIZE;

	ppkmodular = (u8 *)signature_ptr;
	signature_ptr += ZYNQ_RSA_MODULAR_SIZE;
	ppkmodularex = signature_ptr;
	signature_ptr += ZYNQ_RSA_MODULAR_EXT_SIZE;
	signature_ptr += ZYNQ_RSA_EXPO_SIZE;

	sha256_csum_wd((const unsigned char *)signature_ptr,
		       (ZYNQ_RSA_MODULAR_EXT_SIZE + ZYNQ_RSA_EXPO_SIZE +
		       ZYNQ_RSA_MODULAR_SIZE),
		       (unsigned char *)hash_signature, 0x1000);

	spk_modular = (u8 *)signature_ptr;
	signature_ptr += ZYNQ_RSA_MODULAR_SIZE;
	spk_modular_ex = (u8 *)signature_ptr;
	signature_ptr += ZYNQ_RSA_MODULAR_EXT_SIZE;
	signature_ptr += ZYNQ_RSA_EXPO_SIZE;

	public_key.len = ZYNQ_RSA_MODULAR_SIZE / sizeof(u32);
	public_key.modulus = (u32 *)ppkmodular;
	public_key.rr = (u32 *)ppkmodularex;
	public_key.n0inv = zynq_calc_inv();

	status = zynq_rsa_verify_key(&public_key, signature_ptr,
				     ZYNQ_RSA_SPK_SIGNATURE_SIZE,
				     hash_signature);
	if (status)
		return status;

	signature_ptr += ZYNQ_RSA_SPK_SIGNATURE_SIZE;

	sha256_csum_wd((const unsigned char *)buffer,
		       (size - ZYNQ_RSA_PARTITION_SIGNATURE_SIZE),
		       (unsigned char *)hash_signature, 0x1000);

	public_key.len = ZYNQ_RSA_MODULAR_SIZE / sizeof(u32);
	public_key.modulus = (u32 *)spk_modular;
	public_key.rr = (u32 *)spk_modular_ex;
	public_key.n0inv = zynq_calc_inv();

	return zynq_rsa_verify_key(&public_key, (u8 *)signature_ptr,
				   ZYNQ_RSA_PARTITION_SIGNATURE_SIZE,
				   (u8 *)hash_signature);
}

/*
 * Parses the partition header and verfies the authenticated and
 * encrypted image.
 */
static int zynq_verify_image(u32 src_ptr)
{
	u32 silicon_ver, image_base_addr, status;
	u32 partition_num = 0;
	u32 efuseval, srcaddr, size, fsbl_len;
	struct partition_hdr *hdr_ptr;
	u32 part_data_len, part_img_len, part_attr;
	u32 part_load_addr, part_dst_addr, part_chksum_offset;
	u32 part_start_addr, part_total_size, partitioncount;
	bool encrypt_part_flag = false;
	bool part_chksum_flag = false;
	bool signed_part_flag = false;

	image_base_addr = src_ptr;

	silicon_ver = zynq_get_silicon_version();

	/* RSA not supported in silicon versions 1.0 and 2.0 */
	if (silicon_ver == 0 || silicon_ver == 1)
		return -1;

	zynq_get_partition_info(image_base_addr, &fsbl_len,
				&part_hdr[0]);

	/* Extract ppk if efuse was blown Otherwise return error */
	efuseval = readl(&efuse_base->status);
	if (!(efuseval & ZYNQ_EFUSE_RSA_ENABLE_MASK))
		return -1;

	zynq_extract_ppk(fsbl_len);

	partitioncount = zynq_get_part_count(&part_hdr[0]);

	/*
	 * As the first two partitions are related to fsbl,
	 * we can ignore those two in bootimage and the below
	 * code doesn't need to validate it as fsbl is already
	 * done by now
	 */
	if (partitioncount <= 2 ||
	    partitioncount > ZYNQ_MAX_PARTITION_NUMBER)
		return -1;

	while (partition_num < partitioncount) {
		if (((part_hdr[partition_num].partitionattr &
		   ZYNQ_ATTRIBUTE_RSA_PART_OWNER_MASK) >> 16) !=
		   ZYNQ_RSA_PART_OWNER_UBOOT) {
			printf("UBOOT is not Owner for partition %d\n",
			       partition_num);
			partition_num++;
			continue;
		}
		hdr_ptr = &part_hdr[partition_num];
		status = zynq_validate_hdr(hdr_ptr);
		if (status)
			return status;

		part_data_len = hdr_ptr->datawordlen;
		part_img_len = hdr_ptr->imagewordlen;
		part_attr = hdr_ptr->partitionattr;
		part_load_addr = hdr_ptr->loadaddr;
		part_chksum_offset = hdr_ptr->checksumoffset;
		part_start_addr = hdr_ptr->partitionstart;
		part_total_size = hdr_ptr->partitionwordlen;

		if (part_data_len != part_img_len) {
			debug("Encrypted\n");
			encrypt_part_flag = true;
		}

		if (part_attr & ZYNQ_ATTRIBUTE_CHECKSUM_TYPE_MASK)
			part_chksum_flag = true;

		if (part_attr & ZYNQ_ATTRIBUTE_RSA_PRESENT_MASK) {
			debug("RSA Signed\n");
			signed_part_flag = true;
			size = part_total_size << WORD_LENGTH_SHIFT;
		} else {
			size = part_img_len;
		}

		if (!signed_part_flag && !part_chksum_flag) {
			printf("Partition not signed & no chksum\n");
			partition_num++;
			continue;
		}

		srcaddr = image_base_addr +
			  (part_start_addr << WORD_LENGTH_SHIFT);

		/*
		 * This validation is just for PS DDR.
		 * TODO: Update this for PL DDR check as well.
		 */
		if (part_load_addr < gd->bd->bi_dram[0].start &&
		    ((part_load_addr + part_data_len) >
		    (gd->bd->bi_dram[0].start +
		     gd->bd->bi_dram[0].size))) {
			printf("INVALID_LOAD_ADDRESS_FAIL\n");
			return -1;
		}

		if (part_attr & ZYNQ_ATTRIBUTE_PL_IMAGE_MASK)
			part_load_addr = srcaddr;
		else
			memcpy((u32 *)part_load_addr, (u32 *)srcaddr,
			       size);

		if (part_chksum_flag) {
			part_chksum_offset = image_base_addr +
					     (part_chksum_offset <<
					     WORD_LENGTH_SHIFT);
			status = zynq_validate_partition(part_load_addr,
							 (part_total_size <<
							  WORD_LENGTH_SHIFT),
							 part_chksum_offset);
			if (status != 0) {
				printf("PART_CHKSUM_FAIL\n");
				return -1;
			}
			debug("Partition Validation Done\n");
		}

		if (signed_part_flag) {
			status = zynq_authenticate_part((u8 *)part_load_addr,
							size);
			if (status != 0) {
				printf("AUTHENTICATION_FAIL\n");
				return -1;
			}
			debug("Authentication Done\n");
		}

		if (encrypt_part_flag) {
			debug("DECRYPTION\n");

			part_dst_addr = part_load_addr;

			if (part_attr & ZYNQ_ATTRIBUTE_PL_IMAGE_MASK) {
				partition_num++;
				continue;
			}

			status = zynq_decrypt_load(part_load_addr,
						   part_img_len,
						   part_dst_addr,
						   part_data_len,
						   BIT_NONE);
			if (status != 0) {
				printf("DECRYPTION_FAIL\n");
				return -1;
			}
		}
		partition_num++;
	}

	return 0;
}

static int do_zynq_rsa(struct cmd_tbl *cmdtp, int flag, int argc,
		       char *const argv[])
{
	u32 src_ptr;
	char *endp;

	if (argc != cmdtp->maxargs)
		return CMD_RET_FAILURE;

	src_ptr = hextoul(argv[2], &endp);
	if (*argv[2] == 0 || *endp != 0)
		return CMD_RET_USAGE;

	if (zynq_verify_image(src_ptr))
		return CMD_RET_FAILURE;

	return CMD_RET_SUCCESS;
}
#endif

#ifdef CONFIG_CMD_ZYNQ_AES
static int zynq_decrypt_image(struct cmd_tbl *cmdtp, int flag, int argc,
			      char *const argv[])
{
	char *endp;
	u32 srcaddr, srclen, dstaddr, dstlen;
	int status;
	u8 imgtype = BIT_NONE;

	if (argc < 5 && argc > cmdtp->maxargs)
		return CMD_RET_USAGE;

	if (argc == 5) {
		if (!strcmp("load", argv[2]))
			imgtype = BIT_FULL;
		else if (!strcmp("loadp", argv[2]))
			imgtype = BIT_PARTIAL;
		else
			return CMD_RET_USAGE;

		srcaddr = hextoul(argv[3], &endp);
		if (*argv[3] == 0 || *endp != 0)
			return CMD_RET_USAGE;
		srclen = hextoul(argv[4], &endp);
		if (*argv[4] == 0 || *endp != 0)
			return CMD_RET_USAGE;

		dstaddr = 0xFFFFFFFF;
		dstlen = srclen;
	} else {
		srcaddr = hextoul(argv[2], &endp);
		if (*argv[2] == 0 || *endp != 0)
			return CMD_RET_USAGE;
		srclen = hextoul(argv[3], &endp);
		if (*argv[3] == 0 || *endp != 0)
			return CMD_RET_USAGE;
		dstaddr = hextoul(argv[4], &endp);
		if (*argv[4] == 0 || *endp != 0)
			return CMD_RET_USAGE;
		dstlen = hextoul(argv[5], &endp);
		if (*argv[5] == 0 || *endp != 0)
			return CMD_RET_USAGE;
	}

	/*
	 * Roundup source and destination lengths to
	 * word size
	 */
	if (srclen % 4)
		srclen = roundup(srclen, 4);
	if (dstlen % 4)
		dstlen = roundup(dstlen, 4);

	status = zynq_decrypt_load(srcaddr, srclen >> 2, dstaddr,
				   dstlen >> 2, imgtype);
	if (status != 0)
		return CMD_RET_FAILURE;

	return CMD_RET_SUCCESS;
}
#endif

static struct cmd_tbl zynq_commands[] = {
#ifdef CONFIG_CMD_ZYNQ_RSA
	U_BOOT_CMD_MKENT(rsa, 3, 1, do_zynq_rsa, "", ""),
#endif
#ifdef CONFIG_CMD_ZYNQ_AES
	U_BOOT_CMD_MKENT(aes, 6, 1, zynq_decrypt_image, "", ""),
#endif
};

static int do_zynq(struct cmd_tbl *cmdtp, int flag, int argc,
		   char *const argv[])
{
	struct cmd_tbl *zynq_cmd;
	int ret;

	if (!ARRAY_SIZE(zynq_commands)) {
		puts("No zynq specific command enabled\n");
		return CMD_RET_USAGE;
	}

	if (argc < 2)
		return CMD_RET_USAGE;
	zynq_cmd = find_cmd_tbl(argv[1], zynq_commands,
				ARRAY_SIZE(zynq_commands));
	if (!zynq_cmd)
		return CMD_RET_USAGE;

	ret = zynq_cmd->cmd(zynq_cmd, flag, argc, argv);

	return cmd_process_error(zynq_cmd, ret);
}

U_BOOT_LONGHELP(zynq,
	""
#ifdef CONFIG_CMD_ZYNQ_RSA
	"rsa <baseaddr>  - Verifies the authenticated and encrypted\n"
	"                  zynq images and loads them back to load\n"
	"                  addresses as specified in BOOT image(BOOT.BIN)\n"
#endif
#ifdef CONFIG_CMD_ZYNQ_AES
	"aes <srcaddr> <srclen> <dstaddr> <dstlen>\n"
	"                - Decrypts the encrypted image present in source\n"
	"                  address and places the decrypted image at\n"
	"                  destination address\n"
	"aes load <srcaddr> <srclen>\n"
	"aes loadp <srcaddr> <srclen>\n"
	"       if operation type is load or loadp, it loads the encrypted\n"
	"       full or partial bitstream on to PL respectively.\n"
#endif
	);

U_BOOT_CMD(zynq,	6,	0,	do_zynq,
	   "Zynq specific commands", zynq_help_text
);

#ifdef CONFIG_CMD_ZYNQ_RSA

/*
 * bootimg select - Select or show selected flash memory
 */
static int do_bootimg_select(struct cmd_tbl *cmdtp, int flag, int argc,
			     char *const argv[])
{
	char *endp;

	if (argc == 2) {
		/* No flash address provided, show current selection */
		if (bootimg_selected_flash_addr == 0) {
			printf("No flash memory selected\n");
		} else {
			printf("Selected flash memory: 0x%08x\n", bootimg_selected_flash_addr);
		}
		return CMD_RET_SUCCESS;
	}

	if (argc != 3)
		return CMD_RET_USAGE;

	/* Parse and store the flash address */
	bootimg_selected_flash_addr = hextoul(argv[2], &endp);
	if (*argv[2] == 0 || *endp != 0) {
		printf("Error: Invalid flash address\n");
		return CMD_RET_USAGE;
	}

	printf("Flash memory selected: 0x%08x\n", bootimg_selected_flash_addr);
	return CMD_RET_SUCCESS;
}

/*
 * bootimg show - Show partitions from selected flash
 */
static int do_bootimg_show(struct cmd_tbl *cmdtp, int flag, int argc,
			   char *const argv[])
{
	u32 fsbl_len;
	int part_count;
	int i;
	struct partition_hdr *hdr;

	if (bootimg_selected_flash_addr == 0) {
		printf("Error: No flash memory selected. Use 'bootimg select <flash>' first\n");
		return CMD_RET_FAILURE;
	}

	/* Get partition information */
	if (zynq_get_partition_info(bootimg_selected_flash_addr, &fsbl_len, &part_hdr[0]) != 0) {
		printf("Error: Failed to get partition information\n");
		return CMD_RET_FAILURE;
	}

	part_count = zynq_get_part_count(&part_hdr[0]);

	printf("\n=== Boot Image Partitions ===\n");
	printf("Flash Address: 0x%08x\n", bootimg_selected_flash_addr);
	printf("FSBL Length: 0x%08x (%u bytes)\n", fsbl_len, fsbl_len);
	printf("Partition Count: %d\n\n", part_count);

	printf("%-4s %-12s %-12s %-12s %-12s %-12s\n",
	       "Num", "Start", "LoadAddr", "ExecAddr", "ImageLen", "DataLen");
	printf("%-4s %-12s %-12s %-12s %-12s %-12s\n",
	       "---", "-----", "--------", "--------", "--------", "-------");

	for (i = 0; i < part_count; i++) {
		hdr = &part_hdr[i];
		printf("%-4d 0x%08x   0x%08x   0x%08x   0x%08x   0x%08x\n",
		       i,
		       hdr->partitionstart << 2,
		       hdr->loadaddr,
		       hdr->execaddr,
		       hdr->imagewordlen << 2,
		       hdr->datawordlen << 2);
	}
	printf("\n");

	return CMD_RET_SUCCESS;
}

/*
 * bootimg check - Check partition checksum and verify integrity
 */
static int do_bootimg_check(struct cmd_tbl *cmdtp, int flag, int argc,
			    char *const argv[])
{
	u32 fsbl_len;
	int part_count;
	int part_num;
	char *endp;
	struct partition_hdr *hdr;
	u32 part_addr, part_len, chksum_offset;
	int status;

	if (argc != 3)
		return CMD_RET_USAGE;

	if (bootimg_selected_flash_addr == 0) {
		printf("Error: No flash memory selected. Use 'bootimg select <flash>' first\n");
		return CMD_RET_FAILURE;
	}

	/* Parse partition number */
	part_num = (int)dectoul(argv[2], &endp);
	if (*argv[2] == 0 || *endp != 0) {
		printf("Error: Invalid partition number\n");
		return CMD_RET_USAGE;
	}

	/* Get partition information */
	if (zynq_get_partition_info(bootimg_selected_flash_addr, &fsbl_len, &part_hdr[0]) != 0) {
		printf("Error: Failed to get partition information\n");
		return CMD_RET_FAILURE;
	}

	part_count = zynq_get_part_count(&part_hdr[0]);

	if (part_num < 0 || part_num >= part_count) {
		printf("Error: Invalid partition number. Valid range: 0-%d\n", part_count - 1);
		return CMD_RET_FAILURE;
	}

	hdr = &part_hdr[part_num];

	printf("\n=== Checking Partition %d ===\n", part_num);

	/* Validate partition header */
	status = zynq_validate_hdr(hdr);
	if (status != 0) {
		printf("Error: Partition header validation failed\n");
		return CMD_RET_FAILURE;
	}
	printf("Partition header: OK\n");

	/* Check if partition has checksum */
	if (!(hdr->partitionattr & ZYNQ_PARTITION_CHECKSUM_MASK)) {
		printf("Warning: Partition does not have checksum enabled\n");
		return CMD_RET_SUCCESS;
	}

	/* Calculate addresses for checksum validation */
	part_addr = bootimg_selected_flash_addr + (hdr->partitionstart << 2);
	part_len = hdr->partitionwordlen << 2;
	chksum_offset = bootimg_selected_flash_addr + (hdr->checksumoffset << 2);

	printf("Partition start: 0x%08x\n", part_addr);
	printf("Partition length: 0x%08x (%u bytes)\n", part_len, part_len);
	printf("Checksum offset: 0x%08x\n", chksum_offset);

	/* Validate partition data checksum */
	status = zynq_validate_partition(part_addr, part_len, chksum_offset);
	if (status != 0) {
		printf("Error: Partition data checksum validation failed\n");
		return CMD_RET_FAILURE;
	}

	printf("Partition data checksum: OK\n");
	printf("\n=== Partition %d is valid ===\n\n", part_num);

	return CMD_RET_SUCCESS;
}

static struct cmd_tbl bootimg_commands[] = {
	U_BOOT_CMD_MKENT(select, 3, 1, do_bootimg_select, "select flash", ""),
	U_BOOT_CMD_MKENT(show, 2, 1, do_bootimg_show, "show partitions", ""),
	U_BOOT_CMD_MKENT(check, 3, 1, do_bootimg_check, "check partition", ""),
};

static int do_bootimg(struct cmd_tbl *cmdtp, int flag, int argc,
		      char *const argv[])
{
	struct cmd_tbl *bootimg_cmd;
	int ret;

	if (argc < 2)
		return CMD_RET_USAGE;

	bootimg_cmd = find_cmd_tbl(argv[1], bootimg_commands,
				    ARRAY_SIZE(bootimg_commands));
	if (!bootimg_cmd)
		return CMD_RET_USAGE;

	ret = bootimg_cmd->cmd(bootimg_cmd, flag, argc, argv);

	return cmd_process_error(bootimg_cmd, ret);
}

U_BOOT_LONGHELP(bootimg,
	"Zynq boot image management commands\n"
	"bootimg select [<flash>]  - Select flash memory address or show current selection\n"
	"                            <flash> is the base address in hex (e.g., 0x1000000)\n"
	"bootimg show              - Display partition information from selected flash\n"
	"bootimg check <partition> - Verify partition header and checksum integrity\n"
	"                            <partition> is the partition number (0, 1, 2, ...)\n"
);

U_BOOT_CMD(bootimg, 3, 0, do_bootimg,
	   "Zynq boot image partition management", bootimg_help_text
);

#endif /* CONFIG_CMD_ZYNQ_RSA */
