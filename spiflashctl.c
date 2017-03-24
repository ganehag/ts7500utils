/*  Copyright 2004-2011, Unpublished Work of Technologic Systems
 *  All Rights Reserved.
 *
 *  THIS WORK IS AN UNPUBLISHED WORK AND CONTAINS CONFIDENTIAL,
 *  PROPRIETARY AND TRADE SECRET INFORMATION OF TECHNOLOGIC SYSTEMS.
 *  ACCESS TO THIS WORK IS RESTRICTED TO (I) TECHNOLOGIC SYSTEMS EMPLOYEES
 *  WHO HAVE A NEED TO KNOW TO PERFORM TASKS WITHIN THE SCOPE OF THEIR
 *  ASSIGNMENTS  AND (II) ENTITIES OTHER THAN TECHNOLOGIC SYSTEMS WHO
 *  HAVE ENTERED INTO  APPROPRIATE LICENSE AGREEMENTS.  NO PART OF THIS
 *  WORK MAY BE USED, PRACTICED, PERFORMED, COPIED, DISTRIBUTED, REVISED,
 *  MODIFIED, TRANSLATED, ABRIDGED, CONDENSED, EXPANDED, COLLECTED,
 *  COMPILED,LINKED,RECAST, TRANSFORMED, ADAPTED IN ANY FORM OR BY ANY
 *  MEANS,MANUAL, MECHANICAL, CHEMICAL, ELECTRICAL, ELECTRONIC, OPTICAL,
 *  BIOLOGICAL, OR OTHERWISE WITHOUT THE PRIOR WRITTEN PERMISSION AND
 *  CONSENT OF TECHNOLOGIC SYSTEMS . ANY USE OR EXPLOITATION OF THIS WORK
 *  WITHOUT THE PRIOR WRITTEN CONSENT OF TECHNOLOGIC SYSTEMS  COULD
 *  SUBJECT THE PERPETRATOR TO CRIMINAL AND CIVIL LIABILITY.
 */
/* To compile spiflashctl, use the appropriate cross compiler and run the
 * command:
 *
 *   gcc -Wall -O -mcpu=arm9 -o spiflashctl spiflashctl.c -lutil
 *
 * On uclibc based initrd's, the following additional gcc options are
 * necessary: -Wl,--rpath,/slib -Wl,-dynamic-linker,/slib/ld-uClibc.so.0
 */

const char copyright[] = "Copyright (c) Technologic Systems - " __DATE__ ;

#include <arpa/inet.h>
#include <assert.h>
#include <ctype.h>
#include <fcntl.h>
#include <getopt.h>
#include <errno.h>
#include <limits.h>
#include <linux/unistd.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#ifndef TEMP_FAILURE_RETRY
# define TEMP_FAILURE_RETRY(expression) \
  (__extension__                                                              \
    ({ long int __result;                                                     \
       do __result = (long int) (expression);                                 \
       while (__result == -1L && errno == EINTR);                             \
       __result; }))
#endif

static void poke8(unsigned int, unsigned char);
static void poke16(unsigned int, unsigned short);
static unsigned short peek16(unsigned int);

static volatile unsigned int *cvspiregs, *cvgpioregs;
static int size;
static int verify;
static int nbdbufsz;
static unsigned char *nbdbuf;
static unsigned char *csumtbl;
static int opt_lun;

struct nbd_request {
	unsigned int magic;
	char type[4];
	char handle[8];
	unsigned int fromhi;
	unsigned int fromlo;
	unsigned int len;
};

struct nbd_reply {
	char magic[4];
	unsigned int error;
	char handle[8];
};

static unsigned char cavium_mbr[512] = {
0x28,0x31,0x9f,0xe5,0x08,0xd0,0x4d,0xe2,0x01,0x60,0xa0,0xe1,0x00,0x80,0xa0,0xe1,
0x03,0x00,0x93,0xe8,0x0d,0x30,0xa0,0xe1,0x03,0x00,0x83,0xe8,0x10,0x01,0x9f,0xe5,
0x02,0x70,0xa0,0xe1,0x00,0xa0,0x9d,0xe5,0x08,0x41,0x9f,0xe5,0x0f,0xe0,0xa0,0xe1,
0x06,0xf0,0xa0,0xe1,0x00,0x50,0xa0,0xe3,0x12,0x00,0x00,0xea,0x04,0x30,0xd4,0xe5,
0xda,0x00,0x53,0xe3,0x0e,0x00,0x00,0x1a,0xb8,0x10,0xd4,0xe1,0xbc,0xc0,0xd4,0xe1,
0xba,0x00,0xd4,0xe1,0xbe,0x20,0xd4,0xe1,0x08,0xe0,0x8d,0xe2,0x05,0x31,0x8e,0xe0,
0x00,0x08,0x81,0xe1,0x02,0x28,0x8c,0xe1,0x08,0x10,0x13,0xe5,0x0f,0xe0,0xa0,0xe1,
0x08,0xf0,0xa0,0xe1,0xb8,0x00,0x9f,0xe5,0x01,0x50,0x85,0xe2,0x0f,0xe0,0xa0,0xe1,
0x06,0xf0,0xa0,0xe1,0x10,0x40,0x84,0xe2,0xac,0x30,0x9f,0xe5,0x03,0x00,0x54,0xe1,
0xe9,0xff,0xff,0x1a,0x0f,0xe0,0xa0,0xe1,0x07,0xf0,0xa0,0xe1,0x01,0x00,0x55,0xe3,
0x98,0x30,0x9f,0xc5,0x78,0x20,0xe0,0xc3,0x06,0x20,0xc3,0xc5,0x90,0xc0,0x9f,0xe5,
0x01,0x1c,0xa0,0xe3,0x02,0x00,0x5c,0xe5,0x88,0xe0,0x9f,0xe5,0x01,0x20,0x5c,0xe5,
0x3f,0x30,0x00,0xe2,0x03,0x20,0xce,0xe7,0x80,0x00,0x10,0xe3,0x00,0x30,0xde,0x15,
0x00,0x20,0xa0,0x13,0x03,0xe1,0xa0,0x11,0x04,0x00,0x00,0x1a,0x06,0x00,0x00,0xea,
0x60,0x30,0x9f,0xe5,0x02,0x30,0xd3,0xe7,0x02,0x30,0xc1,0xe7,0x01,0x20,0x82,0xe2,
0x0e,0x00,0x52,0xe1,0xf9,0xff,0xff,0x3a,0x0e,0x10,0x81,0xe0,0x40,0x00,0x10,0xe3,
0x02,0xc0,0x8c,0xe2,0xea,0xff,0xff,0x0a,0x3c,0x30,0x9f,0xe5,0x00,0x00,0xa0,0xe3,
0x00,0x10,0x83,0xe5,0x00,0x00,0x81,0xe5,0x01,0x2c,0xa0,0xe3,0x2c,0x10,0x9f,0xe5,
0x0f,0xe0,0xa0,0xe1,0x0a,0xf0,0xa0,0xe1,0x08,0xd0,0x8d,0xe2,0x0e,0xf0,0xa0,0xe1,
0x54,0x41,0x00,0x00,0x5c,0x41,0x00,0x00,0xbe,0x41,0x00,0x00,0xfe,0x41,0x00,0x00,
0x60,0x41,0x00,0x00,0x62,0x41,0x00,0x00,0x00,0x42,0x00,0x00,0x14,0x42,0x00,0x00,
0xd1,0x07,0x00,0x00,0x00,0x80,0x00,0x00,0x00,0x00,0x00,0x01,0x2e,0x0d,0x0a,0x00,
0x00,0x05,0x04,0x01,0x06,0x41,0xc7,0x54,0x04,0x05,0x06,0x42,0x0b,0x01,0x0e,0x40,
0xcf,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0xda,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0xff,0x0f,0x00,0x00,0x00,0x00,
0x00,0x00,0xda,0x00,0x00,0x00,0x00,0x10,0x00,0x00,0x00,0x10,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x55,0xaa,
};

static int hup = 0;
static void hupsig(int x) {
	hup = 1;
}

static void poke8(unsigned int adr, unsigned char dat) {
	if (!cvspiregs) *(unsigned char *)adr = dat;
	else {
		if (adr & 0x1) {
			cvgpioregs[0] = (0x2<<15|1<<17);
			poke16(adr, dat << 8);
		} else {
			cvgpioregs[0] = (0x2<<15|1<<3);
			poke16(adr, dat);
		}
		cvgpioregs[0] = (0x2<<15|1<<17|1<<3);
	}

}


static void poke16(unsigned int adr, unsigned short dat) {
	unsigned int dummy = 0;

	if (!cvspiregs) {
		*(unsigned short *)adr = dat;
	} else asm volatile (
		"mov %0, %1, lsl #18\n"
		"orr %0, %0, #0x800000\n"
		"orr %0, %0, %2, lsl #3\n"
		"3: ldr r1, [%3, #0x64]\n"
		"cmp r1, #0x0\n"
		"bne 3b\n"
		"2: str %0, [%3, #0x50]\n"
		"1: ldr r1, [%3, #0x64]\n"
		"cmp r1, #0x0\n"
		"beq 1b\n"
		"ldr %0, [%3, #0x58]\n"
		"ands r1, %0, #0x1\n"
		"moveq %0, #0x0\n"
		"beq 3b\n"
		: "+r"(dummy) : "r"(adr), "r"(dat), "r"(cvspiregs) : "r1","cc"
	);
}


static inline void 
poke16_stream(unsigned int adr, unsigned short *dat, unsigned int len) {
	volatile unsigned int *spi = cvspiregs;
	unsigned int cmd, ret, i, j;

	spi[0x4c/4] = 0x0;	/* continuous CS# */
	cmd = (adr<<18) | 0x800000 | (dat[0]<<3) | (dat[1]>>13);
	do {
		spi[0x50/4] = cmd;
		cmd = dat[1]>>13;
		while (spi[0x64/4] == 0);
		ret = spi[0x58/4];
		assert (spi[0x64/4] == 0); /* */
	} while (!(ret & 0x1));
	
	spi[0x40/4] = 0x80000c01; /* 16 bit mode */
	i = len - 1;
	len -= 6;
	dat++;

	for (j = 0; j < 4; j++) {
		spi[0x50/4] = (dat[0]<<3) | (dat[1]>>13);
		dat++;
	}

	while (len--) {
		spi[0x50/4] = (dat[0]<<3) | (dat[1]>>13);
		dat++;
		while (spi[0x64/4] == 0);
		spi[0x58/4]; 
		i--;
	} 

	spi[0x4c/4] = 0x4;	/* deassert CS# */
	spi[0x50/4] = dat[0]<<3;

	while (i) {
		while ((spi[0x64/4]) == 0);
		spi[0x58/4];
		i--;
	}

	spi[0x40/4] = 0x80000c02; /* 24 bit mode */

}


static unsigned short peek16(unsigned int adr) {
	unsigned short ret = 0;

	if (!cvspiregs) ret = *(unsigned short *)adr;
	else asm volatile (
		"mov %0, %1, lsl #18\n"
		"2: str %0, [%2, #0x50]\n"
		"1: ldr r1, [%2, #0x64]\n"
		"cmp r1, #0x0\n"
		"beq 1b\n"
		"ldr %0, [%2, #0x58]\n"
		"ands r1, %0, #0x10000\n"
		"bicne %0, %0, #0xff0000\n"
		"moveq %0, #0x0\n"
		"beq 2b\n" 
		: "+r"(ret) : "r"(adr), "r"(cvspiregs) : "r1", "cc"
	);

	return ret;

}


static inline
void peek16_stream(unsigned int adr, unsigned short *dat, unsigned int len) {
	unsigned int dummy = 0;

	asm volatile(
		"mov %0, #0x0\n"
		"str %0, [%4, #0x4c]\n"
		"mov %1, %1, lsl #18\n"
		"orr %1, %1, #(1<<15)\n"
		"2: str %1, [%4, #0x50]\n"
		"1: ldr %0, [%4, #0x64]\n"
		"cmp %0, #0x0\n"
		"beq 1b\n"
		"ldr %0, [%4, #0x58]\n"
		"tst %0, #0x10000\n"
		"beq 2b\n"
		"\n"
		"3:\n"
		"strh %0, [%3], #0x2\n"
		"mov %0, #0x80000001\n"
		"orr %0, %0, #0xc00\n"
		"str %0, [%4, #0x40]\n"
		"ldr %0, [%4, #0x40]\n"
		"str %1, [%4, #0x50]\n"
		"str %1, [%4, #0x50]\n"
		"sub %2, %2, #0x4\n"
		"4: str %1, [%4, #0x50]\n"
		"5: ldr %0, [%4, #0x64]\n"
		"cmp %0, #0x0\n"
		"beq 5b\n"
		"ldr %0, [%4, #0x58]\n"
		"subs %2, %2, #0x1\n"
		"strh %0, [%3], #0x2\n"
		"bne 4b\n"
		"\n"
		"mov %0, #0x4\n"
		"str %0, [%4, #0x4c]\n"
		"mov %1, #0x0\n"
		"str %1, [%4, #0x50]\n"
		"6: ldr %0, [%4, #0x64]\n"
		"cmp %0, #0x0\n"
		"beq 6b\n"
		"ldr %0, [%4, #0x58]\n"
		"strh %0, [%3], #0x2\n"
		"\n"
		"7: ldr %0, [%4, #0x64]\n"
		"cmp %0, #0x0\n"
		"beq 7b\n"
		"ldr %0, [%4, #0x58]\n"
		"strh %0, [%3], #0x2\n"
		"\n"
		"8: ldr %0, [%4, #0x64]\n"
		"cmp %0, #0x0\n"
		"beq 8b\n"
		"ldr %0, [%4, #0x58]\n"
		"strh %0, [%3], #0x2\n"
		"\n"
		"mov %0, #0x80000002\n"
		"orr %0, %0, #0xc00\n"
		"str %0, [%4, #0x40]\n"
		: "+r"(dummy), "+r"(adr), "+r"(len), "+r"(dat)
		: "r"(cvspiregs)
		: "cc", "memory"
	);
}


static void reservemem(void) {
	char dummy[32768];
	int i, pgsize;
	FILE *maps;

	pgsize = getpagesize();
	mlockall(MCL_CURRENT|MCL_FUTURE);
	for (i = 0; i < sizeof(dummy); i += 4096) {
		dummy[i] = 0;
	}

	maps = fopen("/proc/self/maps", "r"); 
	if (maps == NULL) {
		perror("/proc/self/maps");
		exit(1);
	}
	while (!feof(maps)) {
		size_t s, e, x;
		char perms[16];
		int r = fscanf(maps, "%zx-%zx %s %*x %zx:%*x %*d",
		  &s, &e, perms, &x);
		if (r == EOF) break;
		assert (r == 4);

		while ((r = fgetc(maps)) != '\n') if (r == EOF) break;
		assert(s <= e && (s & 0xfff) == 0);
		if (perms[0] == 'r' && perms[3] == 'p' && x != 1)
		  while (s < e) {
			volatile unsigned char *ptr = (unsigned char *)s;
			unsigned char d;
			d = *ptr;
			if (perms[1] == 'w') *ptr = d;
			s += pgsize;
		}
	}
}


static int semid = -1;
static int sbuslocked = 0;
static void sbuslock(void) {
	int r;
	struct sembuf sop;
	if (semid == -1) {
		key_t semkey;
		reservemem();
		semkey = 0x75000000;
		semid = semget(semkey, 1, IPC_CREAT|IPC_EXCL|0777);
		if (semid != -1) {
			sop.sem_num = 0;
			sop.sem_op = 1;
			sop.sem_flg = 0;
			r = semop(semid, &sop, 1);
			assert (r != -1);
		} else semid = semget(semkey, 1, 0777);
		assert (semid != -1);
	}
	sop.sem_num = 0;
	sop.sem_op = -1;
	sop.sem_flg = SEM_UNDO;
	r = TEMP_FAILURE_RETRY(semop(semid, &sop, 1));
	assert (r == 0);
	cvgpioregs[0] = (2<<15|1<<17|1<<3);
	sbuslocked = 1;
	if (hup) {
		hup = 0;
		poke16(0x0, opt_lun << 8);
	}

}


static void sbusunlock(void) {
	struct sembuf sop = { 0, 1, SEM_UNDO};
	int r;
	if (!sbuslocked) return;
	r = semop(semid, &sop, 1);
	assert (r == 0);
	sbuslocked = 0;
}


static void sbuspreempt(void) {
	int r;
	r = semctl(semid, 0, GETNCNT);
	assert (r != -1);
	if (r) {
		sbusunlock();
		sched_yield();
		sbuslock();
	}
}


static inline void wren(void) {
	poke8(0xc, 0x6);
}


static inline void wrdi(void) {
	poke8(0xc, 0x4);
}


static inline int rdsr(void) {
	poke8(0x8, 0x5);
	return peek16(0xc) >> 8;
}


static inline void wrsr(unsigned char sr) {
	poke16(0xc, 0x100|sr);
}


static inline void se(unsigned int sector) {
	poke16(0x8, 0x2000|(sector>>16));
	poke16(0xc, sector);
}


static inline void be(unsigned int block) {
	poke16(0x8, 0xd800|(block>>16));
	poke16(0xc, block);
}


unsigned char ce_opcode = 0x60;
static inline void ce(void) {
	poke8(0xc, ce_opcode);
}


static inline void rdid(int *manufacturer, int *devid) {
	int i, j;

	poke8(0x8, 0x9f);
	i = peek16(0x8);
	if (manufacturer) *manufacturer = i >> 8;
	j = peek16(0xc);
	if (devid) *devid = ((i & 0xff) << 8) | (j >> 8);
}


int sst_special = 0;
static void pp(unsigned int adr, unsigned char *dat, unsigned int len) {
	unsigned short *d;
	int i;
	if (sst_special) {
		d = (unsigned short *)dat;
		poke16(0x8, 0xad00|(adr>>16));
		poke16(0x8, adr);
		poke16(0xc, *d);
		for(i=1; i<len/2; i++) {
			while ((rdsr() & 0x1) == 0x1) {};
			poke8(0x8, 0xad);
			poke16(0xc, d[i]);
		}
		while ((rdsr() & 0x1) == 0x1) {};
		wrdi();
		return;
	}
	poke16(0x8, 0x200|(adr>>16));
	poke16(0x8, adr);
	assert (((unsigned int)dat & 0x1) == 0);
	assert ((len & 0x1) == 0);
	poke16_stream(0x8, (unsigned short *)dat, (len / 2) - 1);
	poke16(0xc, *(unsigned short *)(&dat[len - 2]));
}


static void fastread(unsigned int adr, unsigned char *dat, unsigned int len) {
	if (len == 0) return;
	poke16(0x8, 0xb00|(adr>>16));
	poke16(0x8, adr);
	poke8(0x8, 0x0);
	assert (((unsigned int)dat & 0x1) == 0);
	assert ((len & 0x1) == 0);
	peek16_stream(0xa, (unsigned short *)dat, (len / 2) - 1);
	*(unsigned short *)(&dat[len - 2]) = peek16(0xc);
}


static unsigned char *cache = NULL;
static int cache_startsec = 0;
static int cache_lastsec = 0;
static inline int
iscached(unsigned int sec, unsigned int n) {
	int lastsec;

	if (!cache) return 0;
	if (cache_startsec <= sec && sec <= cache_lastsec) {
		lastsec = sec + n - 1;
		if (lastsec <= cache_lastsec) return n;
		else return cache_lastsec - sec + 1;
	} else return 0;
}


static inline void
update_cache(unsigned int sec, unsigned char *d) {
	if (!cache) return;
	if (cache_startsec <= sec && sec <= cache_lastsec) {
		memcpy(&cache[(sec - cache_startsec)<<9], d, 512);
	}

}


static inline int
spiflashread(unsigned int sec, unsigned char *d, unsigned int n) {
	unsigned char *origd;
	int i, j, orign, origsec;
	int nc;

	if ((sec + n) > size) return 1;
	
	nc = iscached(sec, n);

	if (nc) {
		memcpy(d, &cache[(sec - cache_startsec)<<9], (nc<<9));
		sec += nc;
		n -= nc;
		d += nc<<9;
	} 
	if (n) {
		origd = d;
		orign = n;
		origsec = sec;
		while (n > 16) {
			fastread(sec << 9, d, 16 << 9);
			sec += 16;
			n -= 16;
			d += (16 << 9);
			sbuspreempt();
		}
		fastread(sec << 9, d, n << 9);
		if (verify) for (i = 0; i < orign; i++) {
			unsigned char *dd = &origd[i<<9];
			int csum = 0;
			int s;
			for (j = 0; j < 512; j++) csum += *dd++;
			csum = 0x80 | (csum & 0x7f);
			s = i + origsec;
			if ((csumtbl[s] & 0x80) && (csum != csumtbl[s])) {
				sbusunlock();
				fprintf(stderr, "verify_fail=%d\n", s);
				sbuslock();
				return 1; /* failure! */
			}
			else csumtbl[s] = csum;
		}
	}
	return 0;
}


static int
do_write(unsigned int sec, unsigned char *d, unsigned int n) {
	unsigned short *sbuf[2048];
	unsigned char *buf = (unsigned char *)sbuf;
	int i, j;

	if (n == 0) return 0;

again:
	if ((sec & 0x7f) == 0 && n >= 128) {
		wren();
		be(sec << 9);
		if (verify) for (i = 0; i < 128; i++) {
			int csum = 0;
			unsigned char *dd = &d[i<<9];
			for (j = 0; j < 512; j++) csum += *dd++;
			csumtbl[sec + i] = 0x80 | csum;
		}
		while ((rdsr() & 0x1) == 0x1) {
			sbusunlock();
			usleep(100000);
			sbuslock();
		}
		for (i = 0; i < 128; i++) {
			wren();
			pp(sec << 9, d, 256);
			update_cache(sec, d);
			d += 256;
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
			wren();
			pp((sec << 9) + 256, d, 256);
			sec++;
			n--;
			d += 256;
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
		}
	} else if ((sec & 0x7) == 0 && n >= 8) {
		wren();
		se(sec << 9);
		if (verify) for (i = 0; i < 8; i++) {
			int csum = 0;
			unsigned char *dd = &d[i<<9];
			for (j = 0; j < 512; j++) csum += *dd++;
			csumtbl[sec + i] = 0x80 | csum;
		}
		while ((rdsr() & 0x1) == 0x1) {
			sbusunlock();
			usleep(10000);
			sbuslock();
		}
		for (i = 0; i < 8; i++) {
			wren();
			pp(sec << 9, d, 256);
			update_cache(sec, d);
			d += 256;
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
			wren();
			pp((sec << 9) + 256, d, 256);
			sec++;
			n--;
			d += 256;
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
		}
	} else { /* read-modify-write */
		int erasefirst = 0;
		int s = sec & ~0x7;
		unsigned char *c = buf;
		int r = spiflashread(s, c, 8); // read 4k
		int is, ie;
		if (r) return r;

		is = ie = sec;
		do {
			unsigned int csum = 0;
			unsigned char *b = &c[(sec & 0x7) << 9];
			for (i = 0; i < 512; i++) {
				/* any bits not changing to 0? */
				if (~b[i] & *d) erasefirst = 1;
				csum += *d;
				b[i] = *d++;
			}
			if (verify) csumtbl[sec] = 0x80 | csum;
			sec++;
			n--;
			ie++;
		} while (n && (sec & 0x7) != 0);

		if (erasefirst) {
			wren();
			se(s << 9);
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
			is = s;
			ie = s + 8;
		}

		c = &c[(is & 0x7) << 9];
		for (i = is; i < ie; i++) {
			wren();
			pp(i << 9, c, 256);
			update_cache(i, c);
			c += 256;
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
			wren();
			pp((i << 9) + 256, c, 256);
			c += 256;
			while ((rdsr() & 0x1) == 0x1) sbuspreempt();
		}
	}

	if (n != 0) goto again;
	return 0;

}


static int
spiflashwrite(unsigned int sec, unsigned char *d, unsigned int n) {
	unsigned char *buf;
	unsigned int *update, *erase;
	int i, ssec, r, reread = 0;

	erase = malloc((n>>3) + 4);
	assert(erase != NULL);
	update = malloc((n>>3) + 4);
	assert(update != NULL);
	buf = malloc(n<<9);
	assert(buf != NULL);
	r = spiflashread(sec, buf, n);
	if (r) {
		free(buf);
		free(update);
		free(erase);
		return r;
	}
	cache = buf;
	cache_startsec = sec;
	cache_lastsec = sec + n - 1;
	bzero(erase, (n>>3) + 4);
	bzero(update, (n>>3) + 4);
	for (i = 0; i < (n<<9);) {
		if (buf[i] != d[i]) {
			update[i>>14] |= (1<<((i>>9) & 0x1f));
			reread = 1;
		}
		if (~buf[i] & d[i]) {
			erase[i>>14] |= (1<<((i>>9) & 0x1f));
			i = ((i >> 9) + 1) << 9; // skip to next 512
		} else i++;
	}

	for (ssec = -1, i = 0; i < n; i++) {
		int doupdate;
		int doerase;
		doupdate = update[i>>5] & (1<<(i & 0x1f));
		doerase = erase[i>>5] & (1<<(i & 0x1f));
		if (doerase && ssec == -1) {
			ssec = i;
		} else if (!doerase && ssec >= 0) {
			if (doupdate && ((sec + i) & 0x7)) continue;
			r |= do_write(ssec + sec, &d[ssec<<9], i - ssec);
			ssec = -1;
		} 
		if (doupdate && ssec == -1) {
			r |= do_write(sec + i, &d[i<<9], 1);
		}
	}

	if (ssec >= 0) {
		r |= do_write(sec + ssec, &d[ssec<<9], n - ssec);
	}

	cache = NULL;
	/* One more to verify */
	if (verify && reread) r |= spiflashread(sec, buf, n);
	free(buf);
	free(update);
	free(erase);
	return r;

}


void usage(char **argv) {
	fprintf(stderr, "Usage: %s [OPTION] ...\n"
	  "Technologic Systems SPI flash manipulation.\n"
	  "\n"
	  "General options:\n"
	  "  -R, --read=N            Read N blocks of flash to stdout\n"
	  "  -W, --write=N           Write N blocks to flash\n"
	  "  -x, --writeset=BYTE     Write BYTE as value (default 0)\n"
	  "  -i, --writeimg=FILE     Use FILE as file to write to flash\n"
	  "  -t, --writetest         Run write speed test\n"
	  "  -r, --readtest          Run read speed test\n"
	  "  -n, --random=SEED       Do random seeks for tests\n"
	  "  -z, --blocksize=SZ      Use SZ bytes each sdread/sdwrite call\n"
	  "  -k, --seek=SECTOR       Seek to 512b sector number SECTOR\n"
	  "  -V, --verify            Verify reads and writes\n"
	  "  -e, --erase             Erase entire device\n"
	  "  -d, --nbdserver=NBDSPEC Run NBD userspace block driver server\n"
	  "  -Q, --stats             Print NBD server stats\n"
	  "  -I, --bind=IPADDR       Bind NBD server to IPADDR\n"
	  "  -l, --lun=N             Use chip number N\n"
	  "  -P, --printmbr          Print MBR and partition table\n"
	  "  -M, --setmbr            Write MBR from environment variables\n"
	  "  -h, --help              This help\n"
	  "\n"
	  "When running a NBD server, NBDSPEC is a comma separated list of\n"
	  "devices and partitions for the NBD servers starting at port 7525.\n"
	  "e.g. \"lun0:part1,lun1:disc\" corresponds to 2 NBD servers, one at port\n"
	  "7525 serving the first partition of chip #0, and the other at TCP\n"
	  "port 7526 serving the whole disc device of chip #1.\n",
	  argv[0]
	);
}


static inline
int get_ptbl_offs(int part, int *type, int *sz) {
	unsigned char mbr[512];
	int ret;

	sbuslock();
	ret = spiflashread(0, mbr, 1);
	sbusunlock();
	if (ret != 0) return -1;

	part--;
	ret = mbr[0x1be + (16 * part) + 8];
	ret |= mbr[0x1be + (16 * part) + 9] << 8;
	ret |= mbr[0x1be + (16 * part) + 10] << 16;
	ret |= mbr[0x1be + (16 * part) + 11] << 24;

	if (type) *type = mbr[0x1be + (16 * part) + 4];
	if (sz) {
		*sz = mbr[0x1be + (16 * part) + 12];
		*sz |= mbr[0x1be + (16 * part) + 13] << 8;
		*sz |= mbr[0x1be + (16 * part) + 14] << 16;
		*sz |= mbr[0x1be + (16 * part) + 15] << 24;
	}

	return ret;
}


static
int setmbr(void) {
	unsigned char mbr[512];
	unsigned int sz, offs;
	int ret, i;
	char var[32];
	char *e;
	
	sbuslock();
	ret = spiflashread(0, mbr, 1);
	sbusunlock();
	if (ret) return ret;
	if (mbr[510] != 0x55 || mbr[511] != 0xaa) memcpy(mbr, cavium_mbr, 512);
	else memcpy(mbr, cavium_mbr, 446);

	for (i = 0; i < 4; i++) {
		sprintf(var, "part%d_offs", i+1);
		e = getenv(var);
		if (e) {
			offs = strtoul(e, NULL, 0);
			mbr[0x1be + (16 * i) + 8] = offs & 0xff;
			mbr[0x1be + (16 * i) + 9] |= (offs>>8) & 0xff;
			mbr[0x1be + (16 * i) + 10] |= (offs>>16) & 0xff;
			mbr[0x1be + (16 * i) + 11] |= offs>>24;
		}
		sprintf(var, "part%d_sz", i+1);
		e = getenv(var);
		if (e) {
			sz = strtoul(e, NULL, 0);
			mbr[0x1be + (16 * i) + 12] = sz & 0xff;
			mbr[0x1be + (16 * i) + 13] |= (sz>>8) & 0xff;
			mbr[0x1be + (16 * i) + 14] |= (sz>>16) & 0xff;
			mbr[0x1be + (16 * i) + 15] |= sz>>24;
		}
		sprintf(var, "part%d_type", i+1);
		e = getenv(var);
		if (e) mbr[0x1be + (16 * i) + 4] = strtoul(e, NULL, 0);
	}
	sbuslock();
	spiflashwrite(0, mbr, 1);
	sbusunlock();
	return 0;
}



static inline
void nbdwrite(int fd, unsigned int sector, int len) {
	int ret;
	unsigned char *buf = nbdbuf;

	while (len > nbdbufsz) {
		nbdwrite(fd, sector, nbdbufsz);
		sector += nbdbufsz;
		len -= nbdbufsz;
	}

	sbuslock();
	ret = spiflashread(sector, buf, len);
	sbusunlock();
	assert (ret == 0);

	len = len << 9;
	while (len) {
		ret = TEMP_FAILURE_RETRY(write(fd, buf, len));
		assert (ret > 0);
		len -= ret;
		buf += ret;
	}
}


static inline
void nbdread(int fd, unsigned int sector, int len) {
	int ret;
	unsigned char *buf = nbdbuf;
	int rem;

	while (len > nbdbufsz) {
		nbdread(fd, sector, nbdbufsz);
		sector += nbdbufsz;
		len -= nbdbufsz;
	}

	rem = len << 9;
	while (rem) {
		ret = TEMP_FAILURE_RETRY(read(fd, buf, rem));
		assert (ret > 0);
		rem -= ret;
		buf += ret;
	}

	sbuslock();
	ret = spiflashwrite(sector, nbdbuf, len);
	sbusunlock();
	assert (ret == 0);
}


static inline
int xread(int fd, void *d, int len) {
	int olen = len;
	unsigned char *buf = d;

	if (buf == NULL) {
		buf = nbdbuf;
		while (len > (nbdbufsz << 9)) {
			xread(fd, buf, nbdbufsz);
			len -= nbdbufsz;
		}
		if (len) xread(fd, buf, len);
	}

	while (len > 0) {
		int x = TEMP_FAILURE_RETRY(read(fd, buf, len));
		if (x == 0 || x < 0) return 0;
		buf += x;
		len -= x;
	}
	return olen;
}


static inline
int xwrite(int fd, void *d, int len) {
	int olen = len;
	unsigned char *buf = d;

	while (len > 0) {
		int x = TEMP_FAILURE_RETRY(write(fd, buf, len));
		if (x == 0 || x < 0) return 0;
		buf += x;
		len -= x;
	}
	return olen;
}


static 
void nbdserver(const char *arg, struct in_addr iface) {
	int i, n, maxfd = 0;
	int infd[8], remfd[8];
	int offs[8];
	int numnbd;
	// struct sdcore *sdcs[8], *sdc_wpending = NULL;
	struct sockaddr_in sa;
	struct nbd_request req;
	struct nbd_reply resp;
	unsigned int reqmagic;
	fd_set rfds;
	key_t shmkey;
	int shmid;
	volatile unsigned long long *sbus_shm;


	FD_ZERO(&rfds);

	numnbd = 0;
	while(*arg) {
		if (*arg == ',') arg++;
		if (strncmp(arg, "lun", 3) != 0) break;
		arg += 3;
		if (!isdigit(*arg)) break;
		n = *arg - '0';
		assert(n == 0); /* not yet ready for lun 1 */
		// if (sd->sd_lun == n) sdcs[numnbd] = sd;
		// else sdcs[numnbd] = NULL;
		arg++;
		if (*arg != ':') break;
		arg++;
		if (strncmp(arg, "part", 4) == 0) {
			arg += 4;
			if (!isdigit(*arg)) break;
			offs[numnbd] = -(*arg - '0');
			arg++;
		} else if (strncmp(arg, "disc", 4) == 0) {
			arg += 4;
			offs[numnbd] = 0;
		} else break;
		numnbd++;
	}

	if (*arg != 0) {
		fprintf(stderr, "NBDSPEC parse error\n");
		exit(9);
	}

	sa.sin_family = AF_INET;
	sa.sin_addr.s_addr = iface.s_addr;
	for (i = 0; i < numnbd; i++) {
		int r, sk, x = 1;
		/* TCP server socket */
		sa.sin_port = htons(7525 + i);
		sk = socket(PF_INET, SOCK_STREAM, 0);
		setsockopt(sk, SOL_SOCKET, SO_REUSEADDR, &x, 4);
		assert(sk != -1);
		r = bind(sk, (struct sockaddr *)&sa, sizeof(sa));
		if (r) {
			perror("bind");
			exit(1);
		}
		r = listen(sk, 5);
		assert(r != -1);
		r = fcntl(sk, F_SETFL, O_NONBLOCK);
		assert(r != -1);
		if (sk > maxfd) maxfd = sk;
		FD_SET(sk, &rfds);
		infd[i] = sk;

		remfd[i] = -1;
	}
	resp.magic[0] = 0x67;
	resp.magic[1] = 0x44;
	resp.magic[2] = 0x66;
	resp.magic[3] = 0x98;
	reqmagic = htonl(0x25609513);
	daemon(0, 0);

	signal(SIGHUP, hupsig);
	signal(SIGPIPE, SIG_IGN);
	shmkey = 0x75000000;
	shmid = shmget(shmkey, 0x1000, IPC_CREAT|0666);
	assert(shmid != -1);
	sbus_shm = shmat(shmid, NULL, 0);
	sbus_shm += 32;
	sbus_shm[0] = getpid();

superloop_start:
	select(maxfd + 1, &rfds, NULL, NULL, NULL);

	for (i = 0; i < numnbd; i++) {
		int r;
		if (remfd[i] == -1) continue;

		if (FD_ISSET(remfd[i], &rfds)) {
			unsigned int sec, len;
			req.magic = 0;
			r = xread(remfd[i], &req, sizeof(req));
			if (r == 0) goto eof;
			assert (r == sizeof(req));
			assert (req.magic == reqmagic);

			resp.error = 0;

			/* lazy partition table parse */
			if (offs[i] < 0 && !resp.error) {
				r = get_ptbl_offs(-offs[i], NULL, NULL);
				if (r > 0) offs[i] = r;
				else resp.error = htonl(1);
			}

			memcpy(resp.handle, req.handle, 8);

			len = ntohl(req.len);
			assert ((len & 0x1ff) == 0);
			len = len >> 9;
			sec = (ntohl(req.fromhi) & 0x1ff) << 23;
			sec |= ntohl(req.fromlo) >> 9;
			sec += offs[i];

			if ((sec + len) > size) {
				fprintf(stderr, 
				  "beyond end of device: %x-%x\n", 
				  sec, sec + len - 1);
				resp.error = htonl(1);
				sbus_shm[5]++;
			}

			if (resp.error) {
				if (req.type[3] == 1) {
					fprintf(stderr, "err write %d\n", len);
					xread(remfd[i], NULL, len << 9);
				}
				r = xwrite(remfd[i], &resp, sizeof(resp));
				if (r == 0) goto eof;
				assert (r == sizeof(resp));
				continue;
			}

			if (req.type[3] == 0) { /* READ */
				r = xwrite(remfd[i], &resp, sizeof(resp));
				if (r == 0) goto eof;
				assert (r == sizeof(resp));
				nbdwrite(remfd[i], sec, len);
				sbus_shm[1]++;
				sbus_shm[2] += len;
			} else if (req.type[3] == 1) { /* WRITE */
				nbdread(remfd[i], sec, len);
				sbus_shm[3]++;
				sbus_shm[4] += len;
				r = xwrite(remfd[i], &resp, sizeof(resp));
				if (r == 0) goto eof;
				assert (r == sizeof(resp));
			} else goto eof;

		} else FD_SET(remfd[i], &rfds);

		continue;

eof:
		shutdown(remfd[i], SHUT_RDWR);
		FD_CLR(remfd[i], &rfds);
		close(remfd[i]);
		remfd[i] = -1;
		
	}

	for (i = 0; i < numnbd; i++) {
		/* new connection requests pending accept? */
		if (FD_ISSET(infd[i], &rfds)) {
			int r, sk, tos = IPTOS_LOWDELAY;
			int x;
			char d[128] = 
			  {0x00, 0x00, 0x42, 0x02, 0x81, 0x86, 0x12, 0x53};
			struct linger l;
			if (remfd[i] != -1) {
				shutdown(remfd[i], SHUT_RDWR);
				FD_CLR(remfd[i], &rfds);
				close(remfd[i]);
				remfd[i] = -1;
			}
			sk = accept(infd[i], NULL, 0);
			if (sk == -1) {
				FD_SET(infd[i], &rfds);
				continue;
			}
			setsockopt(sk, IPPROTO_IP, IP_TOS, &tos, 4);
			x = 1;
			setsockopt(sk, IPPROTO_TCP, TCP_NODELAY, &x, 4);
			setsockopt(sk, SOL_SOCKET, SO_KEEPALIVE, &x, 4);
			setsockopt(sk, SOL_SOCKET, SO_OOBINLINE, &x, 4);
			l.l_onoff = 0;
			l.l_linger = 0;
			setsockopt(sk, SOL_SOCKET, SO_LINGER, &l, sizeof(l));
			if (sk > maxfd) maxfd = sk;
			FD_SET(sk, &rfds);
			remfd[i] = sk;
			r = xwrite(sk, "NBDMAGIC", 8);
			assert (r == 8);
			r = xwrite(sk, d, 8);
			assert (r == 8);
			/* size */
			d[0] = 0; d[1] = 0; d[2] = 0; d[3] = 0;
			d[4] = 0; d[5] = 0x40; d[6] = 0; d[7] = 0;
			if (size == 0x800000 / 512) d[5] = 0x80;
			else assert(0);
			r = xwrite(sk, d, 8);
			assert (r == 8);
			bzero(d, 128);
			r = xwrite(sk, d, 128);
			assert (r == 128);
		} else {
			FD_SET(infd[i], &rfds);
		}
	}

	goto superloop_start;

}


int main(int argc, char **argv) {
	int devmem, i, c, ret, partseek;
	int manu, dev;
	int opt_writetest = 0, opt_blocksz = 1;
	int opt_readtest = 0, opt_read = 0, opt_readblks = 0;
	int opt_writeset = 0, opt_write = 0, opt_writeblks = 0;
	int opt_seek = 0, opt_erase = 0, opt_stats = 0;
	int opt_nbdserver = 0;
	struct in_addr opt_bind = { INADDR_ANY };
	char *opt_nbdarg = NULL;
	int opt_random = 0, opt_setmbr = 0, opt_printmbr = 0;
	unsigned int sizemask, randomseed = 0;
	FILE *ifile = NULL;
	static struct option long_options[] = {
	  { "printmbr", 0, 0, 'P' },
	  { "setmbr", 0, 0, 'M' },
	  { "stats", 0, 0, 'Q' },
	  { "bind", 1, 0, 'I' },
	  { "writetest", 0, 0, 't' },
	  { "writeset", 1, 0, 'x' },
	  { "writeimg", 1, 0, 'i' },
	  { "seek", 1, 0, 'k' },
	  { "readtest", 0, 0, 'r' },
	  { "read", 1, 0, 'R' },
	  { "random", 1, 0, 'n' },
	  { "write", 1, 0, 'W' },
	  { "blocksize", 1, 0, 'z' },
	  { "verify", 0, 0, 'V' },
	  { "erase", 0, 0, 'e' },
	  { "nbdserver", 1, 0, 'd' },
	  { "lun", 1, 0, 'l' },
	  { "help", 0, 0, 'h' },
	  { 0, 0, 0, 0 }
	};

	for (i = 0; i < 3; i++) if (fcntl(i, F_GETFD) == -1)
	  dup2(i ? i - 1 : open("/dev/null", O_RDWR), i);     

	while((c = getopt_long(argc, argv,
	  "Vetx:i:k:rR:n:W:z:d:l:hI:QMP", long_options, NULL)) != -1) {
		switch (c) {
		case 'M':
			opt_setmbr = 1;
			break;
		case 'P':
			opt_printmbr = 1;
			break;
		case 'Q':
			opt_stats = 1;
			break;
		case 'I':
			i = inet_aton(optarg, &opt_bind);
			if (i == 0) {
				fprintf(stderr, "Bad arg: %s\n", optarg);
				return 3;
			}
			break;
		case 'l':
			opt_lun = strtoul(optarg, NULL, 0);
			break;
		case 'e':
			opt_erase = 1;
			break;
		case 'V':
			verify = 1;
			break;
		case 'd':
			opt_nbdserver = 1;
			opt_nbdarg = strdup(optarg);
			break;
		case 'k':
			if (strcmp(optarg, "kernel") == 0)
			  opt_seek = -32;
			else if (strcmp(optarg, "initrd") == 0)
			  opt_seek = -33;
			else if (optarg[0] == 'p' && optarg[1] == 'a' &&
			  optarg[2] == 'r' && optarg[3] == 't')
			  opt_seek = -1 * (optarg[4] - '0');
			else opt_seek = strtoul(optarg, NULL, 0);
			break;
		case 'i':
			i = strlen(optarg);
			if (strcmp("-", optarg) == 0) ifile = stdin;
			else if (strcmp(".bz2", &optarg[i - 4]) == 0) {
				char b[512];
				snprintf(b, 512, "exec bunzip2 -c '%s'", optarg);
				ifile = popen(b, "r");
			} else ifile = fopen(optarg, "r");
			if (!ifile) {
				perror(optarg);
				return 3;
			}
			if (opt_writeblks == 0) opt_writeblks = INT_MAX;
			opt_write = 1;
			break;
		case 'n':
			randomseed = strtoul(optarg, NULL, 0);
			fprintf(stderr, "randomseed=0x%x\n", randomseed);
			opt_random = 1;
			break;
		case 'x':
			opt_writeset = strtoul(optarg, NULL, 0);
			break;
		case 'W':
			opt_write = 1;
			opt_writeblks = strtoul(optarg, NULL, 0);
			break;
		case 'R':
			opt_read = 1;
			opt_readblks = strtoul(optarg, NULL, 0);
			break;
		case 'r':
			opt_readtest = 1;
			break;
		case 't':
			opt_writetest = 1;
			break;
		case 'z':
			opt_blocksz = strtoul(optarg, NULL, 0) / 512;
			break;
		case 'h':
		default:
			usage(argv);
			return(1);
		}
	} 

	if (opt_stats) {
		key_t shmkey;
		int shmid;
		unsigned long long *sbus_shm;

		shmkey = 0x75000000;
		shmid = shmget(shmkey, 0x1000, IPC_CREAT|0666);
		assert(shmid != -1);
		sbus_shm = shmat(shmid, NULL, 0);
		sbus_shm += 32;

		errno = 0;
		if (getpriority(PRIO_PROCESS, sbus_shm[0]) == -1 &&
		  errno == ESRCH) sbus_shm[0] = 0;

		fprintf(stderr, "nbdpid=%lld\n", sbus_shm[0]);
		fprintf(stderr, "nbd_readreqs=%lld\n", sbus_shm[1]);
		fprintf(stderr, "nbd_read_blks=%lld\n", sbus_shm[2]);
		fprintf(stderr, "nbd_writereqs=%lld\n", sbus_shm[3]);
		fprintf(stderr, "nbd_write_blks=%lld\n", sbus_shm[4]);
		fprintf(stderr, "nbd_seek_past_eof_errs=%lld\n", sbus_shm[5]);

		return 0;
	}
	
	devmem = open("/dev/mem", O_RDWR|O_SYNC);
	assert(devmem != -1);
	cvspiregs = (unsigned int *) mmap(0, 4096,
	  PROT_READ | PROT_WRITE, MAP_SHARED, devmem, 0x71000000);
	cvgpioregs = (unsigned int *) mmap(0, 4096,
	  PROT_READ | PROT_WRITE, MAP_SHARED, devmem, 0x7c000000);

	sbuslock();
	cvspiregs[0x64 / 4] = 0x0; /* RX IRQ threahold 0 */
	cvspiregs[0x40 / 4] = 0x80000c02; /* 24-bit mode, no byte swap */
	cvspiregs[0x60 / 4] = 0x0; /* 0 clock inter-transfer delay */
	cvspiregs[0x6c / 4] = 0x0; /* disable interrupts */
	cvspiregs[0x4c / 4] = 0x4; /* deassert CS# */
	for (i = 0; i < 8; i++) cvspiregs[0x58 / 4];
	cvgpioregs[0] = (2<<15|1<<17|1<<3);
	poke8(0xc, 0); /* force CS# deassertion just in case */
	sbusunlock();
	fprintf(stderr, "lun=%d\n", opt_lun);
	sbuslock();
	poke16(0x0, opt_lun << 8);

	rdid(&manu, &dev);
	sbusunlock();
	fprintf(stderr, "manufacturer=0x%x\ndevice=0x%x\n", manu, dev);
	/* Hopefully Bob doesn't change flash chips on us */
	/* There was very little hope for that */
	if (manu == 0xc2 && dev == 0x2016) size = 0x400000 / 512;
	else if (manu == 0xc2 && dev == 0x2017) size = 0x800000 / 512;
	else if (manu == 0x20 && dev == 0xba17) { /* Micron */
		ce_opcode = 0xc7;
		size = 0x800000 / 512;
	} else if (manu == 0xbf && dev == 0x2541) { /* SST 16mbit */
		size = 0x200000 / 512;
		sst_special = 1;
	} else size = 0;
	fprintf(stderr, "sectors=%d\n", size);
	fprintf(stderr, "verify=%d\n", verify);
	if (sst_special && (opt_writetest || opt_write || opt_nbdserver)) {
		/* SST chip defaults to all blocks write-protected */
		wren();
		wrsr(0x80);
	}
	if (opt_writetest || opt_readtest || opt_read || opt_write ||
	  opt_nbdserver)
	  fprintf(stderr, "blocksize=%d\n", opt_blocksz * 512);
	sizemask = 0;
	for (i = 0; i < 32; i++) {
		if (size > (1 << (i + 1))) sizemask = (sizemask << 1) | 0x1;
		else break;
	}

	if (verify) {
		csumtbl = malloc(size);
		bzero(csumtbl, size);
	}

	if (opt_printmbr) {
		int ty, sz;
		for (i = 0; i < 4; i++) {
			fprintf(stderr, "part%d_offs=0x%x\n", i+1, 
			  get_ptbl_offs(i, &ty, &sz));
			fprintf(stderr, "part%d_sz=0x%x\n", i+1, sz);
			fprintf(stderr, "part%d_type=0x%x\n", i+1, ty);
		}
	}

	if (opt_setmbr) fprintf(stderr, "setmbr_ok=%d\n", setmbr() ? 0 : 1);

	if (opt_seek == -32) { /* kernel partition */
		int ty;
		partseek = 1;
		for (i = 0; i < 4; i++) {
			opt_seek = get_ptbl_offs(i, &ty, NULL);
			if (ty == 0xda) break;
		}
	} else if (opt_seek == -33) { /* initrd partition */
		int ty, np = 0;
		partseek = 1;
		for (i = 0; i < 4; i++) {
			opt_seek = get_ptbl_offs(i, &ty, NULL);
			if (ty == 0xda) np++;
			if (np == 2) break;
		}
	} else if (opt_seek < 0) {
		opt_seek = get_ptbl_offs(-opt_seek, NULL, NULL);
		partseek = 1;
	} else partseek = 0;

	if (opt_erase) {
		int n = 600;
		sbuslock();
		wren();
		ce();
		while (--n && (rdsr() & 0x1) == 0x1) {
			sbusunlock();
			usleep(100000);
			sbuslock();
		}
		sbusunlock();
		fprintf(stderr, "erase_ok=%d\n", n != 0);
		if (n == 0) exit(1);
		if (verify) memset(csumtbl, 0x80, size);
	}

	if (opt_writetest) {
		time_t start;
		unsigned char *buf, *bufpg;
		unsigned int j;

		buf = malloc(opt_blocksz * 512 + 4095);
		bufpg = (unsigned char *)(((unsigned int)buf + 4095) & ~0xfff);
		memset(bufpg, opt_writeset, opt_blocksz * 512);
		srandom(randomseed);
		fprintf(stderr, "write_byte=0x%x\n", opt_writeset);
		i = 0;
		j = 0;
		/* Synchronize to the next second transition */
		start = time(NULL);
		while (start == time(NULL));
		start = time(NULL);
		while (time(NULL) - start < 10) {
			sbuslock();
			ret = spiflashwrite(j, bufpg, opt_blocksz);
			sbusunlock();
			assert(ret == 0);
			i += opt_blocksz;
			if (opt_random) j = random() & sizemask;
			else {
				j = (j + opt_blocksz) & sizemask;
				if ((j + opt_blocksz) >= size) j = 0;
			}
		}
		
		fprintf(stderr, "writetest_kbps=%d\n", i / 20);
		fprintf(stderr, "writetest_xfrps=%d\n", 
		  i / 10 / opt_blocksz);
		free(buf);
	}

	if (opt_readtest) {
		time_t start;
		unsigned char *buf, *bufpg;
		unsigned int j;
		int l = opt_blocksz * 512;

		buf = malloc(l + 4095);
		bufpg = (unsigned char *)(((unsigned int)buf + 4095) & ~0xfff);
		srandom(randomseed);
		bzero(bufpg, l);
		i = 0;
		j = 0;
		/* Synchronize to the next second transition */
		start = time(NULL);
		while (start == time(NULL));
		start = time(NULL);
		while (time(NULL) - start < 10) {
			sbuslock();
			ret = spiflashread(j, bufpg, opt_blocksz);
			sbusunlock();
			assert(ret == 0);
			i += opt_blocksz;

			if (opt_random) j = random() & sizemask;
			else {
				j = (j + opt_blocksz) & sizemask;
				if ((j + opt_blocksz) >= size) j = 0;
			}
		}

		fprintf(stderr, "readtest_kbps=%d\n", i / 20);
		fprintf(stderr, "readtest_xfrps=%d\n", 
		  i / 10 / opt_blocksz);
		free(buf);
	}

	if (opt_read) {
		unsigned char *buf, *bufpg;
		struct timeval tv1, tv2;
		unsigned int j;

		buf = malloc(opt_blocksz * 512 + 4095);
		bzero(buf, opt_blocksz * 512);
		bufpg = (unsigned char *)(((unsigned int)buf + 4095) & ~0xfff);
		srandom(randomseed);
		if (opt_readblks > (size / opt_blocksz) || opt_readblks == -1)
		  opt_readblks = (size / opt_blocksz);
		gettimeofday(&tv1, NULL);
		for (i = 0, j = opt_seek; i < opt_readblks; i++) {
			sbuslock();
			if ((j + opt_blocksz) > size) {
			  ret = spiflashread(j, bufpg, size - j);
			} else
			  ret = spiflashread(j, bufpg, opt_blocksz);
			sbusunlock();
			assert(ret == 0);
			fwrite(bufpg, opt_blocksz * 512, 1, stdout);

			if (opt_random) j = (unsigned int)random() & sizemask;
			else j += opt_blocksz;
		}
		gettimeofday(&tv2, NULL);
		j = (tv2.tv_sec - tv1.tv_sec) * 1000;
		j += tv2.tv_usec / 1000 - tv1.tv_usec / 1000;
		if (j <= 0) j = 1;
		i = i * opt_blocksz;
		fprintf(stderr, "read_kb=%d\n", i / 2);
		fprintf(stderr, "read_kbps=%d\n", (i * 500 / j));
		free(buf);
	}

	if (opt_write) {
		unsigned char *buf, *bufpg;
		struct timeval tv1, tv2;
		unsigned int j;
		int errs=0;

		buf = malloc(opt_blocksz * 512 + 4095);
		bufpg = (unsigned char *)(((unsigned int)buf + 4095) & ~0xfff);
		memset(bufpg, opt_writeset, opt_blocksz * 512);
		srandom(randomseed);
		if (opt_writeblks > (size / opt_blocksz) || opt_writeblks == -1)
		  opt_writeblks = (size / opt_blocksz);
		gettimeofday(&tv1, NULL);
		if (opt_seek && ifile && !partseek) {
			ret = fseek(ifile, opt_seek * 512, SEEK_SET);
			if (ret == -1) for (i = 0; i < opt_seek; i++) {
				fread(bufpg, 512, 1, ifile);
			}
		}
		for (i = 0, j = opt_seek; i < opt_writeblks; i++) {
			if (ifile) {
				ret = fread(bufpg, opt_blocksz * 512, 1, ifile);
				if (ret == 0 && feof(ifile)) break;
				assert(ret == 1);
			} 
			sbuslock();
			ret = spiflashwrite(j, bufpg, opt_blocksz);
			sbusunlock();
			if (ret != 0) {
				fprintf(stderr, "error%d=%d\n", errs++, j);
				sbuslock();
				ret = spiflashwrite(j, bufpg, opt_blocksz);
				sbusunlock();
			} 
			if (ret != 0) {
				fprintf(stderr, "perm_write_error=1\n");
				exit(1);
			}
			if (opt_random) j = (unsigned int)random() & sizemask;
			else j += opt_blocksz;
		}
		gettimeofday(&tv2, NULL);
		j = (tv2.tv_sec - tv1.tv_sec) * 1000;
		j += tv2.tv_usec / 1000 - tv1.tv_usec / 1000;
		if (j <= 0) j = 1;
		i = i * opt_blocksz;
		fprintf(stderr, "write_kb=%d\n", i / 2);
		fprintf(stderr, "write_kbps=%d\n", (i * 500 / j));
		free(buf);
	}

	if (opt_nbdserver) {
		nbdbufsz = opt_blocksz;
		nbdbuf = malloc(opt_blocksz * 512 + 4095);
		nbdbuf = (unsigned char *)(((unsigned int)nbdbuf + 4095) &
		  ~0xfff);
		bzero(nbdbuf, opt_blocksz * 512);
		nbdserver(opt_nbdarg, opt_bind);
	}

	return 0;
}
