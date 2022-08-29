#include "all.h"

Amd64Op amd64_op[NOp] = {
#define O(op, t, x) [O##op] =
#define X(nm, zf, lf) { nm, zf, lf, },
	#include "../ops.h"
};

static int
amd64_memargs(int op)
{
	return amd64_op[op].nmem;
}

#define AMD64_COMMON \
	.gpr0 = RAX, \
	.ngpr = NGPR, \
	.fpr0 = XMM0, \
	.nfpr = NFPR, \
	.rglob = BIT(RBP) | BIT(RSP), \
	.nrglob = 2, \
	.rsave = amd64_sysv_rsave, \
	.nrsave = {NGPS, NFPS}, \
	.retregs = amd64_sysv_retregs, \
	.argregs = amd64_sysv_argregs, \
	.memargs = amd64_memargs, \
	.abi = amd64_sysv_abi, \
	.isel = amd64_isel, \

Target T_amd64_sysv = {
	.name = "amd64_sysv",
	.emitfn = amd64_sysv_emitfn,
	.emitfin = elf_emitfin,
	.asloc = ".L",
	AMD64_COMMON
};

Target T_amd64_apple = {
	.name = "amd64_apple",
	.emitfn = amd64_apple_emitfn,
	.emitfin = macho_emitfin,
	.asloc = "L",
	.assym = "_",
	AMD64_COMMON
};
