#include "all.h"

static void
blit(Ref sd[2], int sz, Fn *fn)
{
	struct { int st, ld, cls, size; } *p, tbl[] = {
		{ Ostorel, Oload,   Kl, 8 },
		{ Ostorew, Oload,   Kw, 4 },
		{ Ostoreh, Oloaduh, Kw, 2 },
		{ Ostoreb, Oloadub, Kw, 1 }
	};
	Ref r, r1, ro;
	int off, fwd, n;

	fwd = sz >= 0;
	sz = abs(sz);
	off = fwd ? sz : 0;
	for (p=tbl; sz; p++)
		for (n=p->size; sz>=n; sz-=n) {
			off -= fwd ? n : 0;
			r = newtmp("blt", Kl, fn);
			r1 = newtmp("blt", Kl, fn);
			ro = getcon(off, fn);
			emit(p->st, 0, R, r, r1);
			emit(Oadd, Kl, r1, sd[1], ro);
			r1 = newtmp("blt", Kl, fn);
			emit(p->ld, p->cls, r, r1, R);
			emit(Oadd, Kl, r1, sd[0], ro);
			off += fwd ? 0 : n;
		}
}

static int
ulog2_tab64[64] = {
	63,  0, 58,  1, 59, 47, 53,  2,
	60, 39, 48, 27, 54, 33, 42,  3,
	61, 51, 37, 40, 49, 18, 28, 20,
	55, 30, 34, 11, 43, 14, 22,  4,
	62, 57, 46, 52, 38, 26, 32, 41,
	50, 36, 17, 19, 29, 10, 13, 21,
	56, 45, 25, 31, 35, 16,  9, 12,
	44, 24, 15,  8, 23,  7,  6,  5
};

static int
ulog2(uint64_t pow2)
{
	return ulog2_tab64[(pow2 * 0x07EDD5E59A4E28C2) >> 58];
}

static int
ispow2(uint64_t v)
{
	return (v & (v - 1)) == 0;
}

static void
ins(Ins **pi, int *new, Blk *b, Fn *fn)
{
	ulong ni;
	Con *c;
	Ins *i;
	Ref r;
	int n;

	i = *pi;
	/* simplify more instructions here;
	 * copy 0 into xor bit rotations,
	 * etc. */
	switch (i->op) {
	case Oblit1:
		assert(i > b->ins);
		assert((i-1)->op == Oblit0);
		if (!*new) {
			curi = &insb[NIns];
			ni = &b->ins[b->nins] - (i+1);
			curi -= ni;
			icpy(curi, i+1, ni);
			*new = 1;
		}
		blit((i-1)->arg, rsval(i->arg[0]), fn);
		*pi = i-1;
		break;
	case Omul:
	case Oudiv:
	case Ourem:
		r = i->arg[1];
		if (KBASE(i->cls) == 0)
		if (rtype(r) == RCon) {
			c = &fn->con[r.val];
			if (c->type == CBits)
			if (ispow2(c->bits.i)) {
				n = ulog2(c->bits.i);
				if (i->op == Ourem) {
					i->op = Oand;
					i->arg[1] = getcon((1ull<<n) - 1, fn);
				} else if (i->op == Oudiv) {
					i->op = Oshr;
					i->arg[1] = getcon(n, fn);
				} else if (i->op == Omul) {
					i->op = Oshl;
					i->arg[1] = getcon(n, fn);
				}
			}
		}
		/* fall through */
	default:
		if (*new)
			emiti(*i);
		break;
	}
}

void
simpl(Fn *fn)
{
	Blk *b;
	Ins *i;
	int new;

	for (b=fn->start; b; b=b->link) {
		new = 0;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			--i;
			ins(&i, &new, b, fn);
		}
		if (new) {
			b->nins = &insb[NIns] - curi;
			idup(&b->ins, curi, b->nins);
		}
	}
}
