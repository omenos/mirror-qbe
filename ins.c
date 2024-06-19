#include "all.h"

void
addins(Ins **pvins, uint *pnins, Ins *i)
{
	if (i->op == Onop)
		return;
	vgrow(pvins, ++(*pnins));
	(*pvins)[(*pnins)-1] = *i;
}

void
addbins(Blk *b, Ins **pvins, uint *pnins)
{
	Ins *i;

	for (i = b->ins; i < &b->ins[b->nins]; i++)
		addins(pvins, pnins, i);
}

static int
unusedins(Fn *fn, Ins *i);

static int
unusedtmp(Fn *fn, Tmp *t)
{
	if (t->nuse == 0)
		return 1;
	if (t->nuse == 1)
	if (t->use[0].type == UIns)
		return unusedins(fn, t->use[0].u.ins);
	return 0;
}

static int
unusedtmpref(Fn *fn, Ref r)
{
	if (rtype(r) != RTmp)
		return 0;
	return unusedtmp(fn, &fn->tmp[r.val]);
}

static int
unusedins(Fn *fn, Ins *i)
{
	if (!INRANGE(i->op, Opar, Ocall))
	if (unusedtmpref(fn, i->to))
		return 1;
	return 0;
}

/* replace unused ins with nop */
/* needs use; breaks use */
void
nopunused(Fn *fn)
{
	Blk *b;
	Ins *i;

	for (b = fn->start; b; b = b->link)
		for (i = b->ins; i < &b->ins[b->nins]; i++)
			if (unusedins(fn, i))
				*i = (Ins){.op = Onop};
}

typedef struct FromLoc FromLoc;
struct FromLoc {
	InsLoc from;
	uint ton;
};

static int
loccmp(InsLoc *la, InsLoc *lb)
{
	if (la->bid != lb->bid)
		return (int)la->bid - (int)lb->bid;
	return la->insn - lb->insn;
}

static int
tocmp(const void *a, const void *b)
{
	InsMov *ma, *mb;

	ma = (InsMov*)a;
	mb = (InsMov*)b;
	return loccmp(&ma->to, &mb->to);
}

static int
fromcmp(const void *a, const void *b)
{
	FromLoc *fa, *fb;

	fa = (FromLoc*)a;
	fb = (FromLoc*)b;
	return loccmp(&fa->from, &fb->from);
}

static int
loceq(InsLoc *a, InsLoc *b)
{
	return a->bid == b->bid && a->insn == b->insn;
}

/* after, mov is sorted by to, and to.insn, from.insn are updated */
void
movins(Fn *fn, InsMov *mov, uint nmov, int del)
{
	Blk *b, *b2;
	uint bid, n, fromn, ton, ifromn, nins;
	FromLoc *from;
	uint *newbnins;
	Ins **newbins, *vins;

	qsort(mov, nmov, sizeof mov[0], tocmp);

	from = emalloc(nmov * sizeof from[0]);
	for (n = 0; n < nmov; n++) {
		from[n].from = mov[n].from;
		from[n].ton = n;
	}
	qsort(from, nmov, sizeof from[0], fromcmp);

	nins = 0;
	vins = vnew(nins, sizeof vins[0], PFn);

	newbnins = emalloc(fn->nblk * sizeof newbnins[0]);
	newbins = emalloc(fn->nblk * sizeof newbins[0]);

	/* populate new ins buffers */
	/* update mov to.insn, from insn */
	fromn = ton = 0;
	for (bid = 0; bid < fn->nblk; bid++) {
		/* no moves to this block */
		if (nmov <= ton || mov[ton].to.bid != bid) {
			while (fromn < nmov && from[fromn].from.bid == bid)
				fromn++;
			continue;
		}
		b = fn->rpo[bid];
		nins = 0;
		for (ifromn = 0; ifromn < b->nins; ifromn++) {
			/* insert new ins, update to */
			while (ton < nmov && loceq(&mov[ton].to, &(InsLoc){.bid = bid, .insn = ifromn})) {
				b2 = fn->rpo[mov[ton].from.bid];
				assert(mov[ton].from.insn < b2->nins);
				addins(&vins, &nins, &b2->ins[mov[ton].from.insn]);
				mov[ton++].to.insn = nins-1;
			}
			/* update from */
			while (fromn < nmov && loceq(&from[fromn].from, &(InsLoc){.bid = bid, .insn = ifromn}))
				from[fromn++].from.insn = nins;
			/* copy original ins */
			addins(&vins, &nins, &b->ins[ifromn]);
		}
		/* append new ins, update to */
		while (ton < nmov && mov[ton].to.bid == bid) {
			assert(mov[ton].to.insn == b->nins);
			b2 = fn->rpo[mov[ton].from.bid];
			assert(mov[ton].from.insn < b2->nins);
			addins(&vins, &nins, &b2->ins[mov[ton].from.insn]);
			mov[ton++].to.insn = nins-1;
		}
		assert(ifromn == b->nins);
		/* idup(&newbins[bid], vins, nins); */
		newbins[bid] = vins;
		vins = vnew(0, sizeof vins[0], PFn);
		newbnins[bid] = nins;
	}
	assert(fromn == nmov);
	assert(ton == nmov);

	/* install new b->ins */
	for (bid = 0; bid < fn->nblk; bid++) {
		if (newbnins[bid] == 0)
			continue;
		b = fn->rpo[bid];
		b->ins = newbins[bid];
		b->nins = newbnins[bid];
	}

	/* remove from ins, update mov from insn */
	for (fromn = 0; fromn < nmov; fromn++) {
		b = fn->rpo[from[fromn].from.bid];
		assert(from[fromn].from.insn < b->nins);
		if (del)
			b->ins[from[fromn].from.insn] = (Ins){.op = Onop};
		mov[from[fromn].ton].from.insn = from[fromn].from.insn;
	}

	free(from);
	free(newbins);
	free(newbnins);
}
