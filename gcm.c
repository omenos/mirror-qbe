#include "all.h"

#define NOBID (-1u)

/* ins can trap at runtime */
static int
istrapping(Fn *fn, Ins *i)
{
	int64_t v;

	if (KBASE(i->cls) == 0)
	if (INRANGE(i->op, Odiv, Ourem))
	if (!isconbits(fn, i->arg[1], &v) || v == 0)
		return 1;
	return 0;
}

/* fixed ins that can be eliminated if unused */
static int
canelim(Fn *fn, Ins *i)
{
	return isload(i->op) || isalloc(i->op) || istrapping(fn, i);
}

/* ins must stay in def blk */
int
isfixed(Fn *fn, Ins *i)
{
	return optab[i->op].ispinned || istrapping(fn, i);
}

static uint earlyins(Fn *, Blk *, Ins *);

/* return earlybid of ref def ins */
static uint
schedearly(Fn *fn, Ref r)
{
	Tmp *t;
	Blk *b;

	if (rtype(r) != RTmp)
		return 0 /* root/start */;

	t = &fn->tmp[r.val];
	if (t->gcmbid != NOBID)
		return t->gcmbid; /* already visited/visiting */

	b = fn->rpo[t->bid];
	if (t->def) {
		/* def is an ins */
		assert(b->ins <= t->def && t->def < &b->ins[b->nins]);
		t->gcmbid = 0; /* mark visiting root/start blk */
		t->gcmbid = earlyins(fn, b, t->def); /* schedule ins input defs */
	} else {
		/* def is a phi - it stays in its def blk */
		t->gcmbid = t->bid;
	}

	return t->gcmbid;
}

/* return deepest domdpth bid of arg defs */
static uint
earlyins(Fn *fn, Blk *b, Ins* i)
{
	uint earlybid, arg1earlybid;

	earlybid = schedearly(fn, i->arg[0]);
	assert(earlybid != NOBID);
	arg1earlybid = schedearly(fn, i->arg[1]);
	assert(arg1earlybid != NOBID);
	if (fn->rpo[earlybid]->domdpth < fn->rpo[arg1earlybid]->domdpth) {
		assert(dom(fn->rpo[earlybid], fn->rpo[arg1earlybid]));
		earlybid = arg1earlybid;
	}

	/* fixed ins remain in their defining blk */
	return isfixed(fn, i) ? b->id : earlybid;
}

static void
earlyblk(Fn *fn, uint bid)
{
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;

	b = fn->rpo[bid];
	for (p = b->phi; p; p = p->link)
		for (n = 0; n < p->narg; n++)
			schedearly(fn, p->arg[n]);
	for (i = b->ins; i < &b->ins[b->nins]; i++)
		if (isfixed(fn, i))
			earlyins(fn, b, i);
	schedearly(fn, b->jmp.arg);
}

/* least common ancestor in dom tree */
static uint
lcabid(Fn *fn, uint bid1, uint bid2)
{
	Blk *b;

	if (bid1 == NOBID)
		return bid2;
	if (bid2 == NOBID)
		return bid1;

	b = lca(fn->rpo[bid1], fn->rpo[bid2]);
	assert(b);
	return b->id;
}

static uint
bestbid(Fn *fn, uint earlybid, uint latebid)
{
	Blk *curb, *earlyb, *bestb;

	if (latebid == NOBID)
		return NOBID; /* unused */

	assert(earlybid != NOBID);

	earlyb = fn->rpo[earlybid];
	bestb = curb = fn->rpo[latebid];
	assert(dom(earlyb, curb));

	while (curb != earlyb) {
		curb = curb->idom;
		if (curb->loop < bestb->loop)
			bestb = curb;
	}
	return bestb->id;
}

static uint lateins(Fn *, Blk *, Ins *, Ref r);
static uint latephi(Fn *, Phi *, Ref r);
static uint latejmp(Blk *, Ref r);

/* return lca bid of ref uses */
static uint
schedlate(Fn *fn, Ref r)
{
	Tmp *t;
	Blk *b;
	Use *u;
	uint earlybid;
	uint latebid;
	uint uselatebid;

	if (rtype(r) != RTmp)
		return NOBID;

	t = &fn->tmp[r.val];
	if (t->visit)
		return t->gcmbid; /* already visited/visiting */

	t->visit = 1; /* mark visiting/visited */
	earlybid = t->gcmbid;
	if (earlybid == NOBID)
		return NOBID; /* not used */
	t->gcmbid = t->bid; /* t->gcmbid is now latebid */

	latebid = NOBID;
	for (u = t->use; u < &t->use[t->nuse]; u++) {
		assert(u->bid < fn->nblk);
		b = fn->rpo[u->bid];
		switch (u->type) {
		case UXXX:
			die("unreachable");
			break;
		case UPhi:
			uselatebid = latephi(fn, u->u.phi, r);
			break;
		case UIns:
			uselatebid = lateins(fn, b, u->u.ins, r);
			break;
		case UJmp:
			uselatebid = latejmp(b, r);
			break;
		}
		latebid = lcabid(fn, latebid, uselatebid);
	}

	/* phis stay in their def blk */
	if (t->def) {
		/* allow elimination of unused load/alloc/trapping ins */
		if (latebid == NOBID && canelim(fn, t->def))
			t->gcmbid = NOBID;
		/* ... otherwise fixed ins stay in defining blk */
		else if(!isfixed(fn, t->def))
			t->gcmbid = bestbid(fn, earlybid, latebid);
	}

	return t->gcmbid;
}

/* return lca bid of uses, or NOBID if no active uses */
static uint
lateins(Fn *fn, Blk *b, Ins *i, Ref r)
{
	uint latebid;

	assert(i->op == Onop || req(i->arg[0], r) || req(i->arg[1], r));
	if (i->op == Onop)
		return NOBID; /* already eliminated */

	assert(b->ins <= i && i < &b->ins[b->nins]);

	latebid = schedlate(fn, i->to);
	/* allow elimination of unused load/alloc/trapping ins */
	if (latebid == NOBID)
	if (canelim(fn, i))
		return NOBID;
	/* ... otherwise fixed ins stay in defining blk */
	return isfixed(fn, i) ? b->id : latebid;
}

static uint
latephi(Fn *fn, Phi *p, Ref r)
{
	uint n;
	uint latebid;

	if (!p->narg)
		return NOBID; /* marked as unused */

	latebid = NOBID;
	for (n = 0; n < p->narg; n++)
		if (req(p->arg[n], r))
			latebid = lcabid(fn, latebid, p->blk[n]->id);

	assert(latebid != NOBID);
	return latebid;
}

static uint
latejmp(Blk *b, Ref r)
{
	if (req(b->jmp.arg, R))
		return NOBID;
	else {
		assert(req(b->jmp.arg, r));
		return b->id;
	}
}

static void
lateblk(Fn *fn, uint bid)
{
	Blk *b;
	Phi **pp;
	Ins *i;

	b = fn->rpo[bid];
	for (pp = &b->phi; *(pp);)
		if (schedlate(fn, (*pp)->to) == NOBID) {
			/* unused */
			(*pp)->narg = 0; /* mark unused */
			*pp = (*pp)->link; /* remove phi */
		} else
			pp = &(*pp)->link;

	for (i = b->ins; i < &b->ins[b->nins]; i++)
		if (isfixed(fn, i))
			lateins(fn, b, i, i->arg[0]);
}

static void
addgcmins(Fn *fn, Ins *vins, uint nins)
{
	Ins *i;
	Tmp *t;
	Blk *b;

	for (i = vins; i < &vins[nins]; i++) {
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		b = fn->rpo[t->gcmbid];
		addins(&b->ins, &b->nins, i);
	}
}

/* remove unused instructions */
/* move instructions to (end of) target block */
/* use-before-def is fixed up afterwards */
static void
gcmmove(Fn *fn)
{
	Tmp *t;
	Ins *vins, *i;
	uint nins;

	nins = 0;
	vins = vnew(nins, sizeof vins[0], PFn);

	for (t=&fn->tmp[Tmp0]; t < &fn->tmp[fn->ntmp]; t++) {
		if (t->def == 0)
			continue;
		if (t->bid == t->gcmbid)
			continue;
		i = t->def;
		if (isfixed(fn, i) && !canelim(fn, i))
			continue;
		assert(rtype(i->to) == RTmp);
		assert(t == &fn->tmp[i->to.val]);
		if (t->gcmbid != NOBID)
			addins(&vins, &nins, i);
		*i = (Ins){.op = Onop};
	}

	addgcmins(fn, vins, nins);
}

static void
schedins(Fn *fn, Blk *b, Ins *i0, Ins **pvins, uint *pnins)
{
	Ins *i, *i1;
	Tmp *t;
	uint na;

	if (i0->op == Onop)
		return;
	/* arg...call have to stay together */
	/* TODO - sel0...sel1 too */
	for (i1 = i0; isarg(i1->op); i1++) {}
	for (i = i0; i <= i1; i++)
		for (na = 0; na < 2; na++) {
			if (rtype(i->arg[na]) != RTmp)
				continue;
			t = &fn->tmp[i->arg[na].val];
			/* def in different blk, or phi in this blk */
			if (t->bid != b->id || t->def == 0)
				continue;
			/* already scheduled */
			if (t->def->op == Onop) {
				continue;
			}
			schedins(fn, b, t->def, pvins, pnins);
		}
	for (i = i0; i <= i1; i++) {
		addins(pvins, pnins, i);
		*i = (Ins){.op = Onop};
	}
}

static void
fixbub4d(Fn *fn, Blk *b, Ins **pvins)
{
	Ins *i;
	uint nins;

	nins = 0;
	for (i = b->ins; i < &b->ins[b->nins]; i++)
		schedins(fn, b, i, pvins, &nins);
	idup(b, *pvins, nins);
}

static void
fixub4d(Fn *fn)
{
	Blk *b;
	Ins *vins; // TODO insb

	vins = vnew(0, sizeof vins[0], PFn);
	for (b = fn->start; b; b = b->link)
		fixbub4d(fn, b, &vins);
}

static int
iskladdcon(Fn *fn, Ins *i, int64_t *v)
{
	if (i->op == Oadd)
	if (i->cls == Kl)
	if (rtype(i->arg[0]) == RTmp)
	if (isconbits(fn, i->arg[1], v))
		return 1;
	return 0;
}

static void
ireassoc(Fn *fn, Blk *b, Ins *i, Ins **pvins, uint *pnins) 
{
	Blk *b2;
	Tmp *t, *t2;
	Use *u;
	Ref r2;
	int64_t v;
	int x;

	assert(b->ins <= i && i < &b->ins[b->nins]);
	if (!iscmp(i->op, &x, &x))
	if (!iskladdcon(fn, i, &v))
		return;

	assert(rtype(i->to) == RTmp);
	t = &fn->tmp[i->to.val];
	for (u = t->use; u < &t->use[t->nuse]; u++) {
		if (u->type == UPhi)
			continue;
		b2 = fn->rpo[u->bid];
		addins(pvins, pnins, i);
		/* careful, can move fn->tmp */
		r2 = newtmp("rea", t->cls, fn);
		t = &fn->tmp[i->to.val];
		t2 = &fn->tmp[r2.val];
		t2->gcmbid = u->bid;
		(*pvins)[(*pnins)-1].to = r2;
		if (u->type == UIns) {
			assert(req(u->u.ins->arg[0], i->to)
			       || req(u->u.ins->arg[1], i->to));
			if (req(u->u.ins->arg[0], i->to))
				u->u.ins->arg[0] = r2;
			if (req(u->u.ins->arg[1], i->to))
				u->u.ins->arg[1] = r2;
		} else {
			assert(u->type == UJmp);
			assert(req(b2->jmp.arg, i->to));
			b2->jmp.arg = r2;
		}
	}
}

/* Redistribute trivial ops to point of use. */
/* Reduces register pressure. */
/* needs rpo, use; breaks use */
void
reassoc(Fn *fn)
{
	Blk *b;
	Ins *vins, *i;
	uint nins;

	nins = 0;
	vins = vnew(nins, sizeof vins[0], PFn);

	/* identify trivial ins */
	for (b = fn->start; b; b = b->link) {
		for (i = b->ins; i < &b->ins[b->nins]; i++)
			ireassoc(fn, b, i, &vins, &nins);
	}

	addgcmins(fn, vins, nins);
}

static void
cleartmps(Fn *fn)
{
	Tmp *t;

	for (t=&fn->tmp[Tmp0]; t < &fn->tmp[fn->ntmp]; t++) {
		t->visit = 0;
		t->gcmbid = NOBID;
	}
}

/* https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf */
/* require use dom */
/* maintains rpo pred dom */
/* breaks use */
void
gcm(Fn *fn)
{
	uint bid;

	filldomdpth(fn);
	fillloop(fn);

	cleartmps(fn);
	for (bid=0; bid<fn->nblk; bid++)
		earlyblk(fn, bid);
	for (bid=0; bid<fn->nblk; bid++)
		lateblk(fn, bid);

	gcmmove(fn);
	cleartmps(fn); /* filluse() uses visit */
	filluse(fn);
	reassoc(fn);
	filluse(fn);
	fixub4d(fn);
	
	if (debug['G']) {
		fprintf(stderr, "\n> After GCM:\n");
		printfn(fn, stderr);
	}
}
