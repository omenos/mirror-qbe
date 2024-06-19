#include "all.h"

Blk *
newblk()
{
	static Blk z;
	Blk *b;

	b = alloc(sizeof *b);
	*b = z;
	return b;
}

/* TODO - this never seems to do anything??? */
static void
prunephis(Fn *f)
{
	Blk *b;
	Phi *p, **pp;
	uint na, na0;

	for (b = f->start; b; b = b->link) {
		assert(b->id < f->nblk);
		for (pp = &b->phi; (*pp);) {
			p = *pp;
			for (na = na0 = 0; na < p->narg; na++)
				if (p->blk[na]->id != -1u) {
					p->blk[na0] = p->blk[na];
					p->arg[na0] = p->arg[na];
					na0++;
				}
			if (na0 == 0) {
				*pp = p->link;
			} else {
				p->narg = na0;
				pp = &p->link;
			}
		}
	}
}

static void
addpred(Blk *bp, Blk *bc)
{
	++bc->npred;
	if (bc->pred)
		vgrow(&bc->pred, bc->npred);
	else
		bc->pred = vnew(bc->npred, sizeof bc->pred[0], PFn);
	bc->pred[bc->npred-1] = bp;
}

/* fill predecessors information in blocks; prune dead phi refs */
void
fillpreds(Fn *f)
{
	Blk *b;

	for (b=f->start; b; b=b->link)
		b->npred = 0;
	for (b=f->start; b; b=b->link) {
		if (b->s1)
			addpred(b, b->s1);
		if (b->s2 && b->s2 != b->s1)
			addpred(b, b->s2);
	}
	/* TODO - this never seems to do anything??? */
	prunephis(f);
}

static void
porec(Blk *b, uint *npo)
{
	Blk *s1, *s2;

	if (!b || b->id != -1u)
		return;
	b->id = 0; /* marker */
	s1 = b->s1;
	s2 = b->s2;
	if (s1 && s2 && s1->loop > s2->loop) {
		s1 = b->s2;
		s2 = b->s1;
	}
	porec(s1, npo);
	porec(s2, npo);
	b->id = (*npo)++;
}

/* fill the rpo information; prune dead blks */
static void
fillrpo(Fn *f)
{
	Blk *b, **p;

	for (b=f->start; b; b=b->link)
		b->id = -1u;
	f->nblk = 0;
	porec(f->start, &f->nblk);
	if (f->rpo)
		vgrow(&f->rpo, f->nblk);
	else
		f->rpo = vnew(f->nblk, sizeof f->rpo[0], PFn);
	for (p=&f->start; (b=*p);) {
		if (b->id == -1u) {
			*p = b->link;
		} else {
			b->id = f->nblk-b->id-1; /* po -> rpo */
			f->rpo[b->id] = b;
			p = &b->link;
		}
	}
}

/* fill rpo, preds; prune dead blks, prune dead blk refs from phis */
void
fillcfg(Fn *f)
{
	fillrpo(f);
	fillpreds(f);
}

/* for dominators computation, read
 * "A Simple, Fast Dominance Algorithm"
 * by K. Cooper, T. Harvey, and K. Kennedy.
 */

static Blk *
inter(Blk *b1, Blk *b2)
{
	Blk *bt;

	if (b1 == 0)
		return b2;
	while (b1 != b2) {
		if (b1->id < b2->id) {
			bt = b1;
			b1 = b2;
			b2 = bt;
		}
		while (b1->id > b2->id) {
			b1 = b1->idom;
			assert(b1);
		}
	}
	return b1;
}

void
filldom(Fn *fn)
{
	Blk *b, *d;
	int ch;
	uint n, p;

	for (b=fn->start; b; b=b->link) {
		b->idom = 0;
		b->dom = 0;
		b->dlink = 0;
	}
	do {
		ch = 0;
		for (n=1; n<fn->nblk; n++) {
			b = fn->rpo[n];
			d = 0;
			for (p=0; p<b->npred; p++)
				if (b->pred[p]->idom
				||  b->pred[p] == fn->start)
					d = inter(d, b->pred[p]);
			if (d != b->idom) {
				ch++;
				b->idom = d;
			}
		}
	} while (ch);
	for (b=fn->start; b; b=b->link)
		if ((d=b->idom)) {
			assert(d != b);
			b->dlink = d->dom;
			d->dom = b;
		}
}

int
sdom(Blk *b1, Blk *b2)
{
	assert(b1 && b2);
	if (b1 == b2)
		return 0;
	while (b2->id > b1->id)
		b2 = b2->idom;
	return b1 == b2;
}

int
dom(Blk *b1, Blk *b2)
{
	return b1 == b2 || sdom(b1, b2);
}

static void
addfron(Blk *a, Blk *b)
{
	uint n;

	for (n=0; n<a->nfron; n++)
		if (a->fron[n] == b)
			return;
	if (!a->nfron)
		a->fron = vnew(++a->nfron, sizeof a->fron[0], PFn);
	else
		vgrow(&a->fron, ++a->nfron);
	a->fron[a->nfron-1] = b;
}

/* fill the dominance frontier */
void
fillfron(Fn *fn)
{
	Blk *a, *b;

	for (b=fn->start; b; b=b->link)
		b->nfron = 0;
	for (b=fn->start; b; b=b->link) {
		if (b->s1)
			for (a=b; !sdom(a, b->s1); a=a->idom)
				addfron(a, b->s1);
		if (b->s2)
			for (a=b; !sdom(a, b->s2); a=a->idom)
				addfron(a, b->s2);
	}
}

static void
loopmark(Blk *hd, Blk *b, void f(Blk *, Blk *))
{
	uint p;

	if (b->id < hd->id || b->visit == hd->id)
		return;
	b->visit = hd->id;
	f(hd, b);
	for (p=0; p<b->npred; ++p)
		loopmark(hd, b->pred[p], f);
}

void
loopiter(Fn *fn, void f(Blk *, Blk *))
{
	uint n, p;
	Blk *b;

	for (b=fn->start; b; b=b->link)
		b->visit = -1u;
	for (n=0; n<fn->nblk; ++n) {
		b = fn->rpo[n];
		for (p=0; p<b->npred; ++p)
			if (b->pred[p]->id >= n)
				loopmark(b, b->pred[p], f);
	}
}

void
multloop(Blk *hd, Blk *b)
{
	(void)hd;
	b->loop *= 10;
}

void
filldomdpth(Fn *fn)
{
	Blk *b, *dom;
	uint dpth;

	for (b=fn->start; b; b=b->link)
		b->domdpth = -1;

	fn->start->domdpth = 0;

	for (b=fn->start; b; b=b->link) {
		if (b->domdpth != -1)
			continue;
		dpth = 1;
		for (dom = b->idom; dom->domdpth == -1; dom = dom->idom)
			dpth++;
		dpth += dom->domdpth;
		b->domdpth = dpth;
		for (dom = b->idom; dom->domdpth == -1; dom = dom->idom)
			dom->domdpth = --dpth;
	}
}

/* least common ancestor in dom tree */
Blk *
lca(Blk *b1, Blk *b2)
{
	if (!b1)
		return b2;
	if (!b2)
		return b1;
	while (b1->domdpth > b2->domdpth)
		b1 = b1->idom;
	while (b2->domdpth > b1->domdpth)
		b2 = b2->idom;
	while (b1 != b2) {
		b1 = b1->idom;
		b2 = b2->idom;
	}
	return b1;
}

void
fillloop(Fn *fn)
{
	Blk *b;

	for (b=fn->start; b; b=b->link)
		b->loop = 1;
	loopiter(fn, multloop);
}

static void
uffind(Blk **pb, Blk **uf)
{
	Blk **pb1;

	pb1 = &uf[(*pb)->id];
	if (*pb1) {
		uffind(pb1, uf);
		*pb = *pb1;
	}
}

/* requires rpo and no phis, breaks cfg */
void
simpljmp(Fn *fn)
{

	Blk **uf; /* union-find */
	Blk **p, *b, *ret;

	ret = newblk();
	ret->id = fn->nblk++;
	ret->jmp.type = Jret0;
	uf = emalloc(fn->nblk * sizeof uf[0]);
	for (b=fn->start; b; b=b->link) {
		assert(!b->phi);
		if (b->jmp.type == Jret0) {
			b->jmp.type = Jjmp;
			b->s1 = ret;
		}
		if (b->nins == 0)
		if (b->jmp.type == Jjmp) {
			uffind(&b->s1, uf);
			if (b->s1 != b)
				uf[b->id] = b->s1;
		}
	}
	for (p=&fn->start; (b=*p); p=&b->link) {
		if (b->s1)
			uffind(&b->s1, uf);
		if (b->s2)
			uffind(&b->s2, uf);
		if (b->s1 && b->s1 == b->s2) {
			b->jmp.type = Jjmp;
			b->s2 = 0;
		}
	}
	*p = ret;
	free(uf);
}

static void
replacepred(Blk **blks, uint nblk, Blk *to, Blk *from)
{
	uint n;
	for(n=0; n<nblk; n++)
		if (blks[n] == from) {
			blks[n] = to;
			break;
		}
	assert(n != nblk);
}

/* replace b->pred[] and p->blk[] entries */
void
replacepreds(Blk *s, Blk *to, Blk *from)
{
	Phi *p;

	if (!s)
		return;
	assert(s->npred);
	replacepred(s->pred, s->npred, to, from);
	for (p = s->phi; p; p = p->link) {
		assert(p->narg == s->npred);
		replacepred(p->blk, p->narg, to, from);
	}
}

/* remove marked-dead blks - marked as fn->rpo[id] == 0 */
void
killblks(Fn *fn)
{
	Blk **pb;

	for (pb = &fn->start; *pb;)
		if (fn->rpo[(*pb)->id])
			pb = &(*pb)->link;
		else
			*pb = (*pb)->link;
}

/* merge linear jmp chains */
/* requires rpo pred, breaks cfg use */
void
blkmerge(Fn *fn)
{
	uint bid, nins;
	Blk *curb, *b;
	Ins *vins;

	if (debug['B'])
		fputs("\n> Block merge:\n", stderr);

	vins = vnew(0, sizeof vins[0], PFn);
	curb = 0;
	/* linear jmp chains will be consecutive in rpo */
	for (bid=0; bid<fn->nblk; bid++) {
		b = fn->rpo[bid];
		if (curb == 0) {
			curb = b;
			nins = 0;
		} else
			fn->rpo[bid] = 0;
		addbins(b, &vins, &nins);
		/* note - there are cases where GVN does not eliminate singleton phis */
		if (b->jmp.type != Jjmp || b->s1->npred != 1 || b->s1->phi) {
			idup(curb, vins, nins);
			curb->nins = nins;
			curb->jmp = b->jmp;
			replacepreds(b->s1, curb, b);
			if (b->s1 != b->s2)
				replacepreds(b->s2, curb, b);
			curb->s1 = b->s1;
			curb->s2 = b->s2;
			curb = 0;
		} else {
			assert(b->s1->id == bid+1);
			if (debug['B'])
				fprintf(stderr, "    merging blocks @%s -> @%s\n", b->name, b->s1->name);
		}
	}
	assert(curb == 0);
	killblks(fn);
}

int
lonesucc(Blk *b, Blk *s)
{
	assert(s);
	if (s != b)
	if (s->npred == 1)
	if (s->pred[0] == b)
	if (s->phi == 0)
		return 1;
	return 0;
}

int
lonejmpsucc(Blk *b, Blk *s)
{
	return s->jmp.type == Jjmp && lonesucc(b, s);
}

/* (otherwise) isolated if-then[-else] graphlet */
int
ifgraph(Blk *ifb, Blk **pthenb, Blk **pelseb, Blk **pjoinb)
{
	if (ifb->jmp.type != Jjnz)
		return 0;
	assert(ifb->s1 && ifb->s2);
	assert(ifb->s1 != ifb->s2); /* dubious */
	*pthenb = ifb->s1;
	*pelseb = ifb->s2;
	*pjoinb = ifb->s1->s1;
	if (ifb->s1 == ifb->s2->s1) {
		/* empty then */
		*pthenb = ifb;
		*pjoinb = ifb->s1;
	}
	if (ifb->s1->s1 == ifb->s2)
		/* empty else */
		*pelseb = ifb;

	if (*pthenb == ifb ||
	    ((*pthenb)->s1 == *pjoinb && lonejmpsucc(ifb, *pthenb)))
	if (*pelseb == ifb ||
	    ((*pelseb)->s1 == *pjoinb && lonejmpsucc(ifb, *pelseb)))
	/* there are cases where npred == 2 is not strictly needed - ifconvert for example */
	if ((*pjoinb)->npred == 2)
		return 1;

	return 0;
}

/* join blk of if-then[-else] graphlet */
int
ifjoin(Blk *joinb, Blk **pifb, Blk **pthenb, Blk **pelseb)
{
	Blk *joinb1;

	if (joinb->npred)
	if (ifgraph(joinb->pred[0], pthenb, pelseb, &joinb1))
	if (joinb == joinb1) {
		*pifb = joinb->pred[0];
		return 1;
	}
	if (joinb->npred && joinb->pred[0]->npred)
	if (ifgraph(joinb->pred[0]->pred[0], pthenb, pelseb, &joinb1))
	if (joinb == joinb1) {
		*pifb = joinb->pred[0]->pred[0];
		return 1;
	}
	return 0;
}

int
emptyblk(Blk *b)
{
	Ins *i;

	for (i = b->ins; i < &b->ins[b->nins]; i++)
		if (i->op != Onop)
		if (i->op != Odbgloc)
			return 0;
	return 1;
}

/* remove empty jnz graphlets */
/* needs rpo; breaks cfg */
void
ifelim(Fn *fn)
{
	uint bid;
	Blk *ifb, *thenb, *elseb, *joinb;

	for (bid = 0; bid < fn->nblk; bid++) {
		ifb = fn->rpo[bid];
		if (ifb == 0)
			continue;
		if (ifgraph(ifb, &thenb, &elseb, &joinb))
		if (joinb->phi == 0)
		if (thenb == ifb || emptyblk(thenb))
		if (elseb == ifb || emptyblk(elseb)) {
			if (debug['B'])
				fprintf(stderr, "    eliminating empty if @%s -> @%s, @%s -> @%s\n",
					ifb->name, thenb->name, elseb->name, joinb->name);
			if (thenb != ifb)
				fn->rpo[thenb->id] = 0;
			if (elseb != ifb)
				fn->rpo[elseb->id] = 0;
			ifb->jmp.type = Jjmp;
			ifb->jmp.arg = R;
			ifb->s1 = joinb;
			ifb->s2 = 0;
		}
	}
	killblks(fn);
}

void
clrbvisit(Fn *fn)
{
	Blk *b;
	for (b = fn->start; b; b = b->link)
		b->visit = 0;
}

static int
reaches1(Blk *b1, Blk *b2)
{
	assert(b2);
	if (b1 == b2)
		return 1;
	if (b1 == 0 || b1->visit)
		return 0;
	b1->visit = 1;
	return reaches1(b1->s1, b2) || reaches1(b1->s2, b2);
}

/* path from b1 to b2 not thru bnotvia? */
/* uses b->visit */
int
reachesnotvia(Fn *fn, Blk *b1, Blk *b2, Blk *bnotvia)
{
	int rc;

	if (bnotvia)
		bnotvia->visit = 1;
	rc = reaches1(b1, b2);
	clrbvisit(fn);
	return rc;
}

/* path from b1 to b2? */
/* uses b->visit */
int
reaches(Fn *fn, Blk *b1, Blk *b2)
{
	return reachesnotvia(fn, b1, b2, 0);
}

