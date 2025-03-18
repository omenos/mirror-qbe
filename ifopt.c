#if 0
#include "all.h"

enum {
	MaxIns = 2,
	MaxPhis = 2,
};

static int
okbranch(Blk *b)
{
	Ins *i;
	int n;

	n = 0;
	for (i=b->ins; i<&b->ins[b->nins]; i++) {
		if (i->op != Onop && i->op != Odbgloc)
			n++;
		if (pinned(i) && i->op != Odbgloc)
			return 0;
	}
	return n <= MaxIns;
}

static int
okjoin(Blk *b)
{
	Phi *p;
	int n;

	n = 0;
	for (p=b->phi; p; p=p->link) {
		if (KBASE(p->cls) != 0)
			return 0;
		n++;
	}
	return n <= MaxPhis;
}

static int
okgraph(Blk *ifb, Blk *thenb, Blk *elseb, Blk *joinb)
{
	if (joinb->npred != 2 || !okjoin(joinb))
		return 0;
	assert(thenb != elseb);
	if (thenb != ifb && !okbranch(thenb))
		return 0;
	if (elseb != ifb && !okbranch(elseb))
		return 0;
	return 1;
}

static void
convert(Blk *ifb, Blk *thenb, Blk *elseb, Blk *joinb, Ins **pvins)
{
	Phi *p;
	Suc *st, *sf;
	Ref argt, argf;
	uint np, nins;
	Ins *i;

	nins = 0;
	addbins(ifb, pvins, &nins);
	if (thenb != ifb)
		addbins(thenb, pvins, &nins);
	if (elseb != ifb)
		addbins(elseb, pvins, &nins);
	assert(joinb->npred == 2);
	if (joinb->phi) {
		i = &(Ins){
			.op = Osel0, .cls = Kw,
			.arg = {ifb->jmp.arg},
		};
		addins(pvins, &nins, i);
	}
	for (np = 0; np < joinb->nphi; np++) {
		p = &joinb->phi[np];
		st = getsuc(thenb, joinb);
		assert(st->nr == joinb->nphi);
		argt = st->r[np];
		sf = getsuc(elseb, joinb);
		assert(st->nr == joinb->nphi);
		argf = sf->r[np];
		assert(KBASE(p->cls) == 0);
		i = &(Ins){
			.op = Osel1, .cls = p->cls,
			.to = p->to, .arg = {argt, argf}
		};
		addins(pvins, &nins, i);
	}
	idup(ifb, *pvins, nins);
	ifb->jmp.type = Jjmp;
	ifb->jmp.arg = R;
	ifb->s1 = joinb;
	ifb->s2 = 0;
	joinb->npred = 1;
	joinb->pred[0] = ifb;
	joinb->phi = 0;
}

/* eliminate if-then[-else] graphlets
 * using sel instructions
 * needs rpo pred use; breaks cfg use
 */
void
ifconvert(Fn *fn)
{
	Blk *ifb, *thenb, *elseb, *joinb;
	Ins *vins;

	if (debug['K'])
		fputs("\n> If-conversion:\n", stderr);

	/* create more trivial if/then/else graphlets */
	// blkmerge(fn);
	// fillcfg(fn);
	// filluse(fn);

	vins = vnew(0, sizeof vins[0], PHeap);
	for (ifb=fn->start; ifb; ifb=ifb->link) {
		if (ifgraph(ifb, &thenb, &elseb, &joinb)
		&& okgraph(ifb, thenb, elseb, joinb)) {
			if (debug['K'])
				fprintf(stderr,
					"    @%s -> @%s, @%s -> @%s\n",
					ifb->name, thenb->name, elseb->name,
					joinb->name);
			convert(ifb, thenb, elseb, joinb, &vins);
		}
	}
	vfree(vins);

	if (debug['K']) {
		fprintf(stderr, "\n> After if-conversion:\n");
		printfn(fn, stderr);
	}
}
#endif
