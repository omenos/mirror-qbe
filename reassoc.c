#include "all.h"

static void
ireassoc(Fn *fn, Blk *b, Ins *i, uint *pnim, InsMov **pim)
{
	Blk *b2;
	Tmp *t;
	Use *u;
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
		if (u->type == UIns)
		if (INRANGE(u->u.ins->op, Oarg, Ocall))
			continue;
		b2 = fn->rpo[u->bid];
		vgrow(pim, ++(*pnim));
		(*pim)[(*pnim)-1] = (InsMov){
			.from = {.bid = b->id, .insn = i-b->ins},
			.to = {
				.bid = u->bid,
				.insn = u->type == UJmp ? b2->nins : u->u.ins-b2->ins
			}};
	}
}

static void
trealloc(Fn *fn, Blk *b, Ins *i)
{
	Ins *i2;
	Ref r;

	assert(b->ins <= i && i < &b->ins[b->nins]);
	r = newtmp("rea", i->cls, fn);
	if (i < &b->ins[b->nins-1]) {
		i2 = i+1;
		/* special case of both args of target instruction reassociated */
		if (!req(i->to, i2->arg[0]) && !req(i->to, i2->arg[1])) {
			assert(i < &b->ins[b->nins-2]);
			i2 = i+2;
		}
		assert(req(i->to, i2->arg[0]) || req(i->to, i2->arg[1]));
		if (req(i->to, i2->arg[0]))
			i2->arg[0] = r;
		if (req(i->to, i2->arg[1]))
			i2->arg[1] = r;
	} else {
		assert(req(i->to, b->jmp.arg));
		b->jmp.arg = r;
	}
	i->to = r;
}

/* Redistribute trivial ops to point of use. */
/* Reduces register pressure. */
/* needs rpo, use; breaks use */
void
reassoc(Fn *fn)
{
	Blk *b;
	Ins *i;
	InsMov *im;
	uint n, nim;

	nim = 0;
	im = vnew(nim, sizeof im[0], PHeap);

	/* identify trivial ins */
	for (b = fn->start; b; b = b->link) {
		for (i = b->ins; i < &b->ins[b->nins]; i++)
			ireassoc(fn, b, i, &nim, &im);
	}

	/* duplicate trivial ins */
	movins(fn, im, nim, 0/*!del*/);

	/* create new tmps for dups */
	for (n = 0; n < nim; n++) {
		b = fn->rpo[im[n].to.bid];
		i = &b->ins[im[n].to.insn];
		trealloc(fn, b, i);
	}

	/* delete (now) unused ins */
	filluse(fn);
	nopunused(fn);

	if (debug['G']) {
		fprintf(stderr, "\n> After Reassociation:\n");
		printfn(fn, stderr);
	}
}
