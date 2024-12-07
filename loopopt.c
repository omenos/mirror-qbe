#include "all.h"

static int
forloop(Blk *bh, Blk *bb)
{
	if (bh->npred == 2)
	if (bh->jmp.type == Jjnz)
	if (bb->npred == 1)
	if (bb->jmp.type == Jjmp)
	if (bb->jmp.s[0].b == bh)
		return 1;
	return 0;
}

static int
doloop(Blk *bh)
{
	if (bh->npred == 2)
	if (bh->jmp.type == Jjnz)
	if (bh->jmp.s[0].b == bh || bh->jmp.s[1].b == bh)
		return 1;
	return 0;
}

static int
loopvar(Fn *fn, Blk *bh, Blk *bb, uint np, Ref *prl, Ref *pr0, Ref *pri)
{
	Blk *bp;
	Phi *p;
	Suc *sb, *sp;
	Tmp *t;
	Ins *i;

	assert(bh->npred == 2);
	assert(bh->pred[0] == bb || bh->pred[1] == bb);
	bp = bh->pred[bh->pred[0] == bb]; /* pre-header */
	assert(np < bh->nphi);
	p = &bh->phi[np];
	if (KBASE(p->cls) != 0)
		return 0; /* not integer */
	sp = getsuc(bp, bh);
	assert(sp->nr == bh->nphi);
	*pr0 = sp->r[np];
	sb = getsuc(bb, bh);
	assert(sb->nr == bh->nphi);
	*prl = sb->r[np];
	if (rtype(*prl) != RTmp)
		return 0; /* loop var must be an incremented tmp */
	t = &fn->tmp[prl->val];
	if (t->bid != bb->id || t->def == 0)
		return 0; /* loop var must be defined by an add ins in the body */
	i = t->def;
	if (i->op != Oadd || req(i->arg[0], p->to) == req(i->arg[1], p->to))
		return 0;
	*pri = i->arg[req(i->arg[0], p->to)];
	assert(p->cls == i->cls);
	if (rtype(*pri) == RTmp) {
		t = &fn->tmp[pri->val];
		if (t->bid == bh->id || t->bid == bb->id)
			return 0;
		return 1;
	}
	else {
		assert(rtype(*pri) == RCon);
		return 1;
	}
	return 0;
}

static void
mulredux(Fn *fn, Blk *bh, Blk *bb, Blk *bp, uint np, Ref rl, Ref r0, Ref ri, Ins **pvins, uint *pnins)
{
	Ins *i;
	Tmp *t;
	Ref r1, rlop;
	Phi *p;
	Suc *sb, *sp;

	/* dead simple case for now... majority case in practice */
	if (!req(r0, con01[0]) || !req(ri, con01[1]))
		return;

	assert(!req(rl, R)); /* rl unused */
	assert(np < bh->nphi);
	p = &bh->phi[np];
	for (i = bb->ins; i < &bb->ins[bb->nins]; i++) {
		/* TODO i->cls != p->cls is not necessary? */
		if (i->op != Omul || i->cls != p->cls
		    || req(i->arg[0], p->to) == req(i->arg[1], p->to))
			continue;
		r1 = i->arg[req(i->arg[0], p->to)];
		if (rtype(r1) == RTmp) {
			t = &fn->tmp[r1.val];
			if (t->bid == bh->id || t->bid == bb->id)
				continue;
		} else
			assert(rtype(r1) == RCon);
		assert(KBASE(i->cls) == 0);

		rlop = newtmp("lop", i->cls, fn);
		vgrow(&bh->phi, ++bh->nphi);
		bh->phi[bh->nphi-1] = (Phi){.to = i->to, .cls = i->cls};
		sp = getsuc(bp, bh);
		vgrow(&sp->r, ++sp->nr);
		sp->r[sp->nr-1] = con01[0];
		assert(sp->nr == bh->nphi);
		sb = getsuc(bb, bh);
		vgrow(&sb->r, ++sb->nr);
		sb->r[sp->nr-1] = rlop;
		assert(sb->nr == bh->nphi);
		addins(pvins, pnins, &(Ins){.to = rlop, .op = Oadd, .cls = i->cls,
				.arg = {i->to, r1}});
		*i = (Ins){.op = Onop};
	}
}

static void
addbase(Fn *fn, Blk *bh, Blk *bb, Blk *bp, uint np, Ref rl, Ref r0, Ref ri, Ins **pvins, uint *pnins)
{
	Ins *i, *ii, *ib;
	Tmp *t, *ti, *tb;
	Use *u;
	Ref rb;
	Phi *p;
	Suc *sp;

	/* dead simple case for now... majority case in practice */
	if (!req(r0, con01[0]))
		return;

	assert(!req(ri, R)); /* unused */
	assert(pvins && pnins); /* unused */
	assert(np < bh->nphi);
	p = &bh->phi[np];
	assert(rtype(p->to) == RTmp);
	t = &fn->tmp[p->to.val];
	if (t->nuse != 2)
		return;
	
	i = ib = 0;
	for (u = t->use; u < &t->use[t->nuse]; u++) {
		if (u->type != UIns)
			return;
		i = u->u.ins;
		if (i->op != Oadd || i->cls != p->cls || u->bid != bb->id)
			return;
		assert(req(i->arg[0], p->to) || req(i->arg[1], p->to));
		if (req(i->to, rl)) {
			assert(rtype(i->to) == RTmp);
			ti = &fn->tmp[i->to.val];
			if (ti->nuse != 1)
				return;
			assert(ti->use[0].type == UPhi);
			assert(ti->use[0].bid == bh->id);
			assert(ti->use[0].u.p.np == np);
			assert(ti->use[0].u.p.pbid == bb->id);
			ii = i;
			continue;
		}
		rb = i->arg[req(i->arg[0], p->to)];
		if (req(rb, p->to))
			return;
		if (rtype(rb) == RTmp) {
			tb = &fn->tmp[rb.val];
			if (tb->bid == bh->id || tb->bid == bb->id)
				return;
		} else
			assert(rtype(rb) == RCon);
		ib = i;
	}
	assert(ii);
	assert(ib);
	sp = getsuc(bp, bh);
	assert(sp->nr == bh->nphi);
	assert(req(sp->r[np], con01[0]));
	sp->r[np] = rb;
	assert(req(ii->arg[0], p->to) != req(ii->arg[1], p->to));
	ii->arg[!req(ii->arg[0], p->to)] = ib->to;
	p->to = ib->to;
	*ib = (Ins){.op = Onop};
}

typedef void optfn_t(Fn *, Blk *, Blk *, Blk *, uint, Ref, Ref, Ref, Ins **, uint *);

static void
loopvaropt(Fn *fn, optfn_t *optfn)
{
	uint bid;
	Blk *bh, *bb, *bp; /* header, body, pre-header */
	Phi *p;
	Ins *vins;
	uint nins, np;
	Ref rl, r0, ri; /* loop var, loop var init, loop var inc */
	
	nins = 0;
	vins = vnew(nins, sizeof vins[0], PFn); /* TODO use insb */
	
	for (bid = 0; bid < fn->nblk; bid++) {
		bh = fn->rpo[bid];
		if (forloop(bh, bh->jmp.s[0].b))
			bb = bh->jmp.s[0].b;
		else if (forloop(bh, bh->jmp.s[1].b))
			bb = bh->jmp.s[1].b;
		else if (doloop(bh))
			bb = bh; /* header and body */
		else
			continue;
		bp = bh->pred[bh->pred[0] == bh];
		assert(bh->loop > 1);
		assert(bh->loop == bb->loop);
		nins = 0;
		for (np = 0; np < bh->nphi; np++)
			if (loopvar(fn, bh, bb, np, &rl, &r0, &ri)) {
				p = &bh->phi[np];
				assert(KBASE(p->cls) == 0);
				optfn(fn, bh, bb, bp, np, rl, r0, ri, &vins, &nins);
			}
 		addnins(&bb->ins, &bb->nins, vins, nins);
	}
}

void
loopopt(Fn *fn)
{
	/* encourage simple loops */
	ifelim(fn);
	fillcfg(fn);
	blkmerge(fn);
	fillcfg(fn);
	filluse(fn);
	fillloop(fn);

	loopvaropt(fn, mulredux);
	filluse(fn);
	loopvaropt(fn, addbase);
}
