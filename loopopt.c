#include "all.h"

typedef struct Cntr Cntr;
typedef struct Loop Loop;

static int
forloop(Blk *bh, Blk *bb)
{
	if (bh->npred == 2)
	if (bh->jmp.type == Jjnz)
	if (bb->npred == 1)
	if (bb->jmp.type == Jjmp)
	if (bb->s1 == bh)
		return 1;
	return 0;
}

static int
doloop(Blk *bh)
{
	if (bh->npred == 2)
	if (bh->jmp.type == Jjnz)
	if (bh->s1 == bh || bh->s2 == bh)
		return 1;
	return 0;
}

struct Loop {
	Blk *bp; /* pre-header */
	Blk *bh; /* header */
	Blk *bb; /* body */
};

static int
invariant(Ref r, Loop l, Fn *fn)
{
	Tmp *t;

	if (rtype(r) == RCon)
		return 1;
	assert(rtype(r) == RTmp);
	t = &fn->tmp[r.val];
	if (t->bid != l.bh->id)
	if (t->bid != l.bb->id)
		return 1;
	return 0;
}

struct Cntr {
	Phi *p; /* defining phi */
	Ref r0; /* initial value */
	Ref rc; /* post-increment */
	Ref ri; /* increment */
};

/* check if a phi defines an additive
 * induction variable
 */
static int
counter(Fn *fn, Loop l, Phi *p, Cntr *c)
{
	Tmp *t;
	Ins *i;

	assert(l.bh->npred == 2);
	assert(l.bh->pred[0] == l.bb || l.bh->pred[1] == l.bb);
	c->p = p;
	c->r0 = phiarg(p, l.bp);
	c->rc = phiarg(p, l.bb);
	if (KBASE(p->cls) != 0
	|| rtype(c->rc) != RTmp
	|| (t = &fn->tmp[c->rc.val])->bid != l.bb->id
	|| !(i = t->def)
	|| i->op != Oadd
	|| req(i->arg[0], p->to) == req(i->arg[1], p->to))
		return 0;
	c->ri = i->arg[req(i->arg[0], p->to)];
	assert(p->cls == i->cls);
	return invariant(c->ri, l, fn);
}

static void
mulredux(Fn *fn, Loop l, Cntr c)
{
	Ins *i, *ie, ia;
	Phi *p;
	Ref rm;

	/* dead simple case for now...
	 * majority case in practice */
	if (!req(c.r0, con01[0]) || !req(c.ri, con01[1]))
		return;

	ia = (Ins){.op = Oadd};
	ie = &l.bb->ins[l.bb->nins]; /* l.bb->ins may change */
	for (i=l.bb->ins; i<ie; i++) {
		/* TODO i->cls != p->cls is not necessary? */
		if (i->op != Omul
		|| i->cls != p->cls
		|| req(i->arg[0], p->to) == req(i->arg[1], p->to))
			continue;
		assert(KBASE(i->cls) == 0);
		rm = i->arg[req(i->arg[0], p->to)];
		if (!invariant(rm, l, fn))
			continue;

		ia.to = newtmp("lop", i->cls, fn);
		ia.cls = i->cls;
		ia.arg[0] = i->to;
		ia.arg[1] = rm;
		addins(&l.bb->ins, &l.bb->nins, &ia);
		p = alloc(sizeof *p);
		p->cls = i->cls;
		p->to = i->to;
		p->narg = 2;
		p->blk = vnew(2, sizeof p->blk[0], PFn);
		p->blk[0] = l.bp;
		p->blk[1] = l.bb;
		p->arg = vnew(2, sizeof p->arg[0], PFn);
		p->arg[0] = CON_Z;
		p->arg[1] = ia.to;
		p->link = l.bh->phi;
		l.bh->phi = p;
		*i = (Ins){.op = Onop};
	}
}

static void
addbase(Fn *fn, Loop l, Cntr c)
{
	Ins *i, *ii, *ib;
	Tmp *t, *ti;
	Use *u;
	Ref rb;
	uint n;

	/* dead simple case for now...
	 * majority case in practice */
	if (!req(c.r0, CON_Z))
		return;

	assert(rtype(c.p->to) == RTmp);
	t = &fn->tmp[c.p->to.val];
	if (t->nuse != 2)
		return;

	ii = ib = 0;
	for (u=t->use; u<&t->use[t->nuse]; u++) {
		if (u->type != UIns)
			return;
		i = u->u.ins;
		if (i->op != Oadd
		|| i->cls != c.p->cls
		|| u->bid != l.bb->id)
			return;
		assert(req(i->arg[0], c.p->to) || req(i->arg[1], c.p->to));
		if (req(i->to, c.rc)) {
			assert(rtype(i->to) == RTmp);
			ti = &fn->tmp[i->to.val];
			if (ti->nuse != 1)
				return;
			assert(ti->use[0].type == UPhi);
			assert(ti->use[0].bid == l.bh->id);
			assert(ti->use[0].u.phi == c.p);
			ii = i;
		} else {
			rb = i->arg[req(i->arg[0], c.p->to)];
			if (!invariant(rb, l, fn))
				return;
			assert(!req(rb, c.p->to));
			ib = i;
		}
	}
	n = phiargn(c.p, l.bp);
	assert(n != -1u && req(c.p->arg[n], CON_Z));
	c.p->arg[n] = rb;
	ii->arg[!req(ii->arg[0], c.p->to)] = ib->to;
	c.p->to = ib->to;
	*ib = (Ins){.op = Onop};
}

static void
counteropt(Fn *fn, void opt(Fn *, Loop, Cntr))
{
	Loop l;
	Cntr c;
	Phi *p;
	uint n;

	for (n=0; n<fn->nblk; n++) {
		l.bh = fn->rpo[n];
		if (forloop(l.bh, l.bh->s1))
			l.bb = l.bh->s1;
		else if (forloop(l.bh, l.bh->s2))
			l.bb = l.bh->s2;
		else if (doloop(l.bh))
			l.bb = l.bh; /* header and body */
		else
			continue;
		l.bp = l.bh->pred[l.bh->pred[0] == l.bh];
		assert(l.bh->loop > 1);
		assert(l.bh->loop == l.bb->loop);
		for (p=l.bh->phi; p; p=p->link)
			if (counter(fn, l, p, &c)) {
				assert(KBASE(p->cls) == 0);
				opt(fn, l, c);
			}
	}
}

void
loopopt(Fn *fn)
{
	counteropt(fn, mulredux);
	filluse(fn);
	counteropt(fn, addbase);
}
