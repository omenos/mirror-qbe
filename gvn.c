#include "all.h"

/* literal constants 0, 1 */
Ref con01[2];

static inline uint
mix(uint x0, uint x1)
{
	return x0 + 17*x1;
}

static inline uint
rhash(Ref r)
{
	return mix(r.type, r.val);
}

static uint
ihash(Ins *i)
{
	uint a0h, a1h, ah, h;

	a0h = rhash(i->arg[0]);
	a1h = rhash(i->arg[1]);
	ah = mix(a0h, a1h);
	h = mix(i->cls, i->op);
	h = mix(h, ah);

	return h;

}

static int
ieq(Ins *ia, Ins *ib)
{
	if (ia->cls == ib->cls)
	if (ia->op == ib->op)
	if (req(ia->arg[0], ib->arg[0]))
	if (req(ia->arg[1], ib->arg[1]))
		return 1;
	return 0;
}

static Ins** gvntbl;
static uint gvntbln;
static uint lookupn;
static uint proben;
static uint maxproben;

static Ins *
gvndup(Ins *i, int insert) {
	uint idx, n;
	Ins *i2;

	lookupn++;

	idx = ihash(i) % gvntbln;
	for (n = 1;; n++) {
		proben++;
		if (n > maxproben)
			maxproben = n;
		i2 = gvntbl[idx];
		if (!i2)
			break;
		if (ieq(i, i2))
			return i2;

		idx++;
		if (gvntbln <= idx)
			idx = 0;
	}
	/* not found */
	if (insert) {
		gvntbl[idx] = i;
	}
	return 0;
}

static void
replaceref(Ref *r, Ref r1, Ref r2)
{
	if (req(*r, r1))
		*r = r2;
}

static void
replacepuse(Phi *p, Ref r1, Ref r2)
{
	Ref *a;

	for (a = p->arg; a < &p->arg[p->narg]; a++)
		replaceref(a, r1, r2);
}

static void
replaceiuse(Ins *i, Ref r1, Ref r2)
{
	replaceref(&i->arg[0], r1, r2);
	replaceref(&i->arg[1], r1, r2);
}

static void
replacejuse(Blk* b, Ref r1, Ref r2)
{
	replaceref(&b->jmp.arg, r1, r2);
}

static void
replaceuse(Fn *fn, Use* u, Ref r1, Ref r2)
{
	Tmp *t2;
	Blk *b;

	t2 = rtype(r2) == RTmp ? &fn->tmp[r2.val] : 0;
	b = fn->rpo[u->bid];

	switch (u->type) {
	case UXXX:
		die("unreachable");
		break;
	case UPhi:
		replacepuse(u->u.phi, r1, r2);
		if (t2)
			adduse(t2, UPhi, b, u->u.phi);
		break;
	case UIns:
		replaceiuse(u->u.ins, r1, r2);
		if (t2)
			adduse(t2, UIns, b, u->u.ins);
		break;
	case UJmp:
		replacejuse(fn->rpo[u->bid], r1, r2);
		if (t2)
			adduse(t2, UJmp, b);
		break;
	}
}

static void
replaceuses(Fn *fn, Ref r1, Ref r2)
{
	Tmp *t1;
	Use *u;

	assert(rtype(r1) == RTmp);
	t1 = &fn->tmp[r1.val];

	for (u = t1->use; u < &t1->use[t1->nuse]; u++)
		replaceuse(fn, u, r1, r2);

	t1->nuse = 0;
}

static void
rmuse(Fn *fn, Blk *b, uint ty, Ins *i, Phi *p, Ref r, int strict)
{
	Tmp *t;
	Use *u;
	int found, rm;

	if (rtype(r) != RTmp)
		return;
	found = 0;
	t = &fn->tmp[r.val];
	for (u = t->use; u < &t->use[t->nuse];) {
		rm = 0;
		if (u->type == ty) {
			switch (ty) {
			case UXXX:
				die("unreachable");
				break;
			case UIns:
				assert(p == 0);
				assert(i);
				rm = u->u.ins == i;
				break;
			case UPhi:
				assert(i == 0);
				assert(p);
				rm = u->u.phi == p;
				break;
			case UJmp:
				assert(i == 0);
				assert(p == 0);
				rm = u->bid == b->id;
				break;
			default:
				die("unreachable");
				break;
			}
		}
		if (rm) {
			found++;
			assert(u < &t->use[t->nuse]);
			assert(u->bid == b->id);
			/* careful - deleting below iterator */
			memcpy(u, u+1, ((t->nuse) - ((u+1)-t->use)) * sizeof u[0]);
			t->nuse--;
		} else
			u++;
	}
	if (strict)
		assert(found);
}

static int
phieq(Phi *pa, Phi *pb)
{
	uint n;

	assert(pa->narg == pb->narg);
	for (n=0; n<pa->narg; n++) {
		if (!req(pa->arg[n], phiarg(pb, pa->blk[n])))
			return 0;
	}
	return 1;
}

static void
killphi(Fn *fn, Blk *b, Phi **pp, Ref r)
{
	Phi *p;
	uint n;

	p = *pp;
	replaceuses(fn, p->to, r);
	assert(b->npred == p->narg);
	for (n = 0; n < p->narg; n++)
		rmuse(fn, b, UPhi, 0, p, p->arg[n], 0/*!strict TODO dups*/);
	p->narg = 0; /* mark as unused - TODO should not be necessary with rmuse*/
	*pp = p->link;
}

static void
ifphiopt(Fn *fn, Blk *b)
{
	Blk *ifb, *thenb, *elseb, *tmp;
	Phi *p, **pp;
	Tmp *t;
	Ref argt, argf, r1;
	int k, x, caninv;

	/* is b the join blk of an if[-then][-else] graphlet? */
	if (!ifjoin(b, &ifb, &thenb, &elseb))
		return;

	assert(ifb->jmp.type == Jjnz);
	assert(ifb->s1 == b || (ifb->s1 == thenb && thenb->s1 == b));
	assert(ifb->s2 == b || (ifb->s2 == elseb && elseb->s1 == b));
	if (!iswu1(fn, ifb->jmp.arg))
		return; /* no opportunity */

	caninv = 1;
	for (p = b->phi; p; p = p->link)
		if (req(phiarg(p, elseb), con01[0])) {
			caninv = 0;
			break;
		}

	/* phi bool 1/0 "copy" */
	for (pp = &b->phi; *pp;) {
		p = *pp;
		assert(p->narg == 2);
		argt = phiarg(p, thenb);
		argf = phiarg(p, elseb);
		/* jnz jmp.arg in phi is 1/0 */
		if (req(argt, ifb->jmp.arg)) {
			if (!req(argf, ifb->jmp.arg))
				rmuse(fn, b, UPhi, 0, p, argt, 1/*strict*/);
			argt = p->arg[phiargn(p, thenb)] = con01[1];
		}
		if (req(argf, ifb->jmp.arg)) {
			rmuse(fn, b, UPhi, 0, p, argf, 1/*strict*/);
			argf = p->arg[phiargn(p, elseb)] = con01[0];
		}
		/* prefer 0 as argf and/or 1 as argt, so try to invert the cmp */
		if (caninv &&
		    ((req(argt, con01[0]) && !req(argf, con01[0])) ||
		     (req(argf, con01[1]) && !req(argt, con01[1])))) {
			assert(rtype(ifb->jmp.arg) == RTmp);
			t = &fn->tmp[ifb->jmp.arg.val];
			if (t->nuse == 1)
			if (t->def && iscmp(t->def->op, &k, &x) && KBASE(k) == 0) {
				assert(t->use[0].type == UJmp);
				assert(t->bid == ifb->id);
				t->def->op = invcmpwl(t->def->op);
				tmp = ifb->s1;
				ifb->s1 = ifb->s2;
				ifb->s2 = tmp;
				r1 = argt; argt = argf; argf = r1;
				caninv = 0; /* only once */
			}
		}
		if (req(argt, con01[1]) && req(argf, con01[0])) {
			killphi(fn, b, pp, ifb->jmp.arg);
			caninv = 0; /* used already */
			continue;
		}
		pp = &(*pp)->link;
	}
}

/* phi "copy" - singleton or all args identical */
static void
copyphielim(Fn *fn, Blk *b) {
	Phi *p, **pp;
	uint n;

	for (pp = &b->phi; *pp;) {
		p = *pp;
		assert(p->narg == b->npred);
		for (n = 0; n < p->narg-1; n++) {
			if (!req(p->arg[n], p->arg[n+1]))
				goto Skip;
		}
		killphi(fn, b, pp, p->arg[0]);
		continue;
	Skip:;
		pp = &(*pp)->link;
	}
}

/* redundant phis */
static void
dupphielim(Fn *fn, Blk *b) {
	Phi *p, *p2, **pp;

	/* O(N^2.M) but meh */
	for (pp = &b->phi; *pp;) {
		p = *pp;
		assert(p->narg == b->npred);
		for (p2 = p->link; p2; p2 = p2->link) {
			assert(p2->narg == b->npred);
			if (phieq(p, p2)) {
				killphi(fn, b, pp, p2->to);
				goto Skip;
			}
		}
		pp = &(*pp)->link;
	Skip:;
	}
	return;
}

static void
dedupphis(Fn *fn, Blk *b) {
	ifphiopt(fn, b);
	copyphielim(fn,b);
	dupphielim(fn, b);
}

static int
rcmp(Ref a, Ref b)
{
	if (rtype(a) != rtype(b))
		return rtype(a)-rtype(b);
	return a.val - b.val;
}

static void
normins(Fn *fn, Ins *i)
{
	uint n;
	int64_t v;
	Ref r;

	/* truncate constant bits to 32 bits for "s"/w" uses */
	for (n = 0; n < 2; n++) {
		if (!KWIDE(argcls(i, n)))
		if (isconbits(fn, i->arg[n], &v))
		if ((v & 0xffffffff) != v)
			i->arg[n] = getcon(v & 0xffffffff, fn);
	}
	/* order arg[0] <= arg[1] for commutative ops, preferring RTmp in arg[0] */
	if (optab[i->op].commutes)
	if (rcmp(i->arg[0], i->arg[1]) > 0) {
		r = i->arg[1];
		i->arg[1] = i->arg[0];
		i->arg[0] = r;
	}
}

static Ref
negcon(Fn *fn, int cls, Ref r)
{
	int64_t v, v1;

	assert(isconbits(fn, r, &v));
	assert(KBASE(cls) == 0);
	v1 = -v;
	if (cls == Kw)
		v1 = ((int64_t)(-(int32_t)v)) & 0xffffffff;
	return getcon(v1, fn);
}

static void
assoccon(Fn *fn, Blk *b, Ins *i1)
{
	Tmp *t2;
	Ins *i2, i;
	Ref r0, r1, rc;
	int op1, op2;
	int64_t v1, v2, vc;

	op1 = i1->op;
	if (op1 == Osub)
		op1 = Oadd;
	if (!optab[op1].assoc || KBASE(i1->cls) != 0 || rtype(i1->arg[0]) != RTmp
	    || !isconbits(fn, i1->arg[1], &v1) || (optab[op1].hasid && v1 == optab[op1].idval))
		return;
	t2 = &fn->tmp[i1->arg[0].val];
	if (t2->def == 0)
		return;
	i2 = t2->def;
	op2 = i2->op;
	if (op2 == Osub)
		op2 = Oadd;
	if (op1 != op2 || rtype(i2->arg[0]) != RTmp || !isconbits(fn, i2->arg[1], &v2))
		return;
	assert(KBASE(i2->cls) == 0);
	assert(i1->cls == Kl || i2->cls == Kw);
	r0 = i1->arg[1];
	if (i1->op == Osub)
		r0 = negcon(fn, i1->cls, r0);
	r1 = i2->arg[1];
	if (i2->op == Osub)
		r1 = negcon(fn, i2->cls, r1);
	i = (Ins){.to = i2->to, .op = op2, .cls = i2->cls, .arg = {r0, r1}};
	rc = foldref(fn, &i);
	assert(isconbits(fn, rc, &vc));
	if (op1 == Oadd) {
		if (i2->cls == Kw) {
			if ((int32_t)vc < 0) {
				op1 = Osub;
				rc = negcon(fn, Kw, rc);
			}
		} else {
			assert(i2->cls == Kl);
			if (vc < 0) {
				op1 = Osub;
				rc = negcon(fn, Kl, rc);
			}
		}
	}
	i1->op = op1;
	rmuse(fn, b, UIns, i1, 0, i1->arg[0], 1/*strict*/);
	i1->arg[0] = i2->arg[0];
	adduse(&fn->tmp[i1->arg[0].val], UIns, b, i1);
	i1->arg[1] = rc;
}

static void
killins(Fn *fn, Blk *b, Ins *i, Ref r1, Ref r2)
{
	replaceuses(fn, r1, r2);
	rmuse(fn, b, UIns, i, 0, i->arg[0], 1/*strict*/);
	if (!req(i->arg[0], i->arg[1]))
		rmuse(fn, b, UIns, i, 0, i->arg[1], 1/*strict*/);
	*i = (Ins){.op = Onop};
}

static void
dedupi(Fn *fn, Blk *b, Ins *i)
{
	Ref r2;
	Ins *i2;

	if (i->op == Onop || i->op == Odbgloc)
		return;

	normins(fn, i);

	if (optab[i->op].ispinned)
		return;
	assert(rtype(i->to) == RTmp);

	/* merge associative ops with constant arg[1] */
	assoccon(fn, b, i);

	/* effective copy? */
	r2 = copyref(fn, b, i);
	if (!req(r2, R)) {
		killins(fn, b, i, i->to, r2);
		return;
	}

	/* effective constant? */
	r2 = foldref(fn, i);
	if (!req(r2, R)) {
		killins(fn, b, i, i->to, r2);
		return;
	}

	/* do not dedup (trapping) ins that GCM will not move */
	if (isfixed(fn, i))
		return;

	/* duplicate? */
	i2 = gvndup(i, 1);
	if (i2) {
		killins(fn, b, i, i->to, i2->to);
		return;
	}
}

static void
dedupins(Fn *fn, Blk *b)
{
	Ins *i;

	for (i = b->ins; i < &b->ins[b->nins]; i++)
		dedupi(fn, b, i);
}

int
cmpeq0def(Fn *fn, Ref r, Ref *arg0, int *cls, int *eqval)
{
	Ins *i;

	if (rtype(r) != RTmp)
		return 0;
	i = fn->tmp[r.val].def;
	if (i)
	if (optab[i->op].cmpeqwl)
	if (req(i->arg[1], con01[0])) {
		*arg0 = i->arg[0];
		*cls = argcls(i, 0);
		*eqval = optab[i->op].eqval;
		return 1;
	}
	return 0;
}

static int
branchdom(Fn *fn, Blk *bif, Blk *bbr1, Blk *bbr2, Blk *b)
{
	if (bif->jmp.type == Jjnz)
	if (b != bif)
	if (dom(bbr1, b))
	if (!reachesnotvia(fn, bbr2, b, bif))
		return 1;
	return 0;
}

static int
dom0non0(Fn *fn, Blk *bdom, Blk *b, int *is0)
{
	if (branchdom(fn, bdom, bdom->s1, bdom->s2, b)) {
		*is0 = 0;
		return 1;
	}
	if (branchdom(fn, bdom, bdom->s2, bdom->s1, b)) {
		*is0 = 1;
		return 1;
	}
	return 0;
}

/* infer 0/non-0 value from dominating jnz */
int
is0non0(Fn *fn, Blk *b, Ref r, int cls, int *is0)
{
	Blk *bdom;
	Ref arg0;
	int cls1, eqval;

	for (bdom = b->idom; bdom; bdom = bdom->idom) {
		if (bdom->jmp.type != Jjnz)
			continue;
		if (cls == Kw)
		if (req(r, bdom->jmp.arg))
		if (dom0non0(fn, bdom, b, is0))
			return 1;
		if (cmpeq0def(fn, bdom->jmp.arg, &arg0, &cls1, &eqval))
		if (cls == cls1)
		if (req(r, arg0))
		if (dom0non0(fn, bdom, b, is0)) {
			*is0 = *is0 ^ eqval;
			return 1;
		}
	}
	return 0;
}

static int
usecls(Use *u, Ref r)
{
	switch (u->type) {
	case UXXX: break;
	case UIns:
		/* safe to take arg[0] cls if both args == r, even for store */
		if (req(u->u.ins->arg[0], r))
			return argcls(u->u.ins, 0);
		if (req(u->u.ins->arg[1], r))
			return argcls(u->u.ins, 1);
		break;
	case UPhi: return u->u.phi->cls;
	case UJmp: return Kw;
	}
	die("unreachable");
}

static void
propjnz0(Fn *fn, Blk *bif, Blk *s0, Blk *snon0, Ref r, int cls)
{
	Blk *b;
	Tmp *t;
	Use *u;

	if (s0->npred != 1 || rtype(r) != RTmp)
		return;
	t = &fn->tmp[r.val];
	for (u = t->use; u < &t->use[t->nuse]; u++) {
		b = fn->rpo[u->bid];
		if (usecls(u, r) == cls)
		if (branchdom(fn, bif, s0, snon0, b))
			replaceuse(fn, u, r, con01[0]);
	}
}

static void
dedupjmp(Fn *fn, Blk *b) {
	Blk *s1s2[2];
	int64_t v;
	Ref arg0;
	int cls, eqval, is0;

	if (b->jmp.type != Jjnz)
		return;

	/* propagate jmp arg as 0 thru s2 */
	propjnz0(fn, b, b->s2, b->s1, b->jmp.arg, Kw);
	/* propagate cmp eq/ne 0 def of jmp arg as 0 */
	s1s2[0] = b->s1; s1s2[1] = b->s2;
	if (cmpeq0def(fn, b->jmp.arg, &arg0, &cls, &eqval))
		propjnz0(fn, b, s1s2[eqval^1], s1s2[eqval], arg0, cls);

	/* collapse trivial/constant jnz to jmp */
	v = 1;
	is0 = 0;
	if (b->s1 == b->s2
	    || isconbits(fn, b->jmp.arg, &v)
	    || is0non0(fn, b, b->jmp.arg, Kw, &is0)) {
		if (v == 0 || is0)
			b->s1 = b->s2;
		/* we later move active ins out of dead blks */
		b->s2 = 0;
		b->jmp.type = Jjmp;
		rmuse(fn, b, UJmp, 0, 0, b->jmp.arg, 1/*strict*/);
		b->jmp.arg = R;
		return;
	}
}

/* rebuild rpo pred use */
/* careful not to lose active ins in dead blks */
static void
rebuildcfg(Fn *fn) {
	uint n, prevnblk;
	Blk **prevrpo;
	Blk *b;
	Ins *i;

	prevnblk = fn->nblk;
	prevrpo = emalloc(prevnblk * sizeof prevrpo[0]);
	memcpy(prevrpo, fn->rpo, prevnblk * sizeof prevrpo[0]);

	fillcfg(fn); // TODO - OK?

	for (n=0; n<prevnblk; n++) {
		b = prevrpo[n];
		if (b->id == -1u) {
			assert(b != fn->start);
			/* blk unreachable after GVN */
			for (i = b->ins; i < &b->ins[b->nins]; i++)
				if (i->op != Onop)
				if (!optab[i->op].ispinned)
				if (gvndup(i, 0) == i)
					/* (possibly) active ins - add to start blk */
					addins(&fn->start->ins, &fn->start->nins, i);
		}
	}
	free(prevrpo);
}

/* https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf */
/* require rpo pred ssa use */
/* recreates rpo */
/* breaks pred use dom ssa (GCM fixes ssa) */
void
gvn(Fn *fn)
{
	uint n, nins;
	Blk *b;
	Phi *p;

	/* facilitate jnz simplification */
	blkmerge(fn);
	fillcfg(fn);
	filluse(fn);
	filldom(fn);

	con01[0] = getcon(0, fn);
	con01[1] = getcon(1, fn);

	nins = 0;
	for (b=fn->start; b; b=b->link)
		for (p = b->phi; p; p = p->link)
			p->visit = 0;

	/* facilitate ext elimination */
	fillloop(fn);
	narrowpars(fn);
	filluse(fn);
	ssacheck(fn);

	for (b=fn->start; b; b=b->link)
		nins += b->nins;

	gvntbln = nins + nins/2;
	gvntbl = emalloc(gvntbln * sizeof gvntbl[0]);
	lookupn = 0;
	proben = 0;
	maxproben = 0;

	/* GVN */
	clrbvisit(fn);
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		dedupphis(fn, b);
		dedupins(fn, b);
		dedupjmp(fn, b);
	}

	rebuildcfg(fn);

	free(gvntbl);
	gvntbl = 0;
	gvntbln = 0;
	lookupn = 0;
	proben = 0;
	maxproben = 0;

	if (debug['G']) {
		fprintf(stderr, "\n> After GVN:\n");
		printfn(fn, stderr);
	}
}
