#include "all.h"

static uint
u64_wbits(uint64_t v)
{
	uint n;

	n = 0;
	if (v >> 32) { n += 32; v >>= 32; }
	if (v >> 16) { n += 16; v >>= 16; }
	if (v >>  8) { n +=  8; v >>=  8; }
	if (v >>  4) { n +=  4; v >>=  4; }
	if (v >>  2) { n +=  2; v >>=  2; }
	if (v >>  1) { n +=  1; v >>=  1; }
	return n+v;
}

static int
EXTSIGNED[] = { /*extsb*/1, /*extub*/0, /*extsh*/1, /*extuh*/0, /*extsw*/1, /*extuw*/0 };

static uint
EXTMAXW[] = { /*extsb*/7, /*extub*/8, /*extsh*/15, /*extuh*/16, /*extsw*/31, /*extuw*/32 };

static uint
EXTW[] = { /*extsb*/8, /*extub*/8, /*extsh*/16, /*extuh*/16, /*extsw*/32, /*extuw*/32 };

static uint
STW[] = { /*storeb*/8, /*storeh*/16, /*storew*/32, /*storel*/64, /*stores*/32, /*stored*/64 };

/* is the ref used only as a narrow value? */
static int
usewidthle(Fn *fn, Ref r, uint wbits)
{
	Tmp *t;
	Use *u;
	Phi *p;
	int b;
	Ins *i;
	Ref rc;
	int64_t v;

	if (isconbits(fn, r, &v))
	if (u64_wbits(v) <= wbits)
		return 1;
	if (rtype(r) != RTmp)
		return 0;
	t = &fn->tmp[r.val];
	for (u = t->use; u < &t->use[t->nuse]; u++) {
		switch (u->type) {
		case UPhi:
			p = u->u.phi;
			if (p->visit)
				continue;
			p->visit = 1;
			b = usewidthle(fn, p->to, wbits);
			p->visit = 0;
			if (b)
				continue;
			break;
		case UIns:
			i = u->u.ins;
			assert(i != 0);
			if (i->op == Ocopy)
				if (usewidthle(fn, i->to, wbits))
					continue;
			if (isext(i->op)) {
				if (EXTW[i->op - Oextsb] <= wbits)
					continue;
				else
					if (usewidthle(fn, i->to, wbits))
						continue;;
			}
			if (i->op == Oand) {
				if (req(r, i->arg[0]))
					rc = i->arg[1];
				else {
					assert(req(r, i->arg[1]));
					rc = i->arg[0];
				}
				if (isconbits(fn, rc, &v))
				if (u64_wbits(v) <= wbits)
					continue;
				break;
			}
			if (isstore(i->op))
			if (req(r, i->arg[1]))
			if (STW[i->op - Ostoreb] > wbits)
				continue;
			break;
		default:
			break;
		}
		return 0;
	}
	return 1;
}

static Phi*
findphi(Fn *fn, uint bid, Ref to)
{
	Phi *p;
	for (p = fn->rpo[bid]->phi; p; p = p->link)
		if (req(p->to, to))
			break;
	assert(p);
	return p;
}

static uint
uint_min(uint v1, uint v2)
{
	return v1 < v2 ? v1 : v2;
}

/* is the ref def a narrow value? */
static int
defwidthle(Fn *fn, Ref r, uint wbits)
{
	Tmp *t;
	Phi *p;
	Ins *i;
	uint n;
	int64_t v;
	int x;

	if (isconbits(fn, r, &v))
	if (u64_wbits(v) <= wbits)
		return 1;
	if (rtype(r) != RTmp)
		return 0;
	t = &fn->tmp[r.val];
	if (t->cls != Kw)
		return 0;
	i = t->def;
	if (i == 0) {
		/* phi def */
		p = findphi(fn, t->bid, r);
		if (p->visit)
			return 1;
		p->visit = 1;
		for (n = 0; n < p->narg; n++)
			if (!defwidthle(fn, p->arg[n], wbits)) {
				p->visit = 0;
				return 0;
			}
		p->visit = 0;
		return 1;
	}
	/* ins def */
	if (i->op == Ocopy)
                return defwidthle(fn, i->arg[0], wbits);
	if (i->op == Oshr || i->op == Osar) {
		if (isconbits(fn, i->arg[1], &v))
		if (0 < v && v <= 32) {
			if (i->op == Oshr && 32-v <= wbits)
				return 1;
			if (0 <= v && v < 32 && wbits < 32)
				return defwidthle(fn, i->arg[0], uint_min((i->op == Osar ? 31 : 32), wbits+v));
		}
		return defwidthle(fn, i->arg[0], wbits);
	}
	if (iscmp(i->op, &x, &x))
		return wbits >= 1;
	if (i->op == Oand)
		return defwidthle(fn, i->arg[0], wbits) || defwidthle(fn, i->arg[1], wbits);
	if (i->op == Oor || i->op == Oxor)
		return defwidthle(fn, i->arg[0], wbits) && defwidthle(fn, i->arg[1], wbits);
	if (isext(i->op)) {
		if (EXTSIGNED[i->op - Oextsb])
			return defwidthle(fn, i->arg[0], uint_min(wbits, EXTMAXW[i->op - Oextsb]));
		if (EXTW[i->op - Oextsb] <= wbits)
			return 1;
		return defwidthle(fn, i->arg[0], wbits);
	}
	return 0;
}

/* is the ref a boolean - 0, 1 - value? */
int
iswu1(Fn *fn, Ref r)
{
	return defwidthle(fn, r, 1);
}

static int
isnarrowpar(Fn *fn, Ref r)
{
	Tmp *t;

	if (rtype(r) != RTmp)
		return 0;
	t = &fn->tmp[r.val];
	if (t->bid != fn->start->id || t->def == 0)
		return 0;
	return ispar(t->def->op);
}

/* Insert extub/extuh instructions in start for pars used only narrowly */
/* needs use; breaks use */
void
narrowpars(Fn *fn)
{
	Blk *b;
	int loop;
	Ins *i, *ins;
	uint npar, nins;
	enum O extop;
	Ref r;

	/* only useful for functions with loops */
	loop = 0;
	for (b = fn->start; b; b = b->link)
		if (b->loop > 1) {
			loop = 1;
			break;
		}
	if (!loop)
		return;

	b = fn->start;
	npar = 0;

	for (i = b->ins; i < &b->ins[b->nins]; i++) {
		if (!ispar(i->op))
			break;
		npar++;
	}

	if (npar == 0)
		return;

	nins = b->nins + npar;
	ins = vnew(nins, sizeof ins[0], PFn); //alloc(nins * sizeof ins[0]);
	memcpy(ins, b->ins, npar * sizeof ins[0]);
	memcpy(ins + 2*npar, b->ins + npar, (b->nins - npar) * sizeof ins[0]);
	b->ins = ins;
	b->nins = nins;

	for (i = b->ins; i < &b->ins[b->nins]; i++) {
		if (!ispar(i->op))
			break;
		extop = Onop;
		if (i->cls == Kw)
			if (usewidthle(fn, i->to, 16)) {
				if (usewidthle(fn, i->to, 8))
					extop = Oextub;
				else
					extop = Oextuh;
			}
		if (extop == Onop) {
			*(i+npar) = (Ins) {.op = Onop};
		} else {
			r = newtmp("vw", i->cls, fn);
			*(i+npar) = (Ins) {.op = extop, .cls = i->cls, .to = i->to, .arg = {r}};
			i->to = r;
		}
	}
}

/* used by GVN */
Ref
copyref(Fn *fn, Blk *b, Ins *i)
{
	static bits extcpy[] = {
		[WFull] = 0,
		[Wsb] = BIT(Wsb) | BIT(Wsh) | BIT(Wsw),
		[Wub] = BIT(Wub) | BIT(Wuh) | BIT(Wuw),
		[Wsh] = BIT(Wsh) | BIT(Wsw),
		[Wuh] = BIT(Wuh) | BIT(Wuw),
		[Wsw] = BIT(Wsw),
		[Wuw] = BIT(Wuw),
	};
	bits bext;
	Tmp *t;
	int64_t v;
	int is0;

	if (i->op == Ocopy)
		return i->arg[0];

	/* op identity value */
	if (optab[i->op].hasid)
	if (KBASE(i->cls) == 0) /* integer only - fp NaN! */
	if (req(i->arg[1], con01[optab[i->op].idval]))
	if (!optab[i->op].cmpeqwl || iswu1(fn, i->arg[0]))
		return i->arg[0];

	/* idempotent op with identical args */
	if (optab[i->op].idemp)
	if (req(i->arg[0], i->arg[1]))
		return i->arg[0];

	/* integer cmp with identical args */
	if (optab[i->op].cmpeqwl || optab[i->op].cmplgtewl)
	if (req(i->arg[0], i->arg[1]))
		return con01[optab[i->op].eqval];

	/* cmpeq/ne 0 with 0/non-0 inference from dominating jnz */
	if (optab[i->op].cmpeqwl)
	if (req(i->arg[1], con01[0]))
	if (is0non0(fn, b, i->arg[0], argcls(i,0), &is0))
		return con01[optab[i->op].eqval^is0^1];

	/* redundant and mask */
	if (i->op == Oand)
	if (isconbits(fn, i->arg[1], &v))
	if (((v+1) & v) == 0) /* v == 2^N-1 */
	if (defwidthle(fn, i->arg[0], u64_wbits(v)))
		return i->arg[0];

	if (!isext(i->op) || rtype(i->arg[0]) != RTmp)
		return R;
	if (i->op == Oextsw || i->op == Oextuw)
	if (i->cls == Kw)
		return i->arg[0];

	t = &fn->tmp[i->arg[0].val];
	assert(KBASE(t->cls) == 0);
	if (i->cls == Kl && t->cls == Kw)
		return R;
	bext = extcpy[t->width];
	if ((BIT(Wsb + (i->op-Oextsb)) & bext) != 0)
		return i->arg[0];

	if (!isnarrowpar(fn, i->arg[0]))
	if (usewidthle(fn, i->to, EXTW[i->op - Oextsb]))
		return i->arg[0];
	if (defwidthle(fn, i->arg[0], EXTMAXW[i->op - Oextsb]))
		return i->arg[0];

	return R;
}
