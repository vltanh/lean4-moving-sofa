# A stronger endpoint-arm criterion and two explicit curvature-excess windows

**Scope.** This advances the still-unproved weighted one-turn upper bound. It strengthens the sufficient endpoint-arm threshold from 2 to sqrt(17)/2, and confines every possible failure of unit curvature to two short, fixed intervals. It does not establish that an actual maximizer meets the stronger threshold. It does not prove unrestricted ambidextrous optimality. Labels CG are local.

Baseline: `942c3b85553843c6d7d4ced926c1e73e31394989`. Inputs are WR1, AR7/AR5', and PT3 with TS1--TS2. The argument below is pen and paper; no saturated-exposure ODE is assumed. The earlier input chain remains subject to independent review.

## 1. Retain the actual differential inequalities

For any global maximizer of the signed objective Psi, set L=pi/2 and use

$$
p=f'-g+1,\quad q=g'+f-1,\quad u=f''+f,\quad v=g''+g.
$$

The previously established conditions are

$$
p'=u-1-q,\qquad q'=v-1+p,\qquad
p(0)=1/2,\quad q(L)=-1/2,
$$

$$
p\le1,\quad q\ge-1,\quad
0\le u\le\kappa(q),\quad0\le v\le\kappa(p),
\qquad\kappa(z)=\max\{|z|,(1+|z|)/2\}.
\tag{CG.1}
$$

On {p>0,q>0}, AR7 gives u=0 and v<=1/2. On q>0, p'<=-1/2; once p<0, q'<=-1/2. AR5' further shows that every positive-q component starting after time zero has height at most 1/8. These facts hold almost everywhere, with p,q Lipschitz.

Write

$$d_R=1+q(0),\qquad d_L=1-p(L).$$

PT3 and TS2 give d_R,d_L<=9/4 for every weighted maximizer. AR5' consequently bounds q<=5/4 and p>=-5/4 throughout the interval. Thus u,v<=5/4 almost everywhere. PT3 and TS1 also give full niche height at most one half.

## 2. An energy inequality before the first zero of p

Suppose q(0)>0 and consider the initial positive-q component. While p>0, define

$$E(t)=(p(t)-1/2)^2+(q(t)+1)^2.$$

Here u=0 and v<=1/2. Direct differentiation gives the exact identity

$$
\boxed{E'(t)=2(q(t)+1)(v(t)-1/2)\le0.}
\tag{CG.2}
$$

Only an inequality is needed: no exposure is assumed to attain its upper bound. If beta is the first zero of p in that positive-q component, continuity gives

$$
\boxed{(q(\beta)+1)^2+1/4\le d_R^2.}
\tag{CG.3}
$$

On the preceding part q is nonincreasing: p starts at 1/2 and decreases while q>0, so q'=v-1+p<=p-1/2<=0. On the subsequent part of the same component, p remains negative and q decreases with derivative at most -1/2.

## 3. Improved sufficient arm bound

**Theorem CG1.** For a weighted global maximizer,

$$
\boxed{d_R\le\sqrt{17}/2\quad\Longrightarrow\quad u\le1\text{ a.e. on }(0,L).}
\tag{CG.4}
$$

By reflection, d_L<=sqrt(17)/2 implies v<=1. Therefore the two bounds

$$
\boxed{d_R,d_L\le\sqrt{17}/2}
\tag{CG.5}
$$

suffice for the sharp weighted value Psi=M/2 by the already stated AR4/SR1/AF3 chain. For the value-only goal, it suffices that one attained weighted maximizer satisfy CG.5.

**Proof.** If q(0)<=1, AR5' gives q<=1 everywhere, and q>=-1 with CG.1 gives u<=1. Suppose q(0)>1. Any q>1 must belong to the initial positive-q component. Before p first reaches zero there, u=0. At its first zero, CG.3 and d_R^2<=17/4 give (q(beta)+1)^2<=4. Since q(beta)>0, this gives q(beta)<=1. Afterwards q decreases as long as that component lasts. Later positive components have q<=1/8. Thus q>1 occurs only where p>0 and u=0; at all remaining angles kappa(q)<=1. If q reaches zero before p does, the same conclusion follows without using CG.3. Reflection sends (p,q)(t) to (-q(L-t),-p(L-t)), giving the second assertion. QED.

Since sqrt(17)>4, the new criterion is strictly weaker than the old arm requirement d<=2. It is still stronger than the available upper bound 9/4. The remaining potentially offending endpoint range is (sqrt(17)/2,9/4], not (2,9/4].

## 4. No excess can begin before arcsin(2/9)

Set beta0=arcsin(2/9). Suppose an angle with q>1 belongs to the initial positive-q component, and beta is its first possible zero of p. On [0,beta), u=0 and v<=1/2. The equations give

$$p''+p=1-v\ge1/2$$

in the weak sense, with p(0)=1/2 and p'(0)=-d_R. The integral solution is

$$
p(t)=1/2-d_R\sin t+
\int_0^t\sin(t-s)(1/2-v(s))\,ds
\ge1/2-(9/4)\sin t.
\tag{CG.6}
$$

The kernel is nonnegative on this quarter. Hence beta>=beta0. Before beta0, either |q|<=1 and u<=1 follows from CG.1, or q>1 with p>0 and u=0. The possible equality at the one endpoint has no effect on an almost-everywhere assertion.

## 5. No high q can persist until time one half

This step uses the actual full-niche height, not a postulated contact law. Define the second single-wall tangency height

$$D_y(t)=(g(t)-1)\cos t-g'(t)\sin t.$$

It satisfies

$$D_y(0)=0,\qquad D_y'=(1-v)\sin t,\qquad c_y=D_y+q\sin t,$$

where c_y=(f-1)sin t+(g-1)cos t is the corner height. Every positive corner height is approached from below by points in its open forbidden quadrant, so c_y<=1/2 follows from H_N<=1/2 even when that corner is not globally exposed.

Suppose q(1/2)>=1. It lies in the initial positive-q component, so on [0,1/2] one has p<=1/2 and

$$p(t)\ge1/2-(9/4)t\ge-5/8,$$

because u>=0 and q<=5/4. Thus CG.1 bounds v<=13/16 on that whole interval. Consequently

$$D_y(1/2)\ge(3/16)(1-\cos(1/2)),$$

and

$$c_y(1/2)\ge\sin(1/2)+(3/16)(1-\cos(1/2))>1/2.$$

For the strict last comparison, the elementary Taylor bounds give

$$
\sin(1/2)>23/48,\qquad 1-\cos(1/2)>47/384,
$$

$$
23/48+(3/16)(47/384)-1/2=13/6144>0.
\tag{CG.7}
$$

This contradicts the full-niche height bound. The initial positive-q component is nonincreasing, as shown in Section 2; later positive components have height at most 1/8. Therefore q(t)<1 for every t>=1/2. Together with q>=-1, this gives u<=1 almost everywhere after that time. Reflect for v.

**Theorem CG2 (fixed support of possible curvature excess).** Every weighted global maximizer satisfies

$$
\boxed{(u-1)_+=0\text{ a.e. outside }(\arcsin(2/9),1/2),}
$$

$$
\boxed{(v-1)_+=0\text{ a.e. outside }(L-1/2,L-\arcsin(2/9)).}
\tag{CG.8}
$$

In particular both curvatures are at most one on [1/2,L-1/2]. The estimate is global over weighted maximizers, not a neighborhood assumption about the candidate.

A coarse quantitative corollary, using u,v<=5/4 and arcsin(2/9)>2/9, is

$$
\int_0^L[(u-1)_++(v-1)_+]dt<5/36.
\tag{CG.9}
$$

No small positive bound is substituted for zero. CG.9 does not license applying a theorem requiring unit curvature.

## 6. Remaining proof obligation

The new energy argument improves the sufficient arm criterion, and the height argument isolates the only remaining angular windows where a weighted maximizer can violate unit curvature. Neither proves those windows carry no excess. The sharper weighted value remains unproved until CG.5 is established for a maximizer or another valid sharp comparison is supplied.

Even a sharp weighted value still needs an upper comparison for arbitrary ambidextrous bodies. The symmetric construction of TF has zero clipping, but arbitrary two-turn competitors need not be dominated by it. That separate quantifier is retained.

A short exact-arithmetic checker records CG.7 and the elementary threshold comparisons. It is not a proof of the differential-inequality hypotheses or the historical cap reductions. No long search, CI, Lean/Lake compilation, dependency installation, or manuscript build is used.
