# The signed width-penalized one-turn maximum

**Statement and boundary.** The argument below proves the auxiliary weighted value

$$\boxed{\sup_U\bigl(|U|-|N(U)|-W(U)/2\bigr)=M/2,}$$

where U ranges over the normalized full-right-angle caps of PA.1 and N(U) is the entire positive-height niche. This is not unrestricted ambidextrous optimality. The general two-cap identity still has a nonnegative clipping correction, and no universal upper domination by a weighted maximizing cap is proved here.

Labels WV are local. The proof combines the attained maximizer from PA2, the existing selected-polygon and geometric reductions, the new one-good-quarter theorem SE2, and the visible-source flux estimate VE2. These are written, self-reviewed arguments. Their full historical dependency chain has not been independently refereed or kernel-verified.

## 1. Inputs and which maximizer is being studied

Let U be any attained global maximizer of

$$\Psi(U)=|U|-|N(U)|-W(U)/2.$$

Use L=pi/2 and

$$p=f'-g+1,\quad q=g'+f-1,\quad u=f''+f,\quad v=g''+g.$$

WR and AR give Lipschitz p,q and bounded measurable nonnegative u,v, with

$$
p'=u-1-q,\qquad q'=v-1+p,\qquad
p(0)=1/2,\quad q(L)=-1/2,
$$

$$p\le1,\quad q\ge-1,\quad u\le\kappa(q),\quad v\le\kappa(p),\qquad
\kappa(z)=\max(|z|,(1+|z|)/2).\tag{WV.1}$$

On {p>0,q>0}, AR7 gives u=0,v<=1/2. Every positive-q component not starting at zero has q<=1/8. On a positive-q component p'<=-1/2; after p becomes negative, q'<=-1/2. On the initial component before that crossing, p<=1/2 and q'<=p-1/2<=0. Thus q is nonincreasing on its initial positive component, and strictly decreases after p becomes negative.

PT/TS/TF/HF give height one, half-height end edges, full-niche containment and positive tangency heights, and a top face of length T=W/2>1. EB identifies the limiting finite exposure measures with u dt and v dt. None of these inputs asserts the saturated local-exposure ODE.

SE2 proves at least one of the two quarters has unit curvature, using the known ordinary one-turn area upper bound and the stationary core identity. Reflect horizontally if necessary, so that

$$\boxed{0\le v\le1\quad\hbox{a.e. on }(0,L).}\tag{WV.2}$$

Only a symmetry of this same weighted problem is used. No two different optimizers are averaged or spliced.

## 2. Suppose the other quarter has excess

Assume the set {u>1} has positive measure. By WV.1 and q>=-1, u>1 requires q>1. Such a point lies in the initial positive-q component by AR5'. On its part with p>0, AR7 gives u=0; the p=0 level has at most one point there because p'<0. Thus one may choose t_* with

$$p(t_*)<0,\qquad q(t_*)>1.$$

Let tau be the right endpoint of that initial positive-q component. Since q(L)=-1/2, tau<L and q(tau)=0. On [t_*,tau), p remains negative and decreases, and q decreases strictly. There is therefore a unique b in (t_*,tau) with

$$q(b)=1,\qquad p(b)<0,$$

and p<0<q<1 on (b,tau).

Crucially, the *entire future* after b has q<=1. This is true until tau by monotonicity, and later positive components have q<=1/8. Negative q is at least -1. Hence WV.1 implies

$$\boxed{0\le u\le1\quad\hbox{a.e. on }(b,L).}\tag{WV.3}$$

This is a consequence of the hypothetical excess component, not an assumed global curvature bound.

## 3. Two globally visible pieces force exact companion balance

Now WV.2 supplies a globally good second quarter, and WV.3 supplies a good future first quarter. On every compact interval J inside (b,tau), p<0<q. These are exactly VE2's hypotheses.

The second-wall tangency D(t) is globally visible because its horizontal coordinate is nondecreasing on the entire quarter. The corner c(t) is globally visible because all past second-wall values and all future first-wall values are strictly lower there. Their graph images are disjoint on J. The two-source flux calculation reads their contributions as (1-v)dt and -p dt into the limiting second-wall exposure.

Since EB identifies that total exposure with v dt, VE2 gives

$$2v\ge1-p\quad\hbox{a.e. on }(b,\tau).$$

The global bound v<=1 therefore forces p>=-1 almost everywhere, and continuity extends this to [b,tau]. On -1<=p<0, WV.1 gives the opposite bound v<=kappa(p)=(1-p)/2. Consequently

$$\boxed{v=(1-p)/2,\qquad -1\le p<0\quad\hbox{on }(b,\tau)}\tag{WV.4}$$

with the density equality almost everywhere.

This step does not set exposure equal to an arbitrary local upper bound. The required lower bound is proved from globally active pieces and the limiting oriented flux, with staircase contributions retained.

## 4. An increasing energy gives a contradiction

Set

$$x=1-p,\qquad y=1+q.$$

On (b,tau), WV.1 and 0<q<1 give

$$x'=1+q-u\ge(1+q)/2=y/2.$$

Equation WV.4 gives

$$y'=v-1+p=-(1-p)/2=-x/2.$$

Since x>0,

$$\boxed{\frac{d}{dt}(x^2+y^2)=2xx'+2yy'\ge0}\tag{WV.5}$$

almost everywhere. Lipschitz regularity permits integration across the whole interval. At its initial endpoint,

$$x(b)=1-p(b)>1,\qquad y(b)=2,$$

so x(b)^2+y(b)^2>5. At its final endpoint, continuity and WV.4 give 1<=x(tau)<=2 and y(tau)=1, so

$$x(\tau)^2+y(\tau)^2\le5.$$

This contradicts WV.5. Thus the positive-measure set {u>1} cannot exist.

**Theorem WV1 (unit curvature at weighted maximizers).** Every global maximizer of the signed weighted one-turn objective satisfies

$$\boxed{0\le f''+f\le1,\qquad0\le g''+g\le1\quad\hbox{a.e. on }(0,L).}\tag{WV.6}$$

One good quarter supplied by SE2 has forced the other to be good, rather than being incorrectly treated as sufficient by itself.

## 5. Sharp weighted value

The candidate cap is feasible in the PA.1 domain and has Psi=M/2 by AR3. For the attained maximizing cap, WV1 supplies the two curvature hypotheses of AR4. That theorem uses the signed-roof identity SR1 and the calibrated function-space bound AF3, keeping the possible negative signed roof with its favorable sign. Therefore

$$M/2\le\Psi(U)\le M/2.$$

**Theorem WV2 (weighted value).** Every normalized cap in the PA.1 full-right-angle domain satisfies

$$\boxed{|U|-|N(U)|-W(U)/2\le M/2,}\tag{WV.7}$$

and the reference cap attains the bound. The already stated AR4 equality conclusion also identifies every weighted maximizer with that reference cap up to horizontal translation, but unrestricted two-turn uniqueness is not asserted or pursued here.

The use of attainment matters: WV1 is a theorem about maximizing caps. It is not claimed that every cap satisfies its curvature conclusions. PA2 reduces the universal value inequality to that attained maximum.

## 6. Dependency chain for review

```text
PA2: signed maximum is attained
  -> WP/WR: selected polygons, summable defects, regularity and endpoint edges
  -> AR7/AR5': same-sign bounds and positive-component control
  -> PT/TS: positive top face and niche height <= 1/2
  -> TF/HF: positive tangencies, niche confinement, T=W/2, core identity
  -> CG: stronger arm threshold sqrt(17)/2
  -> SE: chord bound + existing ordinary Gerver bound -> one good quarter
  -> VE: actual visible-source lower exposure bound on a good future
  -> WV1: energy contradiction -> both quarters good
  -> SR1/AF3 through AR4 -> WV2: max Psi=M/2.
```

The main new analytic review point is VE's preservation of the two source fluxes, not ordinary perimeter, in the selected finite graphs. The ordinary Gerver theorem is an explicit external dependency in SE, applied only to a feasible one-turn body. None of these steps uses ambidextrous optimality as an input.

## 7. The unrestricted theorem is still a separate problem

For general full-turn cap pairs with nonempty surviving fibers, the exact identity remains

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

WV2 gives |E|<=M+G, not |E|<=M when G>0. Partial-angle bodies require their own coverage argument. The symmetric construction from a weighted maximizer has G=0, but no theorem here says it dominates all two-turn competitors.

Thus this note closes the weighted one-turn subproblem within the displayed written dependency chain. It does not close unrestricted ambidextrous optimality. The next genuine upper-bound task is the two-turn clipping/ordinary-area comparison, not further maximization of Psi or more analysis of the assumed saturated ODE.

No long numerical search, CI, Lean/Lake compilation, dependency installation or manuscript build is used. Short exact checks concern the displayed algebra; they do not replace independent review of the continuum proof or its historical dependencies.
