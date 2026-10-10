# Regularity and exact end-edge heights of every signed weighted maximizer

This supplies a structural conclusion for the attained **one-turn signed** objective, not an assumed property of ambidextrous maximizers. Every maximizing cap has no curvature atoms or singular-continuous curvature in either open upper quarter; its upper support has bounded second derivative there, and its two vertical end edges have length exactly one half. A sharper, arm-dependent curvature inequality is also proved. That inequality is not the still-missing bound rho<=1.

Labels WR are local. The argument uses [WP1--WP2](one-turn-weighted-selection.md), which select any prescribed weighted maximizer and derive summable one-sided facet errors. The neighboring-wall estimate below is the elementary geometry underlying Baek's polygon curvature estimate (compare `MovingSofaUniqueness/Curvature.lean`, `polygon_tau_le_geom`). It is proved explicitly here because our finite domain permits nonzero axis edges and has a different objective.

## 1. The local line calculation

Let a grid cap have spacing delta<=pi/4, height at most one, and supports h_j at theta_j=j delta. Fix a first-quarter interior index 1<=j<n and write

$$f=h_j,\quad g=h_{j+n},\quad c=\cos\delta,\quad s=\sin\delta,\quad T=\tan(\delta/2).$$

The outer facet length is

$$\ell_j=(h_{j-1}+h_{j+1}-2cf)/s.$$

Parameterize its corresponding inner wall by

$$x(v)=(f-1)\mu_{\theta_j}+v\nu_{\theta_j},\qquad v\le v_0:=g-1.$$

The two neighboring companion inner walls give parameter thresholds

$$v_-=(h_{j+n-1}-1-(f-1)s)/c,\qquad
v_+=(h_{j+n+1}-1+(f-1)s)/c.$$

The two neighboring first walls give

$$v_{m lo}=(h_{j+1}-1-(f-1)c)/s,\qquad
v_{m hi}=((f-1)c-h_{j-1}+1)/s.$$

Any point of this ray on the boundary of the finite niche is, except for its corner and its possible floor intersection, in

$$[\min(v_-,v_+),v_0]\ \cup\ [v_{m lo},v_{m hi}].$$

Indeed, if it satisfies a neighboring companion-wall alternative, it lies in the first interval. Otherwise it must satisfy both neighboring first-wall alternatives to avoid their open quadrants and lies in the second interval. The endpoint-angle quadrants used for j=1 or j=n-1 have no part above the floor because the cap height is at most one; the same alternatives therefore remain valid there. No curvature or maximizing premise is used.

Taking lengths gives

$$\boxed{\tau_j\le (v_0-\min(v_-,v_+))_++(2T-\ell_j)_+.}
\tag{WR.1}
$$

The equality v_hi-v_lo=2T-ell_j is direct subtraction. Floor clipping can only shorten these intervals; no niche is clipped to the outer cap.

## 2. A uniform curvature bound with summable errors

All points of the selected caps lie in [-R,R] times [0,1], hence have norm at most B=R+1. Supports are B-Lipschitz in angle and have absolute value at most B. The displayed v thresholds consequently give

$$ (v_0-\min(v_-,v_+))_+\le (6B+4)\delta.$$

For example the numerator of v_0-v_- is bounded in absolute value by

$$B\delta+(B+1)(1-c)+(B+1)s,$$

and division by c>=1/2 gives the stated conservative bound. The other threshold is identical in magnitude. Also 2T<=2delta.

Combine WR.1 with ell_j<=tau_j+b_(n,j) from WP2. If ell_j>=2T the second term vanishes; otherwise ell_j<=2delta already. Thus in every case

$$\ell_j\le C\delta+b_{n,j},\qquad C=6B+6.$$

Horizontal reflection gives the same estimate in the second open upper quarter. On any interval J compactly contained in one of these quarters, summing the grid atoms yields

$$\sigma_{U_n}(J)\le C(|J|+2\delta)+\sum_j b_{n,j}.$$

The last sum tends to zero. Curvature measures converge weakly when convex supports converge uniformly: for a smooth periodic test function phi the identity is simply integral phi d sigma = integral h(phi+phi''). Their total masses are bounded (perimeters of convex bodies in a fixed box), so this determines weak convergence on continuous tests as well. Apply the open-set lower-limit inequality and exhaust each quarter by intervals to conclude

$$\boxed{0\le\sigma_{U_*}\le C\,dt\quad\text{on }(0,\pi/2)\text{ and }(\pi/2,\pi).}
\tag{WR.2}
$$

This is measure domination, not an almost-everywhere calculation that ignores atoms. It rules out both atoms and singular-continuous curvature on these open quarters. Since h is bounded, h''=sigma-h implies W^(2,infinity) regularity on each whole open quarter, with one-sided derivative traces at its endpoints. A jump at the top normal pi/2 is still allowed and represents the horizontal top face.

## 3. The end-edge lengths are exactly the penalty coefficient

For every n the curvature measure on the lower semicircle consists only of its bottom-normal atom. Therefore, near the right axis normal zero, WP2 and the preceding sum give

$$\sigma_{U_n}((-a,a))\le\tfrac12+C(a+2\delta)+\sum_jb_{n,j}.$$

Pass to the limit on this open interval and then let a decrease to zero. This proves sigma_(U_star)({0})<=1/2. The same argument at pi gives sigma_({pi})<=1/2. Importantly, the near-axis floating mass was bounded before taking the limit; unaccounted atoms cannot be manufactured by concentration there.

Superlevel trimming ST1 proves the opposite inequalities: every weighted maximizing cap has upper roof at least one half on its full projection, so each vertical end edge has length at least one half. Consequently

$$\boxed{\sigma_{U_*}(\{0\})=\sigma_{U_*}(\{\pi\})=\tfrac12.}
\tag{WR.3}
$$

For f(t)=h(t), g(t)=h(t+pi/2), let

$$p=f'-g+1,\qquad q=g'+f-1.$$

Since h(pi/2)=1 by HV1, the exact endpoint conditions become

$$\boxed{p(0+)=\tfrac12,\qquad q((\pi/2)-)=-\tfrac12.}
\tag{WR.4}
$$

These are now proved for every signed weighted maximizer. They are not inferred from the candidate's formulas or a smooth transversality sketch.

## 4. Retain the sharper neighboring-wall information

At the companion normal let

$$d_-=(gc-h_{j+n-1})/s,\qquad d_+=(h_{j+n+1}-gc)/s,$$

the two one-sided support derivatives. Define q_-=f+d_--1 and q_+=f+d_+-1, with q_-<=q_+. Direct algebra in WR.1 gives

$$v_0-v_-=\tan\delta(q_-+T),\qquad
v_0-v_+=\tan\delta(-q_++T).$$

Thus

$$\tau_j\le\tan\delta(|q_+|+T)+(2T-\ell_j)_+.$$

Put kappa(z)=max(|z|,(1+|z|)/2). For delta small, tan(delta)<=delta+delta^2 and 2T<=delta+delta^2. Uniform boundedness of q then gives a constant C_1 independent of n,j such that

$$\ell_j\le\kappa(q_+)\delta+C_1\delta^2+b_{n,j}.$$

To check the two cases: if ell_j>=2T, use the |q_+| branch; otherwise move the -ell_j in the positive part to the left and use the (1+|q_+|)/2 branch. This is the usual balancing-function estimate, with the **weighted** defect from WP2.

Between consecutive grid normals both support points are fixed vertices. Accordingly q_n(t)=(A-C) dot mu_t-1 and its variation across a mesh cell is bounded by the diameter times delta. Uniform support convergence implies almost-everywhere convergence of its one-sided derivatives at differentiability points of the limit, using semiconvexity of support functions; their uniform boundedness gives L1 convergence. Since kappa is 1-Lipschitz, the mesh sums converge to the corresponding integrals. Summing and passing to the limit as above proves

$$\boxed{\rho_f(t)\le\kappa(q(t)),\qquad
\rho_g(t)\le\kappa(p(t))\quad\text{a.e. on }(0,\pi/2).}
\tag{WR.5}
$$

For the second inequality, reflect the cap horizontally and exchange the two quarter profiles; the one-sided trace used on p is the reflected counterpart of q_+. The traces agree at interior points of the now-regular limiting quarters. Here rho_f=f''+f and rho_g=g''+g. Their kinematic equations are

$$p'=\rho_f-1-q,\qquad q'=\rho_g-1+p.$$

## 5. The theorem and the precise remaining gap

**Theorem WR1.** Every global maximizer of the signed width-penalized full-right-angle cap objective has height one, contains the half-height rectangle over its full projection, has the exact end-edge lengths WR.3, and has W^(2,infinity) upper-quarter supports satisfying WR.5. The statement applies to every maximizer because WP1 selects an arbitrary prescribed one.

This removes nonsmooth interior curvature measures and establishes the proposed one-half endpoint conditions for this auxiliary problem. It does **not** give rho_f,rho_g<=1: kappa(z)>1 when |z|>1. Nor does it prove that the niche's globally active contact pattern is the candidate pattern, that every niche lies inside its cap, or that the sharp objective value equals M/2.

The earlier C2 regular-critical calculation in Notes 36--37 cannot simply be invoked: WR1 supplies bounded measurable curvature, permitting density jumps, and does not establish that calculation's stable finite contact charts or its two-sided area-variation hypotheses. The still-required sharp step must treat those distinctions explicitly.

No CI or Lean/Lake compilation is used. These are self-reviewed written proofs. Companion exact algebra and finite polygon tests, when executed, check their stated formulas rather than certifying the unrestricted theorem.
