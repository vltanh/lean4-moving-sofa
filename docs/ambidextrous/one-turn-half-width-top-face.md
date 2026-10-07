# A weighted maximizer has top-face length exactly half its width

**Scope.** This continues TF2--TF3 and the finite exposure balance EB. It proves an exact geometric relation, not the optimal value: for every signed weighted maximizing cap, its top-face length is W/2. It also gives a rectangular Minkowski decomposition and an exact perimeter expression for its signed objective. No no-hiding hypothesis, saturated ODE, curvature bound one, or reflection symmetry of the cap is assumed.

Labels HF are local. Dependencies are the written WP/WR/HV/PT/EB results, [TF2--TF3](one-turn-tangency-floor-bound.md), the explicit feasible candidate cap AR3, and the analytic width exclusion AW-W. The chain remains subject to independent review.

## 1. Every weighted maximizer has width greater than two

Let U maximize Psi. Its symmetric two-turn body S_U is compact and connected, and TF3 gives

$$|S_U|=2\Psi(U)\ge M.$$

Its horizontal extreme points at height one half survive, so it has the same width W as U. If W<=2, AW-W gives |S_U|<41/25<M, a contradiction. Thus W>2. This uses one explicit feasible body from the weighted maximizer, not an assumption that it maximizes ambidextrous area.

Write [l,r] for the cap projection and [a,b] for the top face; T=b-a. From the strict baseline intercept inequalities in TF3,

$$a<l+1<r-1<b.\tag{HF.1}$$

The two middle points are in this order because W>2.

## 2. The full niche projects onto exactly the top-face interval

TF3 already gives projection(N(U) intersect {y>0}) contained in (a,b).

For a<x<r-1, the two strict quadrant tests at (x,0) hold at a sufficiently small positive angle t: the first tends to r-1-x>0, while the second is (x-a)t+o(t)>0, using g(0)=1 and g'(0)=-a. Both strict inequalities also hold at a sufficiently small positive height. Thus this entire interval occurs in the positive niche projection.

The reflected end-angle argument covers l+1<x<b. The intervals overlap by HF.1. Therefore

$$\boxed{\operatorname{proj}_x(N(U)\cap\{y>0\})=(a,b).}\tag{HF.2}$$

This asserts connectedness of the **projection**. It does not assert that every positive horizontal level section is an interval or that every corner curve is exposed.

## 3. The required convergence of projection lengths is proved, not assumed

Let U_n be the WP1 polygons selecting this particular U. Let h_n(L)=H_n<=1, W_n its width, T_n its top length, and J_n the positive finite-niche projection. Niche-area convergence alone does not imply |J_n|->T; arbitrarily shallow positive tails would invalidate that inference. Here the support derivative estimates rule out those tails uniformly outside the top face.

The WR grid bound gives, on either open quarter,

$$\sigma_{U_n}((s,t))\le C(t-s+2\delta_n)+e_n,\qquad e_n\to0.$$

In this section e_n denotes the sum of facet-error bounds, not HV's angular area error. Since h_n''=sigma_(U_n)-h_n dt and the supports are uniformly bounded, the interior one-sided derivative traces have modulus

$$|h_n'(t)-h_n'(s)|\le C'(t-s)+o(1),\tag{HF.3}$$

uniformly within each quarter, including its one-sided endpoint traces. Axis atoms are not included when extending from the interior to an endpoint.

Consequently the derivatives converge uniformly to the continuous one-sided derivative of h on each closed quarter. A direct proof is to interpolate the bounded derivative traces on an auxiliary mesh tending to zero; HF.3 makes the interpolation error tend to zero and supplies equicontinuity. Every uniform limit has integral h(t)-h(s), hence is h'. This identifies all subsequential limits. In particular, if f_n,g_n are the quarter profiles,

$$\epsilon_n=\|f_n'-f'\|_\infty+\|g_n'-g'\|_\infty\to0,$$

and the top-atom formula T_n=g_n'(0+)-f_n'(L-) gives T_n->T.

For every interior angle, not only sampled ones,

$$
\frac{f_n(t)-1}{\cos t}
\le\frac{f_n(t)-H_n}{\cos t}
\le\frac{f(t)-1}{\cos t}+\frac\pi2\epsilon_n
\le b+\frac\pi2\epsilon_n.
\tag{HF.4}
$$

Indeed the middle numerator error is bounded by epsilon_n(L-t), and (L-t)/cos(t)<=pi/2. Similarly,

$$\frac{1-g_n(t)}{\sin t}\ge a-\frac\pi2\epsilon_n.\tag{HF.5}$$

Every positive finite-niche fiber must lie between these two baseline intercepts. Hence |J_n|<=T+pi epsilon_n.

Conversely each closed interval [a+eta,b-eta] is eventually contained in J_n. HF.2 supplies a strict interior-angle witness at positive height for each point. A finite subcover and continuity in the angle retain those witnesses after replacing their angles by nearby mesh angles and replacing U by U_n. Thus liminf |J_n|>=T-2eta; let eta decrease to zero. We have proved

$$\boxed{|J_n|\longrightarrow T.}\tag{HF.6}$$

## 4. Projection balance gives the exact ratio

The exact finite identities PT.1--PT.2 are

$$|J_n|=\sum_{j\ne0,n,2n}\tau_{n,j}\sin\theta_j,$$
$$W_n-T_n=\sum_{j\ne0,n,2n}\ell_{n,j}\sin\theta_j.$$

EB.10 gives the vanishing sum of absolute differences between these two sets of coefficients. Use HF.6, W_n->W and T_n->T to obtain W-T=T.

**Theorem HF1 (half-width top face).** Every global maximizer of the signed weighted objective satisfies

$$\boxed{T=W/2>1.}\tag{HF.7}$$

This is not an assertion about arbitrary feasible caps or arbitrary ambidextrous maximizers. The exact limiting exposure balance is essential.

## 5. A genuine rectangular Minkowski decomposition

Write U in vertical sections as 0<=y<=a_U(x). ST1 gives a_U>=1/2, so

$$V_1=\{(x,y):0\le y\le a_U(x)-1/2\}$$

is a convex cap and U=V_1+[0,1/2]e_y. Its height is one half, its end-edge heights are zero, and its top face has length T.

Every horizontal section of V_1 has length at least T. Define V by shortening its right endpoint by exactly T. Equivalently,

$$V=V_1\cap(V_1-Te_x).$$

The section lengths are nonnegative, and V is compact and convex. Its height is one half, its top face is one point, and its width is W-T=T. Section by section, V_1=V+[0,T]e_x. Therefore:

**Corollary HF2 (rectangular core).**

$$\boxed{U=V+([0,T]\times[0,1/2]),\qquad W(V)=T,\quad H(V)=1/2.}\tag{HF.8}$$

The core V is actual convex material obtained by the displayed erosions, not a postulated signed profile. The equality includes a choice of horizontal translation inherited from U.

## 6. A stationary ordinary-area identity

Let rho(theta) denote the two open-upper-quarter curvature densities, with the top atom omitted, and put

$$L_c=\int_{(0,L)\cup(L,\pi)}\rho(\theta)d\theta.$$

For a finite niche, Green's polygon area formula gives

$$2|N_n(U_n)|=\sum_{j\ne0,n,2n}(h_n(\theta_j)-1)\tau_{n,j}.\tag{HF.9}$$

Each exposed source edge has outward normal n_(theta_j), on the line x dot n_(theta_j)=h_n(theta_j)-1. The floor has support zero and contributes zero. Subdivide into polygonal components if necessary. This formula concerns the ordinary finite union, not the area under a multiply wound candidate curve.

Uniform support convergence, HV2's niche-area convergence, and EB1's convergence of the finite exposure measures yield

$$2|N(U)|=\int(h(\theta)-1)\rho(\theta)d\theta.\tag{HF.10}$$

The cap's support-area identity retains its two end atoms of length one half, its top atom T at support one, and its bottom atom at support zero:

$$2|U|=\int h\rho+W/2+T.$$

Subtracting gives

$$\Psi(U)=L_c/2+T/2-W/4=L_c/2,$$

where the last equality is HF1. Since the core V has no top or vertical-side atoms and has bottom length T, Per(V)=L_c+T. Thus:

**Corollary HF3 (stationary perimeter identity).**

$$\boxed{2\Psi(U)=L_c=\operatorname{Per}(V)-T.}\tag{HF.11}$$

This identity is specific to maximizing caps for which EB holds. It is not a universal replacement of signed cap area by perimeter, and no sharp bound on its right side is proved here. Limiting exposure measures need not equal the ordinary perimeter measure of the limiting nonconvex niche; finite staircases may lose boundary length. HF.9--HF.10 only pass the area identity, which is justified by their stated convergences.

## 7. What remains

TF3 and HF1 remove the symmetric clipping term and determine the top length for every weighted maximizer. They do not give endpoint arms at most two or prove that all local wall contributions are exposed. The saturated ODE is still not licensed by balance alone.

Even a sharp bound for the weighted maximum would need a separate ordinary-area comparison for arbitrary two-turn bodies. Their clipping/winding corrections have not been removed by a theorem about S_U. Uniqueness remains deferred.

No long computation, CI, Lean/Lake compilation, dependency installation, or manuscript build is used. The proof is analytic with explicit historical dependencies, not independent or kernel verification.
