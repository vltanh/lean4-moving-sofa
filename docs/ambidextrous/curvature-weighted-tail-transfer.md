# Inward tail transfer without exact reference collars

**Scope.** This generalizes the geometric part of MT to backgrounds not tied to any reference support values or circular collars. The background tail curvature must lie between one half and one; the lower threshold has a geometric role as an area Jacobian, not a numerical fitting condition. Arbitrary inward top-normal changes are permitted. The signed outward extension in MT is separate and is not asserted at this greater generality. Labels CT are local.

The theorem transfers a valid bound for two background caps to their altered ordinary-area envelope. It does not construct such backgrounds for arbitrary competitors. No computer result or weighted-maximizer hypothesis enters the proof.

## 1. Background hypotheses

Let B be a compact convex downward cap with projection I=[l,r], height one, and positive top face [a,b]. Assume

$$I\times[0,1/2]\subseteq B\subseteq I\times[0,1],\qquad r-l>2.$$

Its quarter supports f(t)=h_B(t), g(t)=h_B(t+L), L=pi/2, belong to W^(2,infinity) and obey

$$0\le u=f''+f\le1,\qquad0\le v=g''+g\le1\quad\text{a.e.}$$

Assume the full niche height is at most one half. An explicit sufficient condition is that every inner corner height is at most one half.

Choose 0<eta<L/2 and put t0=L-eta. On the two tail intervals suppose

$$p=f'-g+1>0,\quad q=g'+f-1>0\quad(0\le t\le\eta),$$

$$p<0,\quad q<0\quad(t0\le t\le L),\tag{CT.1}$$

and

$$v\ge1/2\text{ on }(0,\eta),\qquad u\ge1/2\text{ on }(t0,L)\quad\text{a.e.}\tag{CT.2}$$

Let c=(f-1)mu+(g-1)nu, B_t=c+p nu, D_t=c-q mu as in MT. Require

$$(D_\eta)_x<(B_{t0})_x.\tag{CT.3}$$

This separates the left and right inner tail intervals. Whenever a<b, r-a>1, b-l>1, and the tail lower curvature bound holds in neighborhoods of the vertical normal, the strict sign and separation conditions can be achieved by taking eta sufficiently small. Indeed p(0) and -q(L) are the positive endpoint heights, q(0)=r-a-1, p(L)=1-(b-l), while D_x(0)=a and B_x(L)=b. This observation does not impose the endpoint arm inequalities on arbitrary caps.

An altered cap U satisfies

$$I\times[0,1/2]\subseteq U\subseteq B,$$

$$h_U=h_B\quad\text{on }[0,L-\eta]\cup[L+\eta,\pi].\tag{CT.4}$$

The top height may decrease and its face may collapse; middle supports remain those of this background, not necessarily those of the reference. U need not satisfy a curvature bound.

## 2. The old niche can change only in its two tails

Unit curvature makes B_x,D_x nondecreasing, gives nonnegative tangency heights and confines the background niche to (a,b), exactly by the derivatives in MT Section 2. The sign conditions CT.1 let MT.9's two-case argument prune all t>=t0 for x<=(B_(t0))_x, and its reflection prune t<=eta for x>=(D_eta)_x.

Hence every positive background niche value outside

$$J=(a,(D_\eta)_x)\cup((B_{t0})_x,b)$$

has an attaining parameter in [eta,t0]. Both supports at that parameter are unchanged by CT.4. Support monotonicity gives the opposite inequality, so n_U=n_B outside J, apart from immaterial endpoints.

On the right tail, p<0 implies that the first-wall tangency B_t is globally active. The proof is direct: at x=(B_t)_x, the first-wall family is unimodal by MT.7 and achieves its maximum at t; the companion wall is higher because p<0. The left tangency D_t is globally active by q>0. No contact classification of the altered cap is assumed.

## 3. The two area Jacobians explain the threshold one half

Let A_t=f mu+f'nu be the right outer support point. On (t0,L),

$$\frac{d}{dt}(A_t)_x=-u\sin t,\qquad
\frac{d}{dt}(B_t)_x=(1-u)\sin t.\tag{CT.5}$$

Both points approach abscissa b at the top normal. The outer arc runs from (A_(t0))_x to b, outside the face. The inner arc runs from (B_(t0))_x to b, inside it.

Put e_f(t)=h_B(t)-h_U(t)>=0. The same supporting-line tests used in TC give

$$0\le n_B((B_t)_x)-n_U((B_t)_x)\le e_f(t)/\sin t,$$

$$A_B((A_t)_x)-A_U((A_t)_x)\ge e_f(t)/\sin t.\tag{CT.6}$$

For the niche test the companion support is unchanged and lies above the old first wall, so also above the lowered new first wall. A positive part handles values below the baseline.

Integrating with CT.5 gives

$$\text{right niche saving}\le\int_{t0}^L e_f(t)(1-u(t))dt,$$

$$\text{right outer-cap loss}\ge\int_{t0}^L e_f(t)u(t)dt.\tag{CT.7}$$

The change-of-variables step remains valid for bounded measurable curvature. The outer abscissa is absolutely continuous and strictly monotone since u>=1/2 and sin t is bounded away from zero. The inner abscissa is nondecreasing and absolutely continuous; its plateau intervals contribute zero to both the abscissa integral and the factor (1-u). The monotone one-dimensional substitution formula therefore applies without a smoothness assumption.

Since u>=1/2, the difference of the right sides in CT.7 is the nonnegative surplus

$$\int_{t0}^L e_f(t)(2u(t)-1)dt.$$

For the left tail set e_g(t)=h_B(t+L)-h_U(t+L)>=0. The outer abscissa has derivative -v cos t, while the inner abscissa has derivative (1-v)cos t. The identical argument gives surplus

$$\int_0^\eta e_g(t)(2v(t)-1)dt.$$

Thus define

$$J_B(U)=\int_{t0}^L e_f(2u-1)dt+\int_0^\eta e_g(2v-1)dt\ge0.\tag{CT.8}$$

The radius-one-half reference tails are the equality case of these two Jacobians. No exact circular shape was otherwise used.

## 4. Transfer of the face-loss and curvature surplus

All cap losses are nonnegative because U subset B. The two exterior arc intervals in CT.7 are disjoint from [a,b]. The entire niche saving occurs on the paired inner arcs. Subtracting niche saving from total cap loss, with the width unchanged, proves:

**Theorem CT1.**

$$\boxed{\Psi(B)-\Psi(U)\ge
\int_a^b(1-A_U(x))dx+J_B(U).}\tag{CT.9}$$

The last term can be discarded if only a nonnegative budget is needed. It must not be given the same favorable sign for outward support changes: e_f,e_g>=0 is essential unless both tail densities equal one half as in MT.

## 5. Two backgrounds: ordinary area

Let B_1,B_2 have the same projection I and the same positive top-face interval [a,b], each satisfying the hypotheses above, possibly with different cut angles eta. They need not be reflections of each other or have the same middle supporting data. Let U_i be independent CT.4 alterations.

By monotonicity N(U_i) is confined to (a,b) and has height at most one half. Both altered cap roofs are at least one half. The full two-turn envelope E therefore has nonempty interval fibers through the midline and is compact, connected and feasible for both canonical full turns. Its positive clipping obeys

$$G\le\int_a^b(1-A_{U_1}+1-A_{U_2}).$$

Its exact area identity and CT.9 give

$$\boxed{|E|\le\Psi(B_1)+\Psi(B_2)-J_{B_1}(U_1)-J_{B_2}(U_2).}\tag{CT.10}$$

The background caps, unlike the altered caps, have unit curvature and height one. SR1 identifies their signed objectives with the fixed-width functional. After common horizontal centering, both belong to X_(W/2), so AF.7 and AF3 imply

$$\Psi(B_1)+\Psi(B_2)\le\Phi(W/2)\le M.$$

Therefore CT.10 is a sharp ordinary-area bound on this domain, with explicit surplus for cuts where the background tail curvature exceeds one half. It uses the analytic SR/AF chain, not WV's maximizing-cap regularity or the Gerver area bound.

## 6. Remaining admission problem

The exact reference collars of MT are gone for inward alterations. Instead, the backgrounds must have global unit curvature, a half-height rectangle, a common top-face interval, a half-height niche, and the specified tail signs and lower curvature bound. The proof does not repair an arbitrary competitor into such a background, does not prove those properties at an unrestricted maximizing hull, and does not cover changes to the background's middle through CT.4 itself.

In particular there is no new symmetry-reduction or unrestricted full-turn theorem here. The threshold rho>=1/2 is not removable by pointing to an upper curvature bound alone; a separate negative control exhibits an actual area-improving inward cut when it fails.

All new calculations are pen and paper. No long computation, CI, Lean/Lake compilation, dependency installation or manuscript build is used. Unrestricted optimality remains unproved.
