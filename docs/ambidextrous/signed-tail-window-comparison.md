# A signed tail-window comparison allowing outward as well as inward changes

**Scope.** This extends TC beyond subsets of the reference cap. It gives a sharp ordinary-area comparison when the middle supporting data are unchanged and the modified tail supports stay below explicit baseline-intercept barriers. Outward bulges within this domain are allowed. The domain is not every neighborhood of the reference and does not cover arbitrary opposite-face bodies. Labels STW are local.

Only the explicit reference geometry and elementary support/roof comparisons are used. The weighted-maximizer proof WV and Gerver's theorem are not inputs. No computation is a premise.

## 1. Domain with a signed support difference

Use the centered reference, with m in (1,4/3), a=-m/2, b=m/2, projection I=[-m,m], and L=pi/2. Let

$$\eta=2\arctan(1/10),\quad \cos\eta=99/101,\quad\sin\eta=20/101,\quad D=10/101.$$

Consider any compact convex downward cap U such that

$$I\times[0,1/2]\subseteq U\subseteq I\times[0,1],$$

$$h_U(\theta)=h_*(\theta)\quad
(\theta\in[0,L-\eta]\cup[L+\eta,\pi]),\tag{STW.1}$$

and on the remaining interval

$$\boxed{h_U(\theta)\le1+b|\cos\theta|.}\tag{STW.2}$$

There is no assumption U subset U_*. The defect h_*-h_U may have either sign. Two caps U,V may vary independently in this domain.

The known reference bounds m in (1,4/3), eta<beta, and its two circular tail formulas are the same explicit dependencies as TC/RB. In particular the reference itself satisfies STW.2.

## 2. The new niche remains confined and below half height

For the reference, the two baseline intercept inequalities are

$$h_*(t)-1\le b\cos t,\qquad h_*(t+L)-1\le b\sin t.\tag{STW.3}$$

They follow directly from its known curvature densities at most one: the single-wall tangency heights satisfy B_y'=(rho_f-1)cos(t), B_y(L)=0 and D_y'=(1-rho_g)sin(t), D_y(0)=0. Thus B_y,D_y>=0; the two baseline intercepts are monotone with endpoint limits b,a. This uses only the explicit reference densities, not a curvature assertion about U.

The unchanged supports STW.1 and the barrier STW.2 preserve both inequalities STW.3 for U. Every positive-height forbidden point therefore has a<x<b. Hence

$$\operatorname{proj}_x N(U)\subset(a,b).\tag{STW.4}$$

The niche height is at most the largest positive inner-corner height. On the unchanged middle angles the corner is the reference corner and has height at most one half. On a changed late first-quarter angle t in [L-eta,L), put c=cos(t), s=sin(t). The companion support is unchanged and equals

$$g_*(t)=m s+c/2.$$

Using h_U(t)<=1+b c gives

$$c_{U,y}(t)\le(3m/2)sc+c^2/2-c
\le c+c^2/2
\le\frac{2220}{10201}<1/2.\tag{STW.5}$$

Here m<4/3, s<=1 and c<=20/101. Horizontal reflection gives the early-angle bound. Thus the entire new niche has height at most one half, without assuming its maximizing parameter or contact topology.

## 3. The paired inequality still holds with its signs retained

For x_in=b-d, x_out=b+d and 0<d<D, set t=L-arcsin(2d) as in TC. Let u(t)=h_*(t)-h_U(t), now possibly negative. The same outer support test gives

$$\frac{u(t)}{\sin t}\le A_*(x_{out})-A_U(x_{out}).$$

To use the first wall as a niche lower test, its companion must still be higher. At this reference tail point the reference companion gap is

$$L_*(t,x_{in})-n_*(x_{in})=rac{(3m/2)\sin t-1}{\cos t}\ge19/8.$$

The largest allowed upward displacement of the first wall follows from STW.2:

$$\frac{h_U(t)-h_*(t)}{\sin t}
\le\frac{1-\sin t}{2\sin t}\le1/99<19/8.$$

Thus the companion remains strictly higher even when u<0. Taking the positive part of the first-wall lower test proves the **signed** inequality

$$\boxed{n_*(b-d)-n_U(b-d)
\le\frac{u(t)}{\sin t}
\le A_*(b+d)-A_U(b+d).}\tag{STW.6}$$

The left-tail analogue follows by reflection. Neither difference in STW.6 is asserted nonnegative. A positive outward cap change can produce negative cap loss and negative niche saving; the inequality retains those signs.

## 4. Other locations contribute only favorable terms

Outside the two inner tail strips J=(a,a+D) union (b-D,b), every old positive niche value has an attaining middle parameter whose two supports are unchanged. Consequently

$$n_U(x)\ge n_*(x)\quad\text{a.e. outside }J.$$

This is the correct direction without cap inclusion. Additional niche area there only improves the signed comparison.

Outside [a-D,b+D], the reference upper roof is attained by unchanged support normals. The same supporting line bounds U, giving A_U<=A_* there. Over [a,b], A_*=1 and the height bound also gives A_U<=A_*. Therefore any negative cap loss can occur only on the two outer tail strips paired in STW.6.

Integrating STW.6 and the favorable inequalities elsewhere yields

$$|N(U_*)|-|N(U)|
\le\int_{a-D}^a(A_*-A_U)+\int_b^{b+D}(A_*-A_U).$$

The exact cap-area difference then gives:

**Theorem STW1.** With Delta(U)=M/2-Psi(U),

$$\boxed{\Delta(U)\ge\int_a^b(1-A_U(x))dx\ge0.}\tag{STW.7}$$

Only the explicit reference equality Psi(U_*)=M/2 is used to define this difference. The global weighted theorem is not invoked.

## 5. Ordinary two-turn area and the clipping budget

For independent U,V in the domain, define E=(U minus N(U)) intersect rho(V minus N(V)). By Section 2 its fibers all contain y=1/2. Thus E is compact, connected and feasible for both canonical full turns, as in TC.

Both niche roofs vanish outside [a,b], so the exact positive clipping term satisfies

$$G\le\int_a^b(1-A_U+1-A_V)dx\le\Delta(U)+\Delta(V).$$

**Corollary STW2.**

$$\boxed{|E|\le M.}\tag{STW.8}$$

This is an ordinary-area statement with the clipping charged explicitly. It is not the claim that E is a subset of the reference or that the auxiliary caps are reference subsets.

## 6. The extension really allows outward perturbations

Choose a smooth nonnegative, nonzero function phi supported in a closed subinterval of (L-eta,L). Extend it by zero to [0,pi]. For sufficiently small positive epsilon,

$$h_U=h_*+\varepsilon\phi$$

is the upper support of an admissible cap. On the support of phi the reference curvature density is one half, so epsilon can be chosen to keep h_U''+h_U>=0. All support traces, axis atoms and matches outside that compact interval remain unchanged. The cap remains downward-closed and of height one with the same end edges and top face; it contains U_* and hence the half-height rectangle. This is the usual support-measure construction, with no negative curvature introduced.

On that compact interval STW.2 has strictly positive slack `(1-sin(t))/2` at the reference. A further reduction of epsilon preserves it. Thus nontrivial outward cap bulges are included. Their full two-turn envelopes need not be contained in the reference body; STW2 bounds their area nevertheless.

This example establishes nonemptiness of the outward part of the domain. It is not a numerical support tuple asserted feasible without checking convexity and endpoint conditions.

## 7. Remaining boundary

STW does not allow arbitrary changes in the middle supporting data, and its baseline barriers still require proof for any proposed application. No theorem makes an arbitrary saturated opposite-face body satisfy STW.1--STW.2. The full-turn global upper bound and the uncovered partial-turn comparison remain unproved.

The successful mechanism is a comparison at known reference wall parameters: an infimum bounds the changed outer roof from above while a single admissible wall pair bounds the changed niche roof from below. It does not equate a changed local contact with the new global envelope, nor charge the full derivative energy of a moved face.

No long search, CI, Lean/Lake compilation, dependency installation or manuscript build was used. The proof is analytic and self-reviewed; the short checker verifies only the explicit arithmetic and finite local line identities.
