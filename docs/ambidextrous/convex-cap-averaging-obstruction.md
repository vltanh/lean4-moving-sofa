# Convex-cap averaging also fails as an ordinary-area enclosure

**Purpose.** RA1 ruled out Minkowski averaging the actual nonconvex body. This note addresses a different proposed shortcut: average the *convex upper and reflected lower caps*, also with their left-right reflections, and try to use the weighted theorem on that single symmetric cap. The resulting ordinary-area comparison is false even on feasible end-point-face bodies approaching the reference. The negative result below is analytic. Labels MCA are local.

Baseline: `b8e78964127ec7115706016addec0682426f96dd`. The geometric dependencies are the explicit reference and cut formulas already recorded in AX1 and SAC. No unrestricted optimality assumption or new computer certificate is used.

## 1. The comparison being tested

For a body S in 0<=y<=1, let U and V be the downward caps of its actual upper hull roof and reflected lower hull roof. Write J(x,y)=(-x,y), after horizontally centering the projection. A natural symmetric auxiliary cap is

$$C(S)=\tfrac14(U+JU+V+JV).\tag{MCA.1}$$

This is a genuine convex cap. Applying WV2 would prove |S|<=M if the additional inequality

$$|S|\le2\Psi(C(S))\tag{MCA.2}$$

were valid. WV2 alone says nothing about MCA.2. The construction below disproves it. In particular, replacing the failed average of actual sets by convex-cap averaging does not automatically solve the problem.

## 2. A symmetric-in-height but asymmetric-in-length feasible family

Center the reference so its top and bottom face intervals are [-m/2,m/2], its horizontal projection is [-m,m], and its strip is 0<=y<=1. Here m>1 is the reference face length and M is its ordinary area. For small tau>0 put

$$S_\tau=\Sigma\cap\{\tau(x+m/2)\le y\le1-\tau(x+m/2)\}.\tag{MCA.3}$$

The two cuts lie on opposite sides of y=1/2 over the whole projection when tau is small. The reference's interval fibers contain that midline, so S_tau is compact and connected and inherits both full motions. It is symmetric under y -> 1-y but not under J. Its top and bottom faces are the retained points (-m/2,1) and (-m/2,0).

The argument in AX1 applies at the upper tips and, by reflection, the lower tips. It gives

$$0<M-|S_\tau|=O(\tau^{3/2}).\tag{MCA.4}$$

Explicitly, the reference height deficits at its two upper tips are bounded below by a constant times the squared distance to those tips. A cut of vertical depth O(tau) therefore removes material only in intervals of length O(sqrt(tau)). Multiply these bounds and repeat below. The strict loss occurs near the right tips.

Its actual hull is the corresponding double-cut reference hull. The new upper chord joins (-m/2,1) to a retained point on the upper-right circular flank; the lower chord is its reflection. The cuts do not intersect in the hull for small tau. All other extreme points are unchanged retained reference points. Thus every extreme point of the clipped hull belongs to S_tau, proving the hull assertion.

Let U_tau be its downward upper cap. Height symmetry gives V_tau=U_tau, so

$$C(S_\tau)=\tfrac12(U_\tau+JU_\tau)=:C_\tau.\tag{MCA.5}$$

## 3. Exact support defect near the vertical normal

Put L=pi/2. The candidate first-quarter support near L is

$$f_*(t)=\tfrac12+\tfrac m2\cos t+\tfrac12\sin t.$$

Write the upper-right cut intersection as

$$P=(m/2+\tfrac12\sin z,\ \tfrac12(1+\cos z)),\qquad
\tau=\frac{1-\cos z}{2m+\sin z},\qquad\delta=\arctan\tau.\tag{MCA.6}$$

For small tau, z>delta, z^2/tau -> 4m, and the cut normal is L-delta. The support difference u=f_*-f_tau on [0,L] is exactly

$$
u(t)=\begin{cases}
0,&0\le t\le L-z,\\
\tfrac12[1-\sin(t+z)],&L-z\le t\le L-\delta,\\
\tfrac12(1-\sin t)+m\cos t,&L-\delta\le t\le L.
\end{cases}\tag{MCA.7}
$$

The middle piece subtracts P dot n_t from f_*; the last subtracts the support of (-m/2,1). They join continuously by MCA.6. The rest of the upper support of U_tau is unchanged.

The candidate cap is J-symmetric. Therefore the averaged cap C_tau has defect u/2 on the first quarter and its mirror u/2 on the second. All three traces at 0,L,pi are unchanged. In particular C_tau has height one and the same width as the candidate, although its top face is now a single central point.

## 4. Its convex-cap area loses a first-order amount

For a downward cap, ordinary convex area is one half the integral of h^2-h'^2 over [0,pi], as in AR1. Polarize this identity about the reference support. On the support of u the reference curvature density is 1/2; the reference top atom contributes zero because u(L)=0. The equal contributions of the two quarters give the exact identity

$$|U_*|-|C_\tau|
=\tfrac12\int_0^L u(t)dt
+\tfrac14\int_0^L(u'(t)^2-u(t)^2)dt.\tag{MCA.8}$$

Equation MCA.7 gives u=O(z^2) on an interval of length z. On its middle piece u'=O(z), while on [L-delta,L],

$$u'=-\tfrac12\cos t-m\sin t=-m+O(\delta).$$

Consequently

$$\int u=O(z^3),\quad\int u^2=O(z^5),\quad
\int u'^2=m^2\delta+O(z^3+\delta^2).$$

Using delta=tau+O(tau^3) and z=O(sqrt(tau)), MCA.8 becomes

$$\boxed{|U_*|-|C_\tau|=\frac{m^2}{4}\tau+O(\tau^{3/2}).}\tag{MCA.9}$$

No differentiability of the niche functional is used in this calculation. The exposed-face derivative jump is retained in the square integral; averaging convex caps has not made that term disappear.

## 5. The full niche saves only a smaller-order area

Since C_tau is contained in U_*, support monotonicity gives N(C_tau) subset N(U_*). Both quarter supports at turn parameter t agree with the reference when z<=t<=L-z.

The explicit reference roof consists of its fixed central pieces and the two circular tails. Outside the two endpoint strips

$$[-m/2,-m/2+\tfrac12\sin z],\qquad
[m/2-\tfrac12\sin z,m/2],$$

its maximizing angle can be chosen in [z,L-z]. Those points of the old niche therefore remain in the new niche. This follows directly from the old tail tangencies

$$D_x(t)=-m/2+\tfrac12\sin t,\qquad
B_x(L-t)=m/2-\tfrac12\sin t,$$

and the unchanged fixed central-angle interval, for z smaller than its fixed endpoint angle.

In either endpoint strip, the old niche roof at distance d from the tip is

$$\tfrac12-\sqrt{\tfrac14-d^2}
=\frac{2d^2}{1+\sqrt{1-4d^2}}\le2d^2.$$

Its area over a strip of width sin(z)/2 is at most z^3/12. There are two strips. Thus

$$0\le |N(U_*)|-|N(C_\tau)|\le z^3/6=O(\tau^{3/2}).\tag{MCA.10}$$

This is an estimate for the whole positive niche, not for clipping it to a cap. It uses active reference arcs only to show which unchanged constraints retain the old roof; it asserts no contact pattern for C_tau.

## 6. The proposed enclosure fails

The candidate cap has Psi(U_*)=M/2 and all widths above are the same. Subtract MCA.10 from MCA.9 to obtain

$$\boxed{2\Psi(C_\tau)=M-\frac{m^2}{2}\tau+O(\tau^{3/2}).}\tag{MCA.11}$$

Together with MCA.4 this proves:

**Theorem MCA1.** For every sufficiently small positive tau,

$$\boxed{|S_\tau|>2\Psi(C(S_\tau)),\qquad |S_\tau|\longrightarrow M.}\tag{MCA.12}$$

These are actual compact connected full-turn bodies with their actual hull caps, not merely numerical support profiles. Saturating at the same double-cut hull, when using the established same-hull connected saturation, can only strengthen the failed inequality because its right side depends only on that hull.

The result neither contradicts WV2 nor constructs a better-than-reference body. It rules out this particular cap-symmetrization enclosure, including on a high-area threshold below M. A different transformation would need its own ordinary-area comparison.

## 7. Discovery and validation boundary

A short floating-point experiment first tested thirteen prescribed hulls and suggested the failure on the double-cut families. A second bounded run corrected an inconsistent spatial quadrature that had produced a spurious reference discrepancy. The corrected reference comparison agreed to roughly four millionths, while double cuts retained negative margins around seven thousandths at the tested small parameter. Those numbers are not certified bounds and are not premises of MCA1. MCA.3--MCA.12 supply the hand proof.

No long search, CI, Lean/Lake compilation, dependency installation or manuscript build was used. The reference/cut geometry and the new argument remain self-reviewed rather than independently verified.
