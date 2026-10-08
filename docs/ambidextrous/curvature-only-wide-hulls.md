# Wide-hull supplement: curvature domination alone gives the sharp theorem when width is at least two

This uses the signed-roof calculation rather than imposing the old contact-order inequalities. For any ambidextrous body with a unit-span hull of horizontal width at least two, open-quarter curvature domination forces full turns. Connected feasibility then forces the needed face alignment, except for an explicit width-two configuration whose entire hull already has area pi/2.

The resulting sharp theorem assumes neither p<=q, full turns, nor face alignment. It still assumes curvature domination and the stated horizontal width. Neither hypothesis is asserted for every unrestricted maximizer. Labels CW1 onward avoid the existing numbered/WG/AF sequences.

## C.1 A width comparison from the differential inequality alone

Let K be convex with h_K(pi/2)=1, h_K(3pi/2)=0, and horizontal width W=h_K(0)+h_K(pi). Suppose sigma_K=h_K+h_K'' is dominated by dt on each open coordinate quarter. On [0,L], L=pi/2, its width w satisfies

\[
w(0)=W,\qquad w(L)=1,\qquad w''+w\leq2
\quad\text{a.e.}
\]

The same holds for w(-t). Set

\[
v_W(t)=2+(W-2)\cos t-\sin t.
\]

Then v_W has the same endpoint values and v_W''+v_W=2. The difference solves

\[
(-d^2/dt^2-1)(w-v_W)=2-(w''+w)\geq0
\]

with zero Dirichlet endpoints. The Green kernel on length L<pi is positive, namely sin(t_<)sin(L-t_>)/sin L. Therefore

\[
\boxed{w_K(\pm t)\geq2+(W-2)\cos t-\sin t\quad(0\leq t\leq L).}
\tag{C.1}
\]

**Lemma CW1 (automatic full endpoints).** If W>=2, then w_K(t)>1 for every |t|<L. Consequently a competitive body with this hull has both full conventional canonical quarter turns.

**Proof.** For 0<=t<L the right side of (C.1) is at least 2-sin t>1. Apply the previously proved canonical reduction, whose endpoint magnitudes lie in [0,L] and whose outgoing strips require width at most one. Both magnitudes must be L. Bodies of area greater than sqrt(2) have the conventional signs by the wrong-direction bound in Note 10. Smaller-area bodies are already strictly below M and do not require this sign conclusion. QED.

This is not the WG gate: no contact condition or feasible/auxiliary symmetrization was used. For completeness, if W<2 and an endpoint alpha is partial, (C.1) gives the quantitative necessary condition

\[
L-\alpha\leq2\arctan(2-W)
\tag{C.2}
\]

whenever the right side is used in the reduced interval. Indeed put delta=L-alpha and divide cos(delta)+(2-W)sin(delta)>=1 by 2sin(delta/2) when delta>0. This bound does not make a partial turn full for W<2.

## C.2 The baseline intercepts are monotone

Use the full lower-turn functions f,g, and the notation of the signed-roof supplement. Write x_+=h_K(0), x_-=-h_K(pi), so W=x_+-x_-. Set

\[
x_0=x_+-1,\qquad x_1=x_-+1.
\]

Let I_t=[ell_t,r_t] be the top face, and I_b=[ell_b,r_b] the bottom face. From B_x'=(1-rho_f)sin t>=0 and D_x'=(1-rho_g)cos t>=0,

\[
\ell_t\leq x_1,\qquad r_t\geq x_0.
\tag{C.3}
\]

The reflected upper half gives the same inequalities for I_b.

For 0<t<L the intersections of the two inner wall lines with the baseline are

\[
a(t)=\frac{f(t)-1}{\cos t},\qquad
 d(t)=\frac{1-g(t)}{\sin t}.
\]

Their derivatives and endpoint limits are

\[
a'=B_y/\cos^2t\geq0,\quad a(0)=x_0,\quad a(L)=r_t,
\]

\[
d'=D_y/\sin^2t\geq0,\quad d(0)=\ell_t,\quad d(L)=x_1.
\tag{C.4}
\]

Thus the baseline section of a positive-height forbidden triangle is exactly the interval (d(t),a(t)) when d(t)<a(t). Its apex height is (a(t)-d(t))sin t cos t.

## C.3 When W>2, the two exposed faces must be identical

If W>2, then x_1<x_0 and every open baseline interval (d(t),a(t)) contains the common nonempty interval (x_1,x_0). By the endpoint limits and monotonicity in (C.4), their union is precisely (ell_t,r_t). Hence the lower signed roof is strictly positive on the entire interior of the top face and nonpositive outside it. The analogous assertion holds for the reflected roof and the bottom face.

The top and bottom intervals both contain [x_1,x_0]. Every endpoint of either exposed face is an extreme point of K and belongs to the compact body S when K=conv(S). A bottom endpoint in the interior of I_t would lie in the open lower sweep, contrary to feasibility. A top endpoint in the interior of I_b would similarly be excluded by the upper sweep.

**Lemma CW2 (alignment without contact order, W>2).** For a common hull of a feasible connected full-turn body under the curvature bound, W>2 implies I_t=I_b.

**Proof.** The intervals have overlapping interiors, but neither interval has an endpoint in the other's interior. If either their left or their right endpoints differed, that larger left endpoint or smaller right endpoint would lie in the other's interior. They must coincide. QED.

The signed roofs are nonnegative in this case: the two axis-angle quadrant sections cover the entire baseline because x_0>x_1. Therefore the clipping and negative-roof terms in (S.7) both vanish, and ordinary saturated area equals the adaptive functional exactly. Contact signs and switching times were not restricted.

## C.4 The width-two boundary case

Now W=2, so x_0=x_1=:x_*. Both exposed-face intervals contain x_*.

The positive lower-roof set is still exactly the interior of I_t, unless that interval is a single point, in which case it is empty. To see this, a is nondecreasing from x_* and d is nondecreasing to x_*. If r_t>x_*, then a(t)>x_* for every t>0: equality at an interior t would force B_y=0 before that t; its nonnegativity and nonincrease would then make B_y identically zero, forcing a constant and r_t=x_*. Similarly, if ell_t<x_*, then d(t)<x_* for every t<L. The endpoint limits now show that the union of (d(t),a(t)) is (ell_t,r_t), including the cases where one endpoint equals x_*.

Extreme-point retention again forbids an endpoint of either face interval from lying in the other's interior. If the two intervals are not equal, their interiors are disjoint and they lie on opposite sides of x_*, allowing a single-point interval as a preliminary possibility. Exchanging left and right if necessary, this gives

\[
\ell_t=x_*,\qquad r_b=x_*.
\tag{C.5}
\]

These endpoint equalities force all four quarter curvatures, not just their moments. In fact D_x(L)-D_x(0)=0 in the top half implies rho_g=1 a.e. Reflecting, B_x(L)-B_x(0)=0 implies rho_{f^rho}=1 a.e. The first equality places the upper endpoint of the leftmost face at height zero. Strip containment forces the lower endpoint also to have height zero, which in the reflected half implies rho_{g^rho}=0 a.e. The second equality places the lower endpoint of the rightmost face at height one; its upper endpoint must also have height one, forcing rho_f=0 a.e.

These implications can also be checked from the trace identities

\[
f'(0)=1-\int_0^L\rho_f\cos t\,dt,\qquad
 g'(L)=-1+\int_0^L\rho_g\sin t\,dt.
\]

All weights are positive in the open interval, so equality of the extremal moments forces the asserted densities. Solving the elementary support equations with their endpoint values shows that the faces are in fact

\[
I_t=[x_*,x_*+1],\qquad I_b=[x_*-1,x_*].
\]

The remaining boundary consists of a unit quarter-circle above the left face endpoint and a unit quarter-circle below the right one. More explicitly the vertical hull sections are

\[
[0,\sqrt{1-(x-x_*)^2}]
\quad(x_*-1\leq x\leq x_*),
\]

\[
[1-\sqrt{1-(x-x_*)^2},1]
\quad(x_*\leq x\leq x_*+1).
\]

Their total area is pi/2. The preliminary single-point unequal-face cases cannot occur, since the forced support equations give these nondegenerate intervals.

**Lemma CW3 (width-two alternative).** Under the hypotheses above, either the exposed faces align, or |K|=pi/2. This statement does not assert that the exceptional hull itself is a feasible sofa; its hull-area bound is enough for the comparison.

## C.5 The strengthened geometric theorem

**Theorem CW4 (sharp comparison for wide curvature-dominated hulls).** Let S be a compact connected ambidextrous body with arbitrary original motions. In a common incoming unit-span normalization let K=conv(S). Suppose

\[
\sigma_K\leq d\theta\quad\text{on all four open quarters},
\qquad h_K(0)+h_K(\pi)\geq2.
\]

Then

\[
\boxed{|S|\leq M,}
\]

with equality exactly for bodies congruent to Romik's candidate. No contact-order, full-turn, or face-alignment hypothesis is imposed.

**Proof.** If |S|<=sqrt(2), the bound is strict. Otherwise Lemma CW1 supplies the full conventional turns. If W>2, CW2 supplies alignment. If W=2, CW3 either supplies alignment or gives |S|<=|K|=pi/2<M. In the aligned case apply Corollary SR3 from the signed-roof supplement and AF3. Their equality recovery identifies the candidate body up to congruence. The candidate has horizontal width 8A/3>2, curvature dominated by one, and the previously verified value M, so it attains equality. For the strict comparison pi/2<M it suffices to use pi<22/7, hence pi/2<11/7<8/5<M. QED.

## C.6 Exact remaining scope

The theorem is global on the stated wide-hull class and is not a protected-neighborhood result. It removes contact order as an assumption for that class by computing the signed roof directly and deriving alignment from feasibility.

It does not assert that every maximizing hull has curvature domination, or that its horizontal width in an incoming unit-span normalization is at least two. If a curvature-dominated competitor lies in the remaining width range 1<W<2, the signed-roof identity still applies once full turns are available, but its clipping/negative-roof balance and possible partial endpoints must be handled. The area bound |S|<=W disposes only of widths below a chosen target value, not the entire remaining interval.

Thus neither narrow hulls nor violating curvature have been removed from the unrestricted problem. The purpose of CW4 is to make clear which contact-order work is genuinely necessary and which has become redundant after AF3 and the signed-roof calculation.

Only pen-and-paper arguments were used. No CI, Lean/Lake compilation, numerical experiment, computer algebra, or manuscript build was performed. The proof is self-reviewed, not independently verified.
