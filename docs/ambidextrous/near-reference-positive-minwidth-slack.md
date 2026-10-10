# Positive minimum-width clipping arbitrarily close to Romik's value

**Scope.** This strengthens MS3's circular-stadium obstruction from a low-area example to **genuinely feasible, canonically saturated, two-full-turn bodies of area strictly below and arbitrarily close to the reference \(M\)**. Their incoming orientation is a *global minimum-width direction*, and both open-quarter support-curvature densities are bounded by one; the upper and reflected lower caps coincide and have aligned positive faces. Nevertheless the signed minimum-width correction \(G_s\) is **strictly positive**. Thus neither regular curvature, alignment, full symmetry, saturation, nor arbitrarily high subcritical area makes \(G_s\le0\) automatic. The result does not violate or prove the combined sharp inequality \(G_s\le\Delta(U)+\Delta(V)\). Labels NR are local.

The input is the explicit reference support from Note 14 and its strict corner-height margin in ME. The general small-slack law is MS2. The signed regular-cap comparison and its equality case are SR/AF; these replace reliance on WV's long weighted-maximizer selection chain for the area-\(<M\) conclusion.

## 1. Horizontally thicken the reference *convex hull*, not the sofa

Let \(K_*=\operatorname{conv}(\Sigma)\) be the centered Romik reference convex hull, with horizontal projection \([-m,m]\), vertical span \([0,1]\), and identical top and bottom faces \(J_*=[-m/2,m/2]\) of length \(m>1\). Its upper downward cap \(U_*\) has open-quarter curvature densities between zero and one. Let
\[
H_*=\max_{0\le t\le\pi/2}c_{*,y}(t)<13/30<1/2
\]
be the reference inner-corner-height bound proved in ME. The original body is the full canonical envelope of \(K_*\), and its area is \(M=2\Psi(U_*)\).

Fix \(0<\delta\le1/16\), and form the horizontally thickened **convex hull**
\[
K_\delta=K_*+[-\delta/2,\delta/2]e_x.
\tag{NR.1}
\]
This is compact, convex, horizontally and vertically reflection-symmetric, and still has vertical span one. Its top and bottom face intervals agree and have length
\[
\boxed{T_\delta=m+\delta},
\qquad
\boxed{W_\delta=2m+\delta}
\tag{NR.2}
\]
for their common projection width. In particular
\[
\boxed{2T_\delta-W_\delta=\delta>0.}\tag{NR.3}
\]
The downward upper cap \(U_\delta\) has support
\[
h_\delta(\theta)=h_*(\theta)+\frac\delta2|\cos\theta|
\quad(0\le\theta\le\pi).
\tag{NR.4}
\]
On the open first and second upper quarters, the added cosine solves \(h''+h=0\), so the quarter curvature measures of \(U_\delta\) are **exactly those of the reference**. Only the vertical-normal top-face atom and horizontal projection change; no interior facets have been assumed absent without proof.

## 2. Full-turn feasibility and actual hull

For \(0\le t\le L=\pi/2\), the two upper support increments are
\[
f_\delta(t)-f_*(t)=(\delta/2)\cos t,\qquad
g_\delta(t)-g_*(t)=(\delta/2)\sin t.
\]
Therefore the height of their canonical inner corner changes by
\[
c_{\delta,y}(t)-c_{*,y}(t)
=\delta\sin t\cos t\le\delta/2.
\]
Since \(\delta\le1/16\), this gives the explicit strict margin
\[
\boxed{\max_t c_{\delta,y}(t)
<13/30+1/32=223/480<1/2.}\tag{NR.5}
\]
Every positive point of a forbidden open quadrant lies below its inner corner. Thus the full positive niche of \(U_\delta\) has height strictly below one half. Because the open-quarter curvature is still between zero and one and \(W_\delta>2\), the entire positive niche is horizontally confined to \(J_\delta\) by MS1.

The hull \(K_\delta\) contains its full horizontal midline over the projection: take every old midline point of \(K_*\) and add the horizontal segment in NR.1. Consequently the canonical two-turn envelope
\[
E_\delta=E_{\rm full}(K_\delta)
\]
has nonempty vertical interval fibers, each containing \(y=1/2\). It is compact, connected, and satisfies both complete canonical hallway families. Its actual hull is precisely \(K_\delta\): outside the top-face interval \(J_\delta\), the full niches vanish, so all upper and lower outer flanks and both horizontal extreme points are retained. At the four top/bottom face endpoints, the niches also vanish because their projection is inside the *open* face interval. Those retained support points recover the full top and bottom face chords as convex-hull segments. Therefore \(K_\delta=\operatorname{conv}(E_\delta)\), without a hidden larger auxiliary hull.

On the common top-face interval the hull roofs are exactly 1 and 0, so no positive clipping occurs. With the two caps identical,
\[
\boxed{|E_\delta|=2\Psi(U_\delta).}\tag{NR.6}
\]
The regular-cap SR/AF sharp functional bound gives \(\Psi(U_\delta)\le M/2\), and its strict equality characterization identifies only the original reference cap (up to translation). Since \(\delta>0\) increases the top-face length, \(U_\delta\) is not that cap. Hence
\[
\boxed{|E_\delta|<M,\qquad |E_\delta|\longrightarrow M
\quad(\delta\downarrow0).}\tag{NR.7}
\]
The convergence follows from uniform Hausdorff convergence \(U_\delta\to U_*\) and full niche-area continuity HV2, or directly from the exact continuous support-area/niche formulas; it does not rely on the unproved unrestricted sofa conjecture.

## 3. Shrink into the actual global minimum-width frame

For fixed \(\delta>0\) choose \(s>0\) small, put \(k=1-s\), and form
\[
K_{\delta,s}=kK_\delta+(0,s),\qquad
E_{\delta,s}=E_{\rm full}(K_{\delta,s}).
\tag{NR.8}
\]
The translated homothetic copy \(kE_\delta+(0,s)\) is connected and fully feasible, and is contained in \(E_{\delta,s}\). Therefore its canonical saturation is again compact, connected, full-turn feasible and has **actual hull \(K_{\delta,s}\)**.

The hull contains the full rectangle \(kJ_\delta\times[s,1]\), whose horizontal length is \(kT_\delta\) and vertical height \(k\). Since \(T_\delta>1\), every directional width of the original \(K_\delta\) is at least one, attained vertically; the analogous minimum of \(K_{\delta,s}\) is exactly \(k\). Thus the chosen incoming normal is a genuine *global* minimum-width direction; no unproved motion-preserving affine normalization is involved.

The upper and reflected-lower height-one caps of \(K_{\delta,s}\) coincide. They are open-quarter curvature-controlled and have the same positive face interval. MS2 applies with the unscaled data \((T_\delta,W_\delta)\), giving
\[
\boxed{\lim_{s\downarrow0}\frac{G_{\delta,s}}s
=2T_\delta-W_\delta=\delta>0.}\tag{NR.9}
\]
Therefore \(G_{\delta,s}>0\) for **every sufficiently small \(s>0\)** at each fixed \(\delta>0\).

At fixed \(\delta\), both \(\Psi(U_{\delta,s})\to\Psi(U_\delta)\) (by HV2) and \(G_{\delta,s}\to0\). From NR.7 choose s small enough to retain
\[
|E_{\delta,s}|=2\Psi(U_{\delta,s})+G_{\delta,s}<M.
\]
We can simultaneously require \(s\le\delta^4\), so along any sequence \(\delta_j\downarrow0\) a compatible choice \(s_j\downarrow0\) gives
\[
\boxed{
G_{\delta_j,s_j}>0,\qquad
|E_{\delta_j,s_j}|<M,\qquad
|E_{\delta_j,s_j}|\longrightarrow M.}
\tag{NR.10}
\]
Thus the obstruction survives **arbitrarily close to the sharp reference area**; it is not just the nonoptimal stadium geometry.

## 4. Consequences for the remaining general frontiers

The negative slab term \(-sW\) of MF2 is real, and SM1's \(s^{3/2}\) gain for the reference-scale family is real. But the first-order term changes sign under an arbitrarily small, genuine horizontal thickening of the reference hull. Accordingly the following proposed shortcuts are invalid even on regular full-turn bodies of arbitrarily high subcritical area:

- “At a true minimum-width direction the signed correction \(G_s\) is always nonpositive.”
- “If \(\Psi(U)+\Psi(V)\) is arbitrarily close to \(M\), the correction \(G_s\) must be nonpositive.”
- “The two face intervals are identical and curvature controlled, so the slab term automatically wins.”

None of these statements uses the actual weighted cap deficits. The correct outstanding inequality is still
\[
G_s\le\Delta(U_{\delta,s})+\Delta(V_{\delta,s})
\]
and its arbitrary-pair extension. NR.10 is consistent with it: these explicitly constructed bodies remain below M because their regular-cap deficits cover the positive correction.

For partial turns, a bridge based only on comparing asymptotic exponents \(s^{3/2}\) and \(\varepsilon^3\) is also insufficient without geometric relations and an actual signed loss bound. The completed reference-scale safe-strip theorem SB has its separate hypotheses; NR does not put arbitrary competitors into that family.

All new proofs are pen and paper, using the explicit reference, MS, HV2 and the established regular SR/AF comparison. No script, CI, Lean/Lake compilation, dependency installation, or manuscript build is a mathematical premise. Both unrestricted full-turn and partial-turn optimality remain unproved.


## 5. The weighted deficit has an explicit quadratic hand bound

The qualitative strict inequality in NR.7 can be quantified **without** invoking the long WV maximizing-cap source-flux proof. It is a direct application of the already written unrestricted \(H^1\) calibration AF and the reference's exact sign intervals.

On the first quarter write \(f_\delta=f_*+v\), \(g_\delta=g_*+w\), where
\[
v(t)=\frac\delta2\cos t,\qquad
w(t)=\frac\delta2\sin t.
\]
Let \(F\) be the exact signed-roof functional AF equation (A.1). The vertical height is one, the width \(W_\delta>2\), and the support has open-quarter densities between zero and one; hence SR1 identifies the actual full-niche value with
\[
\Psi(U_\delta)=F(f_\delta,g_\delta)-W_\delta/2.
\]
The candidate is an interior stationary point of the **full width-variable** calibrated functional: the interior Euler and switching fluxes vanish and its natural width boundary condition is \(P(0)=1/2\) (AF A.8--A.11). Therefore its exact expansion along this affine admissible direction has **zero linear term** after including the width penalty.

The unpenalized quadratic part of F, computed directly from AF A.1, is
\[
\frac12\int_0^L\left[
2(v^2+w^2)-v'^2-w'^2+v\,w'-w\,v'
\right]dt
=\frac{\delta^2 L}{4},
\quad L=\pi/2.
\]
The two contact-loss functions are \(\min(p,0)^2\) and \(\max(q,0)^2\). Their arguments change by
\[
p_\delta-p_* =v'-w=-\delta\sin t,\qquad
q_\delta-q_*=w'+v=\delta\cos t.
\]
The reference has \(p_*<0\) on \((\beta,L)\) and \(q_*>0\) on \((0,L-\beta)\), with \(\beta=\arctan Y\). These signs remain unchanged under the corresponding one-sided perturbations for **every** \(\delta>0\). On those intervals the respective convex square's Bregman remainder equals exactly \(\delta^2\sin^2t\) or \(\delta^2\cos^2t\). On the other intervals the remainder is nonnegative by convexity; no assumption about their shifted switching locations is needed.

Thus, subtracting the quadratic change from the positive contact remainders gives
\[
\begin{aligned}
\Delta(U_\delta)
&=\frac M2-\Psi(U_\delta)\\
&\ge\frac{\delta^2}{2}\left[
\int_\beta^L\sin^2t\,dt+
\int_0^{L-\beta}\cos^2t\,dt
\right]-\frac{\delta^2 L}{4}\\
&=\boxed{\frac{L-2\beta+\sin(2\beta)}4\,\delta^2.}
\end{aligned}\tag{NR.11}
\]

The coefficient is strictly positive. An entirely rational lower bound is
\[
\frac{L-2\beta+\sin(2\beta)}4
>\frac{3/2-3/5}{4}=\frac9{40},
\]
using \(L=\pi/2>3/2\), \(0<\beta=\arctan Y<Y<3/10\), and \(\sin(2\beta)>0\). Hence
\[
\boxed{|E_\delta|=2\Psi(U_\delta)
\le M-\frac9{20}\delta^2<M.}\tag{NR.12}
\]

This explicitly displays the deficit that pays the later positive signed slab correction for sufficiently small s at each fixed \(\delta\). The bound is uniform over \(0<\delta\le1/16\) and remains a *regular-cap* result; it is not an ordinary-area bound for arbitrary rough opposite-face competitors. As \(\delta,s\downarrow0\), both the positive \(G_{\delta,s}\) and the cap deficit tend to zero, so the general frontier is still a sharp comparison of two small quantities.
