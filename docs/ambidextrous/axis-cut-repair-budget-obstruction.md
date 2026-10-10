# Near-optimal axis cuts defeat an unconditional use of the repair budget

The corrected functionals AC1 and AS1 have proved sharp maxima. Their ordinary-area linkage was deliberately left as a separate hypothesis. This note proves that the proposed blanket linkage AS.10 is false, even for feasible bodies with areas tending to M from below and with the candidate's exact width.

The defect is different from GR1. There, an active middle corner has adverse velocity work, which the corrected functional can accommodate. Here the global repair fills hull area that was already absent from the nonconvex sofa. Charging its entire derivative energy as newly surviving area is too strong. The result is analytic; numerical cut experiments suggested it but are not used in the proof.

Let Sigma be the explicitly constructed candidate, K_*=conv(Sigma), and let [ell,r] be its common top/bottom face interval. Put m=r-ell>0 and let W_* be its horizontal width, with 2<W_*<4. The values and regularity used below are proved from the candidate formulas in Notes 4, 14 and 18.

## 1. A feasible family obtained by an actual half-plane cut

For tau>0 define

\[
H_\tau=\{(x,y):y+\tau(x-\ell)\leq1\},
\qquad S_\tau=\Sigma\cap H_\tau.
\tag{AX.1}
\]

The candidate has vertically convex sections containing y=1/2 throughout its horizontal projection, because its convex hull is reflection symmetric and the two niches have a strict central gap. For sufficiently small tau the cutting line stays above y=1/2 on that whole projection. Consequently S_tau is compact and connected, and it inherits both of Sigma's full motions. No new motion or approximation is asserted.

The left top endpoint (ell,1), the bottom face endpoints, and the horizontal extreme points are retained. The upper-right convex flank meets the new line at a point P_tau with abscissa strictly larger than r. The only new exposed face of the clipped convex hull joins (ell,1) to P_tau. Its two endpoints belong to S_tau; all other extreme points of the clipped hull are unchanged extreme points of K_* that remain in Sigma. It follows that

\[
K_\tau:=\operatorname{conv}(S_\tau)=K_*\cap H_\tau.
\tag{AX.2}
\]

Thus K_tau has the same four axis support values and width W_* as K_*. Its upper face has shrunk to (ell,1), but its vertical span remains one. For normals in all quarters except the first upper quarter, the old support points satisfy the cut and the support is unchanged.

## 2. The actual area deficit is smaller than first order

Write U(x) for the top boundary of Sigma. Its only height-one points are (ell,1) and (r,1). Near both, the candidate formulas give upper boundary pieces on circles of radius 1/2, and in particular

\[
1-U(x)\geq c\,\operatorname{dist}(x,\{\ell,r\})^2
\tag{AX.3}
\]

on the whole compact horizontal projection, for some c>0. To check the local fact directly, the first D and final B niche arcs have

\[
D(t)=(\ell+\tfrac12\sin t,\ \tfrac12(1-\cos t)),
\]

and, with z=L-t,

\[
B(t)=(r-\tfrac12\sin z,\ \tfrac12(1-\cos z)).
\]

Their reflections give the top surviving roof. The outer upper-right flank is
\((r+\tfrac12\sin z,\ \tfrac12(1+\cos z))\). These circle formulas give (AX.3) near the peaks, using 1-sqrt(1-4d^2)>=2d^2. Away from fixed neighborhoods of the two peaks, continuity and the strict height gap give a positive minimum, which completes (AX.3).

A point removed by H_tau has x>ell and height above 1-tau(x-ell). Therefore it can occur only where dist(x,{ell,r})<=sqrt(tau W_*/c). The total horizontal length of this set is at most 4sqrt(tau W_*/c), and the removed height is at most tau W_*. Hence, for a fixed C,

\[
\boxed{0<M-|S_\tau|\leq C\tau^{3/2}.}
\tag{AX.4}
\]

The strict loss follows from the nonempty piece cut near the right height-one point. This is an ordinary-area estimate for the actual bodies, not their hulls.

## 3. What the global curvature majorant does to this cut

Let h_tau be the support of K_tau, let bar h_tau=R(h_tau) be the operator GM2, and let u_tau=bar h_tau-h_tau. All quarters other than the first upper quarter are unchanged and already curvature dominated, so u_tau is supported in that quarter and vanishes at its endpoints.

For small tau,

\[
0\leq h_*-h_\tau\leq W_*\tau.
\tag{AX.5}
\]

One direct Hausdorff proof is vertical: a point of K_* above the cut can be moved down by W_* tau to satisfy it. The moved point remains in its hull fiber for tau small, since that fiber contains y=1/2 and the removed portion is near y=1. Points below the cut do not move. The support estimate follows.

By monotonicity and idempotence of GM2,

\[
h_\tau\leq\bar h_\tau\leq h_*.
\tag{AX.6}
\]

Both bar h_tau and h_* have uniformly bounded second derivatives inside this quarter, including one-sided endpoint traces, because their curvature densities are in [0,1] and their support values are uniformly bounded. The elementary finite-difference estimate therefore gives

\[
\|\bar f_\tau'-f_*'\|_\infty=O(\sqrt\tau).
\tag{AX.7}
\]

For completeness, subtract the functions, bound the derivative by a one-sided difference over length sqrt(tau) plus the uniform second-derivative bound times that length, and use (AX.5)--(AX.6). At an interior point choose either side that remains in the quarter. The same one-sided estimate applies to endpoint traces.

Let delta_tau=arctan(tau) and t_tau=L-delta_tau, the outward normal angle of the new cut face. For t_tau<t<L the exposed point of K_tau is precisely (ell,1), so

\[
f_\tau(t)=\ell\cos t+\sin t,
\qquad f_\tau'(t)=-\ell\sin t+\cos t.
\tag{AX.8}
\]

The reference derivative at L is -r. Equations (AX.7)--(AX.8) show, uniformly on this terminal interval,

\[
u_\tau'(t)=\ell-r+O(\sqrt\tau)=-m+O(\sqrt\tau).
\]

For sufficiently small tau, |u_tau'|>=m/2 there. Since arctan(tau)>=tau/2 for 0<tau<=1,

\[
\boxed{\int_0^L u_\tau'^2\,dt\geq\frac{m^2}{8}\tau.}
\tag{AX.9}
\]

The derivative cost is first order, although the actual missing sofa area is only O(tau^{3/2}). It is the change in a long exposed hull face, not an actual first-order loss of sofa material.

## 4. A rigorous failure of the proposed geometric budget

The candidate's relevant q has maximum strictly less than one. In the present one-quarter repair, g is unchanged and bar q_tau=g_*'+bar f_tau-1<=q_* by (AX.6). Therefore 1-(bar q_tau)_+ is uniformly positive.

Evaluate the proved auxiliary functional AS.1 at the repaired profile and its actual increment. The only nonzero increment is u_tau on this one half, so

\[
\mathcal J_{\rm side}(\bar h_\tau;u_\tau)
=\widetilde{\mathcal Q}(\bar h_\tau)
-\int(1-(\bar q_\tau)_+)u_\tau
-\tfrac12\int(u_\tau'^2-u_\tau^2).
\]

AF3 bounds the first term by M. The linear integral is nonnegative. The quarter Dirichlet inequality bounds integral u_tau^2 by one quarter of integral u_tau'^2. Using (AX.9),

\[
\boxed{\mathcal J_{\rm side}(\bar h_\tau;u_\tau)
\leq M-\frac{3m^2}{64}\tau.}
\tag{AX.10}
\]

For sufficiently small tau, the right side of (AX.4) is less than 3m^2 tau/64. Combining the two estimates proves:

**Theorem AX1 (near-optimal failure of unconditional corrected enclosure).** For all sufficiently small positive tau,

\[
\boxed{|S_\tau|>
\mathcal J_{\rm side}(h_{R(K_\tau)};h_{R(K_\tau)}-h_{K_\tau}),
\qquad |S_\tau|\longrightarrow M.}
\tag{AX.11}
\]

Increments on the other half/quarter are zero as specified above. These are genuinely feasible, connected, full-turn bodies of the candidate's exact width, not a numerical finite-angle witness. The smaller functional AC.1 cannot universally enclose these areas either.

This does not contradict AS1, which bounds a defined functional and explicitly does not assert (AS.10). It does not contradict the valid geometric implications under RC1's full accounting hypotheses: the present cut changes exposed-face/tail geometry, and the extra hull area created by repair can be inside a niche rather than newly surviving body material.

## 5. Consequence for the attempted closure route

The construction GM2, the exact obstruction GR1, and the calibrations AC1/AS1 remain valid. The proposed shortcut of inserting the **entire** least-majorant increment into AS.10 is now explicitly ruled out even by near-optimal inputs. A high-area threshold below M cannot rescue that inequality.

A future successful global comparison must account for which repaired hull area actually survives, or use different auxiliary tail bodies/controls. It cannot charge every exposed-face repair by the positive Dirichlet energy in (AX.9). The already proved statement for genuine standard-corner accounting is unaffected, but it is not an unrestricted proof.

No computer calculation is needed for AX1. Floating-point cuts suggested the mismatch; the inequalities above supply its analytic proof. All previous candidate and calibration dependencies are identified, and the argument remains subject to independent review.
