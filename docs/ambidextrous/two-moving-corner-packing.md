# Joint **moving-corner packing**: a universal two-angle compatibility test

**Date:** 2026-10-08. **Research status:** A new exact *necessary condition* on the trajectories of the **physical inner corners** of both handed hallways, derived without any curvature, contact-order, symmetry, niche-clipping, or full-quarter completion assumption. It is a **test on the proposed actual convex hull**; it does **not** prove the sharp Romik area bound or construct a larger sofa.

It extends the branch's existing [DU2 diagonal-width obstruction](diagonal-width-upper-bound.md) to **two independently selected, unequal turning angles**, expressed solely in terms of outer-wall support functions and the two sharp-corner positions. The reduction at the equal \(45^\circ\) frames recovers DU2 and is **not claimed as new**. The genuinely additional diagnostic is the off-diagonal pair condition, illustrated by an exact rational convex pentagon whose *separate* one-pose canonical survivors are both connected and have the entire original hull, but whose joint survivor loses a complete vertical fiber.

This implements the user's intended **outer wall + physical corner first**, then carve the niche. The moving-corner parameterization itself is Romik's [Section 2](https://arxiv.org/html/1606.08111v3#S2), not an original formula.

## 1. Every moving corner carries a two-sided tent

Let \(S\) be compact and **connected**, contained in the incoming strip \(0\le y\le1\), and let \(K=\operatorname{conv}S\), with horizontal projection \(I=[l,r]\). Suppose a conventional lower turn visits angle \(t\in(0,\pi/2)\) and an independently conventional upper turn visits magnitude \(s\in(0,\pi/2)\). No full-turn premise is made: any competitive partial-turn body visits the angles when they are below its actual terminal magnitudes.

For the lower corner, set
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad
c^-(t)=\bigl(h_K(u_t)-1\bigr)u_t+
        \bigl(h_K(v_t)-1\bigr)v_t
       =(\xi_t,\eta_t).
\]
Reflect \(K\) about \(y=1/2\), writing \(\rho K\) for the reflected hull. Apply the same lower construction to \(\rho K\) at \(s\):
\[
c^+(s)=\bigl(h_{\rho K}(u_s)-1\bigr)u_s+
        \bigl(h_{\rho K}(v_s)-1\bigr)v_s
       =(\zeta_s,\theta_s).
\]
Here \((\zeta_s,\theta_s)\) is the **upper-handed corner expressed in reflected lower-turn coordinates**, not its original physical height. In the original frame the upper corner is at \((\zeta_s,1-\theta_s)\).

Each corner's attached inner-wall rays cut a downward open quadrant with exact tent roof
\[
T^-_t(x)=\eta_t-
 a_t(\xi_t-x)_+-b_t(x-\xi_t)_+,
\quad a_t=\tan t,\ b_t=\cot t,
\tag{CP.1}
\]
\[
T^+_s(x)=\theta_s-
 a_s(\zeta_s-x)_+-b_s(x-\zeta_s)_+,
\quad a_s=\tan s,\ b_s=\cot s.
\tag{CP.2}
\]
The original upper-handed forbidden region is **above** the height \(1-T_s^+(x)\). The outer-wall offsets determine both tents: no independently chosen corner placement is silently being optimized.

## 2. An exact off-angle coupling inequality

**Theorem CP1 (two-corner packing).** For every such actual connected sofa and every pair of **visited** angles,
\[
\boxed{
\eta_t+\theta_s\le 1+
\min_{x\in I}\left[
a_t(\xi_t-x)_++b_t(x-\xi_t)_+
+a_s(\zeta_s-x)_++b_s(x-\zeta_s)_+
\right].
}\tag{CP.3}
\]

The minimum is of a **convex piecewise-affine** function, so it is reached at an endpoint \(l,r\) or one of the corner abscissae lying in \(I\). It is therefore a **finite exact** test once the two corner positions and the two angles are known. If both corner abscissae lie in \(I\), CP.3 simplifies to
\[
\boxed{
\eta_t+\theta_s\le1+
\begin{cases}
\min(\cot t,\tan s)(\zeta_s-\xi_t),&\xi_t\le\zeta_s,\\[3pt]
\min(\tan t,\cot s)(\xi_t-\zeta_s),&\zeta_s\le\xi_t.
\end{cases}
}\tag{CP.4}
\]

**Proof.** Every \(x\in I\) belongs to the horizontal projection of \(S\), by compactness, connectedness, and \(\operatorname{proj}_xK=I\). Choose a point \((x,y)\in S\). Canonical support tightening says that the point avoids each lower forbidden quadrant, so
\(y\ge T_t^-(x)\). The reflected upper turn similarly gives \(y\le1-T_s^+(x)\). Therefore
\[
T^-_t(x)+T_s^+(x)\le1
\quad\text{for every }x\in I.
\]
Substituting CP.1–CP.2 and rearranging gives CP.3.

For CP.4 put \(d=\zeta_s-\xi_t\ge0\). To the left of \(\xi_t\), the bracket decreases; to the right of \(\zeta_s\), it increases. On the interval between the corners its slope is \(b_t-a_s\), so its minimum is one of the two endpoints with value respectively \(a_s d\) or \(b_t d\). Since both corners are in \(I\), their smaller value is the unrestricted minimum. This proves the first case. Exchange their order for the second. \(\square\)

**Important:** This inequality is only **necessary**. It does not certify that all extreme hull points survive every angle, does not ensure terminal outgoing strips, and does not give the sharp area. But any failure proves that **no connected ambidextrous sofa with the specified actual hull can visit the selected pair of angles**. If \(T^-+T^+>1\) at a column, the entire vertical column is forbidden, including points outside the proposed convex hull.

### Quantitative pinching width

The functions in CP.1–CP.2 are globally Lipschitz in \(x\), with constants
\[
L_t=\max(\tan t,\cot t),\quad L_s=\max(\tan s,\cot s).
\]
If their sum has value \(1+\delta\), \(\delta>0\), at \(x_0\in I\), then
\[
T^-_t(x)+T^+_s(x)>1
\quad\text{whenever }x\in I,\
|x-x_0|<\frac{\delta}{L_t+L_s}.
\tag{CP.5}
\]
Thus the incompatibility is an **open horizontal interval of empty fibers**, not a single isolated point. This observation is useful for robust exclusion/certification of proposed hulls; it does not provide an area-above-\(M\) construction.

## 3. At \(45^\circ\), CP1 recovers the known diagonal-width obstruction

For \(t=s=\pi/4\), both moving corner abscissae lie in \(I\) whenever \(W=r-l\ge1\). To see this, write
\[
A=\max_{p\in K}(p_x+p_y),\quad
B=\max_{p\in K}(-p_x+p_y).
\]
Since \(0\le p_y\le1\),
\(r\le A\le r+1\) and \(-l\le B\le-l+1\).
Therefore \(\xi_{\pi/4}=(A-B)/2\in[(l+r-1)/2,(l+r+1)/2]\subseteq I\). Apply the same argument to \(\rho K\) for \(\zeta_{\pi/4}\).

Put \(a=\min_{p\in K}(p_x+p_y)\) and
\(b=\min_{p\in K}(-p_x+p_y)\).
The four corner coordinates at \(45^\circ\) give exactly
\[
\eta_{\pi/4}+\theta_{\pi/4}
=\frac{A+B-a-b+2-4\sqrt2}{2},
\qquad
\xi_{\pi/4}-\zeta_{\pi/4}
=\frac{(A-a)-(B-b)}2.
\tag{CP.6}
\]
Since all four wall slopes are one, CP.4 becomes
\(\eta+\theta\le1+|\xi-\zeta|\). Insert CP.6 to get
\[
\min(A-a,B-b)\le2\sqrt2,
\]
or equivalently
\[
\boxed{\min\{w_K((1,1)/\sqrt2),
w_K((-1,1)/\sqrt2)\}\le2.}\tag{CP.7}
\]
This is **precisely the already proved DU.2**, now explained as a no-overlap inequality for the **two moving sharp corners**. The off-angle constraints are its natural continuum generalization.

## 4. A rational pentagon: individual snapshots work, but two corners conflict

Let \(K\) be the following convex pentagon, vertices in counterclockwise order:
\[
\boxed{
P_1=(-13/10,4/5),\;
P_2=(-19/20,0),\;
P_3=(-7/10,0),\;
P_4=(13/10,3/4),\;
P_5=(13/20,1).
}\tag{CP.8}
\]
All five oriented consecutive cross products are strictly positive; its vertical span is **exactly one** and horizontal width \(13/5\). Its ordinary **outer-hull** area is \(1147/800\), **not** a feasible sofa area.

Take the *lower* normal pair
\[
(\cos t,\sin t)=(20/29,21/29)
\]
and the *upper* reflected normal pair
\[
(\cos s,\sin s)=(4/5,3/5).
\tag{CP.9}
\]
The exact support computations give
\[
\begin{aligned}
c^-(t)&=\left(-\frac{453}{8410},\frac{2215}{3364}\right),\\
c^+(s)&=\left(-\frac7{100},\frac{41}{100}\right).
\end{aligned}\tag{CP.10}
\]
Both abscissae lie inside the hull's projection \([-13/10,13/10]\). Since \(-7/100<-453/8410\), the CP.4 loss for the horizontal corner mismatch is
\[
d=\min(21/20,4/3)\left(\frac7{100}-\frac{453}{8410}\right)
=\frac{28497}{1682000}.
\]
Yet the two tent heights obey
\[
\boxed{
\frac{2215}{3364}+\frac{41}{100}
-\frac{28497}{1682000}
=\frac{2103}{2000}>1.
}\tag{CP.11}
\]
Therefore **no connected body with actual convex hull \(K\)** can satisfy those two ordinary hallway positions simultaneously. A full ambidextrous motion would have to visit both angles, so this hull is impossible for such a motion.

This is a **genuine joint-corner incompatibility**, not merely one extreme vertex colliding with a wall:

- Every one of the pentagon's **five extreme vertices is safe at each of the two individual supporting hallway placements**. The minimum safety margin \(1-\min(D_u,D_v)\) is at least \(2/145>0\) in the lower pose and \(33/100>0\) in the reflected upper pose.
- Even stronger, each **one-pose** canonically carved envelope **separately** has a nonempty vertical interval over *every* x in the whole projection, is connected, and has **actual convex hull \(K\)**. This follows by comparing the one tent roof to the polygon's concave upper hull roof: their difference is piecewise affine, and the maxima at the vertex abscissae and the corner abscissa are exactly
  \[
  \max_x(T^-_t(x)-a_K(x))
   =-\frac{176699}{655980}<0,\quad
  \max_x(T^+_s(x)-a_{\rho K}(x))
   =-\frac{283}{800}<0.
  \tag{CP.12}
  \]
  Because each original vertex is individually safe, the hull is retained after either *separate* carving.
- The old **two-\(45^\circ\) diagonal-width necessary test** passes:
  \[
  \min\{A-a,B-b\}=\frac{53}{20}<2\sqrt2
  \]
  (square both positive sides: \(2809<3200\)).
  Every original vertex is individually safe at both \(45^\circ\) hallway positions as well: their maximum minimum-depth numerators are respectively \(7/5\) and \(9/10\), both strictly below \(\sqrt2\).
  
Thus the off-diagonal corner test detects a **pure two-handed interior-fiber obstruction** missed by the individual one-pose hull/extreme checks and by the diagonal-width condition alone. It gives **no numerical counterexample to Romik**; the actual sofa with this proposed hull does not exist.

The [exact Fraction checker](computer-assisted/check_two_corner_packing.py) computes CP.10–CP.12, the polygon's convexity, and the diagonal rational comparisons. The proof of CP1 itself is elementary and independent of the checker.

## 5. All corner–outer-wall and corner–corner tests give an exact admission criterion

The paired condition CP.3 is necessary but does not, by itself, make the proposed convex hull a genuine full-turn sofa hull. There is a clean **exact converse when every relevant outer boundary and every corner pair is checked**.

For arbitrary compact convex \(K\subset\mathbb R\times[0,1]\), let \(I=[l,r]\), let \(a_K(x),b_K(x)\) be its upper/lower vertical hull roofs, and let \(T_t^-,T_s^+\) be the two moving-corner tent roofs defined by CP.1–CP.2, for **all** \(t,s\in(0,\pi/2)\). Make the following three families of inequalities:
\[
\begin{array}{lll}
\text{lower corner vs. outer top:}
&T_t^-(x)\le a_K(x)&\forall x\in I,\ \forall t,\\
\text{upper corner vs. outer bottom:}
&T_s^+(x)\le1-b_K(x)&\forall x\in I,\ \forall s,\\
\text{lower corner vs. upper corner:}
&T_t^-(x)+T_s^+(x)\le1
&\forall x\in I,\ \forall t,s.
\end{array}\tag{CP.13}
\]

**Proposition CP2 (complete no-pinch criterion).** The full two-handed canonical envelope \(E(K)\) has a nonempty interval fiber over **every** \(x\in I\) if and only if **all three** inequalities in CP.13 hold. In that case \(E(K)\) is connected. Furthermore \(K\) is itself the *actual convex hull of some compact connected full-two-turn sofa* if and only if CP.13 holds **and every extreme point of \(K\)** survives both complete families of corner/ray constraints.

**Proof.** Write \(F(x)=\max(0,\sup_t T_t^-(x))\) and \(G(x)=\max(0,\sup_s T_s^+(x))\). Since \(0\le b_K\le a_K\le1\), the canonical fiber is precisely
\[
E(K)_x=[\max\{b_K(x),F(x)\},
          \min\{a_K(x),1-G(x)\}]
\]
when the left endpoint is no greater than the right, and empty otherwise. If CP.13 holds, its first two families give \(F\le a_K\) and \(G\le1-b_K\). The third gives \(F+G\le1\): when both suprema are positive this follows by taking their double supremum, and when one is zero it follows from \(F\le a_K\le1\), \(G\le1-b_K\le1\). Together these three facts force the displayed lower endpoint to be at most its upper endpoint. Conversely, if a fiber is nonempty, choosing one of its actual points between the two boundaries proves all three inequalities at that \(x\).

Compactness and full interval projection imply connectedness by the standard interval-fiber argument. For the final assertion, a connected feasible body with hull \(K\) must contain all extreme points and occupy every abscissa, so both conditions are necessary. Conversely when both hold, \(E(K)\) is connected, contains every extreme point of \(K\), and has \(\operatorname{conv}E(K)=K\) by the finite-dimensional extreme-point hull theorem; its canonical supporting motions are continuous and its full-quarter endpoint strips are automatic. This is the previously proved hull-admission result [FH2](feasible-hull-minkowski-nonconvexity.md), now written entirely as **outer-wall–corner and corner–corner** geometric tests. \(\square\)

For **partial** terminal turns the same proof works only after adding the two complete outgoing **straight-arm strip barriers** as additional lower/upper affine gates, exactly as in [OS1](original-motion-signed-convex-domain.md). Omitting them invalidates the converse.

### Crucial limitation at the Romik reference: corner pairs have uniform slack

Let \(K_*\) be Romik's actual convex hull. The existing explicit whole-angle corner-ceiling proof [ME/NR](near-reference-positive-minwidth-slack.md) gives
\(\eta_t,\theta_s<13/30\) for **every** pair of complete turning angles, due to the candidate's height-reflection symmetry. Hence
\[
\boxed{
\eta_t+\theta_s<13/15<1
\quad\text{for all }t,s;
\qquad
1+d_{t,s}^I-\eta_t-\theta_s>\frac2{15}.
}\tag{CP.14}
\]
Thus the **pair-corner packing inequality is not even asymptotically active at the proposed optimizer**. It can exclude distant, pinched or asymmetric hulls and supply useful necessary support restrictions, but it cannot *by itself* generate Romik's sharp Euler–Lagrange contact equations or certify area \(M\). A complete proof must also quantitatively charge the movement of the attached **inner-wall ray envelopes** against the gain on the **outer-wall contact curves**. The full ordinary-area niche carving remains indispensable.

## 6. How this might enter a sharp proof

The corner-pair constraints **couple the two turns before any niche area is integrated**. For any candidate maximizing hull, all selected pairs \((t,s)\) in its *actual visited intervals* satisfy CP.3. The constraints depend **only on four support values** (two for each corner), and the support values are affine under Minkowski interpolation. For rational Pythagorean normal pairs they are exactly rational on rational polygonal hulls. They therefore supply inexpensive, continuum-valid rejection inequalities for a future area certificate or for restricting global variational contact paths.

The restriction of a completed sofa's **ordinary surviving area** to a particular hull still requires the full swept rays/tent roof, not just CP.3. A candidate violating CP.3 can be rejected; passing every checked pair is not an area bound. Closing optimality would require using all such geometric coupling together with an upper bound on the *remaining* ordinary area, or proving an equally strong global calibration of outer contacts against their complete niche sweeps.

The known Romik candidate passes these necessary inequalities, but that by itself supplies no global uniqueness or maximum-area theorem. No CI, Lean, manuscript compilation, numerical global optimization or formal proof is claimed here.
