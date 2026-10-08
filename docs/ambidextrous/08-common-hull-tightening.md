# 8. Simultaneous support tightening and removal of angular backtracking

This note proves a reduction missing from the first pass: translations in the two witnesses can be replaced simultaneously by functions of the **same convex hull**. Angular backtracking can then be erased, but the final angle need not be a quarter turn. No single-turn maximizing replacement, symmetry, injectivity, or optimality is used.

The support-function idea is elementary and closely related to canonical hallway placements in the moving-sofa literature. No novelty claim is made. Compare the rotation-path formulation in Romik, [arXiv:1606.08111v3, Section 2](https://arxiv.org/html/1606.08111v3#S2); the quarter-turn endpoint restriction there is stronger than the variable-endpoint conclusion proved here.

## 8.1 Tightening one placement without losing the body

For an ordered orthonormal frame (u,v) and real a,b, write

\[
L_{u,v}(a,b)=\{p:p\cdot u\leq a+1,\ p\cdot v\leq b+1,
\quad p\cdot u\geq a\ \text{or}\ p\cdot v\geq b\}.
\tag{8.1}
\]

The frame may have either handedness. Its incoming arm has v-coordinate in [b,b+1]; its outgoing arm has u-coordinate in [a,a+1]. This is exactly a rigidly placed unit-width hallway, not a convex relaxation.

Let S be nonempty and compact, let K=conv(S), and denote its support function by
\(h_K(n)=\max_{p\in K}p\cdot n=\max_{p\in S}p\cdot n\).
Set

\[
a_K(u)=h_K(u)-1,\qquad b_K(v)=h_K(v)-1,
\qquad c_K(u,v)=a_K(u)u+b_K(v)v.
\tag{8.2}
\]

**Proposition 19 (canonical placement).** If \(S\subseteq L_{u,v}(a,b)\), then

\[
S\subseteq L_{u,v}(a_K(u),b_K(v)).
\tag{8.3}
\]

**Proof.** The original outer-wall inequalities give \(a_K(u)\leq a\) and \(b_K(v)\leq b\). Every p in S satisfies the new outer-wall inequalities by the definition of support. It satisfies at least one of \(p\cdot u\geq a\), \(p\cdot v\geq b\), so it satisfies at least one of the corresponding weaker inequalities with a_K,b_K. This is exactly (8.3). QED.

Equivalently, tightening the two outer support lines moves the forbidden quadrant down in both frame coordinates. Its new forbidden set

\[
Q_K(u,v)=\{p:p\cdot u<h_K(u)-1,\ p\cdot v<h_K(v)-1\}
\tag{8.4}
\]

is a subset of the old forbidden quadrant. The tightening keeps S fixed; it does **not** claim K itself fits the hallway.

If the frame varies continuously, c_K varies continuously, since a compact set has a continuous support function. In fact \(|h_K(n)-h_K(m)|\leq (\max_K|p|)|n-m|\), directly by taking maxima in the defining scalar products.

## 8.2 Endpoints survive tightening

Write \(w_K(n)=h_K(n)+h_K(-n)\) for width in direction n.

**Lemma 20 (endpoint arms).** If \(w_K(v)\leq1\), then the canonical incoming arm contains all of K. If \(w_K(u)\leq1\), then the canonical outgoing arm contains all of K.

**Proof.** The first width inequality says \(p\cdot v\geq h_K(v)-1=b_K(v)\) for every p in K; the other required bounds are the defining support inequalities. Exchange u and v for the outgoing arm. QED.

Thus the initial and terminal strips of an original witness remain valid after tightening. Different initial translations for the two canonical witnesses do not change the incoming orientation. They can be preceded by translations within the convex common incoming arm, as in Proposition 14, to recover a common incoming pose.

## 8.3 Canonical monotone motions, with a variable endpoint

For a fixed handedness use frames

\[
u(t)=R_t e_x,\qquad v(t)=\sigma R_t e_y,\qquad \sigma\in\{+1,-1\}.
\tag{8.5}
\]

The lower-turn hallway uses sigma=+1; the reflected upper-turn hallway uses sigma=-1. Its affine inner-corner offset is absorbed into a,b. A continuous original proper motion has a continuous lifted frame angle alpha(s), with alpha(0)=0. Such a lift can be obtained by choosing an argument locally on the circle and joining the choices on successive overlapping intervals.

**Theorem 21 (erase backtracking).** Every one-turn witness for S can be replaced by a canonical witness whose angle moves monotonically from 0 to some

\[
\omega\in[-\pi/2,\pi/2].
\tag{8.6}
\]

It has the same incoming body orientation and transports the same S into the outgoing arm. Apply this independently to the two original witnesses to obtain two such motions determined by one K and two endpoint angles.

**Proof.** First replace every original placement by its canonical placement using Proposition 19. If alpha first hits either +pi/2 or -pi/2 before the original terminal time, stop at that first hitting time. At this angle u=+/-e_y, so \(w_K(u)=w_K(e_y)\leq1\), inherited from the incoming arm. Lemma 20 therefore puts K, and hence S, into the canonical outgoing arm at that time. If no such angle is hit, keep the original terminal angle; it lies strictly between these two values and has \(w_K(u(\omega))\leq1\) from the original terminal strip.

Every angle between 0 and omega was visited by the original continuous lifted angle before the chosen stopping time, by the intermediate value theorem. At each such angle its canonical placement depends only on K and the angle, not on which visit was selected, and contains S. Traverse these canonical placements in monotone angular order. Continuity follows from support continuity. Lemma 20 verifies the initial and final arms. For omega=0 this is a constant canonical placement containing S in both endpoint arms, with translations in the arms before and after it as necessary. The moving frame has fixed handedness, so changing its angle and translation induces proper motions of the body; no reflection is performed. QED.

**Important limitation.** The theorem does not show \(|\omega|=\pi/2\), nor that the two signs are the conventional signs used by Romik's candidate. It removes translations and backtracking while retaining the endpoint-angle sectors. Claiming an unrestricted quarter-turn reduction here would still be an error.

## 8.4 A canonical common-hull envelope

For the two endpoint angles omega_d supplied above, let I_d be the closed interval between 0 and omega_d, with the appropriate fixed-handedness frame. Define

\[
E_K=K\setminus\bigcup_{d\in\{-,+\}}\bigcup_{t\in I_d}Q_K(u_d(t),v_d(t)).
\tag{8.7}
\]

**Corollary 22 (same-hull connected saturation).** The original S is contained in E_K. The component C of E_K containing S is compact, connected, feasible for both canonical motions, and

\[
S\subseteq C\subseteq K,\qquad |C|\geq|S|,\qquad\operatorname{conv}(C)=K.
\tag{8.8}
\]

**Proof.** S avoids every canonical forbidden quadrant by Proposition 19. Their union is open, so E_K is compact. Every subset of E_K satisfies all canonical hallway inequalities: the outer inequalities hold throughout K and the inner disjunction holds by exclusion from the quadrants. Endpoint widths hold for all of K by Lemma 20. Now apply connected saturation (Proposition 2). Finally \(\operatorname{conv}(S)\subseteq\operatorname{conv}(C)\subseteq K=\operatorname{conv}(S)\). QED.

This replaces the per-witness box by the actual compact convex hull of the body and makes both corner paths functions of a single support function. The envelope E_K may still have additional components; only the component containing S is automatically a connected competitor with the same hull. K, the endpoint angles, and viability of the relevant component remain optimization variables.

## 8.5 An endpoint-angle exclusion that is actually justified

**Proposition 23 (two-strip bound).** For a canonical witness with endpoint \(|\omega|<\pi/2\),

\[
|S|\leq |K|\leq\frac{w_K(e_y)\,w_K(u(\omega))}{|\cos\omega|}
\leq\sec|\omega|.
\tag{8.9}
\]

**Proof.** K lies in its supporting strip normal to e_y and its supporting strip normal to u(omega). The linear map \(p\mapsto(p\cdot e_y,p\cdot u(\omega))\) has determinant of absolute value |cos(omega)|. The intersection of the two strips therefore has area equal to their width product divided by this determinant. Inclusion proves the bound. QED.

If a competitor has area strictly greater than the candidate value M, **each** of its reduced endpoint angles must satisfy

\[
|\omega_d|>\arccos(1/M).
\tag{8.10}
\]

At candidate area M the inequality is non-strict. These are useful exclusions, not a full-angle theorem. The singular quarter-turn case is deliberately excluded from the determinant calculation.

## 8.6 Updated research consequence

The broad two-independent-path first-variation problem can now be replaced, for global coverage, by a one-common-hull support problem with two angular intervals. This avoids treating two unrelated translation paths as independent global optimization variables. A quarter-turn contact calculation remains only one endpoint sector until the other sectors are controlled. The clipped-niche upper bound and its rigidity are still unproved.
