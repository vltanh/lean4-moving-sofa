# Rational polyomino witnesses for a genuinely larger ambidextrous sofa

**Status (2026-10-08):** A universal *counterexample-completeness* theorem for the original two-handed moving-sofa problem. If any compact connected sofa beats the explicit Romik area, then another one beats it with a **finite union of rational grid squares**, two **piecewise-rational continuous rigid motions**, and a **finite, exact algebraic feasibility certificate**. This handles arbitrary partial rotations, reversals and backtracking; it does **not** assume both motions complete a conventional quarter turn, or refer to the two-cap clipping deficit.

This does **not** exhibit a larger sofa, prove sharp optimality or give a complexity bound on searching the resulting countable witnesses. The exact proof uses the rounding observation in [Note 33](33-rounding-and-perimeter.md) but strengthens that note's polygonal density to *rational motions and a proof-complete finite feasibility checker*. The separate canonical polygon angular-candidate reduction [CA-ANGLE](COUNTEREXAMPLE-SEARCH-CONTINUOUS-ANGLES-2026-10-08.md) also does not give this arbitrary-motion witness theorem.

## 1. The original physical hallways

Use the fixed physical unit corridors
\[
H_-=\{(X,Y):X\le1,\ Y\le1,\quad X\ge0\ \text{or}\ Y\ge0\},
\]
\[
H_+=\{(X,Y):X\le1,\ Y\ge0,\quad X\ge0\ \text{or}\ Y\le1\}.
\]
They have the same incoming straight arm \(X\le0,\ 0\le Y\le1\), and different outgoing arms \(0\le X\le1,\ Y\le0\) and \(0\le X\le1,\ Y\ge1\). Each motion is a continuous path in the proper rigid-motion group with its body wholly in its corresponding hallway, starting in the common incoming arm and finishing in the appropriate outgoing arm. No restriction on the intervening rotations is made. A common initial body pose can be obtained by translations in the shared straight arm, as in [Note 5](05-two-sided-variation.md). Start/end points can be chosen arbitrarily far along the respective arms by appending straight translations.

Let \(M=1+4Y_*^2+\arctan(Y_*)\), where \(Y_*>0\) solves \(4Y_*^3+3Y_*-1=0\).

**Theorem RP1 (rational two-motion completeness).** If a compact connected ambidextrous sofa \(S\) satisfies \(|S|>M\), then there exist:

1. A compact connected finite union \(P\) of closed **rational axis-aligned grid squares with disjoint interiors**, and \(|P|>M\);
2. Two continuous physical hallway motions of \(P\), one in each \(H_\pm\), with a common starting pose and the correct outgoing straight arms;
3. A finite subdivision of each path so that, on every subinterval \(s\in[0,1]\), its rotation and translation have the form
\[
\boxed{
R(s)=R_0\frac{1}{1+q^2s^2}
\begin{pmatrix}1-q^2s^2&-2qs\\2qs&1-q^2s^2\end{pmatrix},
\qquad a(s)=a_0+s(a_1-a_0),
}\tag{RP.1}
\]
where \(q\in\mathbb Q\), \(R_0\in SO(2,\mathbb Q)\), and \(a_0,a_1\in\mathbb Q^2\). The initial rotation is the identity and the *same* initial translation is used for both motions;
4. A rational margin \(\mu>0\) such that both outer hallway inequalities have margin at least \(\mu\) and at least one inner-wall alternative has margin at least \(\mu\) at **every** body point and every time. The starting and ending poses satisfy the corresponding straight-arm inequalities with positive margin.

In particular the witness is not just a sequence of finite-angle hallway snapshots: it contains an explicitly specified and continuously feasible pair of **entire motions**.

### Proof, step 1: uniformly robust rounding

Write each original motion as \(g_\pm(t)z=R_\pm(t)z+a_\pm(t)\). Choose rational \(0<\lambda<1\) sufficiently close to one that
\(\lambda^2|S|>M\), and put
\[
\epsilon=\frac{1-\lambda}{4},\qquad
c=\left(\frac{1-\lambda}{2},\frac{1-\lambda}{2}\right),\qquad
S_\lambda=\lambda S+\epsilon B_2,
\]
where \(B_2\) is the closed Euclidean unit disk. Use the new physical placements
\[
\widetilde g_\pm(t)z=R_\pm(t)z+\lambda a_\pm(t)+c.
\]
Because the disk is rotation invariant,
\[
\widetilde g_\pm(t)S_\lambda
=\lambda g_\pm(t)S+c+\epsilon B_2.
\]

Set \(m=(1-\lambda)/4\). For any \(p\in H_-\), every point \(p'=\lambda p+c+\epsilon b\), \(|b|\le1\), satisfies
\[
X'\le1-m,\quad Y'\le1-m,\qquad
X'\ge m\quad\text{or}\quad Y'\ge m.
\tag{RP.2}
\]
Indeed a coordinate originally at most one ends at most \(\lambda+(1-\lambda)/2+\epsilon=1-m\); a coordinate originally at least zero ends at least \((1-\lambda)/2-\epsilon=m\). For \(H_+\) the same computation yields
\[
X'\le1-m,\quad Y'\ge m,\qquad
X'\ge m\quad\text{or}\quad Y'\le1-m.
\tag{RP.3}
\]
These are **uniform** margins: no contact chart, angle monotonicity, or particular safe-wall selection is fixed. The rounded body is compact and connected, contains \(\lambda S\), and has area at least \(\lambda^2|S|>M\).

### Proof, step 2: rational connected grid covering

Take a rational square grid of side \(h>0\), and let \(P\) be the union of **all closed grid squares intersecting** the compact \(S_\lambda\). There are finitely many. Every square intersects \(S_\lambda\), so their union with the connected \(S_\lambda\) is connected; it contains \(S_\lambda\), hence
\[
|P|\ge |S_\lambda|\ge\lambda^2|S|>M.
\]
Every point in \(P\) is within \(\sqrt2 h\) of \(S_\lambda\). Choose \(h\) so small that \(\sqrt2h<m/4\). Under the original modified motions, all inequalities (RP.2)–(RP.3) continue to hold for \(P\) with at least \(3m/4\) margin, because rotations preserve distances. Each selected square has rational vertices, and their interiors are pairwise disjoint. The horizontal and vertical extrema are finite; no disconnected-component area is being credited to one sofa.

### Proof, step 3: rationalize *both entire trajectories*

Every continuous compact-time motion in \(SE(2)\) can be uniformly approximated by piecewise curves of the form RP.1. To see this constructively, choose sufficiently fine time knots so the true rotation changes by less than \(\pi/4\) and the true translation varies negligibly on every time subinterval. Approximate every knot's rotation by a rational point of the unit circle and its translation by a rational pair. Rational unit-circle points are dense by the half-angle map
\[
r\longmapsto\left(\frac{1-r^2}{1+r^2},\frac{2r}{1+r^2}\right);
\]
the rational point \((-1,0)\) also handles its exceptional chart. Choose adjacent approximating rotations with relative angle strictly between \(-\pi\) and \(\pi\), and let their relative sine and cosine be \(s_\Delta,c_\Delta\in\mathbb Q\). Then
\[
q=\frac{s_\Delta}{1+c_\Delta}\in\mathbb Q
\]
makes RP.1 connect the two knot rotations **exactly**, without a jump. Linear interpolation connects the rational translations. Making the knot mesh finer and errors smaller ensures a uniformly close approximation to the original continuous pose path, including arbitrarily nonmonotone winding.

Choose the initial rational knot **identically for both** normalized incoming motions, with rotation exactly \(I\). Approximate their far incoming and outgoing endpoint poses inside the same straight arms; their rationalized endpoint poses remain there with positive clearance. Finally, uniform continuity of rigid actions on the bounded set \(P\) makes all rationalized placements closer than \(m/4\) to the already \(3m/4\)-safe placements. A rational margin \(0<\mu<m/2\) can therefore be assigned to all of RP.2–RP.3 and to the straight-arm endpoints. This proves RP1. \(\square\)

Notice that RP1 does **not** require the area of polygonal outer approximants to converge at a prescribed rate: for a strict counterexample, the inclusion of \(\lambda S\) already secures the positive area excess. Polygonal density in the limiting-value sense is the earlier Note 33 result.

## 2. Exact finite verification is decidable

**Theorem RP2 (fully algebraic witness validation).** Given finite rational grid cells, rational pose knots with no adjacent 180-degree jump, the rational interpolation RP.1, and rational strict margin \(\mu>0\), each of the following is exactly decidable by finite rational-algebraic tests:

- Pairwise interior disjointness and connectedness of the finite union of cells;
- Its exact rational ordinary area (the sum of the nonoverlapping square areas);
- Common initial placement, initial identity orientation, and correct straight-arm terminal placements;
- **Every point of every square**, at **every real time** on **both entire motions**, belongs to the required hallway with the claimed margin.

For the last statement, \(R(s)p+a(s)\) has rational-function coordinates in \((s,p_x,p_y)\), with denominator \(1+q^2s^2>0\). The hallway complement is a Boolean combination of strict linear inequalities. Clearing that *positive* denominator gives a quantified Boolean combination of polynomial inequalities over rational coefficients. The decision procedure for real closed fields therefore decides its emptiness **exactly**. No finite angular sampling is used.

There is a more elementary proof-complete certification procedure for the **strictly robust** witnesses of RP1. Subdivide each compact rational space–time box \([0,1]\times C_i\) into rational subboxes. Evaluate rational interval enclosures for both transformed point coordinates. Accept a lower-hallway subbox if its enclosing ranges obey
\[
X_{\max}\le1-\mu,\quad Y_{\max}\le1-\mu,\quad
\left(X_{\min}\ge\mu\ \text{or}\ Y_{\min}\ge\mu\right),
\]
and analogously for the upper hallway using RP.3. On a box too large to satisfy one branch, subdivide it and retry. Such interval certificates are **sound** for arbitrary inputs. For the robust witnesses of RP1, uniform positive clearance and convergence of rational interval extensions on shrinking boxes guarantee that sufficiently fine rational subdivisions *do* terminate. A checker need not know the optimum subdivision ahead of time; it may increase its resource limit. This is a bona fide finite proof certificate for a continuous motion, rather than a numerical optimizer convergence criterion.

The small, standard-library implementation [check_rational_motion_witness.py](computer-assisted/check_rational_motion_witness.py) implements the strict interval version. Its self-test uses the square \([-1/10,1/10]^2\), with both routes starting at center \((-2,1/2)\), moving to \((1/2,1/2)\), rotating through the two opposite right angles by rational half-angle arcs, then leaving into the appropriate vertical arms. The entire motion is certified with rational margin \(1/4\). Its rational area is \(1/25\), **not** a larger-sofa counterexample. The negative control identifies an exact \(6/5>1\) outer-wall collision at the midpoint of a rotation of a unit square.

### A simpler full-canonical-turn specialization

For a proposed rational polyomino in the fixed incoming orientation, without explicit motion data, both full canonical turns can also be decided directly by **univariate polynomial inequalities of degree at most four**. This is an efficient special case, not a replacement for the arbitrary-motion theorem.

For \(z=\tan(t/2)\in(0,1)\), write
\[
c=\frac{1-z^2}{1+z^2},\qquad s=\frac{2z}{1+z^2}.
\]
On a sector where support vertices \(F,G\in\mathbb Q^2\) attain the two support maxima, put
\[
U(z)=F_x(1-z^2)+2zF_y,\qquad
V(z)=-2zG_x+(1-z^2)G_y.
\]
These are rational quadratic polynomials. For an axis-aligned square \([a,b]\times[y_0,y_1]\), lower-turn forbidden quadrants are downward closed, so **some point in the square is unsafe exactly when some point of its bottom edge is strictly unsafe**. Define
\[
E(z)=U(z)-(1+z^2)-2zy_0,\quad
R(z)=y_0(1-z^2)+(1+z^2)-V(z).
\]
The two inner walls forbid bottom abscissae in the open interval
\[
\left(\frac{R(z)}{2z},\ \frac{E(z)}{1-z^2}\right).
\]
It intersects the square's bottom edge precisely when all three strict polynomial inequalities hold:
\[
\boxed{
\begin{aligned}
 E(z)-a(1-z^2)&>0,\\
 R(z)-2zb&<0,\\
 (1-z^2)R(z)-2zE(z)&<0.
\end{aligned}}\tag{RP.4}
\]
The first two are quadratic and the third at most quartic. Support-vertex activation is specified by additional **quadratic** comparisons, and only finitely many vertices and squares occur. The closed endpoint frames are checked directly using incoming/outgoing strip widths. Real-root isolation and rational sign evaluations therefore produce a finite exact all-angle decision; alternatively apply univariate real quantifier elimination. The reflected body gives the other handedness. This specialization is not used as a substitute for general partial or nonmonotone motions in RP1.

## 3. A mathematically complete falsification search, with a strict stop rule

Let \(\mathcal W_{\mathbb Q}\) be the countable, effectively enumerable family of rational square unions with two rational piecewise rigid-motion paths and positive rational margins, satisfying the explicit endpoint and connectivity requirements.

**Corollary RP3.** The following are equivalent:

1. Some genuine compact connected ambidextrous sofa has ordinary area \(>M\).
2. Some witness in \(\mathcal W_{\mathbb Q}\) has **rational ordinary area** \(>M\) and passes exact full-path feasibility verification.

Hence the **failure** of Romik's sharp upper-bound conjecture is *recursively enumerable*: enumerate witnesses, validate their full continuous paths by exact rational box refinement (or real-algebraic decision), and compare their areas against rational upper enclosures of \(M\). If a larger sofa exists, this process eventually finds a finite rigorous certificate. If no larger sofa exists, **termination is not guaranteed**; this is not a decision procedure for the conjecture itself and not a sharp upper bound.

The candidate threshold must not be fixed at \(329/200\). That rational number is a convenient sufficient test but could miss an excess smaller than \(329/200-M\). A complete comparison uses rational upper bounds \(M_j\downarrow M\): isolate the positive root \(Y_*\in(0,1/3)\) of \(4Y^3+3Y-1\) by rational bisection, producing rational upper endpoints \(u_j\downarrow Y_*\), and use the even-index alternating arctangent truncation
\[
M_j=1+4u_j^2+\sum_{k=0}^{2j}\frac{(-1)^k u_j^{2k+1}}{2k+1}>M.
\]
These are rational and converge to \(M\), so any rational witness area strictly greater than \(M\) eventually exceeds one of them.

**Research interpretation.** RP1–RP3 are a different and globally valid *counterexample mechanism*, not a disguised version of the missing inequality \(G\le\Delta_U+\Delta_V\). They make rational polyominoes and **genuinely certified continuous motions** a complete falsification domain, including all arbitrary partial/backtracking rotations. They offer no shortcut to an upper proof and no claim that an arbitrary numerical optimizer can find a larger sofa. An effective future search should prioritize shape/motion families and use exact certificates only for candidates with a credible strict ordinary-area excess; exhaustive enumeration without a guiding structure is mathematically complete but computationally infeasible.
