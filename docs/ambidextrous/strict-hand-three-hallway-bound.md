# A strictly improved universal ambidextrous area bound by hand

**Theorem.** Every compact connected ambidextrous sofa admitting continuous motions in both handed directions from one common incoming position satisfies
\[
\boxed{|S|\le 2\sqrt2-1-\frac1{10^9}.}\tag{TH.1}
\]
This is a **strict, explicit improvement on the elementary two-\(45^\circ\)-hallway bound, without computation**. It is much weaker than O'Keefe's independently computer-certified global bound \(353/200=1.765\), and **does not prove the sharp Romik area \(M\)**. It uses the geometric ideas behind our midpoint MH, support-tightening CP and exact area-stability certificates BH: make the two-\(45^\circ\) equality configuration rigid, then use a third rational hallway to contradict it quantitatively. No finite-angle optimizer, calibration, reference-tail hypotheses, sample accuracy, or Lean is needed. Labels TH are local.

The corridor and "proper hallway angle" conventions are those of MH and GH, themselves following the external paper's definitions. The original midpoint upper bound \(2\sqrt2-1\) is credited in that source to earlier hand upper-bound work; this note gives a self-contained quantitative extra-angle step.

## 1. Midpoint rectangle and diagonal-band geometry

A body satisfying a proper \(45^\circ\) lower hallway and a proper \(45^\circ\) upper hallway, both from one incoming horizontal strip of height at most one, is contained after an orthogonal coordinate change and translation in
\[
F(P,Q,z)=\left\{(u,v)\in[0,P]\times[0,Q]:
\begin{array}{l}
u\ge P-1\ \text{or}\ v\ge Q-1,\\
u\le1\ \text{or}\ v\le1,\\
z\le u+v\le z+d
\end{array}\right\},\quad d=\sqrt2.
\tag{TH.2}
\]
If the actual incoming height is \(<1\), allowing the full band width \(d\) only enlarges the set. Thus no unit-span normalization or rescaling is assumed. The transforms back to the physical sofa plane, up to translation, are
\[
x=(u-v)/\sqrt2,\qquad y=(u+v)/\sqrt2.
\tag{TH.3}
\]

Put
\[
k=1-d/2,\quad H_1=1-k^2=d-\tfrac12,\quad
B=2H_1=2\sqrt2-1,\quad\varepsilon=10^{-9}.
\tag{TH.4}
\]
A unit square \([0,1]^2\) intersected with a diagonal band of sum-coordinate width \(d\) has area at most \(H_1\), attained uniquely by the centered band. More quantitatively, if the band center is displaced by \(h\) from the square's sum-coordinate center, its area \(J(h)\) satisfies
\[
H_1-J(h)=h^2\quad (|h|\le k),\qquad
H_1-J(h)\ge k^2\quad(|h|\ge k).
\tag{TH.5}
\]
**Proof.** The sum \(u+v\) has symmetric triangular density. When \(|h|\le k\), the omitted lower/upper triangles have legs \(k+h,k-h\), so their combined area is \(k^2+h^2\). Beyond this range the captured area decreases monotonically with \(|h|\), hence the second inequality. QED.

We shall prove the quantitative rigidity implication
\[
\boxed{
\begin{gathered}
S\subset F(P,Q,z),\quad S\text{ connected},\quad |S|>B-\varepsilon\\
\Longrightarrow
|P-2|<1/50,\quad |Q-2|<1/50,\quad
|z+d/2-2|<1/100 .
\end{gathered}}
\tag{TH.6}
\]

## 2. A near-maximal connected survivor forces near-square placements

If \(\min(P,Q)\le1\), integrating the diagonal band across the thinner of the two coordinates gives
\[
|F|\le d<B-\varepsilon,
\]
so this case cannot occur.

If \(P,Q\ge2\), the two inner/outer disjunctions in (TH.2) restrict \(F\) to the two unit corner squares
\[
A=[P-1,P]\times[0,1],\qquad
D=[0,1]\times[Q-1,Q].
\tag{TH.7}
\]
If either \(P>2\) or \(Q>2\), these two squares are disjoint closed sets. A connected \(S\) must lie entirely in one; by (TH.5), its area is at most \(H_1<B-\varepsilon\). Therefore in the case \(P,Q\ge2\) we must have \(P=Q=2\). Their two unit squares each capture at most \(H_1\), and if \(|S|>2H_1-\varepsilon\) both capture at least \(H_1-\varepsilon\). By (TH.5),
\[
|z+d/2-2|\le\sqrt\varepsilon<1/100.
\]
This proves (TH.6) in that case.

It remains to consider \(1<\min(P,Q)<2\). By symmetry interchange u and v if necessary so \(1<Q\le P\), and write
\[
q=Q-1\in(0,1),\qquad t=1-q=2-Q.
\]
Partition the possible surviving points into the three horizontal layers:
\[
\begin{array}{c|c}
0\le v\le q&[P-1,P]\times[0,q]\\
q\le v\le1&[0,P]\times[q,1]\\
1\le v\le Q&[0,1]\times[1,Q].
\end{array}
\tag{TH.8}
\]
At fixed v, the diagonal band has u-length at most \(d\), so the middle layer contributes at most \(dt\). The other two layers are subsets of unit-by-q rectangles. Their individual band area is at most
\[
H_d(q)=q-\tfrac14(1+q-d)_+^2.
\]
Consequently
\[
|S|\le |F|\le f_d(q):=d(1-q)+2q-\tfrac12(1+q-d)_+^2.
\tag{TH.9}
\]
Elementary differentiation gives \(f_d'(q)=2-d>0\) for \(q\le d-1\) and \(f_d'(q)=1-q>0\) for \(q\ge d-1\), with \(f_d(1)=B\). If \(q\le d-1\), then
\[
B-f_d(q)\ge\tfrac12(2-d)^2>\tfrac18>\varepsilon,
\]
using \(d<3/2\). Thus \(q>d-1\), where integration of \(f_d'=1-q\) yields
\[
B-f_d(q)=\frac{(1-q)^2}{2}=\frac{t^2}{2}.
\]
The hypothesis \(|S|>B-\varepsilon\) therefore implies
\[
\boxed{0<t<\sqrt{2\varepsilon}<1/20000.}\tag{TH.10}
\]

Now enlarge the first and last layers in (TH.8) to the **full unit** corner squares \(A,D\) of (TH.7), still intersected with the band. Their captured areas \(J_A,J_D\) are each at most \(H_1\), and the middle layer gives
\[
|F|\le J_A+J_D+dt.
\]
It follows from \(|S|>2H_1-\varepsilon\) that each of \(J_A,J_D\) is strictly above
\[
H_1-\alpha,\qquad \alpha=\varepsilon+dt.
\]
Since \(d<3/2\) and (TH.10),
\[
\alpha<10^{-9}+\frac{3}{40000}<\frac1{110^2}<\frac1{16}<k^2.
\tag{TH.11}
\]
The square \(A\) has sum-coordinate center \(P\), and \(D\) has center \(Q\). Thus the quantitative square estimate (TH.5) forces
\[
|z+d/2-P|<1/110,\qquad
|z+d/2-Q|<1/110.
\tag{TH.12}
\]
In particular
\[
|P-Q|<2/110.
\]
Since \(\min(P,Q)=Q=2-t\),
\[
|Q-2|=t<1/20000,\quad
|P-2|<\frac1{20000}+\frac2{110}<\frac1{50},
\]
and
\[
|z+d/2-2|<\frac1{110}+\frac1{20000}<\frac1{100}.
\]
The case \(P<Q\) is identical after swapping u and v. This completes the **entirely analytic proof of (TH.6)**.

## 3. Three positive-area witness rectangles force a forbidden third hallway

Under the proximity bounds (TH.6), introduce three *closed* rational rectangles in the \((u,v)\) plane:
\[
\begin{aligned}
R_A&=[P-\tfrac3{200},P-\tfrac1{200}]\times[\tfrac1{200},\tfrac3{200}],\\
R_D&=[\tfrac1{200},\tfrac3{200}]\times[Q-\tfrac3{200},Q-\tfrac1{200}],\\
R_p&=[\tfrac{103}{100},\tfrac{104}{100}]
\times[\tfrac{76}{100},\tfrac{77}{100}].
\end{aligned}
\tag{TH.13}
\]
Each has area exactly \(10^{-4}\). We claim all three lie *entirely* inside the midpoint envelope \(F(P,Q,z)\).

- \(R_A\subset A\) and \(R_D\subset D\), and their coordinate sums lie within \(1/100\) of \(P\) and \(Q\) respectively. Since those are within \(1/50\) of 2, and the incoming diagonal band is centered within \(1/100\) of 2, these points lie strictly inside the band of half-width \(d/2>1/2\).
- On \(R_p\), \(u\ge1.03>P-1\), since \(P<2.02\); \(u\le1.04<P\), since \(P>1.98\); and \(0<v<1\). The sum \(u+v\) belongs to \([1.79,1.81]\), less than \(0.22\) from the band center \(z+d/2\in(1.99,2.01)\), so \(R_p\subset A\cap F\).

Since \(S\subset F\), \(|F|\le B\), and \(|S|>B-\varepsilon\),
\[
|F\setminus S|\le B-|S|<10^{-9}<10^{-4}=|R_A|=|R_D|=|R_p|.
\]
Thus **each** of the three rectangles contains at least one point of S. Choose
\[
p_A=(u_A,v_A)\in S\cap R_A,\quad
p_D=(u_D,v_D)\in S\cap R_D,\quad
p=(u_p,v_p)\in S\cap R_p.
\tag{TH.14}
\]

Now add just **one proper lower-turn hallway** at
\[
\nu=(4/5,3/5),\qquad \nu^\perp=(-3/5,4/5).
\]
Up to irrelevant additive translation constants, their coordinate functionals in the \((u,v)\) plane are
\[
\nu\cdot(x,y)=\frac{7u-v}{5\sqrt2},\qquad
\nu^\perp\cdot(x,y)=\frac{u+7v}{5\sqrt2}.
\tag{TH.15}
\]
The rational rectangle bounds and \(|P-2|,|Q-2|<1/50\) give
\[
\begin{aligned}
\nu\cdot(p_A-p)
&\ge \frac{7(1.965-1.04)+(0.76-0.015)}{5\sqrt2}
=\frac{361}{250\sqrt2}>1,\\
\nu^\perp\cdot(p_D-p)
&\ge\frac{(0.005-1.04)+7(1.965-0.77)}{5\sqrt2}
=\frac{733}{500\sqrt2}>1.
\end{aligned}
\tag{TH.16}
\]
Both strict inequalities are hand-checkable by squaring:
\(361^2=130321>125000=2(250)^2\) and \(733^2=537289>500000=2(500)^2\).

Since \(p_A,p_D\in S\), its actual support depths at p satisfy
\[
h_S(\nu)-p\cdot\nu>1,\qquad
h_S(\nu^\perp)-p\cdot\nu^\perp>1.
\tag{TH.17}
\]
But **any** placement of an \(L\)-hallway with those frame normals that contains the whole of S requires, at each point, at least one of these two **actual support depths** to be at most one. Indeed the two outer-wall offsets must dominate the corresponding actual supports; their inner-wall disjunction then implies the support-depth alternative. TH.17 violates both.

**Theorem TH1 (three-hallway explicit hand bound).** No compact connected S in one incoming unit strip can satisfy the two proper \(45^\circ\) opposite-handed hallways *and* the proper lower hallway with normals \((4/5,3/5),(-3/5,4/5)\) if
\[
|S|>2\sqrt2-1-10^{-9}.
\]
Every part of this proof is a finite hand inequality. Connectivity is used only to rule out the completely separated two-square case \(P,Q\ge2\) away from \(P=Q=2\).

## 4. From the three hallways to arbitrary ambidextrous motions

The already proved motion-angle lemma in [GH](midpoint-bound-general-motions.md), equivalently the *no sideways turn* and *turning the right way* lemmas in O'Keefe's paper, says that any ambidextrous sofa of area greater than \(\sqrt2\), moving by **arbitrary continuous** motions in the two directions from the same initial position, must visit the proper \(45^\circ\) hallway frame on each turn. The proof does not assume angular monotonicity: the wrong-way frame has area at most \(\sqrt2\), and the final perpendicular strip forces a right-way endpoint crossing.

Since
\[
2\sqrt2-1-10^{-9}>\sqrt2,
\]
a counterexample to (TH.1) would have the two proper \(45^\circ\) placements. Its lower-turn rotation path also crosses the intermediate proper angle \(\arcsin(3/5)\in(0,\pi/4)\) by continuity, furnishing the third hallway of Theorem TH1. That is impossible. Therefore the claimed universal hand bound (TH.1) follows, for **partial as well as complete turns** in the original common-starting-position definition.

For the full-turn-only problem, the three required orientations are immediately part of the full quarter turns and no motion-angle reduction is needed.

## 5. Interpretation and strict boundary

This theorem advances the elementary \(45^\circ\) upper estimate by a **strict explicit rational amount** without the massive external certificate. The argument illustrates how BH-style area stability and CP-style actual-support witnesses can be used in a **continuous hand exclusion of an entire near-equality region**, rather than proving isolated finite-box bounds or assuming a convenient cap shape.

It does **not** compete numerically with the published externally certified \(\mu_{\rm ambi}\le353/200=1.765\). In particular it supplies neither \(A_F\le M\), the unknown sharp clipping-versus-deficit budget, a sharp partial completion theorem, nor uniqueness. The improved gap \(10^{-9}\) is deliberately conservative: it keeps every step elementary and rational rather than optimizing constants. The statement is self-reviewed and requires independent mathematical review; no computation is a premise.
