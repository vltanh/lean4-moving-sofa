# Gate 0 audit: original ambidextrous motions equal the sharp signed joint-fiber program

**Subsequent value theorem, October 10, 2026:** the
[Gate 2 closure](gate2-sharp-partial-turn-closure.md) now proves the sharp
signed value and uses this bridge for the original-motion upper bound.
The audit below records the independently completed bridge itself; its
historical value-status row does not describe the later closure.

**Status: GATE 0 PASS (self-contained pen-and-paper audit, October 9, 2026).** This note independently checks the *bridge*, not the conjectured upper value: every genuine compact connected ambidextrous sofa of area above \(\sqrt2\) contributes at most the exact signed two-angle value of its actual outer hull, and every auxiliary signed two-angle value is bounded above by the area of a **different genuine compact connected** ambidextrous sofa. The two directions give exact equality of **suprema** in the original unrestricted problem. The outgoing whole-body strips and upper/lower reflection signs are retained. The proof works for subunit-height, partial, nonmonotone, nonsymmetric motions and auxiliary hulls with empty fibers.

The audit corrects one subtle historical **notation misunderstanding**: [Note 9, equation (9.5)](09-separation-from-connectedness.md) correctly defines its \(N_\pm\) as **\(K\)-clipped** swept quadrants, so its connected-hull subtraction is **not false**. Subtracting **ambient untruncated** niches instead would be false, and a near-Romik, **unit-height**, actual high-area counterexample is proved in Section 6. This distinction explains why [OT1](one-turn-reduction.md) carries the positive clipping term \(G\). The newer signed objective in [OS1](original-motion-signed-convex-domain.md) retains precisely the right max/min operation and is valid for auxiliary hulls even when their signed fibers are negative.

**NOT PROVED:** The sharp inequality \(\mathscr V(K,\alpha,\gamma)\le M\) for all the parameters. This audit changes the status of [SHARP-OPTIMALITY-EXECUTION-PLAN.md](SHARP-OPTIMALITY-EXECUTION-PLAN.md) **Gate 0 only**. It is not an improvement over the known unrestricted upper bound, not a proof that partial turns complete, and not a candidate-uniqueness theorem. It is self-reviewed and needs external independent mathematical scrutiny.

## 1. Canonical support geometry, with no unmentioned change to the body

Put the common incoming strip at \(0\le y\le1\). For an orthonormal pair of hallway normals \(u,v\), let
\[
H(u,v;a,b)=
\{p:p\cdot u\le a+1,\ p\cdot v\le b+1,\
       (p\cdot u\ge a\;\text{or}\;p\cdot v\ge b)\}.
\tag{GA.1}
\]
Its **incoming straight arm** is \(b\le p\cdot v\le b+1,\ p\cdot u\le a+1\), and its **outgoing straight arm** is \(a\le p\cdot u\le a+1,\ p\cdot v\le b+1\). The open forbidden corner has both inner inequalities strict.

For compact \(S\) and \(K=\operatorname{conv}S\), every placement containing S obeys
\(a\ge h_K(u)-1,\ b\ge h_K(v)-1\).
Lower both offsets to these exact support values. The new outer inequalities hold automatically on K, and each of the two inner alternatives has a **weaker threshold**. Thus
\[
S\subset H(u,v;h_K(u)-1,h_K(v)-1).
\tag{GA.2}
\]
This supports an *actual continuous placement path* over any continuous interval of frame angles, because \(h_K\) and the frame normals are continuous. One is not claiming that all of K survives the hallway.

For a support normal n, write \(w_K(n)=h_K(n)+h_K(-n)\). If \(w_K(v)\le1\), all of K fits the **incoming** straight arm of the canonical placement; if \(w_K(u)\le1\), all of K fits the **outgoing** straight arm. Indeed its minimum v-projection is \(-h_K(-v)\ge h_K(v)-1\), and similarly for u.

## 2. Original arbitrary motions force both correctly handed partial intervals

Let S have actual incoming vertical span \(H\in(0,1]\). Assume its area is **greater than \(\sqrt2\)**; this is the only regime needed to prove a candidate \(M>\sqrt2\) optimal. Consider the genuine **lower** physical passage. Its lifted body-relative hallway rotation \(\theta(s)\) begins at zero and ends at some \(\omega\). At the end S is contained in an **actual outgoing unit strip** normal to \(u_\omega=(\cos\omega,\sin\omega)\), while at the start it is in the horizontal incoming strip of width H. The determinant of these two strip normals has absolute value \(|\cos\omega|\); consequently, whenever it is nonzero,
\[
|S|\le H/|\cos\omega|.
\tag{GA.3}
\]
As \(|S|>\sqrt2\ge\sqrt2 H\), its endpoint cannot have \(|\cos\omega|\ge1/\sqrt2\).

At a *wrong-handed* \(-\pi/4\) lower frame, the two frame normals are
\((1,-1)/\sqrt2,(1,1)/\sqrt2\), both with positive horizontal component. For an arbitrary placement, a horizontal section of their L-hallway is **exactly a single interval of length \(\sqrt2\)**: in the (unnormalized) x-coordinate the outer right wall is the minimum of two affine expressions, and the union of the two inner alternatives is the same minimum minus \(\sqrt2\). Its intersection with the incoming horizontal H-strip has area at most \(\sqrt2 H\). Thus S cannot visit this orientation.

Now use continuity of the lifted angle: if the lower motion failed to visit the correct-handed \(+\pi/4\), its endpoint either remained in \((-\pi/4,+\pi/4)\), contradicting GA.3, or its lift crossed \(-\pi/4\), contradicting the preceding horizontal-section bound. Hence \(+\pi/4\) is visited. If the lift ever visits \(+\pi/2\), restrict to the first such visit and take \(\alpha=\pi/2\); the terminal outgoing width is then the original incoming height \(H\le1\). Otherwise the actual terminal lift lies in \((\pi/4,\pi/2)\): take it as \(\alpha\), with the original outgoing unit-strip condition. All angles in \([0,\alpha]\) were visited by the actual motion.

Reflect the **geometric constraints**, not the sofa itself, across \(y=1/2\) to repeat this proof for the independent physical upper-handed passage. It supplies a second magnitude \(\gamma\in[\pi/4,\pi/2]\), whose proper downward-reflected normals are again \(u_t,v_t\). The two paths may translate differently and have unrelated angle histories. Apply GA.2 to each visited frame to replace them by continuous support-tightened monotone angular witnesses of S; no new orientation is asserted feasible.

This rederives the only near-optimum motion coverage needed from [GH](midpoint-bound-general-motions.md), [Note 8](08-common-hull-tightening.md) and [Note 10](10-wrong-angle-exclusion.md) without assuming complete quarter-turns.

## 3. The exact two partial **whole-body strip** thresholds and ordinary fibers

For *arbitrary* nonempty compact convex \(K\subseteq\mathbb R\times[0,1]\), let \(I=[l,r]\) be its horizontal projection and denote its **actual** upper/lower convex hull fiber endpoints by \(A_K(x)\), \(B_K(x)\). Define the downward upper cap with roof \(A_U(x)=A_K(x)\), and the downward cap of the vertically reflected lower hull with roof
\[
A_V(x)=1-B_K(x).
\]
Thus
\[
d_U(x)=1-A_K(x),\qquad d_V(x)=B_K(x),
\]
and both deficits are nonnegative even when the actual vertical span is *strictly below* one.

For \(0<t<L=\pi/2\), \(c=\cos t>0,s=\sin t>0\), the **lower** canonical forbidden quadrant gives
\[
y<
\min\left\{
\frac{h_K(u_t)-1-xc}{s},\
\frac{h_K(v_t)-1+xs}{c}
\right\}.
\tag{GA.4}
\]
Define its positive all-visited-angle roof \(n_{K;\alpha}(x)\) as the maximum of zero and the supremum of GA.4 over \(0<t<\alpha\). This is the **whole moving sharp inner corner AND both attached rays**, not merely a corner shadow or a finite contact sample.

The *actual outgoing straight arm* at \(\alpha\) places **the entire body** into the unit strip with normal \(u_\alpha\). Since K's outer support inequality is automatic, the additional lower boundary is
\[
\boxed{
e_{K;\alpha}(x)
=\frac{h_K(u_\alpha)-1-x\cos\alpha}{\sin\alpha}.
}\tag{GA.5}
\]
For the reflected upper passage, take \(\rho(x,y)=(x,1-y)\). Its positive lower-type niche and outgoing strip roofs are \(n_{\rho K;\gamma}\) and \(e_{\rho K;\gamma}\). Reflecting their coordinates **back** gives the upper boundary \(y\le1-\max\{n_{\rho K;\gamma},e_{\rho K;\gamma}\}\); the upper convex hull roof remains \(A_K\).

The actual canonical envelope over I therefore has **closed interval-or-empty** sections
\[
E_{\alpha,\gamma}(K)_x
=\left[
\max\{d_V,n_{K;\alpha},e_{K;\alpha}\},\
1-\max\{d_U,n_{\rho K;\gamma},e_{\rho K;\gamma}\}
\right]
\]
**only when** the left endpoint is no larger than the right; otherwise the section is empty. Put
\[
\boxed{
\ell_{K;\alpha,\gamma}(x)=
1-\max\{d_V,n_{K;\alpha},e_{K;\alpha}\}
-\max\{d_U,n_{\rho K;\gamma},e_{\rho K;\gamma}\}.
}\tag{GA.6}
\]
Then, with Fubini and the true positive-part convention,
\[
\boxed{
\mathscr V(K,\alpha,\gamma)=\int_I\ell\,dx,\qquad
|E_{\alpha,\gamma}(K)|=\int_I(\ell)_+\,dx
=\mathscr V+\int_I(-\ell)_+\,dx.
}\tag{GA.7}
\]
At \(\alpha=L\) the outgoing barrier is \(h_K(e_y)-1\le0\) and is redundant because \(d_V=B_K\ge0\). Its upper analogue is likewise redundant. At a genuine **partial** endpoint, GA.5 generally is **not** redundant and must not be omitted.

For an **actual compact connected feasible S** with \(K=\operatorname{conv}S\), \(S\subseteq E_{\alpha,\gamma}(K)\) by GA.2, and \(\operatorname{proj}_x S=I\) because continuous projection of connected S is the entire interval between its extreme abscissae. Thus **every** E fiber is nonempty and its \(\ell(x)\ge0\) *at every x*, so
\[
\boxed{|S|\le |E_{\alpha,\gamma}(K)|=\mathscr V(K,\alpha,\gamma).}
\tag{GA.8}
\]
This explicitly **does not** apply the unqualified signed identity to a disconnected auxiliary envelope.

### An exact negative-fiber sanity check

Take \(K=[-1,1]\times[0,1]\) and both **complete** turns. At \(t=\pi/4\), \(x=0\), both lower inner-wall heights equal \(2-\sqrt2>1/2\); the reflected upper roof is the same. Therefore
\[
\ell_{K;L,L}(0)\le1-2(2-\sqrt2)=2\sqrt2-3<0.
\]
Its central fiber is empty even though the two side regions of E are nonempty. An expression integrating \(\ell\) as if it were ordinary area would be false. GA.7 gives exactly the required correction.

### An exact outgoing-strip sanity check

The rational partial-turn triangle in [IC1](exact-in-place-completion-obstruction.md) has vertices
\[
(0,0),\quad(1/10,1),\quad(-1,20/99),
\]
and lower terminal normal \(u_\alpha=(20/101,99/101)\) at
\(\alpha=L-2\arctan(1/10)\). The support in that normal equals one, attained at \((1/10,1)\); the minimum projection is zero, at the other two vertices. Formula GA.5 therefore gives **exactly**
\[
e_{K;\alpha}(x)=-20x/99.
\]
The third vertex \((-1,20/99)\) satisfies \(y=e_{K;\alpha}(-1)\) with equality: this is a genuinely binding **whole-body terminal arm**. That triangle has the prescribed partial lower/full upper motions yet fails a late orientation; no in-place zero-loss completion is being smuggled into GA.8.

## 4. The independent width-five box calculation

Suppose \(|S|>\sqrt2\), so the genuine **lower** \(\pi/4\) frame was visited by Section 2. Let its original horizontal projection be \([l,r]\), width \(W\), and vertical span H. Take actual retained extreme points \(P=(l,y_l),Q=(r,y_r)\). For every \(p=(x,y)\in S\),
\[
\begin{aligned}
h_K(u_{\pi/4})-p\cdot u_{\pi/4}
&\ge(r-x-H)/\sqrt2,\\
h_K(v_{\pi/4})-p\cdot v_{\pi/4}
&\ge(x-l-H)/\sqrt2.
\end{aligned}
\tag{GA.9}
\]
One depth must be at most one, hence
\[
x\ge r-(H+\sqrt2)\quad\text{or}\quad
x\le l+(H+\sqrt2).
\]
The horizontal projection of connected S is **all** \([l,r]\), so there cannot be a gap between those two allowed intervals. Consequently
\[
\boxed{W\le2(H+\sqrt2)\le2+2\sqrt2<5.}
\tag{GA.10}
\]
Move the horizontal projection midpoint to zero, and the actual lowest ordinate to zero: the *actual hull* of every potential above-\(\sqrt2\) original competitor is in
\[
\boxed{B=[-5/2,5/2]\times[0,1].}\tag{GA.11}
\]
This does **not** assert a width limit of five for every *auxiliary* convex K in the enlarged domain by a fake feasibility argument: the auxiliary K is simply **required** to lie in that fixed box.

## 5. Connectedification of **arbitrary auxiliary envelopes**, preserving area and both partial terminal strips

Let \(Q=E_{\alpha,\gamma}(K)\) be nonempty for an arbitrary auxiliary K in B. It is compact, has interval-or-empty vertical sections, satisfies both prescribed complete visited angular families, and **satisfies the two whole-body terminal strip inequalities GA.5**. It may be disconnected, or even have huge regions with \(\ell<0\).

Here is the precise contraction step, including its effects on supports. For a compact set Q of actual vertical span \(H_Q\le1\), and any nondecreasing 1-Lipschitz \(T:\mathbb R\to\mathbb R\), let \(F(x,y)=(T(x),y)\). For p,q in Q, n=(n_x,n_y), split according to the sign of \(n_x(q_x-p_x)\). In the nonnegative case the transformed horizontal dot-product difference does **not exceed** the old one. In the negative case the transformed horizontal difference is nonpositive and the vertical difference is bounded by \(H_Q|n_y|\). Maximizing over q yields
\[
\boxed{
h_{F(Q)}(n)-F(p)\cdot n
\le\max\{h_Q(n)-p\cdot n,\ H_Q|n_y|\}.
}\tag{GA.12}
\]
Thus **every inner-wall depth no larger than one remains safe**, regardless of which wall supplied that safety. An entire unit strip is preserved as well, because its width is the maximum support depth across all p. The result applies simultaneously to all four-handedness frame normals and both terminal normal directions.

Put \(D=\operatorname{proj}_xQ\), a compact subset of \([l,r]\), and choose
\[
T(x)=\int_l^x\mathbf1_D(z)\,dz.
\tag{GA.13}
\]
It collapses precisely the open complementary gaps of D and sends D onto the **entire interval** \([0,|D|]\). For every finite collection of gaps, the corresponding partial collapse acts as translations on the occupied x-bands, preserves area exactly, and is 1-Lipschitz. The remaining total gap length tends to zero, so these images converge in Hausdorff distance to \(F(Q)\). Their areas stay \(|Q|\). The area upper-semicontinuity of compact sets gives \(|F(Q)|\ge|Q|\); horizontal-section 1-Lipschitz nonexpansion gives \(|F(Q)|\le|Q|\). Therefore
\[
\boxed{|F(Q)|=|Q|.}\tag{GA.14}
\]
This does **not** assert general continuity of area under Hausdorff convergence.

Fill each vertical fiber of F(Q) to its interval hull. All prescribed canonical hallways have interval intersections with each fixed vertical line: for a lower conventional frame both inner alternatives are **upward** rays, and for the upper frame their reflection makes them **downward** rays. Outer walls and terminal strips are additional half-lines in y. Filling thus stays in **every** previously feasible angular placement and terminal strip. The support does not change because
\(F(Q)\subseteq Q^\sharp\subseteq\operatorname{conv}F(Q)\).
The resulting compact body \(Q^\sharp\) is connected since its projection is an interval and its fibers are intervals.

Finally, vertical filling adds area only at x-values having **more than one preimage under T**; each such value corresponds to a nontrivial interval of constancy of monotone T. Those intervals are countable (each contains a different rational). For all remaining abscissae, F(Q) already had an interval fiber. Hence
\[
\boxed{|Q^\sharp|=|Q|,\qquad Q^\sharp
\text{ is a connected compact body preserving both prescribed angular intervals and both outgoing widths}.}\tag{GA.15}
\]
Its angular support-tightened translations are continuous. The initial and terminal straight motions append since both endpoint strips are genuine *whole-body* strips: translate far along the outgoing arm at fixed terminal orientation, and correspondingly far inside the incoming arm at zero angle. Both incoming paths can be connected to **one common starting pose** while the body is well upstream in the common unit strip; transverse readjustment is permitted there when the actual height is below one.

This proof allows \(Q^\sharp\) to have a **different convex hull, horizontal width and height** from the auxiliary K. It proves an *area-preserving change of feasible shape*, not an invalid claim that the original disconnected auxiliary envelope was already a sofa.

## 6. Why the **ambient-minus-ambient niche** identity would be false even at high competitive area

The [Note 9](09-separation-from-connectedness.md) identity \(|E|=|K|-|N_-|-|N_+|\) is **correct**: there its \(N_\pm\) are **defined as \(K\cap W_\pm\)**. The following example shows precisely why no proof may erase that K-intersection or, equivalently, the clipping credit of [OT1](one-turn-reduction.md). The example uses **actual high-area full-turn sofas with unit vertical span**, not merely an auxiliary incompatible cap pair.

Use the original horizontally and vertically symmetric Romik feasible sofa \(\Sigma_*\) of area M, with hull \(K_*\), horizontal projection \(I=[-m,m]\), and common top/bottom hull face \([-b,b]\) at \(y=1,0\), with \(b=m/2\). The original full positive one-turn reference niche has the **exact terminal circular tail**
\[
\boxed{n_*(b-z)=\frac12-\sqrt{\frac14-z^2}>0
\qquad(0<z<\tfrac12\sin\beta),}
\tag{GA.16}
\]
by [TC.1](tail-paired-cut-deficit.md). The full reference sofa has vertical interval fibers all containing \(y=1/2\), and its lower outer flanks (outside [-b,b]), both bottom face endpoints \((\pm b,0)\), and both horizontal extreme tips \((\pm m,1/2)\) survive the entire reference motion.

For \(0<\varepsilon\le1/1000\), define the **tilted top-only cut**
\[
\boxed{
S_\varepsilon=\Sigma_*\cap
\{(x,y):y\le1-\varepsilon(x+b)\}.
}\tag{GA.17}
\]
The cutting line is at or above \(1/2\) on all of I (use \(m<117/100\)). Therefore every original interval fiber keeps its midpoint and becomes another nonempty interval fiber. The whole x-projection is retained; \(S_\varepsilon\) is **compact connected** and, being a subset of an already feasible body, makes **both full conventional quarter turns without changing either physical motion**.

The point \((-b,1)\) survives and is the only topmost point: for \(x>-b\) the tilted line is below one, whereas for \(x<-b\) the reference outer roof is strictly below one. The bottom hull face endpoints remain, as do the entire lower exterior flanks, since they lie below \(1/2\) and are outside the positive reference niche. Thus the actual hull \(K_\varepsilon=\operatorname{conv}S_\varepsilon\) has **exact unit vertical span** and **the same lower convex boundary** as \(K_*\). Consequently its reflected lower downward cap is **exactly** the original reference cap \(U_*\), and its reflected upper-turn positive complete niche is
\[
\boxed{n_{\rho K_\varepsilon}(x)=n_*(x).}\tag{GA.18}
\]

On the original central horizontal face \([-b,b]\), the new actual upper roof satisfies the tilted halfplane bound
\[
A_{K_\varepsilon}(x)\le1-\varepsilon(x+b),
\quad\text{so}\quad
d_U(x)=1-A_{K_\varepsilon}(x)\ge\varepsilon(x+b).
\tag{GA.19}
\]
For every \(x=b-z\) with \(0<z<\min\{b,\tfrac12\sin\beta\}\), both \(n_{\rho K_\varepsilon}(x)>0\) by GA.16 and \(d_U(x)\ge\varepsilon(2b-z)>0\). Hence the **genuine positive clipping credit** in the exact full-turn signed two-cap identity obeys
\[
\boxed{
G(K_\varepsilon)\ge
\int_{b-\delta}^{b}
\min\left\{
\tfrac12-\sqrt{\tfrac14-(b-x)^2},
\ \varepsilon(x+b)
\right\}dx>0
}
\tag{GA.20}
\]
for any fixed sufficiently small \(0<\delta<\min\{b,\frac12\sin\beta\}\).

The shaved area is at most \(2m\varepsilon(m+b)\), so
\[
|S_\varepsilon|\ge M-2m\varepsilon(m+b)>\sqrt2
\]
for \(\varepsilon\le1/1000\), using \(M>8/5\), \(m<117/100\) and the displayed rational inequality. It also tends to M from below as \(\varepsilon\downarrow0\).

Thus for genuine unit-height, connected, full-turn sofas of area arbitrarily close to M, a **strictly positive part of the ambient upper swept niche lies outside the new convex hull**. The correct formula is the K-clipped Note 9 subtraction, equivalently the positive \(G\) from OT1—not bare subtraction of the two ambient niches. This example illustrates why the seemingly small distinction is **logically essential** in a sharp theorem.

## 7. Final equivalence: what Gate 0 actually establishes

Let \(V_{\rm amb}\) be the true unrestricted optimal area and
\[
\mathcal K_B=\{K:\varnothing\ne K\subseteq B,\ K\text{ compact convex}\}.
\]
For any actual sofa of area \(>\sqrt2\), Sections 1–4 give one K in \(\mathcal K_B\) and independent \(\alpha,\gamma\in[\pi/4,\pi/2]\) with
\(
|S|\le\mathscr V(K,\alpha,\gamma).
\)
Since Romik proves \(V_{\rm amb}\ge M>\sqrt2\), taking a maximizing sequence gives
\[
V_{\rm amb}\le
\sup_{K\in\mathcal K_B,\ \alpha,\gamma\in[\pi/4,\pi/2]}
\mathscr V(K,\alpha,\gamma).
\]

Conversely, for any **arbitrary auxiliary** K and angles in that same domain, GA.7 bounds its signed objective by the **ordinary** area of \(E_{\alpha,\gamma}(K)\). If E is nonempty, Section 5 produces an actual compact connected ambidextrous sofa with the **same** ordinary area. If E is empty, the signed value is nonpositive, already below M. Hence
\[
\boxed{
V_{\rm amb}
=\sup_{\substack{K\in\mathcal K_B\\
\pi/4\le\alpha,\gamma\le\pi/2}}
\mathscr V(K,\alpha,\gamma)
=\sup_{\substack{K,\alpha,\gamma}}
\left[W-\mathcal L(K,\alpha,\gamma)\right].
}\tag{GA.21}
\]

**The exact acceptance target is therefore**
\[
\boxed{
\mathcal L(K,\alpha,\gamma)\ge W-M
\quad\text{for **all** parameters of GA.21}.
}\tag{GA.22 — STILL OPEN}
\]
It would prove sharp unrestricted optimality (the candidate gives equality). Its geometric proof has **not** been supplied. The earlier conditional one-turn value theorem, Romik directional derivative, local no-gain theorems and incorrect universal concavity proposals cannot be substituted for GA.22.

### Audit checklist and scope

| Gate 0 dependency | Audit conclusion |
|---|---|
| Physical wrong-way/partial-angle reduction | PASS: GA.3 plus exact wrong-diagonal horizontal section and intermediate-value theorem |
| Actual outgoing whole-body strip | PASS: GA.5 from full strip, not just terminal corner |
| Correct-handed upper/lower sign and cap normalization | PASS: reflection and both explicit max/min barriers, including height below one |
| Connected S gives nonempty signed fibers | PASS: GA.8, by interval projection |
| Arbitrary auxiliary envelope may have empty fibers | PASS: 2x1 rectangle, GA.7 and negative central signed fiber |
| Horizontal-gap compression and interval filling | PASS: GA.12–GA.15, including angular families and terminal widths |
| Horizontal width/compact box | PASS: GA.9–GA.11, without importing stronger width bounds |
| Correct interpretation of older two-niche subtraction | PASS after clarification: Note 9 clips N to K; ambient-only would fail by GA.20 |
| Candidate calibration | PASS conditional on the documented exact feasible Romik construction; not a proof of maximality |
| **Sharp global area inequality** | **NOT PROVED — Gate 1/2 remain blocked** |

**No CI, Lean/Lake formalization, numerical search, or proof of Romik optimality is claimed.** All results in this note are hand arguments and remain subject to external scrutiny.
