# Arbitrary convex shavings in two fixed boundary layers cannot improve the reference

**Scope.** This gives a concrete geometric admission condition for TC3. It controls the entire full-turn saturation of a cut hull, which can add material outside the original reference body. It is not the trivial assertion that a subset of the reference has smaller area. The cuts are arbitrary within their stated layers and can act independently above and below. Labels RB are local.

Dependencies: the explicit reference geometry and the elementary paired-tail proof [TC](tail-paired-cut-deficit.md). No weighted-maximizer theorem, Gerver bound, computer certificate, curvature bound on competitors, or asymptotic expansion is used.

## 1. One explicit layer thickness

Use the centered reference of TC: hull K_*, downward cap U_*, horizontal extent [-m,m], and top/bottom faces [-m/2,m/2]. Set

$$\eta=2\arctan(1/10),\qquad
\cos\eta=99/101,\quad\sin\eta=20/101.$$

This eta is smaller than the reference beta. Indeed tan(eta)=20/99<2/7<Y=tan(beta), with both angles in (0,pi/2). Define

$$\boxed{\kappa=1/101,\qquad D=10/101.}\tag{RB.1}$$

The reference circular flank at angle L-eta has height

$$1/2+(1/2)\cos\eta=100/101=1-\kappa.$$

As the upper-right outward normal increases from zero to L, the reference boundary height is nondecreasing: its derivative is the nonnegative curvature measure times cos(t). Its left flank has the reflected property. Therefore every reference support at an upper normal outside (L-eta,L+eta) is attained by a point of height at most 100/101. At the two boundary normals that point has height exactly 100/101.

It follows that **any** convex downward cap U satisfying

$$\boxed{U_*\cap\{y\le100/101\}\subseteq U\subseteq U_*}\tag{RB.2}$$

retains all the supports TC.2 requires. It also contains the full half-height rectangle. It is an allowed TC cap, regardless of the regularity or number of its new faces.

## 2. An actual-hull theorem

Let K be any compact convex body such that

$$
\boxed{K_*\cap\{1/101\le y\le100/101\}\subseteq K\subseteq K_*.}\tag{RB.3}
$$

Thus K may differ from the reference hull only in the two horizontal boundary layers of thickness 1/101. It need not preserve either horizontal face, touch y=0 or y=1, or be symmetric.

Let E(K) be its full canonical two-turn envelope: remove from K all its lower and upper forbidden quadrants over the complete conventional quarter turns.

**Theorem RB1.**

$$\boxed{E(K)\text{ is compact, connected and full-turn feasible, and }|E(K)|\le M.}\tag{RB.4}
$$

**Proof.** Write K in vertical fibers [B(x),A(x)]. Since K contains the entire midline segment [-m,m] times {1/2}, its projection is [-m,m] and B<=1/2<=A. Form downward caps U,V with roofs A and 1-B. The reference's upper fiber endpoint lies below 100/101 whenever it lies outside the affected upper layer, so RB.3 implies

$$A(x)\ge\min(A_*(x),100/101).$$

The reflected statement holds for 1-B. Thus both U,V satisfy RB.2 and are independent allowed TC caps.

The upper supporting values of K equal those of U: for an upward normal a maximizing point can be taken on the top of its vertical fiber. The upper supports of rho(K) similarly equal those of V. Consequently

$$E(K)=(U\setminus N(U))\cap\rho(V\setminus N(V)),$$

with the exact full-niche definitions of TC. The common midline is retained because both cap roofs are at least one half and their niche roofs are bounded above by the reference niche roof, which is at most one half. Every fiber is a nonempty closed interval. Compactness and these fibers prove connectedness; the canonical inequalities and endpoint strips supply both continuous full-turn motions. TC3 gives the area upper bound. QED.

The theorem does not assert conv(E(K))=K; support tightening may remove unused hull portions. That hull equality is unnecessary for the inequality and is not silently assumed. Conversely, if a compact connected full-turn body S has actual hull K satisfying RB.3, canonical tightening gives S subset E(K), hence |S|<=M.

## 3. Arbitrarily many independent affine cuts are admitted

For example, take any collections of affine upper bounds

$$y\le1-e_i-s_i x$$

and affine lower bounds

$$y\ge e'_j+s'_j x,$$

and intersect them with K_*. It suffices that each bound obey

$$e_i+m|s_i|\le1/101,\qquad e'_j+m|s'_j|\le1/101.\tag{RB.5}$$

Every upper line then lies at or above 100/101 throughout [-m,m], and every lower line lies at or below 1/101. Their closed intersection contains the belt in RB.3. The families may be finite or infinite; the compact convex intersection still contains that belt. Thus RB1 bounds its full saturation.

The two cut families need not match, and the upper face can collapse to one endpoint while the lower face changes differently. This is an actual finite-parameter range, not only a claim for sufficiently small parameters with an unspecified error term.

In particular, for the familiar cuts through the left reference tips,

$$\tau_-(x+m/2)\le y\le1-\tau_+(x+m/2),$$

it is enough that

$$\boxed{0\le\tau_-,\tau_+\le2/(303m).}\tag{RB.6}$$

Either parameter may be zero. The corresponding fully saturated hull is covered even though saturation can recover niche material that was not in the original cut reference. The two slope parameters are independent.

## 4. The clipping comparison is explicit, not hidden in the area conclusion

For the caps in Section 2, write

$$\Delta(U)=M/2-\Psi(U),\qquad\Delta(V)=M/2-\Psi(V).$$

TC2 proves the stronger bounds

$$\Delta(U)\ge\int_{-m/2}^{m/2}(1-A_U),\qquad
\Delta(V)\ge\int_{-m/2}^{m/2}(1-A_V).$$

The entire positive clipping correction G is bounded by the sum of those two integrals. Hence

$$\boxed{G\le\Delta(U)+\Delta(V)}$$

on this class. This is the desired correctly signed budget, derived from an explicit area-preserving pairing of inner and outer tail abscissae. No support-derivative energy is charged against material that the reference sofa never contained.

## 5. Boundary of this new case

The theorem is not a neighborhood theorem for every hull close to K_*: RB.3 fixes a whole central belt exactly and prohibits outward hull changes. Small perturbations of the middle arcs can fall outside the admitted class. Partial-turn witnesses for an arbitrary S do not by themselves imply S subset E(K); the last implication of RB1 retains the full-turn premise.

Likewise the positive-face density theorem PD does not make arbitrary full-turn competitors satisfy RB.3 relative to the reference. Using it that way would assume the missing global localization. The full opposite-face supremum remains unbounded by the current argument outside this explicit class.

All new proofs are geometric and elementary given the reference formulas. Short rational checks of RB.1 and the paired circle identities are separate diagnostics, not proof certificates. No CI, Lean/Lake compilation, dependency installation, manuscript build, optimizer campaign or long search was used.
