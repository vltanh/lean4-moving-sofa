# A sharp \(P_J\) certificate for top-normal cuts of Romik's cap

**Status and scope.** This is a direct ordinary-area-functional corollary of the
existing [tail-paired cut deficit](tail-paired-cut-deficit.md), specifically TC1–TC4.
It proves the conjectured sharp **one-cap spatial-partition value** on a
nontrivial infinite-dimensional class, with an explicit nonnegative remainder.
It does **not** prove \(P_J(U)\le M/2\) on all convex caps, all caps from feasible
two-turn sofas, or arbitrary near-reference hulls. The global Minkowski
concavity premise CF5 remains false, even with positive top faces
([CN](candidate-functional-concavity-counterexample.md)). No concavity is used.

## Statement

Center Romik's reference downward convex cap \(U_*\) in horizontal projection
\(I=[-m,m]\), where \(m=1/(3\sin\beta)\),
\(\beta=\arctan Y\), and \(4Y^3+3Y-1=0\).
Put \(a=-m/2\), \(b=m/2\), and \(J=[a,b]\), the **middle half** of \(I\).
Let \(A_U(x)\) denote the upper roof of a downward cap \(U\), and
\(n_U(x)\) the nonnegative full-quarter turning-niche roof. Write

\[
P_J(U)=\int_{I\setminus J}A_U(x)\,dx-\int_J n_U(x)\,dx.
\]

Fix \(0<\eta<\beta\) and \(D=(\sin\eta)/2\). Assume precisely the TC admissibility
conditions:

1. \(I\times[0,1/2]\subseteq U\subseteq U_*\), with \(U\) compact, convex
   and downward closed.
2. Its actual upper support agrees with that of \(U_*\) on
   \([0,\pi/2-\eta]\cup[\pi/2+\eta,\pi]\).

**Theorem PJ-CUT1 (sharp spatial-partition budget).**
Every such cap satisfies

\[
\boxed{
\frac M2-P_J(U)
\;\ge\;
\int_{-m}^{a-D}(A_*-A_U)\,dx
+\int_{b+D}^{m}(A_*-A_U)\,dx
\;\ge 0.
}
\tag{PJ-CUT.1}
\]

In particular \(P_J(U)\le M/2\), and the bound is sharp at \(U_*\).
No smoothness, symmetric cutting, positive remaining top face, or
curvature bound on the cut cap is assumed.

## Proof: pair every saved niche slice with an exterior lost slice

The explicit reference construction in TC Section 1 gives
\(n_*=0\) almost everywhere outside \(J\), and
\(P_J(U_*)=\Psi(U_*)=M/2\): its roof is identically one on \(J\),
and its entire positive niche is supported there.

By \(U\subseteq U_*\), roof loss \(d=A_*-A_U\) is nonnegative.
Support monotonicity also gives \(0\le n_U\le n_*\), so the niche
saving \(e=n_*-n_U\) is nonnegative and vanishes outside \(J\).
Subtracting the two \(P_J\) definitions *without moving the middle
window* gives the exact identity

\[
\boxed{
\frac M2-P_J(U)
=\int_{I\setminus J} d(x)\,dx-\int_J e(x)\,dx.
}
\tag{PJ-CUT.2}
\]

TC1 pairs the niche loss at \(b-d_0\) with the actual exterior roof
loss at \(b+d_0\), for \(0<d_0<D\), and similarly pairs \(a+d_0\)
with \(a-d_0\). TC Section 3 proves that every other positive niche
value is unchanged, using the unaltered reference support directions.
Consequently its exact integral comparison TC.4 states

\[
\int_J e(x)\,dx
\le
\int_{a-D}^{a}d(x)\,dx
+
\int_b^{b+D}d(x)\,dx.
\tag{PJ-CUT.3}
\]

These two exterior strips lie inside \(I\setminus J\), are disjoint,
and are **actual roof losses**. Subtract PJ-CUT.3 from PJ-CUT.2.
The resulting untouched exterior integrals are exactly PJ-CUT.1.
The reference itself has \(d=e=0\), proving sharpness. QED.

## Implication and remaining gap

This adds a proved \(P_J\) case to the research ledger, including arbitrary
independent short top-normal convex cuts. Two caps individually satisfying
these hypotheses obey \(P_J(U)+P_J(V)\le M\), and the existing SPB1
ordinary-area enclosure then bounds any actual connected complete-turn
sofa whose two canonical caps are in this domain. This conclusion does
**not** assume that a generic cap pair automatically defines a connected
sofa, and does not cover partial turns with fewer visited angles.

The proof is not global. The support agreement in TC.2 is highly
restrictive; outward perturbations, shifted flank supports, and the
opposite-positive-face class supplied by PD3 generally violate it.
In particular the false global concavity CF5 cannot be revived by
restricting to positive top faces, and the numerical absence of a
\(P_J>M/2\) witness is not itself a theorem.

**Next test:** seek a valid deficit decomposition for arbitrary fixed-width
caps, or exhibit a certified counterexample to the scalar bound.
Any such extension must preserve the exact continuous niche and the
moving width-dependent middle window. Numerical angle samples alone
underestimate the niche, hence overestimate \(P_J\).

This is a self-reviewed pen-and-paper corollary; no Lean formalization,
CI, long search or independent refereeing is claimed.
