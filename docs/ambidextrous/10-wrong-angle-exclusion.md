# 10. Wrong-direction witnesses have area at most sqrt(2)

This note removes the angular-sign restriction from Note 9 for every competitor that could improve on Romik's candidate. The endpoint angles may still be less than a quarter turn. The proof uses only a horizontal section of a wrongly rotated hallway and the two-strip bound.

## 10.1 The decisive hallway orientation

Let

\[
u=\frac{(1,-1)}{\sqrt2},\qquad v=\frac{(1,1)}{\sqrt2}.
\]

This is the lower-turn frame at dual angle -pi/4. For arbitrary placement parameters a,b, the defining inequalities of \(L_{u,v}(a,b)\) become

\[
x\leq\min\{\sqrt2(a+1)+y,\sqrt2(b+1)-y\},
\]

\[
x\geq\min\{\sqrt2 a+y,\sqrt2 b-y\}.
\]

The upper expression is exactly sqrt(2) plus the lower expression.

**Lemma 27 (wrong diagonal slice).** Every horizontal section of this placed hallway is a closed interval of length sqrt(2). Therefore its intersection with any horizontal strip of width at most one has area at most sqrt(2).

**Proof.** The displayed inequalities give the section endpoints and their difference. Integrate this constant section length over the strip. The result is independent of the hallway translation. QED.

For the upper-turn hallway at dual angle +pi/4, its fixed-handedness frame has the same two vectors with the labels exchanged. The identical conclusion holds.

This is a bound for the intersection of the hallway with the **fixed body-frame incoming strip**. The body remains in that strip as a set when the hallway is viewed in its moving frame. It is not necessary that the physical body remain in the original strip during its motion.

## 10.2 All wrong-sign endpoint angles are excluded

**Theorem 28 (wrong-way area bound).** Suppose S has a canonical monotone lower-turn witness ending at an angle omega<=0. Then

\[
|S|\leq\sqrt2.
\tag{10.1}
\]

The same bound holds for an upper-turn witness ending at omega>=0.

**Proof.** For a lower-turn endpoint omega in [-pi/4,0], the two-strip estimate (8.9) gives \(|S|\leq\sec|\omega|\leq\sqrt2\). For omega in [-pi/2,-pi/4], the monotone witness passes through -pi/4. The fixed body S lies in a horizontal strip of width at most one from the incoming condition, and in the corresponding placed hallway. Lemma 27 bounds its area by sqrt(2). The upper-turn case exchanges the two frame vectors and uses +pi/4. QED.

The bound does not require connectedness or optimality. It also applies immediately to any original witness whose lifted angle visits the wrong diagonal orientation, even before canonical tightening.

**Corollary 29 (correct angular signs for competitive bodies).** Every two-turn body S with area greater than sqrt(2) has simultaneous canonical witnesses with

\[
0<\omega_-\leq\pi/2,\qquad
-\pi/2\leq\omega_+<0.
\tag{10.2}
\]

**Proof.** Apply Theorem 21 to both original witnesses. A reduced endpoint with the wrong sign would contradict Theorem 28. QED.

## 10.3 The candidate really lies above this threshold

This comparison can be made exactly from the candidate constants without decimals. Let Y be the positive root of \(4Y^3+3Y-1=0\). Since

\[
4(2/7)^3+3(2/7)-1=-17/343<0,
\]

strict monotonicity of the cubic gives Y>2/7. For x>0,

\[
\arctan x>x-x^3/3,
\]

because the difference has derivative \(x^4/(1+x^2)>0\) and vanishes at zero. Monotonicity of arctangent then yields

\[
M=1+4Y^2+\arctan Y
>\frac{65}{49}+\frac{2}{7}-\frac{8}{1029}
=\frac{1651}{1029}>\frac85>\sqrt2.
\tag{10.3}
\]

The final rational comparison is \(5\cdot1651=8255>8232=8\cdot1029\). The comparison 8/5>sqrt(2) follows by squaring. Here M is the externally attributed candidate area; the algebraic inequalities are proved in this note.

## 10.4 A complete reduction for all potentially improving competitors

Combining the preceding notes gives the following proved statement.

**Theorem 30 (covering separated-hull reduction).** Let S be a compact connected ambidextrous body in the posed problem of Note 1, with \(|S|>\sqrt2\), and let K=conv(S). There are endpoint magnitudes \(\alpha,\gamma\in(0,\pi/2]\) such that:

1. the lower canonical motion uses angles [0,alpha], and the upper canonical motion uses angles [-gamma,0];
2. both corner paths are explicitly determined by h_K through (8.2);
3. K has width at most one in the incoming normal and in both outgoing strip normals;
4. its lower and upper swept niches are disjoint inside K;
5. the full saturated envelope \(E_K\) is compact, connected, feasible, vertically convex, contains S, and has convex hull K;
6. \(|E_K|=|K|-|N_-|-|N_+|\).

**Proof.** Theorem 21 and Corollary 29 supply the motions and signs; Lemma 20 supplies endpoint widths. The remaining assertions are Corollary 25 and Theorem 26. QED.

Thus every body that could equal or beat M is covered by this separated common-hull class. Bodies below or equal to sqrt(2) are already strictly below the candidate. No unrestricted two-independent-translation-path analysis, universal horizontal ceiling, or general disconnected-envelope relaxation is needed for this reduction.

## 10.5 Remaining, more focused problem

It now suffices to prove a sharp inequality

\[
|K|-|N_-(K;\alpha)|-|N_+(K;\gamma)|\leq M
\tag{10.4}
\]

for the viable, connected, correctly signed common-hull configurations in Theorem 30, and characterize equality. Partial endpoint angles are still genuine variables: the two-strip argument only gives \(\alpha,\gamma\geq\arccos(1/M)\) at area M and strict inequalities above M. No full-quarter-turn extension has been proved.

The reduction preserves the original body by containment, so a future equality theorem for E_K can still recover S using regular closedness. This is stronger than a replacement that merely preserves or increases area.
