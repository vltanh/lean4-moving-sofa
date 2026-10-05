# 5. Common-pose normalization and genuinely two-sided variations

A fixed-height certificate needs a fixed coordinate normalization. Also, extremality of an intersection is not extremality of either factor. Both points matter before transferring a single-turn variation argument.

## 5.1 A common incoming pose is available

**Proposition 14 (common-pose normalization).** Every body with witnesses as in Note 1 can, after one translation of its body coordinates, be given two witnesses satisfying

\[
g_-(0)=g_+(0)=\operatorname{Id},\qquad S\subseteq H_0.
\tag{5.1}
\]

Pure translations may need to be prepended. No angle-monotonicity assertion is made.

**Proof.** Write \(g_-(0)=T_a\) and \(g_+(0)=T_b\), since their initial rotational parts are the identity. Put \(S'=T_aS\) and \(\widehat g_d(t)=g_d(t)T_{-a}\). Then \(\widehat g_-(0)=\operatorname{Id}\), \(\widehat g_+(0)=T_{b-a}\), and both \(S'\) and \(T_{b-a}S'\) lie in H_0. Since H_0 is convex,

\[
T_{u(b-a)}S'\subseteq H_0\quad(0\leq u\leq1).
\]

Indeed, for each p in S', the segment joining p to \(p+b-a\) lies in H_0. Prepend this translation to \(\widehat g_+\), then reparametrize the concatenation on [0,1]. It starts at the identity and ends where the original positive-turn path ends. The negative-turn path already starts at the identity. Both retain their endpoint and hallway inclusions. QED.

In this normalization the common K of Note 2 is contained in \(H_0\), in particular in the strip \(0\leq y\leq1\). The midline h=1/2 is then meaningful. Without normalization, translating a tight candidate far above a fixed separator can introduce artificial mask loss. A universal estimate with a fixed h must not silently range over arbitrary translated coordinates.

Reflection of normalized witness data is still normalized: exchange the two labels and replace each path by \(\rho g_d\rho\). Conjugating a proper rigid motion by a reflection remains proper, and \(\rho\operatorname{Id}\rho=\operatorname{Id}\). Thus the normalization itself does not impose symmetry or discard the reflected competitor.

## 5.2 The exact finite-difference identity

Let A and B be measurable finite-area one-turn envelopes. Vary only the first envelope to A_epsilon, leaving B fixed.

**Lemma 15 (masked gain and loss).**

\[
|A_\varepsilon\cap B|-|A\cap B|
=|(A_\varepsilon\setminus A)\cap B|
 -|(A\setminus A_\varepsilon)\cap B|.
\tag{5.2}
\]

**Proof.** Decompose the two intersections into their common part and their respective exclusive parts. Subtract the areas; the common part cancels. QED.

This shows exactly which gain and loss survive the second motion. A one-turn calculation that counts the full gain \(|A_\varepsilon\setminus A|\) may count points forbidden by B.

For a concrete counterexample to transferring maximality, take

\[
A=B=[0,1]\times[0,1],\qquad
A_\varepsilon=[\varepsilon,1+2\varepsilon]\times[0,1].
\]

For small positive epsilon, \(|A_\varepsilon|=1+\varepsilon\) increases but \(|A_\varepsilon\cap B|=1-\varepsilon\) decreases. For small negative epsilon, the intersection area is \(1+2\varepsilon<1\). Thus epsilon=0 maximizes the intersection in this family but does not maximize the first envelope's area. This is a set-theoretic counterexample, not a proposed sofa.

## 5.3 A smooth first variation, with all its hypotheses

Here restrict to bounded planar domains A and B with compact C^2 boundaries. Let their boundaries intersect in finitely many points, transversely. Vary them by C^1-in-epsilon families of C^2 diffeomorphisms, with outward normal speeds v_A and v_B at epsilon=0. Assume the regularity and transversality persist for small epsilon.

**Proposition 16 (exposed-boundary variation).**

\[
\left.\frac{d}{d\varepsilon}|A_\varepsilon\cap B_\varepsilon|
\right|_{\varepsilon=0}
=\int_{\partial A\cap\operatorname{int}B}v_A\,ds
 +\int_{\partial B\cap\operatorname{int}A}v_B\,ds.
\tag{5.3}
\]

**Proof.** Away from the finitely many crossings, each boundary arc has a tubular coordinate system. Its displacement changes area to first order by outward normal speed times arc length. An arc of boundary A contributes precisely where it is inside B; an arc outside the closure of B contributes nothing, and likewise with the labels exchanged. Transversality implies that the crossing points move by O(|epsilon|). The small pieces omitted or added at a crossing occupy a region of diameter O(|epsilon|), so their area is O(epsilon^2). Adding the finitely many arc contributions and dividing by epsilon proves the formula. The same argument works for either sign. QED.

For a smooth common outer set K and smooth ambient niches N_- and N_+, under the same finite transverse-intersection hypotheses and with no triple boundary intersections, the corresponding surviving-area derivative is

\[
\begin{aligned}
\dot A={}&\int_{\partial K\setminus(\overline{N_-}\cup\overline{N_+})}v_K\,ds\\
&-\int_{\partial N_-\cap\operatorname{int}K\setminus\overline{N_+}}v_-\,ds
-\int_{\partial N_+\cap\operatorname{int}K\setminus\overline{N_-}}v_+\,ds.
\end{aligned}
\tag{5.4}
\]

The signs follow because expanding an exposed niche removes surviving area. Here the ambient niches are used to state the smoothness assumptions; their intersections with K are U and V from Note 2. Formula (5.4) is a consequence of the same arc calculation, not an assertion that arbitrary swept niches have smooth boundaries.

To obtain a stationarity equation for a sofa one must additionally prove that the chosen domain variations arise from admissible motion variations and preserve a feasible connected competitor, or justify a suitable relaxation. None of these admissibility statements follows from (5.3).

## 5.4 Shared active arcs need one-sided derivatives

Transversality is not cosmetic. Suppose A and B share a boundary arc and have the same interior side. In signed normal coordinates, let their perturbed boundaries be

\[
r=\varepsilon a(s)+o(\varepsilon),\qquad
r=\varepsilon b(s)+o(\varepsilon),
\]

with uniform remainders, and interiors on the lower-r side. On the common arc the intersection's boundary is the minimum of the two graphs. Consequently its contribution to the **right** area derivative is

\[
\int\min(a,b)\,ds,
\]

whereas its contribution to the **left** derivative is

\[
\int\max(a,b)\,ds.
\tag{5.5}
\]

These assertions follow directly by integrating the height change in normal coordinates; the Jacobian changes only by O(|epsilon|). Boundary arcs with opposite interior sides require a different local formula and are not covered by (5.5).

For a maximum, a right derivative must be nonpositive and a left derivative nonnegative. Replacing these inequalities by an unproved smooth Euler equation can lose precisely the asymmetric perturbations that distinguish a two-turn problem.

## 5.5 Symmetric perturbations are not sufficient

A reflection-invariant objective can have a strict maximum on the symmetric subspace and increase in an antisymmetric direction. For example,

\[
f(x,y)=-(x+y)^2+(x-y)^2
\]

is invariant under swapping x and y. On x=y it has a strict maximum at the origin, but on x=-y it increases away from the origin.

Thus restricting the two witness paths to be reflected copies cannot establish unrestricted local or global maximality. The strict niche separation proved for Romik's candidate eliminates overlap/mask loss locally; it does not eliminate independent motion variables or make all common outer-boundary contacts differentiable.

The next analytic calculation should use (5.2) or an appropriately justified version of (5.3) to derive **two independent families** of variational conditions, with common-arc terms treated separately. The current single-turn curvature/injectivity argument in [the uniqueness manuscript](../paper/sections/07-injectivity.tex) cannot simply be invoked for this different objective.
