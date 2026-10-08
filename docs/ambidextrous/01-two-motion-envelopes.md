# 1. Two-motion envelopes and connected saturation

All areas are planar Lebesgue measures. This note uses compact connected bodies of positive area. When exact set recovery is needed, regular closedness will be an additional hypothesis, not an implicit consequence of area equality.

## 1.1 A posed two-turn problem

Let

\[
H_0=\{(x,y):x\leq1,\ 0\leq y\leq1\},\qquad
V_- =\{(x,y):0\leq x\leq1,\ y\leq1\},
\]

\[
H_- =H_0\cup V_-,\qquad
\rho(x,y)=(x,1-y),\qquad H_+=\rho H_-,\quad V_+=\rho V_-.
\]

A two-turn witness for a body S consists of continuous paths
\(g_d:[0,1]\to SE(2)\), for \(d\in\{-,+\}\), such that

\[
g_d(0)S\subseteq H_0,\qquad
g_d(t)S\subseteq H_d\quad(0\leq t\leq1),\qquad
g_d(1)S\subseteq V_d.
\]

The rotational part of each \(g_d(0)\) is the identity. Initial translations may differ. This specifies a common incoming body orientation; it does not allow choosing two unrelated orientations and calling the result ambidextrous. A motion uses only proper rigid motions; \(\rho\) is not an allowed step of either motion. The body can be translated farther into or out of an arm without difficulty, since the arms are unbounded in the corresponding directions.

These definitions do not fix the angular excursion or require angle monotonicity. A theorem only about monotone quarter-turn witnesses must be labelled as such. Equivalence to other formulations involving two corners separated by a prescribed distance is not asserted here.

## 1.2 Saturate both witnesses, not one

Fix two paths with the prescribed initial rotational parts, and a compact box B. Define

\[
E_d=B\cap g_d(0)^{-1}H_0
       \cap\bigcap_{t\in[0,1]}g_d(t)^{-1}H_d
       \cap g_d(1)^{-1}V_d,
\qquad E=E_-\cap E_+.
\]

Here inverse images, not inverses of sets, are intended. The box merely ensures compactness; for any given compact competitor S one may choose B containing S. It is part of the witness data, not a purported uniform diameter bound.

**Proposition 1 (two-motion envelope).** E is compact. Every compact subset T of E follows both prescribed motions with the required endpoint inclusions. Conversely, any body S contained in B that follows those motions satisfies \(S\subseteq E\).

**Proof.** Hallways and endpoint arms are closed. Their inverse images under rigid motions are closed, so E is closed in compact B. Every defining inclusion for a subset T follows from its containment in every set in the intersection. The converse is the same implication read in reverse. No regularity of the paths beyond their continuity as motions, and no monotonicity of their angles, is needed. QED.

The construction is an exact intersection of the **two** one-turn envelopes. Replacing S by just \(E_-\) can destroy the other turn. Nor is the area of a disconnected E necessarily the area of an admissible connected sofa.

**Proposition 2 (connected saturation).** If a connected S is contained in E, it lies in one connected component C of E. That component is compact, connected, feasible for both motions, and has \(|C|\geq|S|\).

**Proof.** A connected subset lies in one component. Components of a compact set are closed, hence compact. Apply Proposition 1 and monotonicity of measure. QED.

**Proposition 3 (a largest component for fixed witnesses).** If E is nonempty, it has a component of maximal area.

**Proof.** Let m be the supremum of component areas. If m=0, every component attains it. If m>0, there are only finitely many components of area greater than m/2: arbitrarily many disjoint such measurable subsets would contradict the finite area of B. This finite family is nonempty and its largest area equals m; components outside it have area at most m/2. QED.

Thus, for fixed witnesses the connected optimization problem is solved exactly by a largest-area component, not automatically by the entire envelope. Taking a supremum over all pairs of motions and boxes gives the same supremum as the posed body problem: every body is dominated by such a component, and every such component of positive area is feasible. This statement does **not** establish that a globally optimal pair of motions exists.

## 1.3 What global maximality would imply

If S is a global maximizer in the compact connected class, Proposition 2 implies \(|C|=|S|\) for its containing component C. It does not prove \(S=C\). In particular, the one-turn caps generating the two envelopes need not separately maximize either one-turn area functional.

For example, let A be a closed unit disk and let F be A together with a line segment attached to its boundary. A and F are compact and connected, A is a proper subset of F, and their areas agree. This is a warning about the logical implication, not an assertion that this particular pair is a sofa envelope.

**Lemma 4 (regular-closed recovery).** If F is compact and regular closed, S is a closed subset of F, and \(|S|=|F|\), then S=F.

**Proof.** If p belongs to F but not S, closedness of S gives a ball around p disjoint from S. Since \(F=\overline{\operatorname{int}F}\), that ball contains an interior point of F, and hence a smaller open ball in \(F\setminus S\). The smaller ball has positive area, contradicting equality of areas. QED.

The regular-closed hypothesis is on the larger set F. We have not proved that arbitrary two-motion envelopes or their components satisfy it.

## 1.4 The first missing bridge

A cap or rotation-path proof must either represent every relevant two-turn competitor, dominate every competitor by a represented feasible body, or explicitly limit its theorem to the represented subclass. Applying a one-turn envelope separately is safe only after intersecting the two resulting envelopes and retaining connectivity as above. Applying a one-turn **maximizer replacement** is not justified by these propositions.

All four results above are pen-and-paper lemmas with the stated hypotheses; none has been formalized or compiled.
