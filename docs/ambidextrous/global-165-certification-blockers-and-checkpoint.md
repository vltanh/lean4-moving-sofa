# Global 1.65 proof search: exact impossibility gates and an unfinished 1.75 tree

**Status at 2026-10-08:** the proposed complete global proof certificate \(A_F\le33/20=1.65\) is **NOT complete**. This is a progress checkpoint, not an upper-bound theorem. The partial-turn \(1/6\) improvement remains **conditional** on the unproved full-turn bound via JT.

## 1. Two genuine finite-angle obstructions

The exact connected finite-hallway witnesses in [MW1](fullturn-n32-rational-mesh-obstruction.md) and [AW34](fullturn-n34-asymmetric-mesh-obstruction.md) prove
\[
A_{32}\ge1.6500470139016479\ldots>1.65,\qquad
A_{34}\ge\frac{4125119548180921069}{2500000000000000000}
=1.6500478192723684\ldots>1.65.
\]
Both include the extra exact \(45^\circ\) frame on each handed family. Thus **no search using only either specified finite-angle set can certify \(A_n\le1.65\)**; further subdivision does not alter their true optimal values. These are finite-position bodies only; they are **not** continuously feasible full-turn counterexamples.

A change to more angles or an independently proved continuum constraint is logically necessary. The lower witnesses do not prove that every other mesh fails, or that no full-turn global bound exists.

## 2. What the exact near-reference certificate does establish

[NL1](one-sixth-fullturn-near-reference-certificate.md) uses 511 rational angles per hand and exact directed integer slices to establish the **local**, honest full-turn bound
\[
d_H(\operatorname{conv}S,K_*)\le 7/10000
\quad\Longrightarrow\quad
|S|\le
\frac{412456005949545207}{250000000000000000}
=1.649824023798180828\ldots<1.65.
\]
The remaining full-turn shapes can have a wider hull, subunit vertical height, rough/asymmetric supports and arbitrary distance outside this tiny candidate neighborhood. Neither area closeness nor the known \(1.765\) global upper bound proves these shapes lie inside NL1's small support-distance ball.

A complete proof needs a covering/exclusion of **all** admissible shapes in the complement; it cannot silently restrict candidates to the NL neighborhood.

## 3. One longer exact-arithmetic 1.75 discovery run; not a completed certificate

The local compiled C++ executable
\`/mnt/data/certificate_global_attempt/four_angle_exact_tree\` implements a directed integer, canonical-support box search for O'Keefe's four 3–4–5 handed hallways at target **7/4 = 1.75**, using CP's necessary conic support inequalities and an 18-wall piecewise-affine upper area oracle. It is a **discovery tree** until a separate checker verifies a complete tree.

The exact local resumable file \`testresume.tree\` had previously reported
\[
4\,248\,174\text{ processed nodes},\quad23\text{ unvisited frontier nodes},
\quad0\text{ unresolved depth-cap leaves}.
\]
In this continuation, a 25-second resumed segment processed 658,030 additional nodes. Its persisted checkpoint reports
\[
\begin{array}{l}
\text{processed nodes}=4\,906\,204,\\
\text{split nodes}=2\,453\,113,\\
\text{area-passed leaves}=2\,378\,597,\\
\text{support-infeasible leaves}=74\,494,\\
\text{unvisited frontier nodes}=23,\\
\text{unresolved depth-cap leaves}=0,\\
\text{certificate complete}=\mathbf{false}.
\end{array}
\]
These are concrete runtime counters, **not** a global area certificate. The tree remains open despite the additional work, and there is no verified bound \(G\le1.75\) from it. Four angles could never prove the needed \(A_F\le1.65\) by themselves in any event: the exact four-angle finite relaxation admits connected area \(1.7317236488\ldots>1.65\) configurations.

The executable, state and bytes in \`/mnt/data\` are local session resources and are **not** thereby committed, permanent or independently checked. No claim is made that the compiled C++ search itself is a Lean proof.

## 4. Next full-turn obligation and what would constitute success

Prove one of:

- **Finite exact route:** choose a sufficiently strong finite-angle family, rigorously show that its global supremum \(A_\Theta\le1.65\) (or use a complete interval tree with certified virtual-angle constraints that validly strengthens it). Every leaf must be justified by exact rational/algebraic interval arithmetic and every branch covered, with a separate trusted checker.
- **Hybrid route:** exact box exclusion of the complement of NL1's reference-neighborhood, including all asymmetric/rough/subunit-height hulls, plus NL1 for the retained neighborhood. The search must parameterize **all** possible hulls and not assume curvature, symmetry or face alignment.
- **Continuum route:** prove the missing general two-turn ordinary-area comparison directly, e.g. a sharp coupled deficit/overlap inequality. Local finite-angle witnesses do not invalidate a genuine continuum theorem.

Whichever route is used, the entire full-turn \(A_F\le1.65\) theorem must be established **before** invoking JT to claim the unrestricted \(1/6\) result.

**Do not** describe a local optimizer returning \(<1.65\), a complete neighborhood box, a prefix with an unvisited DFS stack, or a two-sided cap inequality requiring unproved regularity as a global certificate. This checkpoint records why longer computation alone cannot finish the incorrect 32/34-angle program. No new global bound is proved in this file.
