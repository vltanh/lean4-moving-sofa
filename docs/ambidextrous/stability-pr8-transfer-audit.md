# PR #8 transfer audit: what stability supplies, and what it does not

This note reads the actual stability argument before importing it into the ambidextrous program. It records a useful method and two invalid shortcuts. No theorem about Gerver is renamed as a theorem about Romik. No Lean source is compiled or copied into the ambidextrous branch.

## Pinned source

PR #8 was inspected at commit `1a97bc70782652f29c29dd4866115bd288c53e86` on `research/quantitative-stability`.

Relevant source files, all at that commit:

- [05-nonsmooth-certificate.md](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability/05-nonsmooth-certificate.md)
- [06-local-upper-bound.md](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability/06-local-upper-bound.md)
- [07-terminal-angle-loss.md](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability/07-terminal-angle-loss.md)
- [08-unrestricted-theorem.md](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability/08-unrestricted-theorem.md)
- [FORMALIZATION.md](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability/FORMALIZATION.md) and [Statement.lean](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/MovingSofaStability/Statement.lean).

The formalization policy calls the new files **uncompiled proof source**. In `Statement.lean`, `UnrestrictedStability` and `TerminalAngleStability` are definitions of propositions to be proved, not declarations of the completed theorem. Its `sofaDeficit_nonneg` invokes the existing one-turn optimality theorem. The written stability proof is not thereby independently checked, and this audit does not claim to verify all its lemmas.

## 1. Different reference bodies and different deficits

Use different symbols throughout:

\[
M_G=|G|,\qquad M_A=|\Sigma|.
\]

PR #8 proves a written estimate of the form

\[
d_H(S_{\rm aligned},G)\leq C\sqrt{M_G-|S|}
\]

for one-turn sofas whose deficit is below an existential entry threshold. The ambidextrous target is an estimate centered at Sigma, with deficit M_A-|S|. These are different quantities even when the same body is admissible for both problems.

At Sigma, M_A-|Sigma|=0, while M_G-|Sigma| is a positive fixed number. The explicit constants in Romik's paper distinguish the two areas; see [arXiv:1606.08111v3, Sections 1.1–1.2](https://arxiv.org/html/1606.08111v3). Therefore ambidextrous near-optimality does not supply the small one-turn deficit needed by PR #8. Its entry threshold is not numerically bounded below in a way that would bridge this gap.

Nor does replacing S by a one-turn enlargement solve this automatically. A proof would have to show that the enlargement has a sufficiently small Gerver deficit and relate its distance or area back to the original intersection. Neither implication is provided by the stability theorem itself.

## 2. Qualitative entry uses already established uniqueness

Section 1 of PR #8's note 08 takes a one-turn maximizing sequence, passes to a compact limit, and invokes the existing Gerver uniqueness theorem to identify that limit. Only then does it enter the fixed neighborhood in which the local nonsmooth certificate applies.

Repeating that paragraph with Sigma in place of G would require the very ambidextrous optimality/uniqueness conclusion being sought. Compactness of our feasible class gives a maximizer, not its identity or proximity to Sigma. The local theorem and the compactness statement cannot be joined by assuming the missing identity.

This is a dependency obstruction, not a claim that stability methods cannot help.

## 3. The transferable part: certify energy and area separately

PR #8's note 05 writes its enlarged-domain certificate as

\[
M_G-Q_G(\xi)=\text{nonnegative dual slack}+\text{residual energy}.
\]

Its note 06 separately proves ordinary-area enclosure near G using convex auxiliary tail bodies, rather than assuming that nearby competitors have bounded curvature. Its note 07 separately pays for missing final angles using a terminal-strip loss. The final nonconvex recovery retains both missing area and approximate hallway slack.

Those separations are exactly the useful lesson for the ambidextrous branch:

\[
D(h):=M_A-\widetilde{\mathcal Q}(h),\qquad
E(S,h):=|S|-\widetilde{\mathcal Q}(h),
\]

so that

\[
M_A-|S|=D(h)-E(S,h).
\tag{T.1}
\]

AF3 controls D and identifies its zero set. It does not bound E by D. AF4 and the narrow curvature-dominated example show that E can be positive on genuine feasible bodies. An energy theorem alone cannot change the minus sign in (T.1).

A correct use of stability should therefore quantify D and prove an **error-absorption or a surrogate-enclosure inequality**. It should not just add a distance estimate to a functional that is below the actual area.

## 4. The terminal-strip method: useful strategy, missing geometric premise

PR #8's angle argument does not extend the original sofa's motion. It proves that a fixed floor region lost to the tilted terminal strip has area c times the missing angle, while the newly available omitted wedges are confined to short endpoint windows and cost less.

An analogous ambidextrous statement could pay for partial endpoints without forcing them geometrically. However its application would require an independently justified local neighborhood or global floor/roof margins. Those are not consequences of the coarse area bound in this branch. The existing wide-hull width gate is a different argument and remains the one currently proved on its stated class.

## 5. Work authorized by this audit

The next transfer is at the **auxiliary-profile level**: the already proved AF3 uniquely maximizes the ambidextrous functional without knowing ordinary sofa optimality. Quantitative fixed-width coercivity and a scalar width-deficit analysis can therefore be developed noncircularly there. They can turn a separately proved enclosure or repair estimate into a sharp comparison, but cannot supply that estimate by definition.

The following claims are not made:

- that PR #8 proves Romik stability;
- that its Green constant for Gerver's cap is the ambidextrous constant;
- that an ambidextrous maximizer already lies near the candidate;
- that defining a Lean proposition proves it;
- that a positive ordinary-area defect is negligible merely because it vanishes at the candidate.

The current analytic and geometric checkpoints must remain separate until (T.1) is controlled. This audit and subsequent transfers are pen-and-paper work. No CI, Lean/Lake build, numerical experiment, or manuscript build was used.
