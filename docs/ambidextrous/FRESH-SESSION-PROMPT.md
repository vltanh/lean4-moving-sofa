# Start a genuinely fresh research session

**Before pursuing any mathematics:** Read [SHARP-OPTIMALITY-EXECUTION-PLAN.md](SHARP-OPTIMALITY-EXECUTION-PLAN.md) and work **only its currently ACTIVE gate**. The chronological note below is historical background and does not supersede the controlling plan. No additional local class exclusions, convex-bound refinements or exploratory screens may be promoted as proof progress. Apply the plan's global-inequality, falsification, and commit acceptance rules.


Paste the following into a new ChatGPT session (preferably with the repository's GitHub connection available). This prompt is a **new research instruction**, not a claim that a proof already exists.

---

We are investigating the **sharp unrestricted ambidextrous moving-sofa problem**. The conjectured optimum is Romik's feasible candidate

\[
M=1+4Y^2+\arctan Y\approx1.6449552184,\qquad 4Y^3+3Y-1=0.
\]

My research lives at [vltanh/lean4-moving-sofa, draft PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3), branch `research/ambidextrous-pen-and-paper`. Read **[CONSOLIDATED-RESEARCH-HANDOFF.md](https://github.com/vltanh/lean4-moving-sofa/blob/research/ambidextrous-pen-and-paper/docs/ambidextrous/CONSOLIDATED-RESEARCH-HANDOFF.md)** FIRST. The previous exploratory commits were squashed; the branch contains the full retained source archive but this handoff, not the chronological notes, is authoritative for the status.

**Unrestricted optimality and uniqueness are NOT proved; no counterexample area above M has been verified.** The central unsolved issue for full-turn sofas with compatible downward one-turn caps U,V is the true ordinary-area clipping correction:

\[
|S|\le\Psi(U)+\Psi(V)+G(U,V),\quad G\ge0.
\]

There is a written but not independently refereed sharp weighted one-turn value \(\Psi(U)\le M/2\). To prove the sharp **full-turn** bound, one sufficient result is

\[
G(U,V)\le(M/2-\Psi(U))+(M/2-\Psi(V))
\]

for all **actual compatible** cap pairs, including nonsmooth/asymmetric cases, with precise normalizations. Arbitrary partial-turn motions remain an additional unresolved obligation. Read the exact OT1 formula and its **nonempty vertical-fiber condition** before using this expression.

We have already tried and hit barriers with: simply reflecting/averaging arbitrary sofas; maximizing two original Gerver sofas independently; width-two filling/squeezing; two-cap weighted-objective interpolation without clipping; false global Minkowski concavity of the old `P_J` functional; three-anchor or forbidden-triple-only area LPs; local/smooth shears, far-width bounds, and long numerical searches; importing PR #7's *different physical hallway bend*. Explicit counterexamples to naive versions are in the handoff.

**Please do NOT** resume the pattern of many small restricted lemmas, small improvements to nonsharp numerical bounds, or increasingly fine near-Romik optimization. Do not call a local conditional result a global breakthrough. No Lean formalization yet, and do not alter the project's original Lean libraries or PR #7.

My task for you:
1. Critically audit the *few mathematical dependencies* relevant to a potential **global** result (especially ordinary-area clipping/connectedness and the cap-pair interaction); explicitly flag any incorrect prior claim rather than inheriting it.
2. Choose **one genuinely new geometric mechanism** that could cover all competitors or global maximizers, and immediately try to falsify its key universal lemma with an explicit feasible configuration. A good alternative is a truly different construction with certified area >M.
3. If the mechanism survives, pursue the full hand proof (including full-vs-partial turn coverage), not just a toy subclass; if it fails, give the exact counterexample and stop the route.
4. Commit only substantive verified progress, sparingly, to PR #3's research branch, preserving its consolidated status. **No Lean**, CI, or broad corpus rewrite.
5. State honestly whether the work materially changes the proof boundary.

External research projects to consult **only where relevant**: [PR #7](https://github.com/vltanh/lean4-moving-sofa/pull/7) changes the actual hallway bend; [PR #4](https://github.com/vltanh/lean4-moving-sofa/pull/4) prescribes net rotation in the ordinary right-angle hallway. Neither supplies Romik optimality.

The goal is **real sharp global progress, or a rigorous reason a proposed shortcut fails**. If there is no credible new mechanism, say so rather than manufacturing intermediate milestones.

---
