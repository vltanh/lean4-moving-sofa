# Archive

Documents kept as they were when the illustrated text in [`docs/proof/`](../proof/README.md) replaced
them. Their links to the Lean code point to the lines of commit `02af501`, and may have drifted
since.

- [`UNIQUENESS.md`](UNIQUENESS.md): the map from the informal uniqueness proof to the Lean code.
- [`BRIDGE.md`](BRIDGE.md): the bridge to formal-conjectures' definitions.
- [`uniqueness/`](uniqueness): ChatGPT Pro 6's notes on the uniqueness argument; note 20,
  [`uniqueness/20-complete-paper-proof.md`](uniqueness/20-complete-paper-proof.md), is the informal
  proof that the formalization follows.
- [`stability/`](stability): the notes, numerical checks and status documents of pull request #8 on
  the stability of Gerver's sofa, as they were at its last commit `8b25774`, before its Lean code
  was compiled; [`docs/stability.md`](../stability.md) replaced them. Notes 08, 05, 06 and 07 are the
  informal proof of the main theorem that the Lean code follows, note 01 that of the cap estimate
  with coefficient 2 sec φ, and note 09 that of the punctured sofas. Their status lines ("not
  Lean-checked") and the status documents describe the pull request before the compilation.
