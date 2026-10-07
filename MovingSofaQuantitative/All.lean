module

public import MovingSofaQuantitative.TranslationQuotient
public import MovingSofaQuantitative.Normalization
public import MovingSofaQuantitative.CenteredKernel
public import MovingSofaQuantitative.CapQuotient
public import MovingSofaQuantitative.Targets
public import MovingSofaQuantitative.CoefficientLowerBound
public import MovingSofaQuantitative.PiecewiseCalculus
public import MovingSofaQuantitative.ResidualAlgebra
public import MovingSofaQuantitative.ProjectionAlgebra
public import MovingSofaQuantitative.ComparisonProfile
public import MovingSofaQuantitative.ComparisonPairing
public import MovingSofaQuantitative.CenteredCap
public import MovingSofaQuantitative.OrthogonalErosion
public import MovingSofaQuantitative.ExplicitBudget
public import MovingSofaQuantitative.ActualSetRecovery
public import MovingSofaQuantitative.FullQConsequences
public import MovingSofaQuantitative.Certificates.Interval
public import MovingSofaQuantitative.Certificates.Expression
public import MovingSofaQuantitative.Certificates.Cover
public import MovingSofaQuantitative.Certificates.Trig

/-!
# Quantitative extension: uncompiled development root

This optional library is not imported by the established paper solutions.
No Lean, Lake, or CI is being run under the current instruction.

There is now an intended end-to-end proof-source chain for the centered cap
estimate: a concrete continuous comparison profile, its actual right derivative
and four residuals, exact endpoint pairing, exact energy polarization, and a
scalar projection argument applied to the integrated pinned estimate. It gives:

* `centered_energy : Targets.CenteredEnergy`;
* `centered_cap : Targets.CenteredCap`;
* `centered_ki : Targets.CenteredKi`.

No Gram-integral or centered-coercivity premise remains in those targets.
The scalar sec(phi) enclosure and puncture coefficient lower bound retain their
separate direct proof source.

The root also includes actual orthogonal erosion and missing-area recovery,
complementary scalar budgets, and implication lemmas for the full-Q finite and
asymptotic consequences. Those implications do not replace the still separate
critical-face/operator and feasible-family proofs.

The certificate foundation includes rational arithmetic with real semantics,
expression evaluation, complete binary covers, and exact Taylor enclosures for
sine and cosine. It is not yet a completed certificate for the .93 operator:
that certificate must instantiate the concrete analytical model and its cover.

All additions remain uncompiled proof source and may contain elaboration or
proof errors. The mandatory 10^-600 arbitrary-sofa target is unchanged. A target
proposition, a conditional transfer lemma, or a Python test is not counted as a
proof of an unconditional quantitative target.

See docs/paper/quantitative_manifest.json and the continuation ledger. No new
kernel-verification or successful full quantitative-gate receipt is claimed.
-/
