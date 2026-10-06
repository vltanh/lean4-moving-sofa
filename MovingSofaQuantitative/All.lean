module

public import MovingSofaQuantitative.TranslationQuotient
public import MovingSofaQuantitative.Normalization
public import MovingSofaQuantitative.CenteredKernel
public import MovingSofaQuantitative.CapQuotient
public import MovingSofaQuantitative.Targets
public import MovingSofaQuantitative.CoefficientLowerBound

/-!
# Quantitative extension: development root

This library is optional and is not imported by the paper's existing solutions.
No file in this extension has been compiled or kernel-checked in this session.

The source currently contains:
* the exact rank-one translation quotient and attainment argument;
* its identification with Euclidean horizontal cap alignment;
* midpoint normalization and its distinction from the existing left-support pin;
* the centered scalar Green profiles and an integral Gram-matrix estimate;
* exact proposition contracts for all fifteen quantitative headline targets;
* proof source for the scalar sec(phi) enclosure and the puncture coefficient
  lower bound 1/sqrt(pi).

The actual centered four-arc Gram identities have NOT yet been instantiated.
There is no completed centered cap theorem in this root, no 2.3/50/3.1 proof,
no checked full-Q interval certificate, and no proof of the 10^-600 cutoff.
The target definitions are propositions to be proved, not axioms or placeholders
counted as completed theorems. The cutoff remains a mandatory target.

See docs/paper/quantitative_manifest.json for the per-target source status and
scripts/quantitative_gate.py for the local exact-statement/axiom acceptance gate.
No successful gate receipt exists. Passing the Python tests checks the gate's
plumbing and rational examples only, not these Lean declarations.
-/
