# Roadmap: paper reorganization and complete formalization of stability/coercivity

This roadmap is for PR #10 and the paper branch `paper/uniqueness-arxiv`.
It records the intended organization and formalization plan before implementation starts.

## Governing rule

Every mathematical result stated as an author result anywhere in the final paper
(main text, appendix, theorem, proposition, lemma, corollary, or quantitative remark)
must have a corresponding Lean theorem whose proof is accepted by the kernel.

For computer-assisted inequalities, Python may generate certificates, but the
paper theorem must be discharged by a Lean checker. Python output is evidence
for development only, not part of the trusted proof.

Externally attributed results may remain external if clearly cited as such.
They must not be presented as new proved results of this paper unless formalized.

The final paper may include the explicit cutoff

    epsilon <= 10^(-600)

as a final proposition. It is deliberately conservative and should be presented
as an effectivity statement, not as a meaningful optimizer tolerance.

---

# I. Paper organization

## Main text: keep the theorem surface small

The main narrative remains

    optimality -> uniqueness -> stability

with the coercive certificate explaining all three.

### Section 10: Stability

Keep only the results and proof architecture that a reader should remember.

1. State the explicit local stability theorem with midpoint/top normalization:

       exists epsilon_0 > 0, for epsilon < epsilon_0:
         d_H(S_c,G) <= (23/10) sqrt(epsilon),
         |S_c triangle G| <= 50 sqrt(epsilon).

2. State the explicit angle theorem:

       pi/2 - omega <= (31/10) epsilon.

3. State the formalized pinned cap estimate:

       d_H(K,K_G+s_left)
         <= 2 sec(phi) sqrt(M-Q)
         < 2.002 sqrt(M-Q).

4. Give a concise proof sketch of stability:
   small deficit -> neighborhood entry -> local Q upper bound ->
   cap coercivity -> actual-set recovery.

5. Keep the punctured-sofa proof of sharpness of exponent 1/2 in the main text.

The current technical subsections of `10-stability.tex` should move to Appendix F.

### Section 11: One coercive certificate

Keep the coercive certificate in the main text:

    Q(xi) <= M,
    d_H(K,K_G+s_left) <= 2 sec(phi) sqrt(M-Q(xi)).

Then give the concise conceptual deductions:

    sign of deficit  -> optimality,
    zero deficit     -> uniqueness,
    small deficit    -> stability.

Keep only enough dependency discussion to establish non-circularity.
Detailed route/dependency bookkeeping moves to Appendix F or the formalization appendix.

### Open questions

Replace the present statement that the stability constants are not explicit.

The revised questions should include:

    1/sqrt(pi) <= C_sofa^* <= 2.3

for the local Hausdorff coefficient, and

    0.922 < C_Q^* <= 0.93

for the intrinsic full-Q coefficient.

Ask for the exact constants, extremizing modes, and whether the global sofa
coefficient is governed by punctures or a different deformation.

---

# II. Appendix F: technical stability proof

Appendix F receives the detailed material currently occupying most of Section 10.

## F.1 Deficit identity for Q

Present the exact decomposition

    M-Q = first-variation slack + nonnegative residual energies.

This is the analytic source of both the sign and the coercivity.

## F.2 Four-arc reconstruction

Present the Green-kernel / fundamental-theorem reconstruction and the formalized
pinned estimate

    ||f||_infty <= 2 sec(phi) sqrt(E).

## F.3 Local geometry near Gerver

Move here the detailed proofs of:

- nearby niche containment,
- canonical auxiliary bodies,
- arm/core margins,
- cut separation,
- A(K) <= Q(xi_K).

## F.4 Missing terminal angle

Move the terminal comparison and area-loss arguments.

## F.5 Actual-set recovery

Move:

- reference roof/outer margins,
- erosion/recovery,
- two directed Hausdorff bounds,
- symmetric-difference control.

## F.6 Compactness entry

Move the Hausdorff compactness and upper-semicontinuity proof that arbitrary
near-maximizers enter the local regime.

## F.7 Non-circularity / route audit

Collect the exact logical dependencies between the coercive route, optimality,
uniqueness and stability.

---

# III. Appendix G: quantitative refinements

Appendix G contains the new numerical and sharpness material.
Historical intermediate constants (80, 84, 30.5, 4.22, etc.) remain in the
repository history and are not paper theorem statements unless specifically needed.

## G.1 Centered cap coercivity

State the midpoint-aligned theorem

    d_H(K,K_G+s_mid) <= sec(phi) sqrt(M-Q(xi)),
    sec(phi) < 1.001.

Explain the exact centered Green-kernel norm and why this differs from the
left-pinned 2 sec(phi) theorem.

### Lean target

New module:

    MovingSofaStability/CenteredCap.lean

Target declarations:

    horizontalMidpoint
    midpointReferenceShift
    centeredCapDifference
    centered_green_control
    centered_wide_cap_support_bound
    centered_wide_cap_distance_bound
    centered_ki_cap_distance_bound
    sec_phi_lt_1001_1000

Acceptance gate:
the paper statement appears only after the full midpoint theorem is kernel checked.

## G.2 Explicit actual-sofa coefficients

State:

    exists epsilon_0 > 0, for epsilon < epsilon_0:
      d_H(S_c,G) <= 23/10 sqrt(epsilon),
      |S_c triangle G| <= 50 sqrt(epsilon),
      pi/2-omega <= 31/10 epsilon.

The appendix proof should emphasize:

1. complementary deficit budget;
2. whole-sector recovery instead of one worst-case interior disk;
3. Euclidean-normal hallway recovery instead of vertical roof depth.

### Lean targets

Suggested modules:

    MovingSofaStability/ExplicitBudget.lean
    MovingSofaStability/SectorRecovery.lean
    MovingSofaStability/NormalRecovery.lean
    MovingSofaStability/ExplicitTerminal.lean
    MovingSofaStability/ExplicitStability.lean

Final theorem surface:

    explicit_unrestricted_stability
    explicit_symmetric_difference_stability
    explicit_terminal_angle_stability

Prefer a bundled theorem if it avoids duplicated hypotheses.

Important:
formalize the 2.3/50/3.1 theorem first using the existing existential entry
mechanism. Do not make progress on these constants depend on the explicit
10^-600 cutoff.

## G.3 Sharpness and lower bounds

### Global sofas

Extract from the formalized puncture family the explicit coefficient lower bound

    C_sofa >= 1/sqrt(pi)

for any universal square-root Hausdorff estimate modulo rigid motions.

### Centered cap residual energy

Formalize limiting sharpness of sec(phi):

for every C < sec(phi) and every neighborhood of K_G, there exists an actual
normalized cap in that neighborhood whose translation-quotient distance exceeds

    C sqrt(E_cap).

### Lean targets

    MovingSofaStability/CoefficientLowerBound.lean
    MovingSofaStability/CenteredCapSharpness.lean

The one-sided smoothing family must be proved to define actual convex caps;
a sampled or Galerkin witness is not sufficient.

## G.4 Full-Q coercivity below one

State direct theorems before introducing an asymptotic optimum.

### Critical-face upper bound

For feasible triples with zero first-variation slack:

    d_tr(K,K_G) <= 93/100 sqrt(M-Q).

### Finite-deficit upper bound

For Delta=M-Q and 0 < Delta <= 1/512:

    d_tr(K,K_G)
      <= 93/100 sqrt(Delta) + 8 Delta^(2/3).

Corollary:

    Delta <= 10^(-18)
      -> d_tr(K,K_G) <= 94/100 sqrt(Delta).

### Feasible lower family

For every eta>0, construct a continuously feasible zero-slack triple with
0<Delta<eta and

    d_tr(K,K_G) > 461/500 sqrt(Delta).

Then define the intrinsic asymptotic coefficient C_Q^* if desired and state

    461/500 < C_Q^* <= 93/100.

### Lean targets

Suggested modules:

    MovingSofaStability/CriticalFace.lean
    MovingSofaStability/TranslationQuotient.lean
    MovingSofaStability/FullQCoercivity.lean
    MovingSofaStability/FeasibleCriticalMode.lean
    MovingSofaStability/CriticalQBounds.lean

Acceptance gate:
the 0.93 upper bound is not a paper theorem until the finite interval certificate
is checked by Lean, and the 0.922 lower bound is not a paper theorem until the
support-function family is proved feasible in Lean.

## G.5 Effective cutoff

Include as the final quantitative proposition:

    if 0 <= epsilon <= 10^(-600), then simultaneously

      d_H(S_c,G) <= 23/10 sqrt(epsilon),
      |S_c triangle G| <= 50 sqrt(epsilon),
      0 <= pi/2-omega <= 31/10 epsilon.

Presentation:
this is an effectivity theorem only. Explicitly say that 10^-600 is conservative
and not claimed quantitatively meaningful.

### Lean targets

Suggested modules:

    MovingSofaStability/EffectiveRightAngle.lean
    MovingSofaStability/EffectiveEntryModulus.lean
    MovingSofaStability/ExplicitLocalRadius.lean
    MovingSofaStability/ExplicitTerminalRadius.lean
    MovingSofaStability/ExplicitNormalCone.lean
    MovingSofaStability/ExplicitCutoff.lean

The final theorem should be a direct kernel-checked statement over arbitrary
original moving sofas, not merely a theorem about already-local caps.

---

# IV. Verified finite certificates in Lean

The current Python interval work should become a certificate GENERATOR only.

Create a small trusted Lean certificate layer, for example:

    MovingSofaStability/Certificates/Dyadic.lean
    MovingSofaStability/Certificates/Trig.lean
    MovingSofaStability/Certificates/Cover.lean
    MovingSofaStability/Certificates/CriticalQData.lean
    MovingSofaStability/Certificates/CriticalQCheck.lean
    MovingSofaStability/Certificates/ReferenceBounds.lean
    MovingSofaStability/Certificates/CutoffData.lean
    MovingSofaStability/Certificates/CutoffCheck.lean

The generic soundness layer should prove:

- outward dyadic interval operations contain the corresponding real operations;
- Taylor/Machin enclosures contain sin, cos and pi;
- matrix determinant/inverse interval bounds are valid;
- a passing cell proves the intended inequality on its whole rectangle;
- the finite binary-cell collection covers the entire parameter/angle domain.

Python may emit the certificate data, but Lean checks:

1. coverage;
2. every local inequality;
3. the final rational comparison.

No paper theorem may rely on an unverified Python assertion.

If the 0.93 certificate is prohibitively expensive for kernel checking, weaken
the paper constant slightly rather than enlarge the trusted base.

---

# V. Theorem manifest and paper audit

Extend the existing paper-route infrastructure so every author theorem has a
Lean counterpart.

Preferred artifact:

    docs/paper/theorem_manifest.tsv

or extend `docs/paper_routes.tsv` with columns:

    paper label
    environment
    Lean declaration
    source module
    formalized?
    external attribution?
    Challenge theorem?

Add a script/audit which fails when:

- an author theorem/proposition/lemma/corollary in the TeX has no Lean declaration;
- a numerical corollary in the paper is not covered by a Lean theorem;
- a theorem label points to a declaration that is missing from the build;
- a declared formalization status in Appendix D disagrees with the manifest.

Generated appendix dictionaries should come from this manifest where practical,
rather than being maintained independently.

---

# VI. Challenge / comparator surface

Do not expose every appendix lemma in `Challenge.lean`.

Add only headline externally meaningful results, tentatively:

    gerver_sofa_stable_explicit
    gerver_sofa_angle_stable_explicit
    gerver_cap_coercive_centered
    gerver_fullQ_coercive
    gerver_sofa_explicit_cutoff

Keep detailed appendix lemmas as library theorems.

Update both proof routes where appropriate:

- `Solution.lean`;
- `SolutionCoercive.lean`;

and extend Comparator so the advertised Challenge statements are proved by the
intended route.

---

# VII. Formalization order

## Phase 0: freeze theorem inventory

Before changing TeX, decide the exact paper theorem statements and constants.
Remove historical intermediate constants from the intended theorem surface.

Deliverable:
a theorem-manifest draft.

## Phase 1: centered cap coercivity

Formalize midpoint normalization, centered reconstruction, and the 1.001 bound.

Gate:
kernel-checked centered cap theorem.

## Phase 2: explicit 2.3 / 50 / 3.1 local stability

Formalize budget, sector recovery, normal recovery and terminal estimate.
Use existential entry.

Gate:
kernel-checked theorem with explicit coefficients and existential epsilon_0.

## Phase 3: sharpness results

Formalize:

- 1/sqrt(pi) global coefficient lower bound;
- sec(phi) centered cap-residual sharpness.

Gate:
both lower/sharpness theorems kernel checked.

## Phase 4: full-Q critical coercivity

Formalize:

- zero-slack face reduction;
- translation quotient;
- endpoint-slack estimate;
- finite-deficit 0.93 + 8 Delta^(2/3) theorem.

Gate:
all analytic reductions kernel checked except the finite numerical certificate.

## Phase 5: Lean certificate layer

Formalize interval arithmetic and generated certificate checking.
Import generated data for the 0.93 upper bound and other reference inequalities.

Gate:
0.93 upper bound kernel checked with no new axioms beyond the project standard.

## Phase 6: feasible critical lower family

Formalize the explicit support perturbation and its convexity, containment and
wall feasibility. Verify its energy certificate in Lean.

Gate:
461/500 lower theorem kernel checked.

## Phase 7: explicit cutoff

Formalize the coarse global entry modulus and every local numerical radius needed
to activate the explicit theorem. Then prove the final proposition:

    epsilon <= 10^(-600)
      -> 2.3 / 50 / 3.1 simultaneously.

Gate:
no existential local radius remains in the cutoff theorem.

## Phase 8: restructure manuscript

Only after the relevant theorem gates pass:

- shorten main Section 10;
- compress Section 11;
- create Appendix F and Appendix G;
- update abstract/introduction;
- update open questions;
- update formalization appendix and theorem dictionary.

## Phase 9: final audits

Run:

- full Lean build;
- axiom audit;
- route audit;
- theorem-manifest audit;
- Challenge comparators;
- certificate re-generation/replay;
- TeX build and cross-reference check.

---

# VIII. Trust and verification policy

Final paper claims should be classified explicitly:

1. **Kernel checked**: all author mathematical results.
2. **External**: clearly attributed external theorems.
3. **Generated certificate data**: untrusted data accepted only through a
   kernel-checked checker.
4. **Diagnostics/research history**: repository-only, not used as theorem evidence.

Do not describe an analytic/Python-only result as formalized.
Do not include a paper theorem before its Lean counterpart exists.

The formalization appendix should say exactly which paper theorem labels correspond
to which Lean declarations and which finite certificates are checked by Lean.

---

# IX. Intended final message of the paper

The main text should read conceptually as:

    coercive deficit
         |
         +-- nonnegative -> optimality
         +-- zero        -> uniqueness
         +-- small       -> stability.

Appendix F answers:
why the local-to-global stability mechanism works for arbitrary nonconvex sofas.

Appendix G answers:
how quantitative the mechanism is, which constants are explicit or sharp, why
the full Q deficit is stronger than cap residual energy, and how effectivity can
be made fully numerical down to the explicit 10^-600 cutoff.

This organization keeps the main paper readable while allowing every stated
result, including the number-crunching appendices and the final cutoff, to be
kernel checked.
