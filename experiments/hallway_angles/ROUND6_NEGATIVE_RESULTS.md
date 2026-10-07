# Sixth-round negative results and boundaries of the conclusions

## 1. A scalar model crossing is not the global phase transition

The new explicit equations have a uniquely certified crossing at a bend between 136.672184698 and 136.672184699 degrees. This is not a theorem that the unrestricted optimizer switches there. The forward contact pattern, all-pose feasibility, a matching forward-class upper bound, and the unrestricted reduction in this middle-angle interval remain separate obligations.

The central fixed-endpoint functional is strictly concave, but varying contact regimes and switch locations is not covered by that lemma. It is therefore incorrect to relabel its stationary solution as the proved forward optimum.

## 2. Flat contacts alone discard useful geometry

The previous cutoff used only the flat-contact rectangle and separately maximized every error term. Exploratory improvements of those constants were still too weak over a substantially larger interval. Interior rectangles of the curved candidate retain more width and give the current sufficient cutoff e<=1/8.

The new proof refuses any cutoff outside its verified foundation interval [0,1/8]. This is a domain restriction of the proof, not evidence that the sofa ceases to be globally optimal immediately beyond it. No critical-angle bracket is inferred from this cutoff.

## 3. A coarse geometric enclosure can destroy a true inside rectangle

Initial direct interval evaluations of the upper contact height lost precision near the flat endpoint and did not certify all mismatch directions. The replacement uses the proved curvature bound e^2 rho<=8/5 and its integrated height estimate Y(u)>=1/2-(4/5)u^2. This endpoint-tight inequality is analytic; midpoint evaluations are not substituted for the missing interval proof.

A one-cell direction cover is rejected. Each retained direction cell separately verifies positive core dimensions, the width excess, and both triangular-cap conditions. The first cell uses a full-height core to avoid dividing by a zero direction component.

## 4. Direct fixed-precision Horner evaluation can be excessively wide

The baseline degree-73 trigonometric enclosure is valid but can amplify coefficient-rounding widths enormously when its argument is about 2.4 radians. At a point interval for 135 degrees it produced a sine interval with width about 0.025, despite the input interval being about 10^-29 wide. That is not a false enclosure, but it is unusable for a tight root proof.

The new crossing checker evaluates at one quarter of the argument, then applies two exact double-angle identities. Regression tests compare the resulting enclosures to independent high-precision values at arguments up to absolute value four. The original baseline file is unchanged.

## 5. Off-root derivative boxes were too conservative

Attempting to bound the signed-area difference derivative on the whole contact-parameter rectangle gave inconclusive cells. The successful proof first establishes a unique T(beta) by F_T>0 and endpoint signs, then covers that root branch by interval-Newton tubes. It checks the implicit derivative only where a root can lie. Coarse tube covers still reject; no inconclusive cell is accepted as monotonicity.

## 6. A sampled nonconvex boundary polygon is not an inner certificate

The analytic model's sampled boundary polygon is valid at the tested angles, and its area converges to the signed-area expression. Nevertheless the floating-point difference from a finite hallway intersection can be positive, typically around 10^-10 with 1025 points per boundary interval and 1025 base poses in the tested cases. Chords of nonconvex boundary portions need not stay inside the continuously feasible region; roundoff is also present.

`forward_contact_diagnostics.py` reports these positive discrepancies without tolerance clipping or polygon repair. Its output is not a continuous-motion or exact-area certificate. It is incorrect to use zero-looking plotted discrepancies or agreement of area quadrature as a feasibility theorem.

## 7. A combined reproduction attempt exceeded the local execution limit

The 12 cutoff tests and 17 contact-model tests initially passed in separate runs. A first combined command exceeded the runtime's 45-second execution limit before finishing. No complete-pass claim was made for that invocation.

A 64-cell parameter cover also proved all of the cutoff inequalities, retaining the full [0,1/8] continuum. Using it in the combined regression suite reduced the work; the complete 29-test reproduction then passed with no skips. The independent 128-cell certificate also passed. The stored result explicitly records the 64-cell run, with minimum directional margin greater than 0.005; the 128-cell run had a margin greater than 0.006.

## 8. Review and novelty remain open

The new cutoff still depends on the analytic cap identity, crossing and excursion inequalities, width correction, quadratic theorem, candidate realization, and alignment lemma. Exact arithmetic does not independently verify these mathematical interpretations. No Lean build or CI/workflow action was attempted.

The competing numerical branches were already reported by Xingyi He, arXiv:2608.11206v1. The present analytic contact equations and scalar crossing require comparison with prior analytic work; no first-discovery claim is made merely from a source search. Both the proof draft and the model equations need independent mathematical review.
