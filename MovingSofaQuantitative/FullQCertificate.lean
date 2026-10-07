module

public import MovingSofaQuantitative.OperatorModelTransfer

/-!
# Full-Q upper theorems: closed certificate draft

UNCOMPILED AND UNEXECUTED. This file closes the numerical premise by a concrete
bounded Boolean computation, not an axiom, an imported Python receipt, or a
hypothesis asserting the desired operator estimate. `decide` uses Lean's own
reduction; no native evaluator or external oracle is introduced.

The reduction below has NOT been run. The direct rational expression checker
can be very expensive, and its chosen depth has not been replayed by the Python
checker. The earlier Python receipt verifies a differently organized evaluator
of the same mathematical model; it is not an execution receipt for this file.
If this closed check exhausts its bound or cannot reduce within practical
resources, the draft must be repaired with explicit accepted subtrees and/or
proved dyadic rounding. Do not report its kernel acceptance before that run.

All endpoint regularity, actual kernel identification, complete-box soundness,
and zero-cosine cases are supplied by the preceding modules. There is no
additional geometric or continuum-operator premise in the final theorem types.
-/

@[expose] public section
noncomputable section

open MovingSofaOptimality

namespace MovingSofaQuantitative

/-- Proposed closed reduction of the finite interval search. This source term
is intentionally isolated: failure or resource exhaustion cannot be mistaken
for verification of the analytic transfer. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem critical_operator_reduction :
    Certificates.CriticalExpression.closedCheck 128 = true := by
  decide

/-- The actual continuum operator, from the exact scalar model and its full cover. -/
theorem critical_operator {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    CriticalOperatorBound hP hbox :=
  operator_of_closed_check 128 critical_operator_reduction hP hbox

/-- Exact paper target on the zero-first-variation face. -/
theorem critical_face_upper : Targets.CriticalFaceUpper :=
  criticalFaceUpper_of_operator (fun _ hP hbox => critical_operator hP hbox)

/-- Exact paper target, including the actual endpoint wall-slack remainder. -/
theorem full_q_finite : Targets.FullQFinite :=
  fullQFinite_of_operator_endpoints
    (fun _ hP hbox => critical_operator hP hbox)
    (fun _ hP hbox => actual_endpoint_slacks hP hbox)

/-- The rational .94 consequence includes a separate zero-deficit argument. -/
theorem full_q_094 : Targets.FullQ094 := fullQ094_of_finite full_q_finite

/-- The higher-order remainder does not increase the asymptotic upper constant. -/
theorem intrinsic_coefficient_upper {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    intrinsicQCoefficient P ≤ (93 / 100 : ℝ) :=
  intrinsic_upper_of_finite full_q_finite hP hbox

end MovingSofaQuantitative
