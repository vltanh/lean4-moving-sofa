module

public import MovingSofaQuantitative.TrialSpline
public import MovingSofaQuantitative.EndpointGapControl

/-!
# The explicit continuously interpolated critical trial

Uncompiled proof source. These are the rational data recorded in
critical_cone/feasible-trial-data.json, not a floating-point eigenvector.
The cut value, initial slope, top value, and harmonic contact slope are exact
expressions in the actual Gerver parameters. All other node data are rational.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative.CriticalTrial

def q : ℝ := 10934514869/10000000000

def c (P : GerverParams) : ℝ := π/2-P.θ

def startValue (P : GerverParams) : ℝ := -cos P.φ+q*sin P.φ

def startSlope (P : GerverParams) : ℝ := sin P.φ+q*cos P.φ

def contactValue : ℝ := -4080320233/10000000000

def contactSlope (P : GerverParams) : ℝ :=
  (contactValue*cos(c P-P.φ)-startValue P)/sin(c P-P.φ)

def x (P : GerverParams) (i : ℕ) : ℝ :=
  if i≤8 then P.φ+(c P-P.φ)*(i:ℝ)/8 else c P+(π/2-c P)*((i:ℝ)-8)/8

def node (P : GerverParams) : Fin 17 → HermiteNode
  | 0 => ⟨P.φ,startValue P,startSlope P⟩
  | 1 => ⟨x P 1,-1078919599/1250000000,4339550711/5000000000⟩
  | 2 => ⟨x P 2,-31126707/40000000,7723585883/10000000000⟩
  | 3 => ⟨x P 3,-437577721/625000000,7028975229/10000000000⟩
  | 4 => ⟨x P 4,-9828693/15625000,6359229927/10000000000⟩
  | 5 => ⟨x P 5,-5650988373/10000000000,569148283/1000000000⟩
  | 6 => ⟨x P 6,-5083771327/10000000000,2552594261/5000000000⟩
  | 7 => ⟨x P 7,-1144865203/2500000000,5349627621/10000000000⟩
  | 8 => ⟨c P,contactValue,contactSlope P⟩
  | 9 => ⟨x P 9,-3500057133/10000000000,3483836151/5000000000⟩
  | 10 => ⟨x P 10,-2944649529/10000000000,6495576867/10000000000⟩
  | 11 => ⟨x P 11,-2403539187/10000000000,6277727561/10000000000⟩
  | 12 => ⟨x P 12,-58691981/312500000,303294039/500000000⟩
  | 13 => ⟨x P 13,-1371834111/10000000000,290950371/500000000⟩
  | 14 => ⟨x P 14,-17763627/200000000,553481437/1000000000⟩
  | 15 => ⟨x P 15,-430688197/10000000000,8158621/15625000⟩
  | 16 => ⟨π/2,0,50024573/100000000⟩

def nodes (P : GerverParams) : List HermiteNode :=
  [node P 0,node P 1,node P 2,node P 3,node P 4,node P 5,node P 6,node P 7,node P 8,
   node P 9,node P 10,node P 11,node P 12,node P 13,node P 14,node P 15,node P 16]

theorem positions {P : GerverParams} (hP : P.IsSolution) :
    P.φ<c P ∧ c P<π/2 := by
  have ho := GerverParams.gs_ord hP
  unfold c
  constructor <;> linarith [ho.1,ho.2.1,ho.2.2]

theorem ordered {P : GerverParams} (hP : P.IsSolution) : OrderedNodes (nodes P) := by
  have h := positions hP
  norm_num [OrderedNodes,nodes,node,x,List.pairwise_cons,List.mem_cons,List.not_mem_nil] <;>
    linarith [h.1,h.2]

/-- The scalar trial profile, with its two one-sided curvature functions and
finite curvature bound, is obtained from actual finite Hermite interpolation. -/
def splineData {P : GerverParams} (hP : P.IsSolution) : TrialSplineData P.φ where
  q := q
  q_nonneg := by norm_num [q]
  head := node P 0
  rest := (nodes P).tail
  ordered := by simpa only [nodes,List.tail_cons] using ordered hP
  head_position := rfl
  head_value := rfl
  head_slope := rfl
  top := node P 16
  top_mem := by simp [nodes]
  top_position := rfl
  top_value := rfl

def profile {P : GerverParams} (hP : P.IsSolution) : HalfCapProfile P.φ :=
  (splineData hP).profile hP.1

@[simp] theorem profile_zero {P : GerverParams} (hP : P.IsSolution) :
    (profile hP).value 0= -1 := TrialSplineData.profile_zero _ hP.1

@[simp] theorem profile_contact_value {P : GerverParams} (hP : P.IsSolution) :
    (profile hP).value (c P)=contactValue := by
  exact ((splineData hP).profile_at_node hP.1 (a := node P 8) (by simp [splineData,nodes])).1

@[simp] theorem profile_contact_slope {P : GerverParams} (hP : P.IsSolution) :
    (profile hP).first (c P)=contactSlope P := by
  exact ((splineData hP).profile_at_node hP.1 (a := node P 8) (by simp [splineData,nodes])).2

@[simp] theorem profile_cut_value {P : GerverParams} (hP : P.IsSolution) :
    (profile hP).value P.φ=startValue P := by
  exact ((splineData hP).profile_at_node hP.1 (a := node P 0) (by simp [splineData,nodes])).1

/-- This exact matching condition removes the linear perturbation term at the
vanishing active endpoint. It is not a rounded node constraint. -/
theorem contact_jet {P : GerverParams} (hP : P.IsSolution) :
    (profile hP).first (π/2-P.θ)=harmonicBridgeFirst P.φ (π/2-P.θ)
      ((profile hP).value P.φ) ((profile hP).value (π/2-P.θ)) (π/2-P.θ) := by
  change (profile hP).first (c P)=harmonicBridgeFirst P.φ (c P)
    ((profile hP).value P.φ) ((profile hP).value (c P)) (c P)
  rw [profile_contact_slope,profile_contact_value,profile_cut_value]
  simp only [contactSlope,harmonicBridgeFirst,sub_self,cos_zero,mul_one]
  ring

/-- Every node is a literal interpolating datum, including the top node. -/
theorem profile_at_node {P : GerverParams} (hP : P.IsSolution) (i : Fin 17) :
    (profile hP).value (node P i).position=(node P i).value ∧
    (profile hP).first (node P i).position=(node P i).slope := by
  apply (splineData hP).profile_at_node hP.1
  fin_cases i <;> simp [splineData,nodes]

end MovingSofaQuantitative.CriticalTrial
