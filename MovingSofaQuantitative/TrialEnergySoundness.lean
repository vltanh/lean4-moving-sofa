module

public import MovingSofaQuantitative.TrialResidualFormulas
public import MovingSofaQuantitative.Certificates.TrigExpression

/-!
# Soundness lemmas for the feasible-trial energy certificate

UNCOMPILED SOURCE.  These lemmas are analytic bridges used by the closed
certificate.  They are independent of the certificate's accepted numerical
upper endpoints.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Finset
open MovingSofaOptimality MovingSofaStability
open MovingSofaQuantitative.Certificates

namespace MovingSofaQuantitative
namespace CriticalTrial

/-- A square of each explicit trial residual is interval-integrable on every
closed subinterval of its nonsingular arc. -/
theorem trial_residual_integrable_r2 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IntervalIntegrable (fun t => r2 P t ^ 2) volume P.φ (π/2-P.φ) := by
  have F := profile hP
  have hd := halfCapProfile_data hP hbox F
  have h := hd.middle_sq
  apply intervalIntegrable_of_eqOn_Ioo (by linarith [(GerverParams.gm_φ_mem_Ioo hP hbox).2]) h
  intro t ht
  rw [(cap_residual_formulas hP).2.1 t ht]

theorem trial_residual_integrable_r3 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IntervalIntegrable (fun t => r3 P t ^ 2) volume (π/2-P.φ) (π/2) := by
  have F := profile hP
  have hd := halfCapProfile_data hP hbox F
  apply intervalIntegrable_of_eqOn_Ioo (by linarith [(GerverParams.gm_φ_mem_Ioo hP hbox).1]) hd.third_sq
  intro t ht
  rw [(cap_residual_formulas hP).2.2 t ht]

theorem trial_residual_integrable_r4 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IntervalIntegrable (fun t => r4 P t ^ 2) volume P.φ (π/2) := by
  have F := profile hP
  have hd := halfCapProfile_data hP hbox F
  have hi := hd.last_sq.comp_sub_left π
  apply intervalIntegrable_of_eqOn_Ioo (by linarith [(GerverParams.gm_φ_mem_Ioo hP hbox).1]) hi
  intro t ht
  have hu : π-t ∈ Ioo (π/2) π := by linarith [ht.1,ht.2,pi_pos]
  rw [last_cap_residual hP hu]
  ring

theorem trial_residual_integrable_B {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IntervalIntegrable (fun t => rB P t ^ 2) volume (c P) (π/2) := by
  obtain ⟨hi,hi2,-⟩ := rightAuxiliary_data hP hbox
    (wideGerverTriple hP hbox)
  apply intervalIntegrable_of_eqOn_Ioo (positions hP).2.le
    (intervalIntegrable_subinterval hi2 (positions hP).1.le (positions hP).2.le le_rfl)
  intro t ht
  rw [(right_aux_residual hP).2 t ht]

theorem trial_residual_integrable_D {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IntervalIntegrable (fun t => rD P t ^ 2) volume (c P) (π/2) := by
  obtain ⟨hi,hi2,-⟩ := leftAuxiliary_data hP hbox
    (wideGerverTriple hP hbox)
  have hi' := hi2.comp_sub_left π
  apply intervalIntegrable_of_eqOn_Ioo (positions hP).2.le
    (intervalIntegrable_subinterval hi' (positions hP).1.le (positions hP).2.le le_rfl)
  intro t ht
  have hu : π-t ∈ Ioo (π/2) (π/2+P.θ) := by
    unfold c at ht
    linarith
  have he := (left_aux_residual hP).1 (π-t) hu
  simp only [sub_sub_cancel] at he
  rw [he]
  ring

/-- Splitting a square integral along a finite ordered chain. -/
theorem arcSquare_chain {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable (fun t => f t^2) volume a b)
    (xs : List ℝ) (hxs : xs.Pairwise (· ≤ ·)) (hhead : xs.head? = some a)
    (hlast : xs.getLast? = some b) :
    arcSquare a b f =
      ((xs.zip xs.tail).map fun p => arcSquare p.1 p.2 f).sum := by
  induction xs using List.twoStepInduction with
  | nil => simp at hhead
  | singleton x =>
      have hx : x=a := by simpa using hhead
      have hy : x=b := by simpa using hlast
      subst a; subst b
      simp [arcSquare]
  | cons_cons x y xs ih₁ ih₂ =>
      have hxy : x≤y := (List.pairwise_cons.mp hxs).1 y (by simp)
      have hyb : y≤b := by
        have := List.pairwise_cons.mp hxs
        exact List.pairwise_le_getLast this.2 hlast
      have hs := arcSquare_split h hxy hyb
      rw [hs]
      simp only [List.zip_cons_cons,List.map_cons,List.sum_cons]
      congr 1
      first | exact ih₂ | exact ih₁

/-- The fixed rational Hermite nodes cover the required trial arcs. -/
theorem node_partition_cover {P : GerverParams} (hP : P.IsSolution)
    (hord : OrderedNodes (nodes P)) (u : ℝ) :
    u∈Icc P.φ (π/2) →
    ∃ i : Fin 16, u∈Icc (node P i).position (node P ⟨i+1,by omega⟩).position := by
  intro hu
  have hfirst : (node P 0).position=P.φ := rfl
  have hlast : (node P 16).position=π/2 := rfl
  exact exists_adjacent_interval_of_mem_ordered_nodes hord hfirst hlast hu

/-- Elementary rational bound for the first harmonic residual energy. -/
theorem r1_closed_interval {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    q^2*tan P.φ ≤
      (58017271195847425899889281 /
        1237940039285380274899124224 : ℚ) := by
  have hφ := hbox.1
  have hp : 0≤P.φ := hφ.1.trans (by norm_num)
  have hc : 1249/1250 ≤ cos P.φ := by
    calc
      (1249/1250:ℝ) ≤ 1-(P.φ)^2/2 := by
        have hs := sq_le_sq₀ hp (hφ.2.trans (by norm_num : (0.04:ℝ)≤0.04))
        nlinarith
      _ ≤ cos P.φ := one_sub_sq_div_two_le_cos
  have hs : sin P.φ ≤ P.φ := Real.sin_le (by linarith)
  have htan : tan P.φ ≤ (0.04:ℝ)/(1249/1250) := by
    rw [tan_eq_sin_div_cos]
    exact div_le_div₀ (by linarith) hs hc (by norm_num)
  unfold q CriticalTrial.q
  norm_num at htan ⊢
  nlinarith

namespace BridgeGapCheck

abbrev E := TrigExpr 2
def φ : E := .variable 0
def θ : E := .variable 1
def πe : E := .pi
def halfPi : E := .mul πe (.rational (1/2))
def c : E := .add halfPi (.neg θ)
def qE : E := .rational (10934514869/10000000000)
def y0 : E := .add (.neg (.cos φ)) (.mul qE (.sin φ))
def y8 : E := .rational (-4080320233/10000000000)
def bridge : E :=
  .mul
    (.pow
      (.mul
        (.add (.mul y8 (.cos φ)) (.neg (.mul y0 (.cos c))))
        (.inv (.sin (.add c (.neg φ))))) 2)
    (.add
      (.mul (.sin c) (.inv (.cos c)))
      (.neg (.mul (.sin φ) (.inv (.cos φ)))))

def box : Box 2
  | 0 => ⟨39177264/1000000000,39177465/1000000000⟩
  | 1 => ⟨681301409/1000000000,681301610/1000000000⟩

def upper : ℚ :=
  99156653185241992015427571 / 1237940039285380274899124224

def check : Bool := TrigExpr.checkUpper box bridge upper

set_option maxHeartbeats 0 in
private theorem reduction : check=true := by decide

theorem sound {P : GerverParams} (hbox : P.InBox) :
    CriticalTrial.bridgeSineCoefficient P^2*(tan (CriticalTrial.c P)-tan P.φ) < upper := by
  have hp : InBox box (fun | 0=>P.φ | 1=>P.θ) := by
    intro i; fin_cases i
    · simpa [box,Interval.Contains] using hbox.1
    · simpa [box,Interval.Contains] using hbox.2.1
  have h := TrigExpr.checkUpper_sound reduction hp
  simpa [bridge,TrigExpr.realValue,φ,θ,πe,halfPi,c,qE,y0,y8,
    CriticalTrial.bridgeSineCoefficient,CriticalTrial.startValue,CriticalTrial.c,
    tan_eq_sin_div_cos] using h

end BridgeGapCheck

theorem bridge_gap_closed_interval {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    bridgeSineCoefficient P^2*(tan (c P)-tan P.φ) ≤
      (99156653185241992015427571 /
        1237940039285380274899124224 : ℚ) :=
  (BridgeGapCheck.sound hbox).le

end CriticalTrial
end MovingSofaQuantitative
