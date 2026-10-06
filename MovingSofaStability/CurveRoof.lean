module

public import MovingSofaStability.EpigraphBalls
public import MovingSofaUniqueness.RegularClosed

/-!
# Lipschitz roof graphs from monotone boundary arcs

Finite exceptional sets of phase junctions are allowed. The derivative condition
controls vertical displacement by horizontal displacement; this supplies a graph
rather than assuming one from a picture.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def VerticalSlopeBound (Γ : Set Point) (L : ℝ) : Prop :=
  ∀ p ∈ Γ, ∀ q ∈ Γ, |p.2 - q.2| ≤ L * |p.1 - q.1|

/-- A derivative cone controls all chords, even across finitely many junctions. -/
theorem scalar_graph_slope {a b L : ℝ} {X Y dX dY : ℝ → ℝ} {F : Set ℝ}
    (hF : F.Finite) (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hdX : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt X (dX t) t)
    (hdY : ∀ t ∈ Ioo a b, t ∉ F → HasDerivAt Y (dY t) t)
    (hpos : ∀ t ∈ Ioo a b, t ∉ F → 0 ≤ dX t)
    (hcone : ∀ t ∈ Ioo a b, t ∉ F → |dY t| ≤ L * dX t) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |Y u - Y v| ≤ L * |X u - X v| := by
  have hmono := env_monotoneOn hF hX hdX hpos
  have hplus : MonotoneOn (fun t => L * X t + Y t) (Icc a b) := by
    apply env_monotoneOn hF (hX.const_mul L |>.add hY)
      (fun t ht he => ((hdX t ht he).const_mul L).add (hdY t ht he))
    intro t ht he
    have h := (abs_le.mp (hcone t ht he)).1
    linarith
  have hminus : MonotoneOn (fun t => L * X t - Y t) (Icc a b) := by
    apply env_monotoneOn hF (hX.const_mul L |>.sub hY)
      (fun t ht he => ((hdX t ht he).const_mul L).sub (hdY t ht he))
    intro t ht he
    have h := (abs_le.mp (hcone t ht he)).2
    linarith
  have ordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      |Y u - Y v| ≤ L * |X u - X v| := by
    intro u hu v hv huv
    have hm := hmono hu hv huv
    have hp := hplus hu hv huv
    have hn := hminus hu hv huv
    rw [abs_of_nonpos (sub_nonpos.mpr hm)]
    apply abs_le.mpr
    constructor <;> nlinarith
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · exact ordered u hu v hv huv
  · simpa only [abs_sub_comm] using ordered v hv u hu hvu

theorem VerticalSlopeBound.mono_constant {Γ : Set Point} {L C : ℝ}
    (h : VerticalSlopeBound Γ L) (hLC : L ≤ C) : VerticalSlopeBound Γ C := by
  intro p hp q hq
  exact (h p hp q hq).trans (mul_le_mul_of_nonneg_right hLC (abs_nonneg _))

/-- Two graphs meeting at one separating vertical line retain a common slope bound. -/
theorem verticalSlopeBound_join {Γ₁ Γ₂ : Set Point} {z : Point} {L : ℝ}
    (h₁ : VerticalSlopeBound Γ₁ L) (h₂ : VerticalSlopeBound Γ₂ L)
    (hz₁ : z ∈ Γ₁) (hz₂ : z ∈ Γ₂)
    (hleft : ∀ p ∈ Γ₁, p.1 ≤ z.1) (hright : ∀ p ∈ Γ₂, z.1 ≤ p.1) :
    VerticalSlopeBound (Γ₁ ∪ Γ₂) L := by
  have cross_bound : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, |p.2 - q.2| ≤ L * |p.1 - q.1| := by
    intro p hp q hq
    have hl := hleft p hp
    have hr := hright q hq
    have hA := h₁ p hp z hz₁
    have hB := h₂ z hz₂ q hq
    rw [abs_of_nonpos (sub_nonpos.mpr hl)] at hA
    rw [abs_of_nonpos (sub_nonpos.mpr hr)] at hB
    rw [abs_of_nonpos (sub_nonpos.mpr (hl.trans hr))]
    have ht := abs_add_le (p.2 - z.2) (z.2 - q.2)
    rw [sub_add_sub_cancel] at ht
    nlinarith
  intro p hp q hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact h₁ p hp q hq
  · exact cross_bound p hp q hq
  · simpa only [abs_sub_comm] using cross_bound q hq p hp
  · exact h₂ p hp q hq

/-- A vertically Lipschitz set has at most one point over each abscissa. -/
theorem eq_of_same_abscissa {Γ : Set Point} {L : ℝ} (h : VerticalSlopeBound Γ L)
    {p q : Point} (hp : p ∈ Γ) (hq : q ∈ Γ) (he : p.1 = q.1) : p = q := by
  have hh := h p hp q hq
  rw [he, sub_self, abs_zero, mul_zero] at hh
  have hy : p.2 = q.2 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  exact Prod.ext he hy

/-- A curve with all abscissas and a chord-slope bound is a genuine Lipschitz graph. -/
theorem exists_roof_function {Γ : Set Point} {a b L : ℝ}
    (hrange : ∀ p ∈ Γ, p.1 ∈ Icc a b)
    (hcover : ∀ x ∈ Icc a b, ∃ p ∈ Γ, p.1 = x)
    (hLip : VerticalSlopeBound Γ L) :
    ∃ γ : ℝ → ℝ,
      (∀ p : Point, p ∈ Γ ↔ p.1 ∈ Icc a b ∧ p.2 = γ p.1) ∧
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|) := by
  classical
  let γ := fun x : ℝ => if hx : x ∈ Icc a b then (hcover x hx).choose.2 else 0
  have graph_mem : ∀ x ∈ Icc a b, (x, γ x) ∈ Γ := by
    intro x hx
    obtain ⟨hp, hpx⟩ := (hcover x hx).choose_spec
    have he : (hcover x hx).choose = (x, γ x) := by
      apply Prod.ext
      · exact hpx
      · simp only [γ, hx, ↓reduceDIte]
    rwa [he] at hp
  refine ⟨γ, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have hx := hrange p hp
      have he := eq_of_same_abscissa hLip hp (graph_mem p.1 hx) rfl
      exact ⟨hx, congrArg Prod.snd he⟩
    · rintro ⟨hx, hy⟩
      have he : p = (p.1, γ p.1) := Prod.ext rfl hy
      rw [he]
      exact graph_mem p.1 hx
  · intro x hx y hy
    exact hLip (x, γ x) (graph_mem x hx) (y, γ y) (graph_mem y hy)

end MovingSofaStability
