module

public import MovingSofaStability.CapEstimate

/-!
# Constructing an actual cap from two positively turning arcs

Uncompiled proof source. This is a realization theorem, not the assumption
that a proposed scalar function already is a support function. The two arcs
have nonnegative turning densities, a correctly oriented horizontal top edge,
and nonnegative endpoint heights. Their supporting half-planes and the floor
then define a genuine cap, with the asserted upper support at every angle.

Derivative jumps in the densities are permitted. The arcs themselves are
continuous, and only right derivatives are required. A new endpoint vertical
face is allowed: the endpoint height need not vanish.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

structure TurningCapData where
  rightArc : ℝ → Point
  leftArc : ℝ → Point
  rightDensity : ℝ → ℝ
  leftDensity : ℝ → ℝ
  right_continuous : ContinuousOn rightArc (Icc 0 (π / 2))
  left_continuous : ContinuousOn leftArc (Icc 0 (π / 2))
  right_derivative : ∀ t ∈ Ico (0 : ℝ) (π / 2),
    HasDerivWithinAt rightArc (rightDensity t • vvec t) (Ici t) t
  left_derivative : ∀ t ∈ Ico (0 : ℝ) (π / 2),
    HasDerivWithinAt leftArc (-(leftDensity t) • uvec t) (Ici t) t
  right_nonneg : ∀ t ∈ Ico (0 : ℝ) (π / 2), 0 ≤ rightDensity t
  left_nonneg : ∀ t ∈ Ico (0 : ℝ) (π / 2), 0 ≤ leftDensity t
  right_top : (rightArc (π / 2)).2 = 1
  left_top : (leftArc 0).2 = 1
  top_order : (leftArc 0).1 ≤ (rightArc (π / 2)).1
  right_floor : 0 ≤ (rightArc 0).2
  left_floor : 0 ≤ (leftArc (π / 2)).2

namespace TurningCapData

variable (D : TurningCapData)

def support (t : ℝ) : ℝ :=
  if t ≤ π / 2 then dot (D.rightArc t) (uvec t)
  else dot (D.leftArc (t - π / 2)) (uvec t)

def body : Set Point :=
  {p | 0 ≤ p.2} ∩ ⋂ t ∈ Icc (0 : ℝ) π, halfMinus t (D.support t)

@[simp] theorem mem_body (p : Point) :
    p ∈ D.body ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ D.support t := by
  simp [body, halfMinus]

private theorem right_dot_continuous (σ : ℝ) :
    ContinuousOn (fun t => dot (D.rightArc t) (uvec σ)) (Icc (0 : ℝ) (π / 2)) :=
  (continuous_dot (uvec σ)).comp_continuousOn D.right_continuous

private theorem left_dot_continuous (σ : ℝ) :
    ContinuousOn (fun t => dot (D.leftArc t) (uvec σ)) (Icc (0 : ℝ) (π / 2)) :=
  (continuous_dot (uvec σ)).comp_continuousOn D.left_continuous

theorem right_mono {σ a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2)
    (hs : ∀ t ∈ Ico a b, 0 ≤ sin (σ - t)) :
    dot (D.rightArc a) (uvec σ) ≤ dot (D.rightArc b) (uvec σ) := by
  apply le_of_right_deriv_nonneg hab
    ((D.right_dot_continuous σ).mono (Icc_subset_Icc ha hb))
  · intro t ht
    have hd := hasDerivWithinAt_dot (D.right_derivative t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (uvec σ)
    simpa only [dot_smul_left, dot_vvec_uvec'] using hd
  · intro t ht
    exact mul_nonneg (D.right_nonneg t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (hs t ht)

theorem right_anti {σ a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2)
    (hs : ∀ t ∈ Ico a b, sin (σ - t) ≤ 0) :
    dot (D.rightArc b) (uvec σ) ≤ dot (D.rightArc a) (uvec σ) := by
  apply le_of_right_deriv_nonpos hab
    ((D.right_dot_continuous σ).mono (Icc_subset_Icc ha hb))
  · intro t ht
    have hd := hasDerivWithinAt_dot (D.right_derivative t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (uvec σ)
    simpa only [dot_smul_left, dot_vvec_uvec'] using hd
  · intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos
      (D.right_nonneg t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (hs t ht)

theorem left_mono {σ a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2)
    (hc : ∀ t ∈ Ico a b, cos (t - σ) ≤ 0) :
    dot (D.leftArc a) (uvec σ) ≤ dot (D.leftArc b) (uvec σ) := by
  apply le_of_right_deriv_nonneg hab
    ((D.left_dot_continuous σ).mono (Icc_subset_Icc ha hb))
  · intro t ht
    have hd := hasDerivWithinAt_dot (D.left_derivative t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (uvec σ)
    simpa only [dot_smul_left, dot_uvec_uvec] using hd
  · intro t ht
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (D.left_nonneg t ⟨ha.trans ht.1, ht.2.trans_le hb⟩)) (hc t ht)

theorem left_anti {σ a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2)
    (hc : ∀ t ∈ Ico a b, 0 ≤ cos (t - σ)) :
    dot (D.leftArc b) (uvec σ) ≤ dot (D.leftArc a) (uvec σ) := by
  apply le_of_right_deriv_nonpos hab
    ((D.left_dot_continuous σ).mono (Icc_subset_Icc ha hb))
  · intro t ht
    have hd := hasDerivWithinAt_dot (D.left_derivative t ⟨ha.trans ht.1, ht.2.trans_le hb⟩) (uvec σ)
    simpa only [dot_smul_left, dot_uvec_uvec] using hd
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (D.left_nonneg t ⟨ha.trans ht.1, ht.2.trans_le hb⟩)) (hc t ht)

theorem support_left {t : ℝ} (ht : π / 2 ≤ t) :
    D.support t = dot (D.leftArc (t - π / 2)) (uvec t) := by
  rcases ht.lt_or_eq with ht | he
  · simp only [support, if_neg (not_le.mpr ht)]
  · subst t
    simp only [support, if_pos le_rfl, sub_self, dot_uvec_pi_div_two, D.right_top, D.left_top]

theorem right_le_support {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) π)
    (hs : s ∈ Icc (0 : ℝ) (π / 2)) : dot (D.rightArc s) (uvec t) ≤ D.support t := by
  rcases le_or_gt t (π / 2) with htv | htv
  · rw [support, if_pos htv]
    rcases le_total s t with hst | hts
    · exact D.right_mono hs.1 hst htv fun r hr =>
        sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.2]) (by linarith [hr.1, hs.1, ht.2])
    · exact D.right_anti ht.1 hts hs.2 fun r hr =>
        sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hr.1]) (by linarith [hr.2, ht.1, pi_pos])
  · rw [D.support_left htv.le]
    have h1 := D.right_mono (σ := t) hs.1 hs.2 le_rfl (fun r hr =>
      sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.2]) (by linarith [hr.1, hs.1, ht.2]))
    have h2 : dot (D.rightArc (π / 2)) (uvec t) ≤ dot (D.leftArc 0) (uvec t) := by
      have hm := mul_le_mul_of_nonpos_right D.top_order
        (cos_nonpos_of_pi_div_two_le_of_le htv.le (by linarith [ht.2, pi_pos]))
      simp only [dot, uvec, D.right_top, D.left_top]
      linarith only [hm]
    have h3 := D.left_mono (σ := t) le_rfl (by linarith : 0 ≤ t - π / 2)
      (by linarith [ht.2] : t - π / 2 ≤ π / 2) (fun r hr => by
        rw [← cos_neg]
        exact cos_nonpos_of_pi_div_two_le_of_le (by linarith [hr.2]) (by linarith [hr.1, ht.2, pi_pos]))
    exact h1.trans (h2.trans h3)

theorem left_le_support {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) π)
    (hs : s ∈ Icc (0 : ℝ) (π / 2)) : dot (D.leftArc s) (uvec t) ≤ D.support t := by
  rcases le_or_gt (π / 2) t with hvt | hvt
  · rw [D.support_left hvt]
    rcases le_total s (t - π / 2) with hst | hts
    · exact D.left_mono hs.1 hst (by linarith [ht.2]) fun r hr => by
        rw [← cos_neg]
        exact cos_nonpos_of_pi_div_two_le_of_le (by linarith [hr.2]) (by linarith [hr.1, hs.1, ht.2, pi_pos])
    · exact D.left_anti (by linarith) hts hs.2 fun r hr =>
        cos_nonneg_of_mem_Icc ⟨by linarith [hr.1], by linarith [hr.2, ht.1]⟩
  · rw [support, if_pos hvt.le]
    have h1 := D.left_anti (σ := t) le_rfl hs.1 hs.2 (fun r hr =>
      cos_nonneg_of_mem_Icc ⟨by linarith [hr.1], by linarith [hr.2, ht.1]⟩)
    have h2 : dot (D.leftArc 0) (uvec t) ≤ dot (D.rightArc (π / 2)) (uvec t) := by
      have hm := mul_le_mul_of_nonneg_right D.top_order
        (cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], hvt.le⟩)
      simp only [dot, uvec, D.right_top, D.left_top]
      linarith only [hm]
    have h3 := D.right_anti (σ := t) ht.1 hvt.le le_rfl (fun r hr =>
      sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hr.1]) (by linarith [hr.2, ht.1, pi_pos]))
    exact h1.trans (h2.trans h3)

theorem right_height {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    0 ≤ (D.rightArc t).2 := by
  have h := D.right_mono (σ := π / 2) le_rfl ht.1 ht.2 (fun r hr =>
    sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.2]) (by linarith [hr.1, pi_pos]))
  rw [dot_uvec_pi_div_two, dot_uvec_pi_div_two] at h
  exact D.right_floor.trans h

theorem left_height {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    0 ≤ (D.leftArc t).2 := by
  have h := D.left_anti (σ := π / 2) ht.1 ht.2 le_rfl (fun r hr =>
    cos_nonneg_of_mem_Icc ⟨by linarith [hr.1, ht.1], by linarith [hr.2, pi_pos]⟩)
  rw [dot_uvec_pi_div_two, dot_uvec_pi_div_two] at h
  exact D.left_floor.trans h

theorem right_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : D.rightArc t ∈ D.body :=
  (D.mem_body _).mpr ⟨D.right_height ht, fun _ hs => D.right_le_support hs ht⟩

theorem left_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : D.leftArc t ∈ D.body :=
  (D.mem_body _).mpr ⟨D.left_height ht, fun _ hs => D.left_le_support hs ht⟩

theorem floor_projection_mem {p : Point} (hp : p ∈ D.body) : (p.1, 0) ∈ D.body := by
  rw [D.mem_body] at hp ⊢
  refine ⟨le_rfl, ?_⟩
  intro t ht
  have hy := mul_nonneg hp.1 (sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
  have hh := hp.2 t ht
  simp only [dot, uvec, zero_mul, add_zero] at hh ⊢
  linarith only [hh, hy]

@[simp] theorem support_top : D.support (π / 2) = 1 := by
  simp only [support, if_pos le_rfl, dot_uvec_pi_div_two, D.right_top]

theorem body_bounds {p : Point} (hp : p ∈ D.body) :
    -D.support π ≤ p.1 ∧ p.1 ≤ D.support 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [D.mem_body] at hp
  have h0 := hp.2 0 ⟨le_rfl, pi_pos.le⟩
  have h1 := hp.2 (π / 2) ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have h2 := hp.2 π ⟨pi_pos.le, le_rfl⟩
  rw [dot_uvec_zero] at h0
  rw [dot_uvec_pi_div_two, D.support_top] at h1
  simp only [dot, uvec, cos_pi, sin_pi, mul_neg_one, mul_zero, add_zero] at h2
  exact ⟨by linarith, h0, hp.1, h1⟩

theorem body_halfplanes : D.body =
    halfMinus (3 * π / 2) 0 ∩ ⋂ t ∈ Icc (0 : ℝ) π, halfMinus t (D.support t) := by
  ext p
  simp only [body, mem_inter_iff, mem_setOf_eq, halfMinus, dot_uvec_three_pi_div_two]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

theorem body_closed : IsClosed D.body := by
  rw [D.body_halfplanes]
  exact (isClosed_halfMinus _ _).inter (isClosed_biInter fun _ _ => isClosed_halfMinus _ _)

theorem body_convex : Convex ℝ D.body := by
  rw [D.body_halfplanes]
  exact (convex_halfMinus _ _).inter (convex_iInter₂ fun _ _ => convex_halfMinus _ _)

theorem body_convexBody : IsConvexBody D.body := by
  refine ⟨⟨_, D.right_mem ⟨le_rfl, by linarith [pi_pos]⟩⟩, ?_, D.body_convex⟩
  exact Metric.isCompact_of_isClosed_isBounded D.body_closed
    (ms_isBounded_of_bounds _ _ _ _ fun p hp => D.body_bounds hp)

theorem body_support {t : ℝ} (ht : t ∈ Icc (0 : ℝ) π) : supp D.body t = D.support t := by
  have hK := D.body_convexBody
  refine le_antisymm (supp_le_of_forall hK.1 (fun p hp => (D.mem_body p).mp hp |>.2 t ht)) ?_
  rcases le_or_gt t (π / 2) with htv | htv
  · rw [support, if_pos htv]
    exact dot_le_supp hK.2.1 (D.right_mem ⟨ht.1, htv⟩) t
  · rw [D.support_left htv.le]
    exact dot_le_supp hK.2.1 (D.left_mem ⟨by linarith, by linarith [ht.2]⟩) t

theorem body_floor_support : supp D.body (3 * π / 2) = 0 := by
  have hK := D.body_convexBody
  have hp := D.floor_projection_mem (D.right_mem ⟨le_rfl, by linarith [pi_pos]⟩)
  apply le_antisymm
  · apply supp_le_of_forall hK.1
    intro p hp
    rw [dot_uvec_three_pi_div_two]
    exact neg_nonpos.mpr ((D.mem_body p).mp hp).1
  · simpa only [dot_uvec_three_pi_div_two, neg_zero] using
      dot_le_supp hK.2.1 hp (3 * π / 2)

/-- The actual cap, not just a formal perturbation of a support function. -/
theorem body_isCap : IsCap D.body (π / 2) := by
  have ht : supp D.body (π / 2) = 1 :=
    (D.body_support ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).trans D.support_top
  refine ⟨⟨by linarith [pi_pos], le_rfl⟩, D.body_convexBody, ht, ht, ?_, D.body_floor_support, ?_⟩
  · simpa only [show π / 2 + π = 3 * π / 2 by ring] using D.body_floor_support
  · refine ⟨Option (Icc (0 : ℝ) π), fun i => i.elim (3 * π / 2) (fun t => t.1),
      fun i => i.elim 0 (fun t => D.support t.1), ?_, ?_⟩
    · intro i
      rcases i with _ | ⟨t, ht⟩
      · exact Or.inr (Or.inr rfl)
      · rcases le_or_gt t (π / 2) with h | h
        · exact Or.inl (Or.inl ⟨ht.1, h⟩)
        · exact Or.inl (Or.inr ⟨h.le, by linarith [ht.2]⟩)
    · rw [D.body_halfplanes]
      ext p
      simp only [mem_inter_iff, mem_iInter, Option.forall, Option.elim, Subtype.forall]

end TurningCapData
end MovingSofaQuantitative
