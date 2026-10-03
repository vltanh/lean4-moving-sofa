module

public import SofaUniqueness.FloatingVariation
public import MovingSofa.Angle.HorizontalSide

/-!
# Uniform control of the structured pinned-strip move

For omega<pi/2 a standard cap contains O and its top corner o. Raising either
pinned height by epsilon simultaneously moves the corresponding lower strip.
For 0<=epsilon<=1 the resulting assigned cap K' satisfies

  (1-epsilon) K + epsilon o subset K' subset (1+epsilon) K.

This specific sandwich, rather than a false general diameter-to-height
perturbation estimate, gives a mesh-independent support bound. Feasibility as
a translated polygon cap is supplied by the existing Lemma 3.4.8. Width one
then determines the normalization translation directly.

Uncompiled source. No admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa

namespace SofaUniqueness

/-- The assigned height at a pinned normal before subtracting the unit width. -/
theorem pinned_support_value {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {s : ℝ} (hs : s = Θ.ω ∨ s = π / 2) : supp K s = 1 := by
  rcases hs with rfl | rfl
  · exact hK.1.2.2.1
  · exact hK.1.2.2.2.1

/-- Both scalar products of the common top corner with the pinned normals
are exactly one. -/
theorem pinned_corner_dot {Θ : AngleSet} {s : ℝ}
    (hs : s = Θ.ω ∨ s = π / 2) : dot (oPt Θ.ω) (uvec s) = 1 := by
  rcases hs with rfl | rfl
  · exact mpc_oPt_dot_uvec Θ.hω
  · rw [mpc_dot_uvec_pi_div_two, mpc_oPt_snd]

/-- The common origin makes every upper support nonnegative. -/
theorem pinned_support_nonneg {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) (s : ℝ) : 0 ≤ supp K s := by
  have h := dot_le_supp hK.1.2.1.2.1 (ang_cap_origin_mem hK.1 hω) s
  simpa only [dot_zero_left] using h

/-- Contracting toward the common top corner produces points of the moved
assigned cap. The statement covers both distinct pinned normals. -/
theorem pinned_contract_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ K) :
    (1 - ε) • p + ε • oPt Θ.ω ∈ floatingCap Θ K t ε := by
  classical
  have ho := mpc_oPt_mem hK hω
  have hcombo : (1 - ε) • p + ε • oPt Θ.ω ∈ K :=
    hK.1.2.1.2.2 hp ho (by linarith [hε.2]) hε.1 (by ring)
  change _ ∈ capH Θ (Function.update (supp K) t (supp K t + ε))
  rw [mpc_mem_capH]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have h := dot_le_supp hK.1.2.1.2.1 hcombo s
    by_cases hst : s = t
    · subst s
      rw [Function.update_self]
      linarith [hε.1]
    · rw [Function.update_of_ne hst]
      exact h
  · by_cases hst : Θ.ω = t
    · rw [hst, Function.update_self, pinned_support_value hK ht]
      have hp0 : 0 ≤ dot p (uvec t) := by
        rw [← hst]
        exact (mpc_cap_nonneg hK.1 hp).2
      rw [dot_add_left, dot_smul_left, dot_smul_left, pinned_corner_dot ht]
      nlinarith [hε.2]
    · rw [Function.update_of_ne hst, hK.1.2.2.1]
      have h := (mpc_cap_nonneg hK.1 hcombo).2
      simpa only [sub_self] using h
  · by_cases hst : π / 2 = t
    · rw [hst, Function.update_self, pinned_support_value hK ht]
      have hp0 : 0 ≤ dot p (uvec t) := by
        rw [← hst, mpc_dot_uvec_pi_div_two]
        exact (mpc_cap_nonneg hK.1 hp).1
      rw [dot_add_left, dot_smul_left, dot_smul_left, pinned_corner_dot ht]
      nlinarith [hε.2]
    · rw [Function.update_of_ne hst, hK.1.2.2.2.1]
      have h := (mpc_cap_nonneg hK.1 hcombo).1
      simpa only [sub_self, mpc_dot_uvec_pi_div_two] using h

/-- Contracting the moved assigned cap toward the common origin by
1/(1+epsilon) puts it back in the original cap. -/
theorem pinned_div_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : 0 ≤ ε)
    {p : ℝ × ℝ} (hp : p ∈ floatingCap Θ K t ε) :
    (1 / (1 + ε)) • p ∈ K := by
  classical
  have hden : 0 < 1 + ε := by linarith
  change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
  rw [mpc_mem_capH] at hp
  rw [mpc_polycap_mem_iff hK]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hu := hp.1 s hs
    rw [dot_smul_left, one_div, inv_mul_eq_div, div_le_iff₀ hden]
    by_cases hst : s = t
    · subst s
      rw [Function.update_self, pinned_support_value hK ht] at hu
      rw [pinned_support_value hK ht]
      nlinarith
    · rw [Function.update_of_ne hst] at hu
      have hnonneg := pinned_support_nonneg hK hω s
      nlinarith
  · have hlo : 0 ≤ dot p (uvec Θ.ω) := by
      have h := hp.2.1
      by_cases hst : Θ.ω = t
      · rw [hst, Function.update_self, pinned_support_value hK ht] at h ⊢
        linarith
      · rw [Function.update_of_ne hst, hK.1.2.2.1] at h
        linarith
    rw [dot_smul_left]
    exact mul_nonneg (by positivity) hlo
  · have hlo : 0 ≤ dot p (uvec (π / 2)) := by
      have h := hp.2.2
      by_cases hst : π / 2 = t
      · rw [hst, Function.update_self, pinned_support_value hK ht] at h ⊢
        linarith
      · rw [Function.update_of_ne hst, hK.1.2.2.2.1] at h
        linarith
    rw [dot_smul_left]
    exact mul_nonneg (by positivity) hlo

/-- A bounded-support consequence of the structured contraction sandwich.
It is independent of the number or spacing of polygon normals. -/
theorem pinned_raw_support_bound {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε R : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R) (s : ℝ) :
    |supp (floatingCap Θ K t ε) s - supp K s| ≤ 2 * R * ε := by
  have hcpt : IsCompact (floatingCap Θ K t ε) := mpc_isCompact_capH Θ _
  obtain ⟨q, hq, hqs⟩ := exists_dot_eq_supp hK.1.2.1.2.1 hK.1.2.1.1 s
  have hmem := pinned_contract_mem hK hω ht hε hq
  have hne : (floatingCap Θ K t ε).Nonempty := ⟨_, hmem⟩
  have hupper : supp (floatingCap Θ K t ε) s ≤ (1 + ε) * supp K s := by
    apply nef_supp_le hne
    intro p hp
    have h := dot_le_supp hK.1.2.1.2.1 (pinned_div_mem hK hω ht hε.1 hp) s
    rw [dot_smul_left, one_div, inv_mul_eq_div, div_le_iff₀ (by linarith : 0 < 1 + ε)] at h
    nlinarith
  have hlower := dot_le_supp hcpt hmem s
  rw [dot_add_left, dot_smul_left, dot_smul_left, hqs] at hlower
  have ho := mpc_oPt_mem hK hω
  have hodot : -R ≤ dot (oPt Θ.ω) (uvec s) := by
    have h := dot_le_supp hK.1.2.1.2.1 ho (s + π)
    rw [mpc_dot_uvec_add_pi] at h
    have hb := (abs_le.mp (hsupp (s + π))).2
    linarith
  have hKs := abs_le.mp (hsupp s)
  rw [abs_le]
  constructor <;> nlinarith [hε.1]

/-- An actual width-one translated cap fitting between the assigned two strip
bounds has exactly those two supports: there is no hidden strip slack. -/
theorem translated_strip_support {Θ : AngleSet} {C : Set (ℝ × ℝ)}
    (hC : IsPolygonCap Θ C) (v : ℝ × ℝ) {s a : ℝ}
    (hs : s = Θ.ω ∨ s = π / 2)
    (hlo : ∀ p ∈ (fun q => q + v) '' C, a ≤ dot p (uvec s))
    (hhi : ∀ p ∈ (fun q => q + v) '' C, dot p (uvec s) ≤ a + 1) :
    dot v (uvec s) = a := by
  have hc := hC.1.2.1
  have htop : supp C s = 1 := pinned_support_value hC hs
  have hbot : supp C (s + π) = 0 := by
    rcases hs with rfl | rfl
    · exact hC.1.2.2.2.2.1
    · rw [show π / 2 + π = 3 * π / 2 by ring]
      exact hC.1.2.2.2.2.2.1
  obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hc.2.1 hc.1 s
  obtain ⟨q, hq, hqs⟩ := exists_dot_eq_supp hc.2.1 hc.1 (s + π)
  rw [htop] at hps
  rw [hbot, mpc_dot_uvec_add_pi] at hqs
  have hu := hhi (p + v) ⟨p, hp, rfl⟩
  have hl := hlo (q + v) ⟨q, hq, rfl⟩
  rw [dot_add_left, hps] at hu
  rw [dot_add_left] at hl
  linarith

/-- The normalization displacement of a pinned move has uniformly controlled
scalar products. The denominator cos(omega) is fixed, not a mesh sine. -/
theorem pinned_translation_bound {Θ : AngleSet} {K C : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C) (hω : Θ.ω < π / 2)
    {t ε : ℝ} (ht : t = Θ.ω ∨ t = π / 2) (hε : 0 ≤ ε)
    (v : ℝ × ℝ) (hset : floatingCap Θ K t ε = (fun p => p + v) '' C) (s : ℝ) :
    |dot v (uvec s)| ≤ (2 / cos Θ.ω + 1) * ε := by
  classical
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hsin : 0 ≤ sin Θ.ω := sin_nonneg_of_nonneg_of_le_pi Θ.hω.1.le
    (by linarith [hω, pi_pos])
  let a : ℝ → ℝ := fun r => Function.update (supp K) t (supp K t + ε) r - 1
  have ha : ∀ r, (r = Θ.ω ∨ r = π / 2) → a r ∈ Icc (0 : ℝ) ε := by
    intro r hr
    dsimp [a]
    by_cases hrt : r = t
    · subst r
      rw [Function.update_self, pinned_support_value hK ht]
      constructor <;> linarith
    · rw [Function.update_of_ne hrt, pinned_support_value hK hr]
      constructor <;> linarith
  have hv : ∀ r, (r = Θ.ω ∨ r = π / 2) → dot v (uvec r) = a r := by
    intro r hr
    apply translated_strip_support hC v hr
    · intro p hp
      rw [← hset] at hp
      change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
      rw [mpc_mem_capH] at hp
      rcases hr with rfl | rfl
      · exact hp.2.1
      · exact hp.2.2
    · intro p hp
      rw [← hset] at hp
      change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
      rw [mpc_mem_capH] at hp
      have hrd : r ∈ Θ.diamond := by
        rcases hr with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have h := hp.1 r hrd
      dsimp [a]
      linarith
  have hy := ha (π / 2) (Or.inr rfl)
  have hx := ha Θ.ω (Or.inl rfl)
  rw [← hv (π / 2) (Or.inr rfl), mpc_dot_uvec_pi_div_two] at hy
  rw [← hv Θ.ω (Or.inl rfl)] at hx
  have hyabs : |v.2| ≤ ε := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hxy : |v.1| ≤ 2 * ε / cos Θ.ω := by
    rw [le_div_iff₀ hcos]
    simp only [dot, uvec] at hx
    have hs := sin_le_one Θ.ω
    have hprod : v.2 * sin Θ.ω ≤ ε := by nlinarith [hy.1, hy.2]
    rw [← abs_of_pos hcos, ← abs_mul, abs_le]
    constructor <;> nlinarith [hx.1, hx.2, hy.1]
  have hdot := mpc_abs_dot_uvec_le v s
  have hbound : |v.1| + |v.2| ≤ (2 / cos Θ.ω + 1) * ε := by
    have heq : 2 * ε / cos Θ.ω + ε = (2 / cos Θ.ω + 1) * ε := by ring
    rw [← heq]
    exact add_le_add hxy hyabs
  exact hdot.trans hbound

/-- Uniform support error AFTER normalization to the original two strips. -/
theorem pinned_normalized_support_bound {Θ : AngleSet} {K C : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C) (hω : Θ.ω < π / 2)
    {t ε R : ℝ} (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R)
    (v : ℝ × ℝ) (hset : floatingCap Θ K t ε = (fun p => p + v) '' C) (s : ℝ) :
    |supp C s - supp K s| ≤ (2 * R + 2 / cos Θ.ω + 1) * ε := by
  have hraw := pinned_raw_support_bound hK hω ht hε hR hsupp s
  have hv := pinned_translation_bound hK hC hω ht hε.1 v hset s
  have heq : supp (floatingCap Θ K t ε) s = supp C s + dot v (uvec s) := by
    rw [hset]
    exact supp_translate C v s hC.1.2.1.2.1 hC.1.2.1.1
  rw [heq] at hraw
  have htri := abs_sub (supp C s + dot v (uvec s) - supp K s) (dot v (uvec s))
  have halg : supp C s + dot v (uvec s) - supp K s - dot v (uvec s) =
      supp C s - supp K s := by ring
  rw [halg] at htri
  nlinarith

end SofaUniqueness
