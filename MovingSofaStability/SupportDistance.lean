module

public import MovingSofaStability.EuclideanGeometry
public import MovingSofaStability.CapCoercivity

/-!
# From convex support bounds to actual Euclidean distance

Uncompiled proof source. The proof uses the Euclidean parallel body K + rB,
whose support is h_K + r. It supplies witnesses in the actual convex set and
does not equate support distance with Hausdorff distance for nonconvex sofas.
-/

@[expose] public section
noncomputable section

open Real Set
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem continuous_norm2 : Continuous (norm2 : Point → ℝ) := by
  unfold norm2 dot
  fun_prop

theorem norm2_smul (a : ℝ) (p : Point) : norm2 (a • p) = |a| * norm2 p := by
  have hsq : norm2 (a • p) ^ 2 = (|a| * norm2 p) ^ 2 := by
    rw [norm2_sq, mul_pow, sq_abs, norm2_sq, dot_smul_left, dot_smul_right]
    ring
  have h₁ := norm2_nonneg (a • p)
  have h₂ := mul_nonneg (abs_nonneg a) (norm2_nonneg p)
  nlinarith

theorem abs_fst_le_norm2 (p : Point) : |p.1| ≤ norm2 p := by
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, abs_nonneg p.1, sq_abs p.1, sq_nonneg p.2]

theorem abs_snd_le_norm2 (p : Point) : |p.2| ≤ norm2 p := by
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, abs_nonneg p.2, sq_abs p.2, sq_nonneg p.1]

/-- Comparison with the product norm is used only for topology and compactness. -/
theorem product_norm_le_norm2 (p : Point) : ‖p‖ ≤ norm2 p := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_fst_le_norm2 p) (abs_snd_le_norm2 p)

theorem norm2_le_two_product_norm (p : Point) : norm2 p ≤ 2 * ‖p‖ := by
  have h₁ := norm_fst_le p
  have h₂ := norm_snd_le p
  rw [Real.norm_eq_abs] at h₁ h₂
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, norm_nonneg p, abs_nonneg p.1, abs_nonneg p.2,
    sq_abs p.1, sq_abs p.2]

def euclideanDisk (r : ℝ) : Set Point := {p | norm2 p ≤ r}

theorem euclideanDisk_isConvexBody {r : ℝ} (hr : 0 ≤ r) : IsConvexBody (euclideanDisk r) := by
  have hclosed : IsClosed (euclideanDisk r) := isClosed_le continuous_norm2 continuous_const
  have hsub : euclideanDisk r ⊆ Icc (-r) r ×ˢ Icc (-r) r := by
    intro p hp
    exact ⟨abs_le.mp ((abs_fst_le_norm2 p).trans hp),
      abs_le.mp ((abs_snd_le_norm2 p).trans hp)⟩
  refine ⟨⟨0, by simpa only [euclideanDisk, mem_setOf_eq, norm2_zero] using hr⟩,
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub, ?_⟩
  intro p hp q hq a b ha hb hab
  change norm2 (a • p + b • q) ≤ r
  have h := norm2_add_le (a • p) (b • q)
  rw [norm2_smul, norm2_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h
  have hpa := mul_le_mul_of_nonneg_left hp ha
  have hqb := mul_le_mul_of_nonneg_left hq hb
  have he : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  linarith

/-- Minkowski sums of nonempty compact convex sets stay in the same class. -/
theorem convexBody_add {K L : Set Point} (hK : IsConvexBody K) (hL : IsConvexBody L) :
    IsConvexBody (K + L) := by
  obtain ⟨p, hp⟩ := hK.1
  obtain ⟨q, hq⟩ := hL.1
  exact ⟨⟨p + q, ⟨p, hp, q, hq, rfl⟩⟩, hK.2.1.add hL.2.1, hK.2.2.add hL.2.2⟩

/-- Euclidean parallel bodies add exactly r to every support value. -/
theorem supp_add_euclideanDisk {K : Set Point} (hK : IsConvexBody K)
    {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : supp (K + euclideanDisk r) t = supp K t + r := by
  have hD := euclideanDisk_isConvexBody hr
  have hsum := convexBody_add hK hD
  obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  have hrad : r • uvec t ∈ euclideanDisk r := by
    change norm2 (r • uvec t) ≤ r
    rw [norm2_smul, norm2_uvec, mul_one, abs_of_nonneg hr]
  apply supp_eq_of_mem hsum.2.1
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    rw [dot_add_left]
    exact add_le_add (dot_le_supp hK.2.1 hq t) ((dot_uvec_le_norm2 z t).trans hz)
  · exact ⟨p, hp, r • uvec t, hrad, rfl⟩
  · rw [dot_add_left, hps, dot_smul_left, dot_uvec_self, mul_one]

/-- Support containment supplies an actual point of the target within Euclidean radius r. -/
theorem directedClose_of_support_le {S T : Set Point} (hS : IsCompact S)
    (hT : IsConvexBody T) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, supp S t ≤ supp T t + r) : DirectedClose r S T := by
  sorry

/-- The support criterion for Euclidean Hausdorff distance between convex bodies. -/
theorem euclideanClose_of_support_bound {K L : Set Point}
    (hK : IsConvexBody K) (hL : IsConvexBody L) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, |supp K t - supp L t| ≤ r) : EuclideanClose r K L := by
  constructor
  · apply directedClose_of_support_le hK.2.1 hL hr
    intro t
    have ht := (abs_le.mp (h t)).2
    linarith
  · apply directedClose_of_support_le hL.2.1 hK hr
    intro t
    have ht := (abs_le.mp (h t)).1
    linarith

/-- A translation preserves compact convexity. -/
theorem convexBody_translate {K : Set Point} (hK : IsConvexBody K) (v : Point) :
    IsConvexBody ((fun p => p + v) '' K) := by
  refine ⟨hK.1.image _, hK.2.1.image (continuous_id.add continuous_const), ?_⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, hK.2.2 hp hq ha hb hab, ?_⟩
  have hv : (a + b) • v = v := by rw [hab, one_smul]
  calc
    (a • p + b • q) + v = (a • p + b • q) + (a + b) • v := by rw [hv]
    _ = a • (p + v) + b • (q + v) := by
      simp only [add_smul, smul_add]
      abel

end MovingSofaStability
