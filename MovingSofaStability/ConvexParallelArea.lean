module

public import MovingSofaStability.LocalSofaRecovery
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A linear area bound for an outer parallel layer

Uncompiled proof source. One fixed interior disk bounds the Euclidean parallel
body by a homothetic copy. The area calculation uses two-dimensional Haar
scaling and requires no smoothness or perimeter formula.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def homotheticBody (K : Set Point) (z : Point) (λ : ℝ) : Set Point :=
  (fun p => λ • (p - z) + z) '' K

theorem homotheticBody_convexBody {K : Set Point} (hK : IsConvexBody K) (z : Point) (λ : ℝ) :
    IsConvexBody (homotheticBody K z λ) := by
  refine ⟨hK.1.image _, hK.2.1.image (by fun_prop), ?_⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, hK.2.2 hp hq ha hb hab, ?_⟩
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith

theorem homotheticBody_support {K : Set Point} (hK : IsConvexBody K) (z : Point)
    {λ : ℝ} (hλ : 0 ≤ λ) (t : ℝ) :
    supp (homotheticBody K z λ) t = λ * supp K t + (1 - λ) * dot z (uvec t) := by
  have hC := homotheticBody_convexBody hK z λ
  obtain ⟨p, hp, he⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  apply supp_eq_of_mem hC.2.1
  · rintro _ ⟨q, hq, rfl⟩
    have h := mul_le_mul_of_nonneg_left (dot_le_supp hK.2.1 hq t) hλ
    rw [dot_add_left, dot_smul_left, dot_sub_left]
    linarith
  · exact mem_image_of_mem _ hp
  · rw [dot_add_left, dot_smul_left, dot_sub_left, he]
    ring

theorem area_homotheticBody (K : Set Point) (z : Point) (λ : ℝ) :
    area (homotheticBody K z λ) = λ ^ 2 * area K := by
  have hdim : Module.finrank ℝ Point = 2 := by
    simp [Point, Module.finrank_prod]
  have he := addHaar_image_homothety (volume : Measure Point) z λ K
  change volume (homotheticBody K z λ) = _ at he
  unfold area
  rw [he, hdim, abs_of_nonneg (sq_nonneg λ), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg λ)]

/-- A fixed inscribed ball provides a support margin in every direction. -/
theorem support_margin_of_ball {K : Set Point} (hK : IsConvexBody K) {z : Point} {r : ℝ}
    (hr : 0 ≤ r) (hball : euclideanBall z r ⊆ K) (t : ℝ) :
    dot z (uvec t) + r ≤ supp K t := by
  have hp : z + r • uvec t ∈ euclideanBall z r := by
    change norm2 (z - (z + r • uvec t)) ≤ r
    rw [show z - (z + r • uvec t) = -(r • uvec t) by abel,
      norm2_neg, norm2_smul, norm2_uvec, abs_of_nonneg hr, mul_one]
  have he := dot_le_supp hK.2.1 (hball hp) t
  simpa only [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] using he

/-- The parallel body fits inside a dilation by factor 1+d/r about the ball center. -/
theorem parallel_subset_homothetic {K : Set Point} (hK : IsConvexBody K) {z : Point}
    {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hball : euclideanBall z r ⊆ K) :
    K + euclideanDisk d ⊆ homotheticBody K z (1 + d / r) := by
  intro p hp
  apply (mem_iff_forall_dot_le_supp (homotheticBody_convexBody hK z (1 + d / r)) p).2
  intro t
  have hsum := convexBody_add hK (euclideanDisk_isConvexBody hd)
  have h1 := dot_le_supp hsum.2.1 hp t
  rw [supp_add_euclideanDisk hK hd] at h1
  have h2 := support_margin_of_ball hK hr.le hball t
  have hratio : 0 ≤ d / r := div_nonneg hd hr.le
  have hm := mul_le_mul_of_nonneg_left h2 hratio
  rw [homotheticBody_support hK z (by positivity)]
  have hc : d / r * r = d := div_mul_cancel₀ _ hr.ne'
  nlinarith

/-- The excess area of an arbitrary subset of a thin parallel layer is linear in thickness. -/
theorem area_parallel_layer_le {K : Set Point} (hK : IsConvexBody K) {z : Point} {r d : ℝ}
    (hr : 0 < r) (hd : d ∈ Icc (0 : ℝ) 1) (hball : euclideanBall z r ⊆ K)
    {E : Set Point} (hE : E ⊆ (K + euclideanDisk d) \ K) :
    area E ≤ area K * (2 / r + 1 / r ^ 2) * d := by
  let λ := 1 + d / r
  let C := homotheticBody K z λ
  have hCK := homotheticBody_convexBody hK z λ
  have hsub := parallel_subset_homothetic hK hr hd.1 hball
  have hKsum : K ⊆ K + euclideanDisk d := by
    intro p hp
    exact ⟨p, hp, 0, by simpa only [euclideanDisk, mem_setOf_eq, norm2_zero] using hd.1,
      add_zero p⟩
  have hKC : K ⊆ C := hKsum.trans hsub
  have hEC : E ⊆ C \ K := fun p hp => ⟨hsub (hE hp).1, (hE hp).2⟩
  have he := area_mono_of_finite hEC
    (volume_ne_top_of_subset sdiff_subset hCK.2.1.measure_lt_top.ne)
  have harea := area_inter_add_sdiff (S := C) hK.2.1.measurableSet hCK.2.1.measure_lt_top.ne
  rw [inter_eq_right.mpr hKC] at harea
  have hscale : area C = λ ^ 2 * area K := area_homotheticBody K z λ
  have hK0 : 0 ≤ area K := ENNReal.toReal_nonneg
  have hd2 : d ^ 2 ≤ d := by nlinarith [hd.1, hd.2]
  have hpoly : λ ^ 2 - 1 ≤ (2 / r + 1 / r ^ 2) * d := by
    dsimp [λ]
    field_simp [hr.ne']
    nlinarith [mul_nonneg hd.1 hr.le]
  have hm := mul_le_mul_of_nonneg_left hpoly hK0
  nlinarith

/-- Every fixed convex body with interior has a uniform linear outer-layer bound. -/
theorem exists_parallel_layer_constant {K : Set Point} (hK : IsConvexBody K)
    (hint : (interior K).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ d ∈ Icc (0 : ℝ) 1, ∀ E : Set Point,
      E ⊆ (K + euclideanDisk d) \ K → area E ≤ A * d := by
  obtain ⟨z, r, hr, hb⟩ := exists_euclideanBall_subset_of_interior hint
  let A := 1 + area K * (2 / r + 1 / r ^ 2)
  have ha : 0 ≤ area K * (2 / r + 1 / r ^ 2) := by
    have hk : 0 ≤ area K := ENNReal.toReal_nonneg
    positivity
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro d hd E hE
  have he := area_parallel_layer_le hK hr hd hb hE
  have hm : area K * (2 / r + 1 / r ^ 2) * d ≤ A * d := by dsimp [A]; nlinarith [hd.1]
  exact he.trans hm

end MovingSofaStability
