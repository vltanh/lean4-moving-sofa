module

public import MovingSofaUniqueness.Rigid

/-!
# Euclidean closeness of sets, the stability statements, and the terminal area comparison

The Euclidean distance between points and the closeness of sets (`EuclideanClose`); the deficit
and the normalization of a moving sofa and the two stability statements (`sofaDeficit`,
`normalizedSofa`, `UnrestrictedStability`, `TerminalAngleStability`); and the comparison of areas
that bounds the terminal angle of a partial motion (`terminal_region_comparison`).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-!
## Euclidean distance and closeness of sets

The product `ℝ × ℝ` carries the sup metric, so distances use the Euclidean norm `norm2`.
`EuclideanClose r S T` gives both directed bounds by point witnesses: for nonempty compact sets it
says that their Euclidean Hausdorff distance is at most `r`. Unlike a bound on support functions,
it does not identify a nonconvex set with its convex hull.
-/

/-- A point of the plane. -/
abbrev Point := ℝ × ℝ

/-- The Euclidean distance between two points. -/
def euclideanDist (p q : Point) : ℝ := norm2 (p - q)

/-- The Euclidean norm is nonnegative. -/
theorem norm2_nonneg (p : Point) : 0 ≤ norm2 p := Real.sqrt_nonneg _

/-- The square of the Euclidean norm of `p` is `p · p`. -/
theorem norm2_sq (p : Point) : norm2 p ^ 2 = dot p p :=
  Real.sq_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

/-- The zero vector has norm zero. -/
@[simp] theorem norm2_zero : norm2 (0 : Point) = 0 := by
  simp [norm2, dot]

/-- Negation preserves the Euclidean norm. -/
@[simp] theorem norm2_neg (p : Point) : norm2 (-p) = norm2 p := by
  simp [norm2, dot]

/-- The Cauchy–Schwarz inequality. -/
theorem dot_le_norm2_mul (p q : Point) : dot p q ≤ norm2 p * norm2 q := by
  rw [norm2, norm2, ← Real.sqrt_mul ((sq_nonneg _).trans_eq (norm2_sq p))]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  simp only [dot]
  nlinarith [sq_nonneg (p.1 * q.2 - p.2 * q.1)]

/-- The triangle inequality for the Euclidean norm. -/
theorem norm2_add_le (p q : Point) : norm2 (p + q) ≤ norm2 p + norm2 q := by
  refine (Real.sqrt_le_left (add_nonneg (norm2_nonneg p) (norm2_nonneg q))).2 ?_
  have h : dot (p + q) (p + q) = dot p p + 2 * dot p q + dot q q := by
    simp only [dot, Prod.fst_add, Prod.snd_add]
    ring
  nlinarith [norm2_sq p, norm2_sq q, dot_le_norm2_mul p q]

/-- Rotations preserve the Euclidean norm. -/
@[simp] theorem norm2_rot (a : ℝ) (p : Point) : norm2 (rot a p) = norm2 p := by
  simp only [norm2, dot, rot]
  congr 1
  linear_combination (p.1 ^ 2 + p.2 ^ 2) * cos_sq_add_sin_sq a

/-- The unit vector `u_t` has norm one. -/
@[simp] theorem norm2_uvec (t : ℝ) : norm2 (uvec t) = 1 := by
  simp [norm2, dot_uvec_self]

/-- The component of a vector along a unit vector is at most its norm. -/
theorem dot_uvec_le_norm2 (p : Point) (t : ℝ) : dot p (uvec t) ≤ norm2 p := by
  simpa only [norm2_uvec, mul_one] using dot_le_norm2_mul p (uvec t)

/-- The Euclidean distance is nonnegative. -/
theorem euclideanDist_nonneg (p q : Point) : 0 ≤ euclideanDist p q :=
  norm2_nonneg _

/-- A point is at distance zero from itself. -/
@[simp] theorem euclideanDist_self (p : Point) : euclideanDist p p = 0 := by
  simp [euclideanDist]

/-- The Euclidean distance is symmetric. -/
theorem euclideanDist_comm (p q : Point) : euclideanDist p q = euclideanDist q p := by
  rw [euclideanDist, euclideanDist, ← norm2_neg, neg_sub]

/-- The triangle inequality for the Euclidean distance. -/
theorem euclideanDist_triangle (p q r : Point) :
    euclideanDist p r ≤ euclideanDist p q + euclideanDist q r := by
  simpa only [euclideanDist, sub_add_sub_cancel] using norm2_add_le (p - q) (q - r)

/-- Two points are at distance zero exactly when they are equal. -/
@[simp] theorem euclideanDist_eq_zero_iff (p q : Point) : euclideanDist p q = 0 ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ euclideanDist_self p⟩
  have hs : dot (p - q) (p - q) = 0 := by
    rw [← norm2_sq, show norm2 (p - q) = 0 from h, sq, mul_zero]
  obtain ⟨h1, h2⟩ := mul_self_add_mul_self_eq_zero.1 hs
  exact Prod.ext (sub_eq_zero.1 h1) (sub_eq_zero.1 h2)

/-- Rigid motions preserve the Euclidean distance. -/
@[simp] theorem euclideanDist_rigid (g : Rigid) (p q : Point) :
    euclideanDist (g p) (g q) = euclideanDist p q := by
  have h : g p - g q = rot g.angle (p - q) := by
    ext <;> simp [Rigid.apply, rot] <;> ring
  rw [euclideanDist, h, norm2_rot, euclideanDist]

/-- Every point of `S` lies within Euclidean distance `r` of a point of `T`. -/
def DirectedClose (r : ℝ) (S T : Set Point) : Prop :=
  ∀ p ∈ S, ∃ q ∈ T, euclideanDist p q ≤ r

/-- Each of `S` and `T` lies within Euclidean distance `r` of the other: for nonempty compact sets,
their Euclidean Hausdorff distance is at most `r`. -/
def EuclideanClose (r : ℝ) (S T : Set Point) : Prop :=
  DirectedClose r S T ∧ DirectedClose r T S

/-- A directed bound holds for every larger radius. -/
theorem DirectedClose.mono {r R : ℝ} {S T : Set Point}
    (h : DirectedClose r S T) (hr : r ≤ R) : DirectedClose R S T :=
  fun p hp => (h p hp).imp fun _ hq => ⟨hq.1, hq.2.trans hr⟩

/-- Directed bounds add along a chain of sets. -/
theorem DirectedClose.trans {r s : ℝ} {S T U : Set Point}
    (hST : DirectedClose r S T) (hTU : DirectedClose s T U) : DirectedClose (r + s) S U := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hST p hp
  obtain ⟨u, hu, hqu⟩ := hTU q hq
  exact ⟨u, hu, (euclideanDist_triangle p q u).trans (add_le_add hpq hqu)⟩

/-- A set is close to itself for every nonnegative radius. -/
theorem EuclideanClose.refl (S : Set Point) {r : ℝ} (hr : 0 ≤ r) : EuclideanClose r S S :=
  have h : DirectedClose r S S := fun p hp => ⟨p, hp, by simpa using hr⟩
  ⟨h, h⟩

/-- Closeness is symmetric. -/
theorem EuclideanClose.symm {r : ℝ} {S T : Set Point} (h : EuclideanClose r S T) :
    EuclideanClose r T S := ⟨h.2, h.1⟩

/-- Closeness holds for every larger radius. -/
theorem EuclideanClose.mono {r R : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (hr : r ≤ R) : EuclideanClose R S T :=
  ⟨h.1.mono hr, h.2.mono hr⟩

/-- Closeness radii add along a chain of sets. -/
theorem EuclideanClose.trans {r s : ℝ} {S T U : Set Point}
    (hST : EuclideanClose r S T) (hTU : EuclideanClose s T U) :
    EuclideanClose (r + s) S U :=
  ⟨hST.1.trans hTU.1, by simpa only [add_comm] using hTU.2.trans hST.2⟩

/-- Closeness with radius zero is equality, also for nonconvex sets. -/
theorem EuclideanClose.eq_of_zero {S T : Set Point} (h : EuclideanClose 0 S T) : S = T := by
  have sub {A B : Set Point} (hAB : DirectedClose 0 A B) : A ⊆ B := fun p hp => by
    obtain ⟨q, hq, hd⟩ := hAB p hp
    rwa [(euclideanDist_eq_zero_iff p q).1 (hd.antisymm (euclideanDist_nonneg p q))]
  exact (sub h.1).antisymm (sub h.2)

/-- Closeness bounds the difference of the support functions. The converse fails for nonconvex
sets. -/
theorem EuclideanClose.abs_supp_sub_le {r : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (hS : IsCompact S) (hT : IsCompact T)
    (hneS : S.Nonempty) (hneT : T.Nonempty) (t : ℝ) :
    |supp S t - supp T t| ≤ r := by
  have forward {A B : Set Point} (ha : IsCompact A) (hb : IsCompact B)
      (hne : A.Nonempty) (hab : DirectedClose r A B) : supp A t - supp B t ≤ r := by
    obtain ⟨p, hp, he⟩ := exists_dot_eq_supp ha hne t
    obtain ⟨q, hq, hd⟩ := hab p hp
    have hproj := dot_uvec_le_norm2 (p - q) t
    rw [dot_sub_left] at hproj
    linarith [dot_le_supp hb hq t, show norm2 (p - q) ≤ r from hd]
  exact abs_le.2 ⟨by linarith [forward hT hS hneT h.2], forward hS hT hneS h.1⟩

/-!
## The stability statements

The deficit is that of the sofa's own area, the normalization is a translation that fixes the top
and left supports, and the conclusions compare the actual, possibly nonconvex, sets.
`MovingSofaStability.Global` proves both statements.
-/

/-- The area deficit `|G| - |S|` of `S` against Gerver's sofa `G`. -/
def sofaDeficit (P : GerverParams) (S : Set Point) : ℝ :=
  area (gerverSofa P) - area S

/-- The translation that moves the top support of `S` to `1` and its left support to that of
Gerver's sofa. -/
def normalizingShift (P : GerverParams) (S : Set Point) : Point :=
  (supp S π - supp (gerverSofa P) π, 1 - supp S (π / 2))

/-- The translate of `S` by `normalizingShift P S`. -/
def normalizedSofa (P : GerverParams) (S : Set Point) : Set Point :=
  Rigid.translate (normalizingShift P S) '' S

/-- The area of the symmetric difference of two sets. -/
def symmetricDifferenceArea (S T : Set Point) : ℝ :=
  area ((S \ T) ∪ (T \ S))

/-- Normalization preserves area. -/
@[simp] theorem area_normalizedSofa (P : GerverParams) (S : Set Point) :
    area (normalizedSofa P S) = area S :=
  (Rigid.translate (normalizingShift P S)).area_image S

/-- The normalized sofa has top support `1`. -/
theorem normalizedSofa_top (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) : supp (normalizedSofa P S) (π / 2) = 1 := by
  rw [normalizedSofa, Rigid.coe_translate, supp_translate S _ _ hS hne, dot_uvec_pi_div_two]
  simp [normalizingShift]

/-- The normalized sofa has the left support of Gerver's sofa. -/
theorem normalizedSofa_left (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) :
    supp (normalizedSofa P S) π = supp (gerverSofa P) π := by
  rw [normalizedSofa, Rigid.coe_translate, supp_translate S _ _ hS hne, dot_uvec_pi]
  simp [normalizingShift]

/-- The stability of Gerver's sofa: there are `C, Carea, ε₀ > 0` such that the normalization of
every moving sofa of deficit `ε < ε₀` is `C √ε`-close to Gerver's sofa, and their symmetric
difference has area at most `Carea √ε`. -/
def UnrestrictedStability (P : GerverParams) : Prop :=
  ∃ C Carea ε₀ : ℝ, 0 < C ∧ 0 < Carea ∧ 0 < ε₀ ∧
    ∀ S : Set Point, IsMovingSofa S → sofaDeficit P S < ε₀ →
      EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
      symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤
        Carea * sqrt (sofaDeficit P S)

/-- The stability of the rotation angle: there are `Cangle, ε₀ > 0` such that every moving sofa of
deficit `ε < ε₀` with rotation angle `ω ∈ [arccos (5/11), π/2]` has `0 ≤ π/2 - ω ≤ Cangle ε`. -/
def TerminalAngleStability (P : GerverParams) : Prop :=
  ∃ Cangle ε₀ : ℝ, 0 < Cangle ∧ 0 < ε₀ ∧
    ∀ (S : Set Point) (ω : ℝ), IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
      0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S

/-!
## The area comparison for the terminal angle

A sofa that stops before the right-angle turn may contain points of the omitted wedges, so the
lemmas do not assume `S ⊆ U`. The excluded floor region and the bound on the omitted wedges are
hypotheses of `terminal_region_comparison`.
-/

/-- Area is monotone on subsets of a set of finite measure. -/
theorem area_mono_of_finite {S T : Set Point} (hST : S ⊆ T) (hT : volume T ≠ ⊤) :
    area S ≤ area T :=
  ENNReal.toReal_mono hT (measure_mono hST)

/-- A subset of a set of finite measure has finite measure. -/
theorem volume_ne_top_of_subset {S T : Set Point} (hST : S ⊆ T)
    (hT : volume T ≠ ⊤) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top hT (measure_mono hST)

/-- Area is additive on disjoint sets of finite measure. -/
theorem area_union_of_disjoint {S T : Set Point} (hd : Disjoint S T)
    (hT : MeasurableSet T) (hSf : volume S ≠ ⊤) (hTf : volume T ≠ ⊤) :
    area (S ∪ T) = area S + area T :=
  measureReal_union hd hT hSf hTf

/-- A measurable set `T` splits the area of a set `S` of finite measure, without `S ⊆ T`. -/
theorem area_inter_add_sdiff {S T : Set Point} (hT : MeasurableSet T)
    (hSf : volume S ≠ ⊤) : area (S ∩ T) + area (S \ T) = area S :=
  measureReal_inter_add_sdiff hT hSf

/-- The two directed missing areas differ by the area deficit. -/
theorem area_sdiff_balance {S U : Set Point} (hS : MeasurableSet S)
    (hU : MeasurableSet U) (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) :
    area (U \ S) = area U - area S + area (S \ U) := by
  have h₁ := area_inter_add_sdiff hS hUf
  have h₂ := area_inter_add_sdiff hU hSf
  rw [inter_comm U S] at h₁
  linarith

/-- The terminal comparison. Let `S ⊆ V` and `U ⊆ V`, where `U` is the full-angle set and `V` the
partial-angle set. If the floor region `F ⊆ U`, which `S` avoids, has area at least `2 c α` and the
omitted wedges `V \ U` have area at most `c α`, then `|S| ≤ |U| - c α`, and `α`, `M - |U|` and both
missing areas are bounded by multiples of the deficit `M - |S|`. -/
theorem terminal_region_comparison {S U V F : Set Point} {M c α : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α)
    (hSV : S ⊆ V) (hUV : U ⊆ V) (hFU : F ⊆ U) (hSF : Disjoint S F)
    (hS : MeasurableSet S) (hU : MeasurableSet U) (hF : MeasurableSet F)
    (hVf : volume V ≠ ⊤)
    (hfloor : 2 * c * α ≤ area F) (homitted : area (V \ U) ≤ c * α)
    (hmax : area U ≤ M) :
    area S ≤ area U - c * α ∧
      α ≤ (M - area S) / c ∧
      M - area U ≤ M - area S ∧
      area (S \ U) ≤ M - area S ∧
      area (U \ S) ≤ 2 * (M - area S) := by
  have hUf := volume_ne_top_of_subset hUV hVf
  have hSf := volume_ne_top_of_subset hSV hVf
  have hFV := hFU.trans hUV
  -- `S` and `F` are disjoint in `V`, and `V` is `U` together with the omitted wedges
  have hsum : area S + area F ≤ area V := by
    rw [← area_union_of_disjoint hSF hF hSf (volume_ne_top_of_subset hFV hVf)]
    exact area_mono_of_finite (union_subset hSV hFV) hVf
  have hsplit := area_inter_add_sdiff hU hVf
  rw [inter_eq_right.mpr hUV] at hsplit
  have hloss : area S ≤ area U - c * α := by linarith
  have hca : 0 ≤ c * α := mul_nonneg hc.le hα
  have hpay : c * α ≤ M - area S := by linarith
  have hleft : area (S \ U) ≤ M - area S :=
    ((area_mono_of_finite (sdiff_subset_sdiff_left hSV)
      (volume_ne_top_of_subset sdiff_subset hVf)).trans homitted).trans hpay
  have hbalance := area_sdiff_balance hS hU hSf hUf
  exact ⟨hloss, (le_div_iff₀ hc).2 (by linarith), by linarith, hleft, by linarith⟩

end MovingSofaStability
