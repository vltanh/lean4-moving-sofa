module

public import MovingSofaUniqueness.Rigid

/-!
# Euclidean distances and closeness of sets, the statements of the stability theorems, and the constraints of a partial motion

Euclidean distances between points and sets (`EuclideanClose`), the deficit and the normalization of a
moving sofa and the two stability statements (`sofaDeficit`, `normalizedSofa`, `UnrestrictedStability`,
`TerminalAngleStability`), and the constraints that a sofa moving through a partial hallway satisfies.

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Euclidean distance for the actual sofa sets

The ambient product `Real × Real` has the sup metric; Baek's `hausdorffDist` is
a support-function expression for convex bodies and would identify a nonconvex
sofa with its convex hull. Neither is silently used as the actual-set Euclidean
Hausdorff distance here.

`EuclideanClose r S T` expresses both directed distance bounds by witnesses.
For nonempty compact sets this is precisely Euclidean Hausdorff distance at
most r. The witness form is also useful in the geometric recovery argument.
-/

section EuclideanGeometry

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev Point := ℝ × ℝ

/-- Euclidean point distance, using the repository's separate Euclidean norm. -/
def euclideanDist (p q : Point) : ℝ := norm2 (p - q)

theorem norm2_nonneg (p : Point) : 0 ≤ norm2 p := Real.sqrt_nonneg _

theorem norm2_sq (p : Point) : norm2 p ^ 2 = dot p p := by
  apply Real.sq_sqrt
  dsimp [dot]
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

@[simp] theorem norm2_zero : norm2 (0 : Point) = 0 := by
  simp [norm2, dot]

@[simp] theorem norm2_neg (p : Point) : norm2 (-p) = norm2 p := by
  unfold norm2
  congr 1
  simp only [dot, Prod.fst_neg, Prod.snd_neg]
  ring

theorem dot_le_norm2_mul (p q : Point) : dot p q ≤ norm2 p * norm2 q := by
  have hp := norm2_sq p
  have hq := norm2_sq q
  have hpn := norm2_nonneg p
  have hqn := norm2_nonneg q
  have hsq : dot p q ^ 2 ≤ (norm2 p * norm2 q) ^ 2 := by
    rw [mul_pow, hp, hq]
    dsimp [dot]
    nlinarith [sq_nonneg (p.1 * q.2 - p.2 * q.1)]
  have hprod : 0 ≤ norm2 p * norm2 q := mul_nonneg hpn hqn
  nlinarith

/-- Euclidean triangle inequality, not the triangle inequality of the product norm. -/
theorem norm2_add_le (p q : Point) : norm2 (p + q) ≤ norm2 p + norm2 q := by
  have hp := norm2_sq p
  have hq := norm2_sq q
  have hdot := dot_le_norm2_mul p q
  have hsym : dot q p = dot p q := by unfold dot; ring
  change Real.sqrt (dot (p + q) (p + q)) ≤ norm2 p + norm2 q
  apply (Real.sqrt_le_left (add_nonneg (norm2_nonneg p) (norm2_nonneg q))).2
  rw [dot_add_left, dot_add_right, dot_add_right, hsym]
  nlinarith

@[simp] theorem norm2_rot (a : ℝ) (p : Point) : norm2 (rot a p) = norm2 p := by
  unfold norm2
  congr 1
  calc
    dot (rot a p) (rot a p) =
        (cos a ^ 2 + sin a ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by
      unfold dot rot
      ring
    _ = dot p p := by rw [cos_sq_add_sin_sq]; unfold dot; ring

@[simp] theorem norm2_uvec (t : ℝ) : norm2 (uvec t) = 1 := by
  simp [norm2, dot_uvec_self]

theorem dot_uvec_le_norm2 (p : Point) (t : ℝ) : dot p (uvec t) ≤ norm2 p := by
  simpa only [norm2_uvec, mul_one] using dot_le_norm2_mul p (uvec t)

theorem euclideanDist_nonneg (p q : Point) : 0 ≤ euclideanDist p q :=
  norm2_nonneg _

@[simp] theorem euclideanDist_self (p : Point) : euclideanDist p p = 0 := by
  simp [euclideanDist]

theorem euclideanDist_comm (p q : Point) : euclideanDist p q = euclideanDist q p := by
  unfold euclideanDist
  rw [show p - q = -(q - p) by abel, norm2_neg]

theorem euclideanDist_triangle (p q r : Point) :
    euclideanDist p r ≤ euclideanDist p q + euclideanDist q r := by
  unfold euclideanDist
  rw [show p - r = (p - q) + (q - r) by abel]
  exact norm2_add_le _ _

@[simp] theorem euclideanDist_eq_zero_iff (p q : Point) : euclideanDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hs := norm2_sq (p - q)
    change norm2 (p - q) = 0 at h
    rw [h] at hs
    have hcoords : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 0 := by
      dsimp [dot] at hs
      nlinarith
    apply Prod.ext
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  · rintro rfl
    exact euclideanDist_self p

@[simp] theorem euclideanDist_rigid (g : Rigid) (p q : Point) :
    euclideanDist (g p) (g q) = euclideanDist p q := by
  have h : g p - g q = rot g.angle (p - q) := by
    ext <;> simp [Rigid.apply, rot] <;> ring
  unfold euclideanDist
  rw [h, norm2_rot]

/-- Directed Euclidean distance bound with an actual point witness. -/
def DirectedClose (r : ℝ) (S T : Set Point) : Prop :=
  ∀ p ∈ S, ∃ q ∈ T, euclideanDist p q ≤ r

/-- Euclidean Hausdorff bound for actual sets, rather than their support functions. -/
def EuclideanClose (r : ℝ) (S T : Set Point) : Prop :=
  DirectedClose r S T ∧ DirectedClose r T S

theorem DirectedClose.mono {r R : ℝ} {S T : Set Point}
    (h : DirectedClose r S T) (hr : r ≤ R) : DirectedClose R S T := by
  intro p hp
  obtain ⟨q, hq, hd⟩ := h p hp
  exact ⟨q, hq, hd.trans hr⟩

theorem DirectedClose.trans {r s : ℝ} {S T U : Set Point}
    (hST : DirectedClose r S T) (hTU : DirectedClose s T U) :
    DirectedClose (r + s) S U := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hST p hp
  obtain ⟨u, hu, hqu⟩ := hTU q hq
  exact ⟨u, hu, (euclideanDist_triangle p q u).trans (add_le_add hpq hqu)⟩

theorem EuclideanClose.refl (S : Set Point) {r : ℝ} (hr : 0 ≤ r) :
    EuclideanClose r S S := by
  have h : DirectedClose r S S := fun p hp => ⟨p, hp, by simpa using hr⟩
  exact ⟨h, h⟩

theorem EuclideanClose.symm {r : ℝ} {S T : Set Point} (h : EuclideanClose r S T) :
    EuclideanClose r T S := ⟨h.2, h.1⟩

theorem EuclideanClose.mono {r R : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (hr : r ≤ R) : EuclideanClose R S T :=
  ⟨h.1.mono hr, h.2.mono hr⟩

theorem EuclideanClose.trans {r s : ℝ} {S T U : Set Point}
    (hST : EuclideanClose r S T) (hTU : EuclideanClose s T U) :
    EuclideanClose (r + s) S U := by
  refine ⟨hST.1.trans hTU.1, ?_⟩
  simpa only [add_comm] using hTU.2.trans hST.2

/-- Zero radius recovers equality of actual sets, even when they are nonconvex. -/
theorem EuclideanClose.eq_of_zero {S T : Set Point} (h : EuclideanClose 0 S T) : S = T := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨q, hq, hd⟩ := h.1 p hp
    have he := (euclideanDist_eq_zero_iff p q).1
      (le_antisymm hd (euclideanDist_nonneg p q))
    simpa only [he] using hq
  · intro q hq
    obtain ⟨p, hp, hd⟩ := h.2 q hq
    have he := (euclideanDist_eq_zero_iff q p).1
      (le_antisymm hd (euclideanDist_nonneg q p))
    simpa only [he] using hp

/-- Actual-set closeness controls every support value. The converse is not
claimed for nonconvex sets. -/
theorem EuclideanClose.abs_supp_sub_le {r : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (hS : IsCompact S) (hT : IsCompact T)
    (hneS : S.Nonempty) (hneT : T.Nonempty) (t : ℝ) :
    |supp S t - supp T t| ≤ r := by
  have forward {A B : Set Point} (ha : IsCompact A) (hb : IsCompact B)
      (hne : A.Nonempty) (hab : DirectedClose r A B) : supp A t - supp B t ≤ r := by
    obtain ⟨p, hp, he⟩ := exists_dot_eq_supp ha hne t
    obtain ⟨q, hq, hd⟩ := hab p hp
    have hqle := dot_le_supp hb hq t
    have hproj := dot_uvec_le_norm2 (p - q) t
    rw [dot_sub_left] at hproj
    change norm2 (p - q) ≤ r at hd
    linarith
  have h₁ := forward hS hT hneS h.1
  have h₂ := forward hT hS hneT h.2
  exact abs_le.2 ⟨by linarith, h₁⟩

end MovingSofaStability

end EuclideanGeometry

/-!
## The unrestricted stability target

`UnrestrictedStability` and `TerminalAngleStability` state the main theorems;
`GlobalStability.lean` proves them (`unrestricted_stability`,
`terminal_angle_stability`).

The metric conclusion uses both directed Euclidean bounds on the actual
nonconvex sets. The normalization agrees with note 08 and uses translation
only. No injective-cap or special-envelope hypothesis appears in the target.
-/

section Statement

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The deficit of the original sofa's area, not that of a surrogate cap. -/
def sofaDeficit (P : GerverParams) (S : Set Point) : ℝ :=
  area (gerverSofa P) - area S

/-- Pin the top support and the leftmost coordinate without a small-angle denominator. -/
def normalizingShift (P : GerverParams) (S : Set Point) : Point :=
  (supp S π - supp (gerverSofa P) π, 1 - supp S (π / 2))

def normalizedSofa (P : GerverParams) (S : Set Point) : Set Point :=
  Rigid.translate (normalizingShift P S) '' S

/-- Symmetric-difference area is written explicitly to keep its set meaning visible. -/
def symmetricDifferenceArea (S T : Set Point) : ℝ :=
  area ((S \ T) ∪ (T \ S))

@[simp] theorem area_normalizedSofa (P : GerverParams) (S : Set Point) :
    area (normalizedSofa P S) = area S :=
  (Rigid.translate (normalizingShift P S)).area_image S

theorem normalizedSofa_top (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) : supp (normalizedSofa P S) (π / 2) = 1 := by
  unfold normalizedSofa
  rw [Rigid.coe_translate, supp_translate S _ _ hS hne]
  simp only [normalizingShift, dot, uvec_fst, uvec_snd, cos_pi_div_two, sin_pi_div_two]
  ring

theorem normalizedSofa_left (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) :
    supp (normalizedSofa P S) π = supp (gerverSofa P) π := by
  unfold normalizedSofa
  rw [Rigid.coe_translate, supp_translate S _ _ hS hne]
  simp only [normalizingShift, dot, uvec_fst, uvec_snd, cos_pi, sin_pi]
  ring

/-- Note 08's unrestricted theorem, in the original sofa definitions;
`unrestricted_stability` proves it. -/
def UnrestrictedStability (P : GerverParams) : Prop :=
  ∃ C Carea ε₀ : ℝ, 0 < C ∧ 0 < Carea ∧ 0 < ε₀ ∧
    ∀ S : Set Point, IsMovingSofa S → sofaDeficit P S < ε₀ →
      EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
      symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤
        Carea * sqrt (sofaDeficit P S)

/-- The angle-rate target is separate from the Hausdorff conclusion. -/
def TerminalAngleStability (P : GerverParams) : Prop :=
  ∃ Cangle ε₀ : ℝ, 0 < Cangle ∧ 0 < ε₀ ∧
    ∀ (S : Set Point) (ω : ℝ), IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
      0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S

end MovingSofaStability

end Statement

/-!
## Terminal-angle loss: finite-measure bookkeeping

These lemmas implement the set/area comparison in stability note 07. In
particular they do not assume `S ⊆ U`: `S` can contain points in the wedges
omitted by stopping before a right-angle turn.

The geometric construction of the excluded floor rectangle and the upper
bound for the omitted wedges are NOT proved by this file. Those are explicit
hypotheses of `terminal_region_comparison`, rather than hidden axioms.
-/

section TerminalBookkeeping

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Finiteness of the containing set is essential when using `area = toReal volume`. -/
theorem area_mono_of_finite {S T : Set Point} (hST : S ⊆ T) (hT : volume T ≠ ⊤) :
    area S ≤ area T :=
  ENNReal.toReal_mono hT (measure_mono hST)

theorem volume_ne_top_of_subset {S T : Set Point} (hST : S ⊆ T)
    (hT : volume T ≠ ⊤) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top hT (measure_mono hST)

theorem area_union_of_disjoint {S T : Set Point} (hd : Disjoint S T)
    (hT : MeasurableSet T) (hSf : volume S ≠ ⊤) (hTf : volume T ≠ ⊤) :
    area (S ∪ T) = area S + area T := by
  unfold area
  rw [measure_union hd hT, ENNReal.toReal_add hSf hTf]

/-- Partition a finite set by a measurable set, without assuming containment. -/
theorem area_inter_add_sdiff {S T : Set Point} (hT : MeasurableSet T)
    (hSf : volume S ≠ ⊤) : area (S ∩ T) + area (S \ T) = area S := by
  have hi : volume (S ∩ T) ≠ ⊤ := volume_ne_top_of_subset inter_subset_left hSf
  have hd : volume (S \ T) ≠ ⊤ := volume_ne_top_of_subset sdiff_subset hSf
  have h := congrArg ENNReal.toReal (measure_inter_add_sdiff (μ := volume) S hT)
  simpa only [ENNReal.toReal_add hi hd, area] using h

/-- The two directed missing areas differ by the area deficit. -/
theorem area_sdiff_balance {S U : Set Point} (hS : MeasurableSet S)
    (hU : MeasurableSet U) (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) :
    area (U \ S) = area U - area S + area (S \ U) := by
  have h₁ := area_inter_add_sdiff hS hUf
  have h₂ := area_inter_add_sdiff hU hSf
  rw [inter_comm U S] at h₁
  linarith

/-- If a finite containing region is `U` plus a remainder, its area splits that way. -/
theorem area_eq_add_remainder {U V : Set Point} (hUV : U ⊆ V)
    (hU : MeasurableSet U) (hVf : volume V ≠ ⊤) :
    area V = area U + area (V \ U) := by
  have h := area_inter_add_sdiff hU hVf
  rw [inter_eq_right.mpr hUV] at h
  exact h.symm

/-- Excluding a disjoint measurable region loses its full area. -/
theorem area_add_excluded_le {S F V : Set Point}
    (hSV : S ⊆ V) (hFV : F ⊆ V) (hSF : Disjoint S F)
    (hF : MeasurableSet F) (hVf : volume V ≠ ⊤) :
    area S + area F ≤ area V := by
  have hSf := volume_ne_top_of_subset hSV hVf
  have hFf := volume_ne_top_of_subset hFV hVf
  rw [← area_union_of_disjoint hSF hF hSf hFf]
  exact area_mono_of_finite (union_subset hSV hFV) hVf

/-- The terminal strip wins when its excluded floor region costs at least
`2 c α` and the omitted wedges gain at most `c α`.

`U` is the full-angle set, `V` the partial-angle set, and `F` the excluded
floor region. The conclusion includes BOTH missing-set bounds. -/
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
  have hsum := area_add_excluded_le hSV (hFU.trans hUV) hSF hF hVf
  rw [area_eq_add_remainder hUV hU hVf] at hsum
  have hloss : area S ≤ area U - c * α := by linarith
  have hca : 0 ≤ c * α := mul_nonneg hc.le hα
  have hpay : c * α ≤ M - area S := by linarith
  have hangle : α ≤ (M - area S) / c := by
    apply (le_div_iff₀ hc).2
    nlinarith
  have hsub : S \ U ⊆ V \ U := fun p hp => ⟨hSV hp.1, hp.2⟩
  have hleft : area (S \ U) ≤ M - area S :=
    ((area_mono_of_finite hsub (volume_ne_top_of_subset sdiff_subset hVf)).trans
      homitted).trans hpay
  have hbalance := area_sdiff_balance hS hU hSf hUf
  refine ⟨hloss, hangle, ?_, hleft, ?_⟩
  · linarith
  · linarith


end MovingSofaStability

end TerminalBookkeeping
