module

public import MovingSofa.Basic.SurfaceArea
public import MovingSofa.External.AreaFormulaParam
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The area of a planar convex body (Schneider, Remark 5.1.2)

The paper cites from Schneider's *Convex Bodies: The Brunn–Minkowski Theory* (Remark 5.1.2 and
Equation (5.19)) the formula `|K| = ½ ∫_{S¹} h_K dσ_K` for a planar convex body `K` (the paper's
Theorem 7.1.3). This file proves it for the surface area measure `σ_K` of `Basic/SurfaceArea.lean`.

## Proof

We use the arc-length parametrization `γ` of `∂K` and the normal angle `τ(y)` at arc length `y`
from `External/AreaFormulaParam.lean`: `γ` is Lipschitz, `γ(y) · u_{τ(y)} = h_K(τ(y))`, `γ' = v_τ`
outside the countable set of discontinuities of `τ`, and `τ` pushes the Lebesgue measure forward to
`σ_K`.

* *Nondegenerate case.* Fix an interior point `c` of `K`. The cone map
  `Ψ(y, λ) = c + λ (γ(y) - c)` on `([F(0), F(0) + P) \ bad) × (0, 1)` (`P` the perimeter) is
  injective (each ray from `c` meets `∂K` once, and `γ` is injective on a period), has Jacobian
  determinant of absolute value `λ (h_K(τ(y)) - c · u_{τ(y)})`, and its image is `K` up to the
  null set `∂K ∪ {c} ∪ (countably many lines)`. The change of variables formula
  (`lintegral_abs_det_fderiv_eq_addHaar_image`), Tonelli and the push-forward give
  `|K| = ½ ∫_{(0, 2π]} (h_K(t) - c · u_t) dσ_K(t)`, and `∫_{(0, 2π]} u_t dσ_K = 0`
  (from `v_K⁺(2π) - v_K⁺(0) = ∫_{(0, 2π]} v_t dσ_K = 0`).
* *Degenerate case.* If `K` has empty interior then `K` lies on a line, `|K| = 0` (the frontier of a
  convex set is null), and `h_K(τ(y)) - c · u_{τ(y)} = (γ(y) - c) × γ'(y) = 0` almost everywhere
  since `γ(y) - c` and `γ'(y)` are both parallel to that line.

Finally `[0, 2π)` and `(0, 2π]` give the same integral since `σ_K` and `h_K` are `2π`-periodic.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

section AreaFormulaProof

open Filter Topology Function

section Boundary

variable {K : Set (ℝ × ℝ)}

/-- `‖u_t‖ ≤ 1` for the sup norm of `ℝ × ℝ`. -/
lemma af_norm_uvec_le (t : ℝ) : ‖uvec t‖ ≤ 1 := by
  rw [Prod.norm_def]
  simp only [uvec, Real.norm_eq_abs]
  exact max_le (abs_cos_le_one t) (abs_sin_le_one t)

lemma af_dot_uvec_le_abs (p : ℝ × ℝ) (t : ℝ) : dot p (uvec t) ≤ |p.1| + |p.2| := by
  simp only [dot, uvec]
  have h1 : p.1 * cos t ≤ |p.1| := by
    calc p.1 * cos t ≤ |p.1 * cos t| := le_abs_self _
      _ = |p.1| * |cos t| := abs_mul _ _
      _ ≤ |p.1| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one t) (abs_nonneg _)
      _ = |p.1| := mul_one _
  have h2 : p.2 * sin t ≤ |p.2| := by
    calc p.2 * sin t ≤ |p.2 * sin t| := le_abs_self _
      _ = |p.2| * |sin t| := abs_mul _ _
      _ ≤ |p.2| * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one t) (abs_nonneg _)
      _ = |p.2| := mul_one _
  linarith

/-- A point of a convex body that is not an interior point lies on a supporting line. -/
lemma af_exists_dot_eq_supp (hK : IsConvexBody K) {q : ℝ × ℝ} (hq : q ∈ K)
    (hqi : q ∉ interior K) : ∃ t, dot q (uvec t) = supp K t := by
  by_contra hcon
  have hlt : ∀ t, dot q (uvec t) < supp K t := fun t =>
    lt_of_le_of_ne (dot_le_supp hK.2.1 hq t) (fun h => hcon ⟨t, h⟩)
  set g : ℝ → ℝ := fun t => supp K t - dot q (uvec t) with hg_def
  have hg : Continuous g :=
    (continuous_supp hK.2.1 hK.1).sub (by unfold dot uvec; fun_prop)
  have hgper : Periodic g (2 * π) := fun t => by
    simp only [hg_def, supp_add_two_pi, uvec_add_two_pi]
  obtain ⟨t₀, -, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 two_pi_pos.le) hg.continuousOn
  have hε : 0 < g t₀ := sub_pos.2 (hlt t₀)
  have hgε : ∀ t, g t₀ ≤ g t := by
    intro t
    obtain ⟨t', ht', heq⟩ := hgper.exists_mem_Ico₀ two_pi_pos t
    rw [heq]
    exact hmin (Ico_subset_Icc_self ht')
  apply hqi
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨g t₀ / 2, half_pos hε, fun x hx => ?_⟩
  rw [mem_iff_forall_dot_le_supp hK]
  intro t
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 : |(x - q).1| < g t₀ / 2 := lt_of_le_of_lt (norm_fst_le (x - q)) hx
  have h2 : |(x - q).2| < g t₀ / 2 := lt_of_le_of_lt (norm_snd_le (x - q)) hx
  have h3 := af_dot_uvec_le_abs (x - q) t
  rw [dot_sub_left] at h3
  have h4 := hgε t
  simp only [hg_def] at h4
  linarith

/-- An interior point is strictly inside every supporting half-plane. -/
lemma af_dot_lt_supp (hK : IsConvexBody K) {c : ℝ × ℝ} (hc : c ∈ interior K) (t : ℝ) :
    dot c (uvec t) < supp K t := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hc
  obtain ⟨r, hr, hball⟩ := hc
  have hmem : c + (r / 2) • uvec t ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    have := af_norm_uvec_le t
    nlinarith)
  have := dot_le_supp hK.2.1 hmem t
  rw [dot_add_left, dot_smul_left, dot_uvec_self, mul_one] at this
  linarith

/-- A convex body with an interior point has positive width in every direction. -/
lemma af_width_pos (hK : IsConvexBody K) {c : ℝ × ℝ} (hc : c ∈ interior K) (t : ℝ) :
    0 < supp K t + supp K (t + π) := by
  have h1 := af_dot_lt_supp hK hc t
  have h2 := af_dot_lt_supp hK hc (t + π)
  rw [uvec_add_pi, dot_neg_right] at h2
  linarith

/-- Moving along a ray from an interior point, one can go a bit further inside `K`. -/
lemma af_exists_gt_of_mem_interior {c p : ℝ × ℝ} {μ : ℝ}
    (h : c + μ • (p - c) ∈ interior K) : ∃ μ' > μ, c + μ' • (p - c) ∈ K := by
  have hcont : Continuous fun μ : ℝ => c + μ • (p - c) := by fun_prop
  have hopen : IsOpen ((fun μ : ℝ => c + μ • (p - c)) ⁻¹' interior K) :=
    isOpen_interior.preimage hcont
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen μ h
  refine ⟨μ + δ / 2, by linarith, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
  linarith

/-- The ray from `c` through an interior point `p ≠ c` of `K` leaves `K` at a point
`c + μ (p - c)` with `μ > 1` which is not an interior point. -/
lemma af_exists_boundary_on_ray (hK : IsConvexBody K) {c p : ℝ × ℝ}
    (hp : p ∈ interior K) (hpc : p ≠ c) :
    ∃ μ : ℝ, 1 < μ ∧ c + μ • (p - c) ∈ K ∧ c + μ • (p - c) ∉ interior K := by
  set S : Set ℝ := {μ | 0 ≤ μ ∧ c + μ • (p - c) ∈ K} with hS
  have hcont : Continuous fun μ : ℝ => c + μ • (p - c) := by fun_prop
  have hSc : IsClosed S := isClosed_Ici.inter (hK.isClosed.preimage hcont)
  have h1S : (1 : ℝ) ∈ S := ⟨zero_le_one, by simpa using interior_subset hp⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hpc' : 0 < ‖p - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hpc)
  have hSb : BddAbove S := by
    refine ⟨(R + ‖c‖) / ‖p - c‖, fun μ hμ => ?_⟩
    rw [le_div_iff₀ hpc']
    have h1 := hR _ hμ.2
    have h2 : ‖μ • (p - c)‖ ≤ ‖c + μ • (p - c)‖ + ‖c‖ := by
      have := norm_sub_le (c + μ • (p - c)) c
      rwa [add_sub_cancel_left] at this
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1] at h2
    linarith
  have hmem : sSup S ∈ S := hSc.csSup_mem ⟨1, h1S⟩ hSb
  refine ⟨sSup S, ?_, hmem.2, fun hint => ?_⟩
  · obtain ⟨μ', hμ', hμ'K⟩ := af_exists_gt_of_mem_interior (μ := 1) (c := c) (p := p)
      (by simpa using hp)
    exact lt_of_lt_of_le hμ' (le_csSup hSb ⟨by linarith, hμ'K⟩)
  · obtain ⟨μ', hμ', hμ'K⟩ := af_exists_gt_of_mem_interior hint
    have := le_csSup hSb ⟨le_trans hmem.1 hμ'.le, hμ'K⟩
    linarith

end Boundary

section Cone

variable {K : Set (ℝ × ℝ)}

/-- The cone map `Ψ(y, λ) = c + λ (γ(y) - c)`. -/
noncomputable def af_cone (K : Set (ℝ × ℝ)) (c : ℝ × ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  c + z.2 • (af_gamma K z.1 - c)

/-- The derivative of the cone map at `z` (valid where `τ` is continuous at `z.1`). -/
noncomputable def af_coneDeriv (K : Set (ℝ × ℝ)) (c : ℝ × ℝ) (z : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![z.2 * (vvec (af_tau K z.1)).1, (af_gamma K z.1 - c).1;
         z.2 * (vvec (af_tau K z.1)).2, (af_gamma K z.1 - c).2])

/-- The cone map is differentiable at `(y, λ)` whenever `τ` is continuous at `y`. -/
lemma af_hasFDerivAt_cone (hK : IsConvexBody K) (hP : 0 < af_perim K) (c : ℝ × ℝ) {z : ℝ × ℝ}
    (hz : ContinuousAt (af_tau K) z.1) : HasFDerivAt (af_cone K c) (af_coneDeriv K c z) z := by
  have hγ := (af_hasDerivAt_gamma hK hP hz).hasFDerivAt
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => af_gamma K z.1 - c)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (vvec (af_tau K z.1))).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    (hγ.comp z hasFDerivAt_fst).sub_const c
  have h2 := (hasFDerivAt_snd (p := z)).smul h1
  have h3 := h2.const_add c
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  simp [af_coneDeriv]
  ext <;> simp [vvec] <;> ring

/-- The Jacobian determinant of the cone map is `-λ (h_K(τ(y)) - c · u_{τ(y)})`: the cross
product of `λ v_{τ(y)}` and `γ(y) - c`, where `(γ(y) - c) × v_{τ(y)} = (γ(y) - c) · u_{τ(y)}`. -/
lemma af_det_coneDeriv (hK : IsConvexBody K) (hP : 0 < af_perim K) (c z : ℝ × ℝ) :
    (af_coneDeriv K c z).det =
      -(z.2 * (supp K (af_tau K z.1) - dot c (uvec (af_tau K z.1)))) := by
  unfold af_coneDeriv
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  have h2 := cross_vvec (af_gamma K z.1 - c) (af_tau K z.1)
  rw [dot_sub_left, af_dot_gamma hK hP] at h2
  simp only [cross] at h2
  rw [← h2]; ring

/-- The cone map is injective on `[a, a + P) × (0, ∞)` when `c` is an interior point: each ray
from `c` meets `∂K` once, and `γ` is injective on a period. -/
lemma af_cone_injOn (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ}
    (hc : c ∈ interior K) (a : ℝ) :
    InjOn (af_cone K c) (Ico a (a + af_perim K) ×ˢ Ioi 0) := by
  have key : ∀ y y' l l' : ℝ, 0 < l' → l • (af_gamma K y - c) = l' • (af_gamma K y' - c) →
      l ≤ l' := by
    intro y y' l l' hl' h
    have e1 : dot (af_gamma K y - c) (uvec (af_tau K y)) =
        supp K (af_tau K y) - dot c (uvec (af_tau K y)) := by
      rw [dot_sub_left, af_dot_gamma hK hP]
    have e2 : dot (af_gamma K y' - c) (uvec (af_tau K y)) ≤
        supp K (af_tau K y) - dot c (uvec (af_tau K y)) := by
      rw [dot_sub_left]; linarith [dot_le_supp hK.2.1 (af_gamma_mem hK hP y') (af_tau K y)]
    have e3 : l * (supp K (af_tau K y) - dot c (uvec (af_tau K y))) =
        l' * dot (af_gamma K y' - c) (uvec (af_tau K y)) := by
      rw [← e1, ← dot_smul_left, h, dot_smul_left]
    have hpos : 0 < supp K (af_tau K y) - dot c (uvec (af_tau K y)) :=
      sub_pos.2 (af_dot_lt_supp hK hc _)
    by_contra hlt
    nlinarith [not_le.1 hlt]
  rintro ⟨y, l⟩ ⟨hy, hl⟩ ⟨y', l'⟩ ⟨hy', hl'⟩ heq
  simp only [af_cone] at heq
  have heq' : l • (af_gamma K y - c) = l' • (af_gamma K y' - c) := add_left_cancel heq
  have hll : l = l' := le_antisymm (key y y' l l' hl' heq') (key y' y l' l hl heq'.symm)
  subst hll
  have hγ : af_gamma K y = af_gamma K y' := by
    have := smul_right_injective (ℝ × ℝ) (ne_of_gt (show (0 : ℝ) < l from hl)) heq'
    simpa using this
  have := af_gamma_injOn hK hP (af_width_pos hK hc) a hy hy' hγ
  simp only at this
  rw [this]

/-- The cone map sends `[0, 1]`-heights into `K`. -/
lemma af_cone_mem (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ} (hcK : c ∈ K)
    {z : ℝ × ℝ} (hz : z.2 ∈ Icc (0 : ℝ) 1) : af_cone K c z ∈ K :=
  hK.2.2.add_smul_sub_mem hcK (af_gamma_mem hK hP z.1) hz

/-- The arc-length positions where `τ` is discontinuous (a countable set). -/
def af_bad (K : Set (ℝ × ℝ)) : Set ℝ := {y | ¬ContinuousAt (af_tau K) y}

lemma af_bad_countable (hK : IsConvexBody K) (hP : 0 < af_perim K) : (af_bad K).Countable :=
  (af_tau_mono hK hP).countable_not_continuousAt

/-- The domain `([a, a + P) \ bad) × (0, 1)` of the cone map. -/
def af_dom (K : Set (ℝ × ℝ)) (a : ℝ) : Set (ℝ × ℝ) :=
  (Ico a (a + af_perim K) \ af_bad K) ×ˢ Ioo 0 1

lemma af_measurableSet_dom (hK : IsConvexBody K) (hP : 0 < af_perim K) (a : ℝ) :
    MeasurableSet (af_dom K a) :=
  (measurableSet_Ico.diff (af_bad_countable hK hP).measurableSet).prod measurableSet_Ioo

/-- A line `{c + s w}` is a null set. -/
lemma af_volume_line (c w : ℝ × ℝ) : volume (range fun s : ℝ => c + s • w) = 0 := by
  have h : (range fun s : ℝ => c + s • w) =
      (fun z : ℝ × ℝ => c + z.1 • w) '' (univ ×ˢ {0}) := by
    ext p
    simp only [mem_range, mem_image, mem_prod, mem_univ, mem_singleton_iff, true_and,
      Prod.exists]
    exact ⟨fun ⟨y, h⟩ => ⟨y, 0, rfl, h⟩, fun ⟨a, b, _, h⟩ => ⟨a, h⟩⟩
  rw [h]
  apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · exact (by fun_prop : Differentiable ℝ fun z : ℝ × ℝ => c + z.1 • w).differentiableOn
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- Every point of `K` is in the image of the cone map, on the frontier of `K`, at `c`, or on one
of the countably many lines through `c` and `γ(y)` with `y` a discontinuity of `τ`. -/
lemma af_subset_cone (hK : IsConvexBody K) (hP : 0 < af_perim K) (c : ℝ × ℝ) (a : ℝ) :
    K ⊆ af_cone K c '' af_dom K a ∪ ((frontier K ∪
      ⋃ y ∈ af_bad K, range fun s : ℝ => c + s • (af_gamma K y - c)) ∪ {c}) := by
  intro p hp
  by_cases hpf : p ∈ frontier K
  · exact Or.inr (Or.inl (Or.inl hpf))
  have hpi : p ∈ interior K := by
    rw [hK.isClosed.frontier_eq] at hpf
    by_contra h; exact hpf ⟨hp, h⟩
  by_cases hpc : p = c
  · exact Or.inr (Or.inr hpc)
  obtain ⟨μ, hμ1, hμK, hμi⟩ := af_exists_boundary_on_ray hK hpi hpc
  obtain ⟨t, ht⟩ := af_exists_dot_eq_supp hK hμK hμi
  obtain ⟨y₀, hy₀⟩ := af_exists_gamma_eq hK hP (q := c + μ • (p - c)) (t := t) ⟨hμK, ht⟩
  have hy : toIcoMod hP a y₀ ∈ Ico a (a + af_perim K) := toIcoMod_mem_Ico hP a y₀
  have hγy : af_gamma K (toIcoMod hP a y₀) = c + μ • (p - c) := by
    rw [← hy₀, ← self_sub_toIcoDiv_zsmul]
    exact (af_gamma_periodic hK hP).sub_zsmul_eq _
  have hμ0 : μ ≠ 0 := by positivity
  have hpeq : c + μ⁻¹ • (af_gamma K (toIcoMod hP a y₀) - c) = p := by
    rw [hγy, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hμ0, one_smul, add_sub_cancel]
  by_cases hbad : toIcoMod hP a y₀ ∈ af_bad K
  · exact Or.inr (Or.inl (Or.inr (mem_iUnion₂.2 ⟨_, hbad, μ⁻¹, hpeq⟩)))
  · refine Or.inl ⟨(toIcoMod hP a y₀, μ⁻¹), ⟨⟨hy, hbad⟩, ?_, ?_⟩, hpeq⟩
    · exact inv_pos.2 (by linarith)
    · exact inv_lt_one_of_one_lt₀ hμ1

/-- `|K| = |Ψ(([a, a + P) \ bad) × (0, 1))|`. -/
lemma af_volume_eq_cone (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ}
    (hc : c ∈ interior K) (a : ℝ) : volume K = volume (af_cone K c '' af_dom K a) := by
  have hN : volume ((frontier K ∪
      ⋃ y ∈ af_bad K, range fun s : ℝ => c + s • (af_gamma K y - c)) ∪ {c}) = 0 :=
    measure_union_null (measure_union_null (Convex.addHaar_frontier volume hK.2.2)
      ((measure_biUnion_null_iff (af_bad_countable hK hP)).2 fun y _ => af_volume_line _ _))
      (measure_singleton c)
  apply le_antisymm
  · calc volume K ≤ volume (af_cone K c '' af_dom K a ∪ ((frontier K ∪
          ⋃ y ∈ af_bad K, range fun s : ℝ => c + s • (af_gamma K y - c)) ∪ {c})) :=
          measure_mono (af_subset_cone hK hP c a)
      _ ≤ volume (af_cone K c '' af_dom K a) + volume ((frontier K ∪
          ⋃ y ∈ af_bad K, range fun s : ℝ => c + s • (af_gamma K y - c)) ∪ {c}) :=
          measure_union_le _ _
      _ = volume (af_cone K c '' af_dom K a) := by rw [hN, add_zero]
  · apply measure_mono
    rintro _ ⟨z, hz, rfl⟩
    exact af_cone_mem hK hP (interior_subset hc) ⟨hz.2.1.le, hz.2.2.le⟩

end Cone

section Integral

variable {K : Set (ℝ × ℝ)}

/-- The height `h_K(τ(y)) - c · u_{τ(y)}` of the cone over the boundary point `γ(y)`. -/
noncomputable def af_height (K : Set (ℝ × ℝ)) (c : ℝ × ℝ) (y : ℝ) : ℝ :=
  supp K (af_tau K y) - dot c (uvec (af_tau K y))

/-- `t ↦ h_K(t) - c · u_t` is continuous. -/
lemma af_continuous_supp_sub (hK : IsConvexBody K) (c : ℝ × ℝ) :
    Continuous fun t => supp K t - dot c (uvec t) :=
  (continuous_supp hK.2.1 hK.1).sub (by unfold dot uvec; fun_prop)

lemma af_measurable_height (hK : IsConvexBody K) (hP : 0 < af_perim K) (c : ℝ × ℝ) :
    Measurable (af_height K c) :=
  (af_continuous_supp_sub hK c).measurable.comp (af_measurable_tau hK hP)

/-- The change of variables formula for the cone map. -/
lemma af_volume_cone_eq_lintegral (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ}
    (hc : c ∈ interior K) (a : ℝ) :
    volume (af_cone K c '' af_dom K a) =
      ∫⁻ z in af_dom K a, ENNReal.ofReal |(af_coneDeriv K c z).det| :=
  (lintegral_abs_det_fderiv_eq_addHaar_image volume (af_measurableSet_dom hK hP a)
    (fun _ hz => (af_hasFDerivAt_cone hK hP c (not_not.1 hz.1.2)).hasFDerivWithinAt)
    ((af_cone_injOn hK hP hc a).mono (prod_mono sdiff_subset Ioo_subset_Ioi_self))).symm

/-- The absolute Jacobian determinant `λ (h_K(τ(y)) - c · u_{τ(y)})` for `λ ≥ 0`. -/
lemma af_abs_det (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ} (hc : c ∈ interior K)
    {z : ℝ × ℝ} (hz : 0 ≤ z.2) : |(af_coneDeriv K c z).det| = z.2 * af_height K c z.1 := by
  rw [af_det_coneDeriv hK hP, abs_neg,
    abs_of_nonneg (mul_nonneg hz (sub_pos.2 (af_dot_lt_supp hK hc _)).le)]
  rfl

/-- `∫_0^1 λ g dλ = g / 2`. -/
lemma af_lintegral_Ioo_mul {g : ℝ} (hg : 0 ≤ g) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l * g) = ENNReal.ofReal (g / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_mul_const, integral_id]
    ring
  · exact (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact ae_restrict_of_forall_mem measurableSet_Ioo fun l hl => mul_nonneg hl.1.le hg

/-- Tonelli on a product set of the plane. -/
lemma af_lintegral_prod_set {A B : Set ℝ} (f : ℝ × ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ z in A ×ˢ B, f z = ∫⁻ y in A, ∫⁻ l in B, f (y, l) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hf.aemeasurable]

/-- Integrating out `λ`: `∫∫ λ g(y) dλ dy = ∫ g(y) / 2 dy`. -/
lemma af_lintegral_dom (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ}
    (hc : c ∈ interior K) (a : ℝ) :
    ∫⁻ z in af_dom K a, ENNReal.ofReal |(af_coneDeriv K c z).det| =
      ∫⁻ y in Ico a (a + af_perim K) \ af_bad K, ENNReal.ofReal (af_height K c y / 2) := by
  have h1 : ∫⁻ z in af_dom K a, ENNReal.ofReal |(af_coneDeriv K c z).det| =
      ∫⁻ z in af_dom K a, ENNReal.ofReal (z.2 * af_height K c z.1) := by
    refine setLIntegral_congr_fun (af_measurableSet_dom hK hP a) fun z hz => ?_
    rw [af_abs_det hK hP hc hz.2.1.le]
  rw [h1, af_dom, af_lintegral_prod_set (fun z => ENNReal.ofReal (z.2 * af_height K c z.1))
    (measurable_snd.mul ((af_measurable_height hK hP c).comp measurable_fst)).ennreal_ofReal]
  refine setLIntegral_congr_fun
    (measurableSet_Ico.diff (af_bad_countable hK hP).measurableSet) fun y _ => ?_
  have hy : 0 ≤ af_height K c y := (sub_pos.2 (af_dot_lt_supp hK hc _)).le
  exact af_lintegral_Ioo_mul (g := af_height K c y) hy

/-- Pushing the arc-length integral forward to `σ_K`. -/
lemma af_lintegral_height (hK : IsConvexBody K) (hP : 0 < af_perim K) {c : ℝ × ℝ}
    (hc : c ∈ interior K) :
    ∫⁻ y in Ico (sigmaStieltjes K 0) (sigmaStieltjes K 0 + af_perim K) \ af_bad K,
        ENNReal.ofReal (af_height K c y / 2) =
      ENNReal.ofReal ((1 / 2) * ∫ t in Ioc 0 (2 * π), (supp K t - dot c (uvec t)) ∂(sigma K)) := by
  have hF : sigmaStieltjes K 0 + af_perim K = sigmaStieltjes K (2 * π) := by
    unfold af_perim; ring
  rw [hF]
  have hae : (Ico (sigmaStieltjes K 0) (sigmaStieltjes K (2 * π)) \ af_bad K : Set ℝ) =ᵐ[volume]
      Ioc (sigmaStieltjes K 0) (sigmaStieltjes K (2 * π)) :=
    (sdiff_null_ae_eq_self ((af_bad_countable hK hP).measure_zero _)).trans Ico_ae_eq_Ioc
  rw [setLIntegral_congr hae]
  have hint : IntegrableOn (af_height K c) (Ioc (sigmaStieltjes K 0) (sigmaStieltjes K (2 * π))) :=
    af_integrableOn_comp_tau hK hP (af_continuous_supp_sub hK c) 0 (2 * π)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const 2)]
  · congr 1
    rw [integral_div, ← af_setIntegral_tau hK hP (af_continuous_supp_sub hK c)]
    simp only [af_height]
    ring
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun y _ =>
      div_nonneg (sub_pos.2 (af_dot_lt_supp hK hc _)).le zero_le_two

/-- A convex body with an interior point has positive perimeter `σ_K((0, 2π])`. -/
lemma af_perim_pos (hK : IsConvexBody K) {c : ℝ × ℝ} (hc : c ∈ interior K) : 0 < af_perim K := by
  by_contra h
  have hP0 : af_perim K = 0 := le_antisymm (not_lt.1 h) (af_perim_nonneg K)
  have hσ : sigma K (Ioc 0 π) = 0 := by
    apply measure_mono_null (Ioc_subset_Ioc_right (by linarith [pi_pos] : π ≤ 2 * π))
    rw [af_sigma_Ioc]
    have : sigmaStieltjes K (2 * π) - sigmaStieltjes K 0 = 0 := hP0
    rw [this, ENNReal.ofReal_zero]
  have hv := vplus_sub_vplus hK pi_pos.le
  rw [setIntegral_measure_zero _ hσ, sub_eq_zero] at hv
  have hw := af_width_pos hK hc 0
  have h1 : supp K π = -supp K 0 := by
    rw [← dot_vplus_uvec K π, hv, ← dot_vplus_uvec K 0, ← dot_neg_right, ← uvec_add_pi, zero_add]
  rw [zero_add, h1] at hw
  linarith

/-- The area formula relative to an interior point `c`:
`|K| = ½ ∫_{(0, 2π]} (h_K(t) - c · u_t) dσ_K(t)`. -/
lemma af_area_eq_of_interior (hK : IsConvexBody K) {c : ℝ × ℝ} (hc : c ∈ interior K) :
    area K = (1 / 2) * ∫ t in Ioc 0 (2 * π), (supp K t - dot c (uvec t)) ∂(sigma K) := by
  have hP := af_perim_pos hK hc
  rw [area, af_volume_eq_cone hK hP hc (sigmaStieltjes K 0),
    af_volume_cone_eq_lintegral hK hP hc, af_lintegral_dom hK hP hc, af_lintegral_height hK hP hc,
    ENNReal.toReal_ofReal]
  exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc
    fun t _ => (sub_pos.2 (af_dot_lt_supp hK hc t)).le)

end Integral

section Degenerate

variable {K : Set (ℝ × ℝ)}

/-- A convex body with empty interior has area `0`. -/
lemma af_area_eq_zero (hK : IsConvexBody K) (h : interior K = ∅) : area K = 0 := by
  have : volume K = 0 := by
    refine measure_mono_null (fun p hp => ?_) (Convex.addHaar_frontier volume hK.2.2)
    rw [hK.isClosed.frontier_eq, h, sdiff_empty]
    exact hp
  rw [area, this, ENNReal.toReal_zero]

/-- A planar convex body with empty interior lies on a line: some nonzero `n` is orthogonal to all
differences of its points. -/
lemma af_exists_normal (hK : IsConvexBody K) (h : interior K = ∅) :
    ∃ n : ℝ × ℝ, n ≠ 0 ∧ ∀ p ∈ K, ∀ q ∈ K, dot (p - q) n = 0 := by
  have hspan : affineSpan ℝ K ≠ ⊤ := by
    intro htop
    have := (hK.2.2.interior_nonempty_iff_affineSpan_eq_top).2 htop
    rw [h] at this
    exact not_nonempty_empty this
  obtain ⟨c, hc⟩ := hK.1
  have hdir : (affineSpan ℝ K).direction < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hspan ?_
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨c, mem_affineSpan ℝ hc⟩).1 htop
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
  have hf : ∀ x : ℝ × ℝ, f x = dot x (f (1, 0), f (0, 1)) := by
    intro x
    have : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, dot]
  refine ⟨(f (1, 0), f (0, 1)), fun hn => hf0 ?_, fun p hp q hq => ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [hf x, hn, dot_zero_right, LinearMap.zero_apply]
  · rw [← hf]
    exact hfker (AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hp) (mem_affineSpan ℝ hq))

/-- Two vectors orthogonal to the same nonzero vector are parallel. -/
lemma af_cross_eq_zero {a b n : ℝ × ℝ} (hn : n ≠ 0) (ha : dot a n = 0) (hb : dot b n = 0) :
    cross a b = 0 := by
  simp only [dot] at ha hb
  have h1 : cross a b * n.1 = 0 := by
    simp only [cross]; linear_combination b.2 * ha - a.2 * hb
  have h2 : cross a b * n.2 = 0 := by
    simp only [cross]; linear_combination a.1 * hb - b.1 * ha
  by_contra hne
  apply hn
  ext
  · exact (mul_eq_zero.1 h1).resolve_left hne
  · exact (mul_eq_zero.1 h2).resolve_left hne

/-- If `K` lies on the line `{p | (p - c) · n = 0}`, then so does the direction `γ'(y) = v_{τ(y)}`
of the boundary curve, wherever `τ` is continuous. -/
lemma af_dot_vvec_tau_eq_zero (hK : IsConvexBody K) (hP : 0 < af_perim K) {n c : ℝ × ℝ}
    (hn : ∀ p ∈ K, dot (p - c) n = 0) {y : ℝ} (hy : ContinuousAt (af_tau K) y) :
    dot (vvec (af_tau K y)) n = 0 := by
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    n.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + n.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ∀ p, L p = dot p n := fun p => by simp [L, dot]; ring
  have h1 := L.hasFDerivAt.comp_hasDerivAt y ((af_hasDerivAt_gamma hK hP hy).sub_const c)
  have h2 : (L ∘ fun y => af_gamma K y - c) = fun _ => 0 := by
    funext y
    simp only [comp_apply, hL]
    exact hn _ (af_gamma_mem hK hP y)
  rw [h2, hL] at h1
  exact h1.unique (hasDerivAt_const y 0)

/-- For a convex body with empty interior, `∫_{(0, 2π]} (h_K(t) - c · u_t) dσ_K(t) = 0`: the
integrand is `(γ(y) - c) × γ'(y) = 0` in the arc-length variable. -/
lemma af_integral_eq_zero (hK : IsConvexBody K) (h : interior K = ∅) {c : ℝ × ℝ} (hcK : c ∈ K) :
    ∫ t in Ioc 0 (2 * π), (supp K t - dot c (uvec t)) ∂(sigma K) = 0 := by
  rcases (af_perim_nonneg K).eq_or_lt with hP0 | hP
  · apply setIntegral_measure_zero
    rw [af_sigma_Ioc]
    have : sigmaStieltjes K (2 * π) - sigmaStieltjes K 0 = 0 := hP0.symm
    rw [this, ENNReal.ofReal_zero]
  · obtain ⟨n, hn0, hn⟩ := af_exists_normal hK h
    rw [← af_setIntegral_tau hK hP (af_continuous_supp_sub hK c)]
    apply integral_eq_zero_of_ae
    have hnull : volume (af_bad K) = 0 := (af_bad_countable hK hP).measure_zero _
    refine ae_restrict_of_ae ((measure_eq_zero_iff_ae_notMem.1 hnull).mono fun y hy => ?_)
    have hcont : ContinuousAt (af_tau K) y := not_not.1 hy
    have h1 := af_dot_vvec_tau_eq_zero hK hP (fun p hp => hn p hp c hcK) hcont
    have h2 : dot (af_gamma K y - c) n = 0 := hn _ (af_gamma_mem hK hP y) c hcK
    have h3 := af_cross_eq_zero hn0 h2 h1
    rw [cross_vvec, dot_sub_left, af_dot_gamma hK hP] at h3
    exact h3

end Degenerate

section Main

variable {K : Set (ℝ × ℝ)}

/-- `dot` with a fixed vector commutes with set integrals. -/
lemma af_dot_setIntegral {μ : Measure ℝ} {s : Set ℝ} {g : ℝ → ℝ × ℝ} (hg : IntegrableOn g s μ)
    (w : ℝ × ℝ) : dot (∫ t in s, g t ∂μ) w = ∫ t in s, dot (g t) w ∂μ := by
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ∀ p, L p = dot p w := fun p => by simp [L, dot]; ring
  rw [← hL, ← L.integral_comp_comm hg]
  simp_rw [hL]

/-- Continuous functions are `σ_K`-integrable on `(0, 2π]`. -/
lemma af_integrableOn_Ioc {G : ℝ → ℝ} (hG : Continuous G) (K : Set (ℝ × ℝ)) :
    IntegrableOn G (Ioc 0 (2 * π)) (sigma K) :=
  hG.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- `∫_{(0, 2π]} c · u_t dσ_K(t) = 0`. -/
lemma af_integral_dot_uvec (hK : IsConvexBody K) (c : ℝ × ℝ) :
    ∫ t in Ioc 0 (2 * π), dot c (uvec t) ∂(sigma K) = 0 := by
  have hw : ∀ t, dot c (uvec t) = dot (vvec t) (-c.2, c.1) := fun t => by
    simp only [dot, uvec, vvec]; ring
  simp_rw [hw]
  rw [← af_dot_setIntegral (af_continuous_vvec.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
    ← vplus_sub_vplus hK two_pi_pos.le]
  have := af_vplus_add_two_pi K 0
  rw [zero_add] at this
  rw [this, sub_self, dot_zero_left]

/-- `[0, 2π)` and `(0, 2π]` give the same `σ_K`-integral of a `2π`-periodic function. -/
lemma af_integral_Ico_eq_Ioc (hK : IsConvexBody K) {G : ℝ → ℝ} (hG : Continuous G)
    (hGp : G (2 * π) = G 0) :
    ∫ t in Ico 0 (2 * π), G t ∂(sigma K) = ∫ t in Ioc 0 (2 * π), G t ∂(sigma K) := by
  have h2π : (0 : ℝ) < 2 * π := two_pi_pos
  have hσ : sigma K {2 * π} = sigma K {0} := by
    have := sigma_periodic hK {0}
    rwa [image_singleton, zero_add] at this
  have hint : ∀ s : Set ℝ, s ⊆ Icc 0 (2 * π) → IntegrableOn G s (sigma K) := fun s hs =>
    hG.integrableOn_Icc.mono_set hs
  rw [← Ioo_union_left h2π, ← Ioo_union_right h2π,
    setIntegral_union (disjoint_singleton_right.2 fun h => lt_irrefl _ h.1)
      (measurableSet_singleton _) (hint _ Ioo_subset_Icc_self)
      (hint _ (singleton_subset_iff.2 (left_mem_Icc.2 h2π.le))),
    setIntegral_union (disjoint_singleton_right.2 fun h => lt_irrefl _ h.2)
      (measurableSet_singleton _) (hint _ Ioo_subset_Icc_self)
      (hint _ (singleton_subset_iff.2 (right_mem_Icc.2 h2π.le))),
    integral_singleton, integral_singleton, hGp, Measure.real, Measure.real, hσ]

end Main

end AreaFormulaProof

/-- `|K| = ½ ∫_{[0, 2π)} h_K dσ_K` for every planar convex body `K`. -/
theorem area_eq_half_integral_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    area K = (1 / 2) * ∫ t in Ico 0 (2 * π), supp K t ∂(sigma K) := by
  have hsupp : Continuous (supp K) := continuous_supp hK.2.1 hK.1
  have hper : supp K (2 * π) = supp K 0 := by
    have := supp_add_two_pi K 0
    rwa [zero_add] at this
  rw [af_integral_Ico_eq_Ioc hK hsupp hper]
  have hdot : ∀ c : ℝ × ℝ, Continuous fun t => dot c (uvec t) := fun c => by
    unfold dot uvec; fun_prop
  rcases (interior K).eq_empty_or_nonempty with h | ⟨c, hc⟩
  · obtain ⟨c, hcK⟩ := hK.1
    have := af_integral_eq_zero hK h hcK
    rw [integral_sub (af_integrableOn_Ioc hsupp K) (af_integrableOn_Ioc (hdot c) K),
      af_integral_dot_uvec hK c, sub_zero] at this
    rw [af_area_eq_zero hK h, this, mul_zero]
  · rw [af_area_eq_of_interior hK hc, integral_sub (af_integrableOn_Ioc hsupp K)
      (af_integrableOn_Ioc (hdot c) K), af_integral_dot_uvec hK c, sub_zero]

end MovingSofa
