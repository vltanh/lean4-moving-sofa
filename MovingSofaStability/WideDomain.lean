module

public import MovingSofaOptimality.Convex.ConvexDomain
public import MovingSofaUniqueness.Mamikon

/-!
# Baek's upper bound on the enlarged domain of triples

Baek's upper bound `𝒬` extended to the enlarged domain `T̄` of triples, on which the cap may have
corners (curvature atoms): the quadratic deficit identity, the Mamikon energies, the domain and its
algebra of curves of bounded variation, the concavity of `𝒬` on `T̄`, and the first variation of
the area of a cap.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-! ## The deficit of a quadratic functional -/

/-- Four times the midpoint concavity gap. For a quadratic functional this is its negative quadratic
part in the direction from `x` to `y`. -/
def segmentEnergy {V : Type} (D : ConvexDomain V) (Q : V → ℝ) (x y : V) : ℝ :=
  4 * (Q (D.comb (1 / 2) x y) - (Q x + Q y) / 2)

/-- The deficit of a quadratic functional is its negative first variation plus the segment
energy. -/
theorem deficit_eq_neg_dirDeriv_add_energy {V : Type} (D : ConvexDomain V)
    {Q : V → ℝ} (hq : D.IsQuadratic Q) (x y : V) :
    Q x - Q y = -D.dirDeriv Q x y + segmentEnergy D Q x y := by
  obtain ⟨g, hg, hfg⟩ := hq
  obtain rfl : Q = fun z => g z z := funext hfg
  simp only [lemma7_1_4 D hg, segmentEnergy,
    cvx_bilin_comb D hg x y (c := 1 / 2) ⟨by norm_num, by norm_num⟩]
  ring

/-! ## Mamikon energies

Along the Minkowski combinations `(1 - c) K₀ + c K₁` of two convex bodies, the convexity gap of
Mamikon's area is `c (1 - c)` times half the integral of the squared difference of their tangent
displacements.
-/

/-- Half the integral of the squared difference of two tangent displacements on the open arc
`(a, b)`. -/
def displacementEnergy (a b : ℝ) (z : ConvexBodySet → ℝ → ℝ × ℝ)
    (K₀ K₁ : ConvexBodySet) : ℝ :=
  halfSquareIntegral (volume.restrict (Ioo a b))
    (fun t => displacement K₀.1 (z K₀) t - displacement K₁.1 (z K₁) t)

/-- The displacement energy is nonnegative. -/
theorem displacementEnergy_nonneg (a b : ℝ)
    (z : ConvexBodySet → ℝ → ℝ × ℝ) (K₀ K₁ : ConvexBodySet) :
    0 ≤ displacementEnergy a b z K₀ K₁ :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

/-- The convexity gap of Mamikon's area along `(1 - c) K₀ + c K₁` is `c (1 - c)` times the
displacement energy. -/
theorem mamikon_combo_energy {a b : ℝ} (hab : a < b) (hb : b < a + π)
    (z : ConvexBodySet → ℝ → ℝ × ℝ) (hz : ∀ K, IsCBV (z K) a b)
    (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)
    (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)
    (K₀ K₁ : ConvexBodySet) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁) -
      mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      c * (1 - c) * displacementEnergy a b z K₀ K₁ := by
  have hM := mamikon_eq_halfSquareIntegral hab hb z hz hzl
  have hI := displacement_mul_integrable hab hb z hz hzl
  have hsq : ∀ K, Integrable (fun t => displacement K.1 (z K) t ^ 2) (volume.restrict (Ioo a b)) :=
    fun K => (hI K K).congr (.of_forall fun t => (sq _).symm)
  -- the displacement of the combination is the combination of the displacements
  have hcombo : mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      halfSquareIntegral (volume.restrict (Ioo a b))
        (fun t => (1 - c) * displacement K₀.1 (z K₀) t + c * displacement K₁.1 (z K₁) t) := by
    rw [hM, halfSquareIntegral, halfSquareIntegral]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    simp only [displacement_combo z hlin K₀ K₁ hc (Ioo_subset_Icc_self ht)]
  rw [hcombo, hM, hM, halfSquareIntegral_combo_gap _ c (hsq K₀) (hsq K₁) (hI K₀ K₁),
    displacementEnergy, halfSquareIntegral]
  ring

/-! ## The enlarged domain `T̄`

The triples of Baek's domain `𝓛`, with the condition `K ∈ 𝒦^i` on the cap weakened to `K` being a
normalized cap with rotation angle `π/2`.
-/

/-- The wall constraints of `𝓛`, with `IsCap` instead of `IsKi`. -/
def InWideL (φ : ℝ) (K B D : Set (ℝ × ℝ)) : Prop :=
  IsCap K (π / 2) ∧ IsConvexBody B ∧ IsConvexBody D ∧ B ⊆ K ∧ D ⊆ K ∧
    (∀ t ∈ Icc φ (π / 2), supp K t + supp B (π + t) ≤ 1) ∧
    supp K φ + supp B (π + φ) = 1 ∧ supp K (π / 2) + supp B (π + π / 2) = 1 ∧
    (∀ t ∈ Icc 0 (π / 2 - φ), supp K (π / 2 + t) + supp D (3 * π / 2 + t) ≤ 1) ∧
    supp K (π / 2 + 0) + supp D (3 * π / 2 + 0) = 1 ∧
    supp K (π / 2 + (π / 2 - φ)) + supp D (3 * π / 2 + (π / 2 - φ)) = 1

/-- A triple of `𝓛` satisfies the constraints of `T̄`. -/
theorem inWideL_of_inL {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    InWideL φ K B D := ⟨h.1.1, h.2⟩

/-- The tails touch their walls: `h_B(3π/2) = h_D(3π/2) = 0`, `h_B(π + φ) = 1 - h_K(φ)` and
`h_D(3π/2 + φ^L) = 1 - h_K(π - φ)`. Only the cap normalization and the contacts are used. -/
theorem inWideL_supp {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InWideL φ K B D) :
    supp B (3 * π / 2) = 0 ∧ supp D (3 * π / 2) = 0 ∧
      supp B (π + φ) = 1 - supp K φ ∧
      supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ) := by
  obtain ⟨hK, -, -, -, -, -, e1, e1', -, e2, e2'⟩ := h
  rw [hK.2.2.2.1, show π + π / 2 = 3 * π / 2 by ring] at e1'
  rw [add_zero, add_zero, hK.2.2.2.1] at e2
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at e2'
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The constraints of `T̄` are preserved by componentwise Minkowski combinations. -/
theorem inWideL_comb {φ : ℝ} {K₁ B₁ D₁ K₂ B₂ D₂ : Set (ℝ × ℝ)}
    (h₁ : InWideL φ K₁ B₁ D₁) (h₂ : InWideL φ K₂ B₂ D₂)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    InWideL φ ((1 - c) • K₁ + c • K₂) ((1 - c) • B₁ + c • B₂)
      ((1 - c) • D₁ + c • D₂) := by
  obtain ⟨hK₁, hB₁, hD₁, hBK₁, hDK₁, i1, e1, e1', i2, e2, e2'⟩ := h₁
  obtain ⟨hK₂, hB₂, hD₂, hBK₂, hDK₂, j1, f1, f1', j2, f2, f2'⟩ := h₂
  have sK := supp_comb hK₁.2.1 hK₂.2.1 hc
  have sB := supp_comb hB₁ hB₂ hc
  have sD := supp_comb hD₁ hD₂ hc
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  refine ⟨opt_comb_isCap hK₁ hK₂ hc, isConvexBody_comb hB₁ hB₂, isConvexBody_comb hD₁ hD₂,
    Set.add_subset_add (smul_set_mono hBK₁) (smul_set_mono hBK₂),
    Set.add_subset_add (smul_set_mono hDK₁) (smul_set_mono hDK₂),
    fun t ht => ?_, ?_, ?_, fun t ht => ?_, ?_, ?_⟩ <;> simp only [sK, sB, sD]
  · linarith [mul_le_mul_of_nonneg_left (i1 t ht) hc1, mul_le_mul_of_nonneg_left (j1 t ht) hc.1]
  · linear_combination (1 - c) * e1 + c * f1
  · linear_combination (1 - c) * e1' + c * f1'
  · linarith [mul_le_mul_of_nonneg_left (i2 t ht) hc1, mul_le_mul_of_nonneg_left (j2 t ht) hc.1]
  · linear_combination (1 - c) * e2 + c * f2
  · linear_combination (1 - c) * e2' + c * f2'

/-- The enlarged domain `T̄`: the triples of convex bodies satisfying `InWideL`. -/
def WideTriple (φ : ℝ) : Type :=
  {x : ConvexBodySet × ConvexBodySet × ConvexBodySet //
    InWideL φ x.1.1 x.2.1.1 x.2.2.1}

open Classical in
/-- The componentwise barycentric operation on `T̄`. -/
noncomputable def WideTriple.comb {φ : ℝ} (c : ℝ) (x y : WideTriple φ) : WideTriple φ :=
  if hc : c ∈ Icc (0 : ℝ) 1 then
    ⟨(convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
      convexBodyComb c x.1.2.2 y.1.2.2), by
        simpa [convexBodyComb, hc] using inWideL_comb x.2 y.2 hc⟩
  else x

/-- The support functions embed `T̄` in a real vector space, turning `WideTriple.comb` into convex
combinations. -/
theorem wideTriple_embeds (φ : ℝ) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : WideTriple φ → E),
      Function.Injective e ∧ ∀ c ∈ Icc (0 : ℝ) 1, ∀ x y,
        e (WideTriple.comb c x y) = (1 - c) • e x + c • e y := by
  obtain ⟨E, i1, i2, e, he, hlin⟩ := theorem7_1_1
  refine ⟨E × E × E, inferInstance, inferInstance, fun x => (e x.1.1, e x.1.2.1, e x.1.2.2),
    fun x y hxy => ?_, fun c hc x y => ?_⟩
  · simp only [Prod.mk.injEq] at hxy
    exact Subtype.ext (Prod.ext (he hxy.1) (Prod.ext (he hxy.2.1) (he hxy.2.2)))
  · simp only [WideTriple.comb, hc, ↓reduceDIte, hlin c hc, Prod.smul_mk, Prod.mk_add_mk]

/-- `T̄` as a convex domain. -/
noncomputable def wideDomain (φ : ℝ) : ConvexDomain (WideTriple φ) where
  comb := WideTriple.comb
  embeds := wideTriple_embeds φ

/-- Baek's upper bound `𝒬` on `T̄`, with its original curve-area definition. -/
def wideUpperQ (φ : ℝ) (x : WideTriple φ) : ℝ :=
  upperQ φ x.1.1.1 x.1.2.1.1 x.1.2.2.1

/-- A triple of `𝓛` as a triple of `T̄`. -/
def toWideTriple {φ : ℝ} (x : LTriple φ) : WideTriple φ :=
  ⟨x.1, inWideL_of_inL x.2⟩

/-- At Gerver's triple, `𝒬` is the area of Gerver's sofa. -/
theorem gerver_upperQL_eq_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    upperQL P.φ (gerverTriple hP hbox) = area (gerverSofa P) :=
  (theorem8_4_6 hP hbox).symm.trans (GerverParams.gm_sofaArea_cap hP hbox)

/-! ## The tail decomposition

Baek's Lemma 8.3.4, `𝒬(K, B, D) = 𝒫_K - ℛ_B - ℒ_D`, holds on `T̄`: its proof uses only the cap
normalization and the wall contacts.
-/

/-- `𝐥_K^t(t) = v_K⁻(t)`. -/
private theorem tangentParam_self (K : Set (ℝ × ℝ)) (t : ℝ) :
    tangentParam K t t = vminus K t :=
  ite_eq_right (lt_irrefl t)

/-- The tail decomposition `𝒬(K, B, D) = 𝒫_K - ℛ_B - ℒ_D` on `T̄`. -/
theorem wide_upperQ_decomposition {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K B D : Set (ℝ × ℝ)} (h : InWideL φ K B D) :
    upperQ φ K B D = upperP φ K - mamikonR φ B - mamikonL φ D := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  obtain ⟨hB3, hD3, hBa, hDb⟩ := inWideL_supp h
  obtain ⟨-, hBcb, hDcb, -⟩ := h
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- the tangent line pieces of `ℛ_B` and `ℒ_D` are the segments `[W_K^R, v_B⁻(3π/2)]` and
  -- `[Z_K^L, v_D⁻(3π/2 + φ^L)]` (Theorem 8.3.1)
  have tR : tangentParam B (3 * π / 2) (π + φ) = wRight φ K := by
    simp only [tangentParam, show π + φ < 3 * π / 2 by linarith, ↓reduceIte]
    exact opt_vint_right_eq ⟨hφ0, by linarith⟩ hBa hB3
  have tL : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2) = zLeft φ K := by
    simp only [tangentParam, show 3 * π / 2 < 3 * π / 2 + (π / 2 - φ) by linarith, ↓reduceIte]
    exact opt_vint_left_eq hD3 hDb
  have hlR := (theorem8_3_1 hBcb (t := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) le_rfl).2.2
  have hlL := (theorem8_3_1 hDcb (t := 3 * π / 2 + (π / 2 - φ)) (a := 3 * π / 2)
    (b := 3 * π / 2 + (π / 2 - φ)) (by linarith) (by linarith) le_rfl).2.2
  -- the segment terms: points on the `x`-axis, and collinear points on `b_K^R` and `d_K^L`
  have z1 := segArea_of_snd_eq_zero (p := wRight φ K) rfl (opt_snd_vminus_three_pi_div_two hB3)
  have z2 := segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3) (q := zLeft φ K)
    (by rw [opt_zLeft_eq])
  obtain ⟨hXB, hWl, hxR⟩ := opt_right_mem_line hc.ne' hBa
  obtain ⟨hYD, hZl, hxL⟩ := opt_left_mem_line hc.ne' hDb
  have c1 := segArea_add_of_mem_line hxR hXB hWl
  have c2 := segArea_add_of_mem_line hZl hYD hxL
  simp only [upperQ, upperP, mamikonR, mamikonL, mamikon, hlR, hlL, tR, tL, tangentParam_self,
    segArea_self]
  simp only [xB, yD] at c1 c2 ⊢
  linarith

/-! ## The corner curves differ by a fixed curve

The outer corner curve is the inner one plus the fixed curve `u_t + v_t`. In the vector space of
continuous curves of bounded variation, Lemma 7.1.6 then makes the difference of their curve areas
affine on all convex bodies (Baek's Lemma 8.3.6 (1) without `𝒦^i`).
-/

/-- The continuous curves of bounded variation on `[a, b]` form a submodule. -/
def cbvSubmodule (a b : ℝ) : Submodule ℝ (ℝ → ℝ × ℝ) where
  carrier := {x | IsCBV x a b}
  zero_mem' := ⟨continuousOn_const, by simp [BoundedVariationOn, eVariationOn]⟩
  add_mem' hx hy := ⟨hx.1.add hy.1, boundedVariationOn_add hx.2 hy.2⟩
  smul_mem' c _ hx := ⟨hx.1.const_smul c, cvx_bv_const_smul hx.2 c⟩

/-- The vector space of continuous curves of bounded variation on `[a, b]`. -/
abbrev CBVSpace (a b : ℝ) := ↥(cbvSubmodule a b)

/-- The curve bilinear form is convex-bilinear on `CBVSpace a b`. -/
theorem cbvSpace_bilinear {a b : ℝ} (hab : a ≤ b) :
    (vectorDomain (CBVSpace a b)).IsConvexBilinear (vectorDomain (CBVSpace a b)) realDomain
      (fun x y => curveBilin x.1 y.1 a b) :=
  ⟨fun x _ _ y z => cvx_curveBilin_comb_right hab x.2.1 y.2 z.2,
    fun y c _ x z => cvx_curveBilin_comb_left y.1 x.2.1 z.2.1 c⟩

/-- `𝒥(𝐲_K|_{[a,b]}) - 𝒥(𝐱_K|_{[a,b]})` is affine under Minkowski combinations of convex
bodies. -/
theorem outer_inner_area_affine {a b c : ℝ} (hab : a ≤ b)
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    curveArea (outerCorner ((1 - c) • K₁ + c • K₂)) a b -
      curveArea (innerCorner ((1 - c) • K₁ + c • K₂)) a b =
      (1 - c) * (curveArea (outerCorner K₁) a b - curveArea (innerCorner K₁) a b) +
      c * (curveArea (outerCorner K₂) a b - curveArea (innerCorner K₂) a b) := by
  let x : CBVSpace a b := ⟨innerCorner K₁, opt_innerCorner_cbv h₁ a b⟩
  let y : CBVSpace a b := ⟨innerCorner K₂, opt_innerCorner_cbv h₂ a b⟩
  -- the fixed curve `w = 𝐲_K - 𝐱_K`
  let w : CBVSpace a b := ⟨outerCorner K₁, opt_outerCorner_cbv h₁ a b⟩ - x
  have hw : ∀ (K : Set (ℝ × ℝ)) (v : CBVSpace a b), v.1 = innerCorner K →
      (v + w).1 = outerCorner K := by
    intro K v hv
    funext t
    change v.1 t + (outerCorner K₁ t - innerCorner K₁ t) = _
    rw [hv, opt_outer_eq_inner_add K₁, opt_outer_eq_inner_add K]
    abel
  have hz : ((1 - c) • x + c • y).1 = innerCorner ((1 - c) • K₁ + c • K₂) :=
    (opt_innerCorner_comb h₁ h₂ hc).symm
  -- Lemma 7.1.6: `v ↦ 𝒥(v) - 𝒥(v + w)` is affine
  have he := lemma7_1_6 (cbvSpace_bilinear hab) w w c hc x y
  change curveArea ((1 - c) • x + c • y).1 a b - curveArea ((1 - c) • x + c • y + w).1 a b =
    (1 - c) * (curveArea x.1 a b - curveArea (x + w).1 a b) +
      c * (curveArea y.1 a b - curveArea (y + w).1 a b) at he
  rw [hw _ _ hz, hz, hw K₁ x rfl, hw K₂ y rfl] at he
  linarith

/-! ## The cap area with its curvature atoms

A cap may have curvature atoms at `0`, `φ`, `π/2 - φ`, `π/2` and `π`. Splitting
`|K| = ½ ∫_{[0, π]} h_K dσ_K` along the four Mamikon arcs keeps the supporting face of each atom.
-/

/-- The signed area `𝒥(v_K⁻(t), v_K⁺(t))` of the supporting face `e_K(t)`. -/
def edgeArea (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  segArea (vminus K t) (vplus K t)

/-- A curvature atom contributes its supporting face: `𝒥(e_K(t)) = σ_K({t}) h_K(t) / 2`. -/
theorem edgeArea_eq_atom {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    edgeArea K t = (1 / 2) * (sigma K).real {t} * supp K t := by
  have hcross : cross (vminus K t) (vvec t) = supp K t := by
    simpa [cross, vvec, dot, uvec] using dot_vminus_uvec K t
  rw [edgeArea, segArea, (proposition2_1_2 hK t).2, cross_add_right, cross_self,
    cross_smul_right, hcross]
  simp only [zero_add, sigmaAt, measureReal_def]
  ring

/-- Adding a point to a bounded set adds the point's atom to the integral of a continuous
function. -/
private theorem setIntegral_union_singleton {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : Bornology.IsBounded s) {x : ℝ}
    (hx : x ∉ s) : ∫ t in s ∪ {x}, f t ∂μ = ∫ t in s, f t ∂μ + μ.real {x} * f x := by
  rw [setIntegral_union (disjoint_singleton_right.2 hx) (measurableSet_singleton x)
    ((hf.continuousOn.integrableOn_compact hs.isCompact_closure).mono_set subset_closure)
    (hf.continuousOn.integrableOn_compact isCompact_singleton), integral_singleton, smul_eq_mul]

/-- The area of a cap is the sum of the four cap Mamikon arcs and the five supporting faces between
them. No atom is omitted. -/
theorem cap_area_four_arcs {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    area K = convexCurveArea K 0 φ + convexCurveArea K φ (π / 2 - φ) +
      convexCurveArea K (π / 2 - φ) (π / 2) + convexCurveArea K (π / 2) π +
      edgeArea K 0 + edgeArea K φ + edgeArea K (π / 2 - φ) +
      edgeArea K (π / 2) + edgeArea K π := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hcb := hK.2.1
  have hf := hcb.continuous_supp
  -- `|K| = ½ ∫_{[0, π]} h_K dσ_K` splits at `π/2` into two arcs and the atoms at `0`, `π/2`, `π`
  have h2 : area K = convexCurveArea K 0 (π / 2) + convexCurveArea K (π / 2) π +
      edgeArea K 0 + edgeArea K (π / 2) + edgeArea K π := by
    rw [theorem7_1_3 hcb, opt_Ico_eq_Icc hK hf hK.2.2.2.2.2.1, ← Ioc_union_left hpi.le,
      setIntegral_union_singleton hf (Metric.isBounded_Ioc _ _),
      ← intervalIntegral.integral_of_le hpi.le,
      ← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 (π / 2))
        (hf.intervalIntegrable (π / 2) π),
      intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
      ← Ioo_union_right (by linarith : (0 : ℝ) < π / 2),
      ← Ioo_union_right (by linarith : π / 2 < π),
      setIntegral_union_singleton hf (Metric.isBounded_Ioo _ _),
      setIntegral_union_singleton hf (Metric.isBounded_Ioo _ _), edgeArea_eq_atom hcb,
      edgeArea_eq_atom hcb, edgeArea_eq_atom hcb, convexCurveArea, convexCurveArea]
    · ring
    all_goals simp
  -- Lemma 7.3.4 splits the arc `(0, π/2)` at `φ` and `π/2 - φ`, with the faces there
  have c1 := (lemma7_3_4 hcb hφ0 (by linarith : φ < π / 2) (by linarith)).2.2.2
  have c2 := (lemma7_3_4 hcb (by linarith : φ < π / 2 - φ) (by linarith : π / 2 - φ < π / 2)
    (by linarith)).2.2.2
  unfold edgeArea at *
  linarith

/-! ## The affine part of `𝒮_K + 𝒫_K`

Baek's Lemma 8.3.7 for all caps: `𝒮_K + 𝒫_K` is affine in `K`. Each supporting face is joined to its
adjacent connector segments, so `v_K⁻ = v_K⁺` is nowhere assumed. Unlike in the proof for `𝒦^i`, the
boundary part has no vertex coordinates: the top face cancels them.
-/

/-- The boundary part of `𝒮_K + 𝒫_K` left after joining the five supporting faces. -/
def capAffineBoundary (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  supp K 0 + supp K π + (2 * sin φ - supp K φ - supp K (π - φ)) / (2 * cos φ)

/-- `𝒥(𝐥_K^{π/2}(φ), 𝐲_K(φ)) - 𝒥(W_K^R, 𝐱_K^R)`. -/
def rightSegmentRemainder (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  segArea (tangentParam K (π / 2) φ) (outerCorner K φ) -
    segArea (wRight φ K) (xRight φ K)

/-- `𝒥(𝐥_K^{π/2 + φ^L}(π/2), 𝐲_K(φ^L)) - 𝒥(Z_K^L, 𝐱_K^L)`. -/
def leftSegmentRemainder (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2))
      (outerCorner K (π / 2 - φ)) -
    segArea (zLeft φ K) (xLeft φ K)

/-- Joining the supporting face `e_K(t)` between two points of the supporting line `l_K(t)`. -/
private theorem segArea_join_face {K : Set (ℝ × ℝ)} {t : ℝ} {z₁ z₂ : ℝ × ℝ}
    (hz₁ : z₁ ∈ line t (supp K t)) (hz₂ : z₂ ∈ line t (supp K t)) :
    segArea z₁ (vminus K t) + segArea (vplus K t) z₂ + edgeArea K t = segArea z₁ z₂ := by
  have h1 := segArea_add_of_mem_line hz₁ (dot_vminus_uvec K t) (dot_vplus_uvec K t)
  have h2 := segArea_add_of_mem_line hz₁ (dot_vplus_uvec K t) hz₂
  rw [edgeArea]
  linarith

/-- `𝒮_K + 𝒫_K` for every normalized cap: the boundary part, the two segment remainders and the
curve-area difference of the corner curves. -/
theorem mamikonS_add_upperP_nonsmooth {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    mamikonS φ K + upperP φ K = capAffineBoundary φ K + rightSegmentRemainder φ K +
      (curveArea (outerCorner K) φ (π / 2 - φ) -
        curveArea (innerCorner K) φ (π / 2 - φ)) - leftSegmentRemainder φ K := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hcb := hK.2.1
  have htop : supp K (π / 2) = 1 := hK.2.2.2.1
  -- `𝐥_K^t(s) = v_K(s, t)` lies on `l_K(s)` for `s < t`
  have hmem : ∀ {s t : ℝ}, s < t → tangentParam K t s ∈ line s (supp K s) := fun hst => by
    rw [tangentParam, ite_eq_left hst]
    exact vint_mem_line_left K _ _
  -- the tangent line pieces are segments (Theorem 8.3.1), with these endpoints
  have c1 := (theorem8_3_1 hcb (t := π / 2) (a := 0) (b := φ) (by linarith) hφ0.le
    (by linarith)).2.2
  have c3 := (theorem8_3_1 hcb (t := π / 2 + (π / 2 - φ)) (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith)).2.2
  have c4 := (theorem8_3_1 hcb (t := π) (a := π / 2) (b := π) (by linarith) (by linarith)
    le_rfl).2.2
  have l10 : tangentParam K (π / 2) 0 = (supp K 0, 1) := by
    simp only [tangentParam, show (0 : ℝ) < π / 2 by linarith, ↓reduceIte, vint, htop,
      sub_zero, cos_pi_div_two, sin_pi_div_two, uvec_zero, vvec_zero]
    ext <;> simp
  have l3b : tangentParam K (π / 2 + (π / 2 - φ)) (π / 2 - φ) = outerCorner K (π / 2 - φ) := by
    rw [show π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 by ring]
    simp only [tangentParam, show π / 2 - φ < π / 2 - φ + π / 2 by linarith, ↓reduceIte, vint,
      add_sub_cancel_left, cos_pi_div_two, sin_pi_div_two, mul_zero, sub_zero, div_one,
      proposition2_2_2_outerCorner]
  have l4v : tangentParam K π (π / 2) = (-supp K π, 1) := by
    simp only [tangentParam, show π / 2 < π by linarith, ↓reduceIte, vint, htop,
      show π - π / 2 = π / 2 by ring, cos_pi_div_two, sin_pi_div_two, mul_zero, sub_zero,
      div_one, uvec_pi_div_two, vvec_pi_div_two]
    ext <;> simp
  -- each of the five supporting faces is joined to its adjacent connector segments
  have e0 := segArea_join_face (dot_vminus_uvec K 0) (hmem (by linarith : (0 : ℝ) < π / 2))
  have eφ := segArea_join_face (hmem hφ2.2) (inj_dot_outerCorner_uvec K φ)
  have eb := segArea_join_face (inj_dot_outerCorner_uvec K (π / 2 - φ))
    (inj_dot_outerCorner_uvec K (π / 2 - φ))
  have ev := segArea_join_face (hmem (by linarith : π / 2 < π / 2 + (π / 2 - φ)))
    (hmem (by linarith : π / 2 < π))
  have eπ := segArea_join_face (show tangentParam K π (π / 2) ∈ line π (supp K π) by
    rw [l4v]; simp [line, dot, uvec]) (dot_vplus_uvec K π)
  simp only [segArea_self] at e0 eb eπ
  -- the joined boundary segments have explicit endpoints
  have hboundary : segArea (vminus K 0) (tangentParam K (π / 2) 0) +
      segArea (tangentParam K (π / 2) 0) (tangentParam K (π / 2) φ) +
      segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2)) (tangentParam K π (π / 2)) +
      segArea (tangentParam K π (π / 2)) (vplus K π) = capAffineBoundary φ K := by
    have hc : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, hφ2.2⟩).ne'
    rw [(inj_cap_consecutive hK).1, opt_cap_vplus_pi hK, l10, l4v,
      opt_tangent_right_eq hφ2 htop, opt_tangent_left_eq hφ2 htop, opt_wRight_eq, opt_zLeft_eq]
    simp only [capAffineBoundary, segArea, cross, Prod.fst_add, Prod.snd_add]
    field_simp
    ring
  rw [rightSegmentRemainder, leftSegmentRemainder]
  simp only [mamikonS, mamikon, upperP, c1, c3, c4, l3b, tangentParam_self, segArea_self]
  linarith only [cap_area_four_arcs ⟨hφ0, hφ4⟩ hK, e0, eφ, eb, ev, eπ, hboundary,
    segArea_swap (xRight φ K) (wRight φ K),
    segArea_swap (outerCorner K (π / 2 - φ)) (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2))]

/-- Baek's Lemma 8.3.7 for all normalized caps: `𝒮_K + 𝒫_K` is affine under Minkowski
combinations. -/
theorem cap_mamikon_upperP_affine {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    mamikonS φ ((1 - c) • K₁ + c • K₂) + upperP φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * (mamikonS φ K₁ + upperP φ K₁) +
      c * (mamikonS φ K₂ + upperP φ K₂) := by
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ.1, by linarith [hφ.2, pi_pos]⟩
  have hM := opt_comb_isCap h₁ h₂ hc
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  -- the boundary part is affine in the support function
  have hboundary : capAffineBoundary φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * capAffineBoundary φ K₁ + c * capAffineBoundary φ K₂ := by
    simp only [capAffineBoundary, supp_comb hcb₁ hcb₂ hc]
    ring
  -- the segment remainders: `𝐥_K^{π/2}(φ) - W_K^R`, `𝐥_K^{π/2 + φ^L}(π/2) - Z_K^L` and
  -- `𝐲_K - 𝐱_K` are constant, and `W_K^R`, `Z_K^L` and `𝐱_K` are affine in `K`
  have hright : rightSegmentRemainder φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * rightSegmentRemainder φ K₁ + c * rightSegmentRemainder φ K₂ := by
    simp only [rightSegmentRemainder, xRight, opt_tangent_right_eq hφ2 hM.2.2.2.1,
      opt_tangent_right_eq hφ2 h₁.2.2.2.1, opt_tangent_right_eq hφ2 h₂.2.2.2.1,
      opt_outer_eq_inner_add, opt_wRight_comb hcb₁ hcb₂ hc, opt_innerCorner_comb hcb₁ hcb₂ hc,
      segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have hleft : leftSegmentRemainder φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * leftSegmentRemainder φ K₁ + c * leftSegmentRemainder φ K₂ := by
    simp only [leftSegmentRemainder, xLeft, opt_tangent_left_eq hφ2 hM.2.2.2.1,
      opt_tangent_left_eq hφ2 h₁.2.2.2.1, opt_tangent_left_eq hφ2 h₂.2.2.2.1,
      opt_outer_eq_inner_add, opt_zLeft_comb hcb₁ hcb₂ hc, opt_innerCorner_comb hcb₁ hcb₂ hc,
      segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have hcurve := outer_inner_area_affine (a := φ) (b := π / 2 - φ) (by linarith [hφ.2]) hcb₁ hcb₂ hc
  rw [mamikonS_add_upperP_nonsmooth hφ hM, mamikonS_add_upperP_nonsmooth hφ h₁,
    mamikonS_add_upperP_nonsmooth hφ h₂]
  linarith

/-! ## Concavity of `𝒬` on `T̄` -/

/-- The projection `(K, B, D) ↦ K` is convex-linear on `T̄`. -/
theorem wide_projK_linear (φ : ℝ) :
    (wideDomain φ).IsConvexLinear convexBodyDomain (fun x : WideTriple φ => x.1.1) :=
  fun c hc x y => by simp only [wideDomain, convexBodyDomain, WideTriple.comb, hc, ↓reduceDIte]

/-- The projection `(K, B, D) ↦ B` is convex-linear on `T̄`. -/
theorem wide_projB_linear (φ : ℝ) :
    (wideDomain φ).IsConvexLinear convexBodyDomain (fun x : WideTriple φ => x.1.2.1) :=
  fun c hc x y => by simp only [wideDomain, convexBodyDomain, WideTriple.comb, hc, ↓reduceDIte]

/-- The projection `(K, B, D) ↦ D` is convex-linear on `T̄`. -/
theorem wide_projD_linear (φ : ℝ) :
    (wideDomain φ).IsConvexLinear convexBodyDomain (fun x : WideTriple φ => x.1.2.2) :=
  fun c hc x y => by simp only [wideDomain, convexBodyDomain, WideTriple.comb, hc, ↓reduceDIte]

/-- Baek's Proposition 8.2.1 on `T̄`: `𝒬` is quadratic. -/
theorem wideUpperQ_quadratic {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (wideDomain φ).IsQuadratic (wideUpperQ φ) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have t1 : (wideDomain φ).IsQuadratic (fun x => area x.1.1.1) :=
    opt_isQuadratic_comp (wide_projK_linear φ) theorem7_1_3_quadratic
  have t2 : (wideDomain φ).IsQuadratic
      (fun x => convexCurveArea x.1.2.2.1 (3 * π / 2) (3 * π / 2 + (π / 2 - φ))) :=
    opt_isQuadratic_comp (wide_projD_linear φ) theorem7_3_2_quadratic
  have t3 : (wideDomain φ).IsQuadratic
      (fun x => segArea (yD φ x.1.2.2.1) (xLeft φ x.1.1.1)) :=
    opt_isQuadratic_segArea
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (wide_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (wide_projK_linear φ) (opt_innerCorner_linear _))
  have t4 : (wideDomain φ).IsQuadratic
      (fun x => curveArea (innerCorner x.1.1.1) φ (π / 2 - φ)) :=
    opt_isQuadratic_comp
      (opt_isConvexLinear_comp (wide_projK_linear φ) (opt_innerCBV_linear φ (π / 2 - φ)))
      (proposition7_2_2 (by linarith))
  have t5 : (wideDomain φ).IsQuadratic
      (fun x => segArea (xRight φ x.1.1.1) (xB φ x.1.2.1.1)) :=
    opt_isQuadratic_segArea
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (wide_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (wide_projB_linear φ) (opt_vplus_linear _))
  have t6 : (wideDomain φ).IsQuadratic
      (fun x => convexCurveArea x.1.2.1.1 (π + φ) (3 * π / 2)) :=
    opt_isQuadratic_comp (wide_projB_linear φ) theorem7_3_2_quadratic
  exact opt_isQuadratic_add (opt_isQuadratic_add (opt_isQuadratic_sub
    (opt_isQuadratic_add (opt_isQuadratic_add t1 t2) t3) t4) t5) t6

/-- The cap Mamikon sum `𝒮_K` is convex on all convex bodies, not only on `𝒦^i`. -/
theorem mamikonS_convex_all {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    convexBodyDomain.IsConvexFun (fun K => mamikonS φ K.1) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have c1 := (opt_mamikon_tangent (t := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith)).2
  have c2 := (opt_mamikon_outer (a := φ) (b := π / 2 - φ) (by linarith) (by linarith)).2
  have c3 := (opt_mamikon_tangent (t := π / 2 + (π / 2 - φ)) (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)).2
  have c4 := (opt_mamikon_tangent (t := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl).2
  exact opt_isConvexFun_add (opt_isConvexFun_add (opt_isConvexFun_add c1 c2) c3) c4

/-- Baek's Theorem 8.3.8 on `T̄`: `𝒬` is concave, with no regularity of the cap. -/
theorem wideUpperQ_concave {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (wideDomain φ).IsConcave (wideUpperQ φ) := by
  intro x y c hc
  obtain ⟨-, -, -, cR, -, cL⟩ := lemma8_3_3 hφ
  have hS := mamikonS_convex_all hφ x.1.1 y.1.1 c hc
  have hR := cR x.1.2.1 y.1.2.1 c hc
  have hL := cL x.1.2.2 y.1.2.2 c hc
  have hlin := cap_mamikon_upperP_affine hφ x.2.1 y.2.1 hc
  simp only [convexBodyDomain, cvx_convexBodyComb_val hc] at hS hR hL
  simp only [wideUpperQ, wideDomain, WideTriple.comb, hc, ↓reduceDIte, cvx_convexBodyComb_val hc]
  rw [wide_upperQ_decomposition hφ (inWideL_comb x.2 y.2 hc), wide_upperQ_decomposition hφ x.2,
    wide_upperQ_decomposition hφ y.2]
  linarith

/-- Theorem 7.1.5 on `T̄`: a triple maximizes `𝒬` if and only if no first variation of `𝒬` at it
is positive. -/
theorem wide_maximum_iff_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x₀ : WideTriple φ) :
    (∀ x, wideUpperQ φ x ≤ wideUpperQ φ x₀) ↔
      ∀ x, (wideDomain φ).dirDeriv (wideUpperQ φ) x₀ x ≤ 0 :=
  theorem7_1_5 (wideDomain φ) (wideUpperQ_quadratic hφ) (wideUpperQ_concave hφ) x₀

/-! ## The first variation of the area

The mixed area `∫_{[0, 2π)} h_{K₁} dσ_{K₂}` is symmetric for all convex bodies: the atoms at `0` and
`2π` are kept, and periodicity makes their contributions equal. For caps the first variation of the
area is then an integral over `[0, π]`.
-/

/-- The mixed area is symmetric for arbitrary convex bodies. -/
theorem mixedArea_symm {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) :
    opt_Bs (Ico 0 (2 * π)) K₁ K₂ = opt_Bs (Ico 0 (2 * π)) K₂ K₁ := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- integration by parts against `σ_{L₂}`, after moving the atom at `0` to `2π`
  have key : ∀ {L₁ L₂ : Set (ℝ × ℝ)}, IsConvexBody L₁ → IsConvexBody L₂ →
      opt_Bs (Ico 0 (2 * π)) L₁ L₂ =
        -(∫ t in (0 : ℝ)..(2 * π), opt_g L₁ t * opt_g L₂ t) +
          ∫ t in (0 : ℝ)..(2 * π), supp L₁ t * supp L₂ t := by
    intro L₁ L₂ hL₁ hL₂
    have hs : supp L₁ (2 * π) = supp L₁ 0 := by
      simpa only [zero_add] using supp_add_two_pi L₁ 0
    have hμ : (sigma L₂).real {2 * π} = (sigma L₂).real {0} := by
      simpa only [measureReal_def, image_singleton, zero_add] using
        congrArg ENNReal.toReal (sigma_periodic hL₂ {0})
    have hIco : ∫ t in Ico 0 (2 * π), supp L₁ t ∂(sigma L₂) =
        ∫ t in Ioc 0 (2 * π), supp L₁ t ∂(sigma L₂) := by
      rw [← Ioo_union_left h2π, ← Ioo_union_right h2π,
        setIntegral_union_singleton hL₁.continuous_supp (Metric.isBounded_Ioo _ _),
        setIntegral_union_singleton hL₁.continuous_supp (Metric.isBounded_Ioo _ _), hμ, hs]
        <;> simp
    rw [opt_Bs, hIco, opt_supp_ibp hL₁ hL₂ h2π.le, opt_g_two_pi, hs]
    ring
  rw [key h₁ h₂, key h₂ h₁]
  simp only [mul_comm]

/-- For normalized caps the first variation of the area is `∫_{[0, π]} (h_{K*} - h_K) dσ_K`:
the lower half circle contributes nothing, even with atoms. -/
theorem area_firstVariation_caps (K Ks : ConvexBodySet)
    (hK : IsCap K.1 (π / 2)) (hKs : IsCap Ks.1 (π / 2)) :
    convexBodyDomain.dirDeriv (fun C => area C.1) K Ks =
      ∫ t in Icc 0 π, (supp Ks.1 t - supp K.1 t) ∂(sigma K.1) := by
  have hint : ∀ C : ConvexBodySet, IntegrableOn (supp C.1) (Ico 0 (2 * π)) (sigma K.1) :=
    fun C => (C.2.continuous_supp.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ico_subset_Icc_self
  have hsymm := mixedArea_symm K.2 Ks.2
  rw [opt_Bs, opt_Bs] at hsymm
  -- `|K| = 𝓑(K, K)` (Theorem 7.1.3), so Lemma 7.1.4 gives the first variation
  rw [show (fun C : ConvexBodySet => area C.1) =
      fun C => (1 / 2) * ∫ t in Ico 0 (2 * π), supp C.1 t ∂(sigma C.1) from
      funext fun C => theorem7_1_3 C.2,
    lemma7_1_4 convexBodyDomain
      ((cvx_integral_supp_sigma_bilin (Metric.isBounded_Ico 0 (2 * π))).const_mul (1 / 2)) K Ks,
    ← opt_Ico_eq_Icc hK (f := fun t => supp Ks.1 t - supp K.1 t)
      (Ks.2.continuous_supp.sub K.2.continuous_supp)
      (by simp only [hKs.2.2.2.2.2.1, hK.2.2.2.2.2.1, sub_self]),
    integral_sub (hint Ks) (hint K), hsymm]
  ring

end MovingSofaStability
