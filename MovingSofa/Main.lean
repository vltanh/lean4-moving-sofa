module

public import MovingSofa.Gerver.Properties
public import MovingSofa.Gerver.Romik

/-!
# Optimality of Gerver's sofa

Theorem 8.1.1 (`thm:cap-space-special`) parts (2)–(3), Theorem 8.5.7 (`thm:variation-a2-gerver`),
Corollary 8.5.8 (`cor:gerver-max-cap`), the existence and uniqueness of the parameters of Gerver's
sofa (implicit in Definition 8.1.2), and the main Theorem 1.1.1 (`thm:main`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

open GerverParams

/-- Romik's system has a solution in the box (implicit in Definition 8.1.2; Romik, Section 4 and
Table 1). -/
theorem definition8_1_2_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox :=
  romik_exists

/-- The solution of Romik's system in the box is unique, so Gerver's sofa is well defined. -/
theorem definition8_1_2_unique {P Q : GerverParams} (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q :=
  romik_unique hP hPb hQ hQb

/-- **Theorem 8.1.1** (`thm:cap-space-special`) (2): every balanced maximum cap with rotation angle
`π/2` lies in `𝒦^i`. -/
theorem theorem8_1_1_balanced {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) : IsKi K := by
  refine ⟨hK.2.1, theorem6_1_1 hK, ?_⟩
  obtain ⟨P, hP, hbox⟩ := definition8_1_2_exists
  have h1 := theorem3_5_5 hK P.cap (gm_isCap hP hbox)
  have h2 := gm_sofaArea_cap hP hbox
  have h3 := gerverSofa_area hP hbox
  have h4 : sofaArea (π / 2) K ≤ area K := by
    unfold sofaArea
    have : 0 ≤ area (niche K (π / 2)) := ENNReal.toReal_nonneg
    linarith
  linarith

/-- **Theorem 8.1.1** (3): the cap of Gerver's sofa lies in `𝒦^i`. -/
theorem theorem8_1_1_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : IsKi P.cap :=
  gm_isKi hP hbox

/-- The triple `(K, B_K, D_K)` of Gerver's sofa lies in `𝓛`. -/
theorem gerver_inL {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    InL P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) :=
  theorem8_1_8 hbox.1 (theorem8_1_1_gerver hP hbox) (gm_niche_subset hP hbox)

/-- Gerver's triple as an element of `𝓛`. -/
noncomputable def gerverTriple {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : LTriple P.φ :=
  ⟨(⟨P.cap, (gerver_inL hP hbox).1.1.2.1⟩, ⟨rightBody P.φ P.cap, (gerver_inL hP hbox).2.1⟩,
    ⟨leftBody P.φ P.cap, (gerver_inL hP hbox).2.2.1⟩), gerver_inL hP hbox⟩

lemma gm_restrict_Ico_split (μ : Measure ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    μ.restrict (Ico a c) = μ.restrict (Ico a b) + μ.restrict (Ico b c) := by
  rw [← Ico_union_Ico_eq_Ico hab hbc, Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico]

lemma gm_restrict_Ioc_split (μ : Measure ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    μ.restrict (Ioc a c) = μ.restrict (Ioc a b) + μ.restrict (Ioc b c) := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc,
    Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]

lemma gm_restrict_Icc_split (μ : Measure ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    μ.restrict (Icc a c) = μ.restrict (Ico a b) + μ.restrict {b} + μ.restrict (Ioc b c) := by
  have e : Icc a c = (Ico a b ∪ {b}) ∪ Ioc b c := by
    rw [Ico_union_right hab, Icc_union_Ioc_eq_Icc hab hbc]
  rw [e, Measure.restrict_union (Set.disjoint_left.2 fun t h1 h2 => by
      rcases h1 with h1 | h1
      · exact absurd h2.1 (not_lt.2 h1.2.le)
      · rw [mem_singleton_iff] at h1; rw [h1] at h2; exact lt_irrefl _ h2.1) measurableSet_Ioc,
    Measure.restrict_union (Set.disjoint_left.2 fun t h1 h2 => by
      rw [mem_singleton_iff] at h2; rw [h2] at h1; exact lt_irrefl _ h1.2)
      (measurableSet_singleton b)]

lemma gm_restrict_Icc_eq_Ico {μ : Measure ℝ} {a b : ℝ} (hab : a ≤ b) (h : μ {b} = 0) :
    μ.restrict (Icc a b) = μ.restrict (Ico a b) := by
  rw [← Ico_union_right hab, Measure.restrict_union (Set.disjoint_left.2 fun t h1 h2 => by
      rw [mem_singleton_iff] at h2; rw [h2] at h1; exact lt_irrefl _ h1.2)
      (measurableSet_singleton b), Measure.restrict_eq_zero.2 h, add_zero]

lemma gm_restrict_Icc_eq_Ioc {μ : Measure ℝ} {a b : ℝ} (hab : a ≤ b) (h : μ {a} = 0) :
    μ.restrict (Icc a b) = μ.restrict (Ioc a b) := by
  rw [← Ioc_union_left hab, Measure.restrict_union (Set.disjoint_left.2 fun t h1 h2 => by
      rw [mem_singleton_iff] at h2; rw [h2] at h1; exact lt_irrefl _ h1.1)
      (measurableSet_singleton a), Measure.restrict_eq_zero.2 h, add_zero]

/-- The measure identity behind Theorem 8.5.7: `σ_K` on `[0, π]` splits into `ι_K` on
`I ∪ (I + π/2)`, `σ̆_B` on `J_4 ∪ J_5`, `σ̆_D` on `J_6 ∪ J_7` and the top edge. -/
lemma gm_sigma_decomp {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (sigma P.cap).restrict (Icc 0 π) =
      (iota P.cap).restrict (Icc P.φ (π / 2 - P.φ) ∪ Icc (P.φ + π / 2) (π - P.φ)) +
      (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2)) +
      (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ)) +
      (sigma P.cap).restrict {π / 2} := by
  have h01 := gm_φ_pos hP; have h12 := gm_φ_lt_θ hP; have h23 := gm_θ_lt_c hP
  have h34 := gm_c_lt_d hP; have h45 := gm_d_lt hP; have hpi := pi_pos
  obtain ⟨e1, e23, e4, e5, e6, e7, e89, e10⟩ := theorem8_4_5 hP hbox
  rw [gm_jInt_1] at e1
  rw [gm_jInt_2, gm_jInt_3, Ico_union_Ico_eq_Ico h12.le h23.le] at e23
  rw [gm_jInt_4] at e4
  rw [gm_jInt_5] at e5
  rw [gm_jInt_6] at e6
  rw [gm_jInt_7] at e7
  rw [gm_jInt_8, gm_jInt_9, Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)] at e89
  rw [gm_jInt_10] at e10
  have hι : ∀ t, iota P.cap {t} = 0 := fun t => gm_withDensity_singleton _ _
  rw [gm_restrict_Icc_split (sigma P.cap) (by linarith : (0 : ℝ) ≤ π / 2) (by linarith),
    gm_restrict_Ico_split (sigma P.cap) h01.le (by linarith : P.φ ≤ π / 2),
    gm_restrict_Ico_split (sigma P.cap) (h12.trans h23).le (by linarith : π / 2 - P.θ ≤ π / 2),
    gm_restrict_Ico_split (sigma P.cap) h34.le h45.le,
    gm_restrict_Ioc_split (sigma P.cap) (by linarith : π / 2 ≤ π / 2 + P.φ)
      (by linarith : π / 2 + P.φ ≤ π),
    gm_restrict_Ioc_split (sigma P.cap) (by linarith : π / 2 + P.φ ≤ π / 2 + P.θ)
      (by linarith : π / 2 + P.θ ≤ π),
    gm_restrict_Ioc_split (sigma P.cap) (by linarith : π / 2 + P.θ ≤ π - P.φ)
      (by linarith : π - P.φ ≤ π),
    e1, e23, e4, e5, e6, e7, e89, e10,
    Measure.restrict_union (Set.disjoint_left.2 fun t h1 h2 => by
      linarith [h1.2, h2.1]) measurableSet_Icc,
    gm_restrict_Icc_eq_Ico (by linarith) (hι _), gm_restrict_Icc_eq_Ioc (by linarith) (hι _),
    gm_restrict_Ico_split (iota P.cap) (h12.trans h23).le h34.le,
    show P.φ + π / 2 = π / 2 + P.φ by ring,
    gm_restrict_Ioc_split (iota P.cap) (by linarith : π / 2 + P.φ ≤ π / 2 + P.θ)
      (by linarith : π / 2 + P.θ ≤ π - P.φ),
    gm_restrict_Ico_split (sigmaBreve (rightBody P.φ P.cap)) h34.le h45.le,
    gm_restrict_Ioc_split (sigmaBreve (leftBody P.φ P.cap)) (by linarith : π / 2 ≤ π / 2 + P.φ)
      (by linarith : π / 2 + P.φ ≤ π / 2 + P.θ)]
  abel

/-- **Theorem 8.5.7** (`thm:variation-a2-gerver`). At Gerver's triple, the directional derivative of
`𝒬` towards any `(K*, B*, D*) ∈ 𝓛` is nonpositive. -/
theorem theorem8_5_7 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) (xs : LTriple P.φ) :
    (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox) xs ≤ 0 := by
  have hφ := gm_φ_mem_Ioo hP hbox
  obtain ⟨h1, -, -, h4, -, -⟩ := theorem8_4_3_two hP hbox
  rw [theorem8_5_6 hφ (gerverTriple hP hbox) xs h4.symm h1.symm]
  have hL : InL P.φ xs.1.1.1 xs.1.2.1.1 xs.1.2.2.1 := xs.2
  have hKs : IsConvexBody xs.1.1.1 := xs.1.1.2
  have hBs : IsConvexBody xs.1.2.1.1 := xs.1.2.1.2
  have hDs : IsConvexBody xs.1.2.2.1 := xs.1.2.2.2
  have hK := gm_isConvexBody_cap hP hbox
  have hB := gm_isConvexBody_B hP hbox
  have hD := gm_isConvexBody_D hP hbox
  have h01 := gm_φ_pos hP; have h12 := gm_φ_lt_θ hP; have h23 := gm_θ_lt_c hP
  have h34 := gm_c_lt_d hP; have h45 := gm_d_lt hP; have hpi := pi_pos
  set f : ℝ → ℝ := fun t => supp xs.1.1.1 t - supp P.cap t with hf
  set gB : ℝ → ℝ := fun t => suppBreve xs.1.2.1.1 t - suppBreve (rightBody P.φ P.cap) t with hgB
  set gD : ℝ → ℝ := fun t => suppBreve xs.1.2.2.1 t - suppBreve (leftBody P.φ P.cap) t with hgD
  have hfc : Continuous f :=
    (continuous_supp hKs.2.1 hKs.1).sub (continuous_supp hK.2.1 hK.1)
  have hgBc : Continuous gB :=
    ((continuous_supp hBs.2.1 hBs.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp hB.2.1 hB.1).comp (continuous_id.add continuous_const))
  have hgDc : Continuous gD :=
    ((continuous_supp hDs.2.1 hDs.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp hD.2.1 hD.1).comp (continuous_id.add continuous_const))
  set Sι := Icc P.φ (π / 2 - P.φ) ∪ Icc (P.φ + π / 2) (π - P.φ) with hSι
  set ι := (iota P.cap).restrict Sι
  set β := (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2))
  set δ := (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ))
  set τ := (sigma P.cap).restrict {π / 2}
  have hdec : (sigma P.cap).restrict (Icc 0 π) = ι + β + δ + τ := gm_sigma_decomp hP hbox
  -- integrability
  have iσ : ∀ g : ℝ → ℝ, Continuous g → Integrable g ((sigma P.cap).restrict (Icc 0 π)) :=
    fun g hg => hg.continuousOn.integrableOn_compact isCompact_Icc
  have leι : ι ≤ ι + β + δ + τ :=
    Measure.le_add_right (Measure.le_add_right (Measure.le_add_right le_rfl))
  have leβ : β ≤ ι + β + δ + τ :=
    Measure.le_add_right (Measure.le_add_right (Measure.le_add_left le_rfl))
  have leδ : δ ≤ ι + β + δ + τ := Measure.le_add_right (Measure.le_add_left le_rfl)
  have leτ : τ ≤ ι + β + δ + τ := Measure.le_add_left le_rfl
  have iι : Integrable f ι := (iσ f hfc).mono_measure (by rw [hdec]; exact leι)
  have iβ : ∀ g : ℝ → ℝ, Continuous g → Integrable g β :=
    fun g hg => (iσ g hg).mono_measure (by rw [hdec]; exact leβ)
  have iδ : ∀ g : ℝ → ℝ, Continuous g → Integrable g δ :=
    fun g hg => (iσ g hg).mono_measure (by rw [hdec]; exact leδ)
  have iτ : Integrable f τ := (iσ f hfc).mono_measure (by rw [hdec]; exact leτ)
  -- the four terms
  have eI1 : (∫ t in Icc 0 π, f t ∂(sigma P.cap)) =
      (∫ t, f t ∂ι) + (∫ t, f t ∂β) + (∫ t, f t ∂δ) := by
    rw [hdec, integral_add_measure ((iι.add_measure (iβ f hfc)).add_measure (iδ f hfc)) iτ,
      integral_add_measure (iι.add_measure (iβ f hfc)) (iδ f hfc),
      integral_add_measure iι (iβ f hfc)]
    have : ∫ t, f t ∂τ = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      rw [mem_singleton_iff] at ht
      simp only [hf, ht, hL.1.1.2.2.2.1, gm_supp_cap_pi_div_two hP hbox, sub_self]
    rw [this, add_zero]
  have eI2 : (∫ t in Sι, f t * iFun P.cap t) = ∫ t, f t ∂ι := by
    have hS : Sι ⊆ Icc 0 π := by
      rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm : Measurable (fun t => ENNReal.ofReal (iFun P.cap t)) := by
      unfold iFun
      exact (Measurable.ite measurableSet_Iic
        (gm_measurable_dot (measurable_deriv _) (by unfold vvec; fun_prop))
        (gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _))
          (by unfold uvec; fun_prop)).neg).ennreal_ofReal
    rw [show ι = (volume.restrict Sι).withDensity (fun t => ENNReal.ofReal (iFun P.cap t)) from
        gm_iota_restrict (measurableSet_Icc.union measurableSet_Icc) hS,
      integral_withDensity_eq_integral_toReal_smul hm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply setIntegral_congr_fun (measurableSet_Icc.union measurableSet_Icc)
    intro t ht
    have hpos : 0 ≤ iFun P.cap t := by
      rcases ht with ht | ht
      · have hlo : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_left hlo.2.le]
        exact ((theorem6_1_2 hP hbox).2.2 t hlo).2.le
      · have hτ : t - π / 2 ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_right (not_le.2 (by linarith [ht.1]))]
        linarith [((theorem6_1_2 hP hbox).2.2 _ hτ).1]
    simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_comm]
  have eI3 : (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) =
      ∫ t, gB t ∂β := by
    rw [gm_sigmaBreve_B_restrict hP hbox]
  have eI4 : (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
      ∂(sigmaBreve (leftBody P.φ P.cap))) = ∫ t, gD t ∂δ := by
    rw [gm_sigmaBreve_D_restrict hP hbox]
  change (∫ t in Icc 0 π, f t ∂(sigma P.cap)) - (∫ t in Sι, f t * iFun P.cap t) +
      (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) +
      (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
        ∂(sigmaBreve (leftBody P.φ P.cap))) ≤ 0
  rw [eI1, eI2, eI3, eI4]
  have kB : (∫ t, f t ∂β) + (∫ t, gB t ∂β) ≤ 0 := by
    rw [← integral_add (iβ f hfc) (iβ gB hgBc)]
    apply setIntegral_nonpos measurableSet_Ico
    intro t ht
    have h1 := hL.2.2.2.2.2.1 t ⟨by linarith [ht.1], ht.2.le⟩
    have h2 := (theorem8_4_3_three hP hbox).2 t ⟨ht.1, ht.2.le⟩
    simp only [hf, hgB, suppBreve]
    rw [add_comm t π]
    linarith
  have kD : (∫ t, f t ∂δ) + (∫ t, gD t ∂δ) ≤ 0 := by
    rw [← integral_add (iδ f hfc) (iδ gD hgDc)]
    apply setIntegral_nonpos measurableSet_Ioc
    intro t ht
    have h1 := hL.2.2.2.2.2.2.2.2.1 (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 := (theorem8_4_3_three hP hbox).1 (t - π / 2)
      ⟨show (0 : ℝ) ≤ t - π / 2 by linarith [ht.1], show t - π / 2 ≤ P.θ by linarith [ht.2]⟩
    rw [show π / 2 + (t - π / 2) = t by ring, show 3 * π / 2 + (t - π / 2) = t + π by ring] at h1 h2
    simp only [hf, hgD, suppBreve]
    linarith
  linarith

/-- **Corollary 8.5.8** (`cor:gerver-max-cap`). Gerver's triple `(K, B_K, D_K)` maximizes `𝒬` on `𝓛`. -/
theorem corollary8_5_8 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) {K B D : Set (ℝ × ℝ)}
    (h : InL P.φ K B D) :
    upperQ P.φ K B D ≤ upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) := by
  have hφ := gm_φ_mem_Ioo hP hbox
  have key := (theorem7_1_5 (lDomain P.φ) (proposition8_2_1 hφ) (theorem8_3_8 hφ)
    (gerverTriple hP hbox)).2 (theorem8_5_7 hP hbox)
  exact key ⟨(⟨K, h.1.1.2.1⟩, ⟨B, h.2.1⟩, ⟨D, h.2.2.1⟩), h⟩

/-- The rotation `R_s` as a linear map. -/
noncomputable def gm_rotLM (s : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := rot s
  map_add' := rot_add_vec s
  map_smul' := fun a p => rot_smul s a p

lemma gm_det_rotLM (s : ℝ) : LinearMap.det (gm_rotLM s) = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, gm_rotLM, rot]
  nlinarith [sin_sq_add_cos_sq s]

/-- Rotations preserve areas. -/
lemma gm_area_rot (s : ℝ) (X : Set (ℝ × ℝ)) : area (rot s '' X) = area X := by
  unfold area
  have := MeasureTheory.Measure.addHaar_image_linearMap volume (gm_rotLM s) X
  have e : (⇑(gm_rotLM s) : ℝ × ℝ → ℝ × ℝ) = rot s := rfl
  rw [e, gm_det_rotLM] at this
  rw [this]; simp

lemma gm_arcsec22_pos : 0 < arcsec22 := by
  unfold arcsec22
  exact Real.arccos_pos.2 (by norm_num)

/-- A moving sofa of area at least `2.2` has area at most that of Gerver's sofa. -/
lemma gm_area_le {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) {S : Set (ℝ × ℝ)}
    (hS : IsMovingSofa S) (h22 : 2.2 ≤ area S) : area S ≤ area (gerverSofa P) := by
  obtain ⟨w, hw, hSw⟩ := theorem1_5_1 hS h22
  have hw' : w ∈ Ioc 0 (π / 2) := ⟨gm_arcsec22_pos.trans_le hw.1, hw.2⟩
  obtain ⟨Kw, -, hSKw, -, hmaxw⟩ := theorem3_5_6 hw'
  have e1 : area S ≤ area (Kw \ niche Kw w) := hmaxw S hSw
  obtain ⟨s, hs⟩ := theorem1_5_2 hSKw (h22.trans e1) hw
  have e2 := gm_area_rot s (Kw \ niche Kw w)
  obtain ⟨K, hK, hSK, hcapK, hmaxK⟩ := theorem3_5_6 pi_div_two_mem_Ioc
  have e3 : area (rot s '' (Kw \ niche Kw w)) ≤ area (K \ niche K (π / 2)) := hmaxK _ hs
  have e4 : sofaArea (π / 2) K = area (K \ niche K (π / 2)) := by
    have := theorem2_5_10 hSK.1
    rwa [hcapK] at this
  have hKi := theorem8_1_1_balanced hK
  have hN := theorem3_5_4 hK
  have e5 := theorem8_2_4 hbox.1 hKi hN
  have e6 := corollary8_5_8 hP hbox (theorem8_1_8 hbox.1 hKi hN)
  have e7 := theorem8_4_6 hP hbox
  have e8 := gm_sofaArea_cap hP hbox
  linarith

/-- **Theorem 1.1.1** (`thm:main`). Gerver's sofa attains the maximum area of a moving sofa: it is a
moving sofa, and every moving sofa has area at most that of Gerver's sofa. -/
theorem theorem1_1_1 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) := by
  have hG : IsMovingSofa (gerverSofa P) := ⟨π / 2, (gm_movingSofa_std hP hbox).1⟩
  refine ⟨hG, fun S hS => ?_⟩
  have hSfin : volume S ≠ ⊤ := (isBounded_of_isMovingSofa hS).measure_lt_top.ne
  have hGfin : volume (gerverSofa P) ≠ ⊤ := (isBounded_of_isMovingSofa hG).measure_lt_top.ne
  rw [← ENNReal.toReal_le_toReal hSfin hGfin]
  change area S ≤ area (gerverSofa P)
  have hGarea := gerverSofa_area hP hbox
  by_cases hS22 : area S < 2.2
  · linarith
  · exact gm_area_le hP hbox hS (not_lt.1 hS22)

end MovingSofa
