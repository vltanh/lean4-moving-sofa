module

public import MovingSofa.Gerver.Envelope
public import MovingSofa.Gerver.EnvelopeArea
public import MovingSofa.Gerver.NicheBounds
public import MovingSofa.Gerver.StructureCap
public import MovingSofa.Gerver.AreaBounds

/-!
# The niche, the cap and the area of Gerver's sofa

For a solution `P` of Romik's system with the enclosures `P.Bounds`, this file proves:

* `gv_niche` (Theorem 8.4.1 (2), as the paper uses it): the curves `𝐁|_{[t₃, π/2]}`,
  `𝐱|_{[t₁, t₄]}` and `𝐃|_{[0, t₂]}` lie on the boundary of the niche `𝒩(K)` of the cap
  `K = 𝓒(G)`, with `𝐁(t₃) = 𝐱(t₁)`, `𝐱(t₄) = 𝐃(t₂)`, `𝐃(0)_y = 𝐁(π/2)_y = 0`, and
  `|𝒩(K)| = 𝒥(𝐱|_{[t₁, t₄]}) - 𝒥(𝐁|_{[t₃, π/2]}) - 𝒥(𝐃|_{[0, t₂]})`;
* `gv_cap_area`: `|K| = 𝒥(𝐀|_{[0, π/2]}) + 𝒥(𝐂|_{[0, π/2]}) + 𝒥(𝐀(π/2), 𝐂(0))`;
* `gv_area`: `|G| ≥ 2.2`.

Here `t₁ = φ`, `t₂ = θ`, `t₃ = π/2 - θ`, `t₄ = π/2 - φ`.

## Proof

* *Niche.* The one-variable facts of `MovingSofa.Gerver.NicheBounds` are the hypotheses
  `EnvHyp` of the envelope theorem (`gn_envHyp`, with `s_A = 0.62`, `s_C = 0.95`). Since
  `K = K_G` (`gs_monotone_K`), `h_K(t) = 𝐱(t) · u_t + 1` and `h_K(t + π/2) = 𝐱(t) · v_t + 1`
  (`gs_supp_K_eq`), the quadrants `Q_K⁻(t)` are those of the rotation path and the fan `F_{π/2}`
  is the upper half-plane, so `𝒩(K) = envNiche 𝐱` (`gn_niche_eq`). The envelope theorem
  (`env_mem_closure`, `env_not_mem_niche`, `env_area`) then gives `gv_niche`.
* *Cap.* `K_G` is the region between the `x`-axis and its upper boundary: `𝐀|_{[0, π/2]}` (from
  `𝐀(0) = (1, 0)` to `𝐀(π/2)`), the horizontal top edge from `𝐀(π/2)` to `𝐂(0)` at height `1`
  (`gn_seg`), and `𝐂|_{[0, π/2]}` (from `𝐂(0)` to `𝐂(π/2)` on the `x`-axis) (`gn_K_eq`). A point
  below a point of `K_G` is in `K_G` since the normal angles of `K_G` lie in `[0, π]`
  (`gn_mem_K_of_below`); conversely a point `q ∈ K_G` with `q_x = 𝐀(t)_x`, `t ∈ (0, π/2]`,
  satisfies `q_y ≤ 𝐀(t)_y` by the support inequality `q · u_t ≤ 𝐀(t) · u_t`, and the endpoint
  cases follow by continuity (similarly for `𝐂` with the normals `v_t`). All three pieces have
  nonincreasing abscissa (`𝐀' = ρ_A v_t`, `𝐂' = -ρ_C u_t` with `ρ_A, ρ_C ≥ 0`), so
  `env_volume_region_of_antitoneOn` gives their areas `𝒥(z) - ½ [z_x z_y]`, they are separated by
  vertical lines (`env_volume_union_of_sep`), and the boundary terms cancel since
  `𝐀(0)_y = 𝐂(π/2)_y = 0` and `𝐀(π/2)_y = 𝐂(0)_y = 1`; the top edge has `𝒥 = segArea`
  (`proposition7_2_4`).
* *Area.* `G = K_G \ 𝒩(K_G)` with `𝒩(K_G) ⊆ K_G` measurable and `K_G` compact
  (`gs_gerverSofa_eq`, `gs_niche_subset`), so `|G| = |K_G| - |𝒩(K_G)|`, and `ga_area_lower` bounds
  the resulting combination of curve areas below by `2.2`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace MovingSofa.GerverParams

variable {P : GerverParams}

/-- The hypotheses of the envelope theorem for Gerver's rotation path. -/
lemma gn_envHyp (hP : P.IsSolution) (hB : P.Bounds) :
    EnvHyp P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ) 0.62 0.95 P.path P.gs_α P.gs_β (gb_rhoA P)
      (gb_rhoC P) where
  ht := gb_order hP
  hsA := gb_sA_mem hB
  hsC := gb_sC_mem hB
  x_cont := gb_x_cont hP
  x_deriv := gb_x_deriv hP
  α_cont := gb_α_cont hP
  β_cont := gb_β_cont hP
  B_deriv := gb_B_deriv hP
  D_deriv := gb_D_deriv hP
  α_neg := gb_α_neg hP hB
  β_pos := gb_β_pos hP hB
  ratio_mono := gb_ratio_mono hP hB
  ρA_le := gb_rhoA_le hP hB
  ρA_lt := gb_rhoA_lt hP hB
  ρC_le := gb_rhoC_le hP hB
  ρC_lt := gb_rhoC_lt hP hB
  I_nonneg := gb_I_nonneg hP hB
  I'_nonneg := gb_I'_nonneg hP hB
  corner_B := gb_corner_B hP hB
  corner_D := gb_corner_D hP hB
  x_pos := gb_x_pos hP hB
  B_t₃ := gb_B_t₃ hP
  D_t₂ := gb_D_t₂ hP
  B_end := gb_B_end hP
  D_end := gb_D_end hP

/-- `𝐁 = 𝐱 + α v_t` is the curve `envB` of the envelope theorem. -/
lemma gn_contactB_eq : contactB P.path = envB P.path P.gs_α := rfl

/-- `𝐃 = 𝐱 - β u_t` is the curve `envD` of the envelope theorem. -/
lemma gn_contactD_eq : contactD P.path = envD P.path P.gs_β := rfl

/-- The niche of the cap of Gerver's sofa is the niche of its rotation path. -/
lemma gn_niche_eq (hP : P.IsSolution) (hB : P.Bounds) :
    niche (capOf (gerverSofa P) (π / 2)) (π / 2) = envNiche P.path := by
  rw [(gs_monotone_K hP hB).2]
  ext q
  simp only [niche, fan, envNiche, mem_inter_iff, inter_self, mem_iUnion, exists_prop]
  have hfan : q ∈ halfPlus (π / 2) 0 ↔ q ∈ {q : ℝ × ℝ | 0 ≤ q.2} := by
    simp [halfPlus, ms_dot_uvec_pi_div_two]
  have hq : ∀ t ∈ Ioo 0 (π / 2), q ∈ qMinus P.gs_K t ↔ q ∈ envQuad P.path t := fun t ht => by
    obtain ⟨h1, h2⟩ := gs_supp_K_eq hP hB ht.1.le ht.2.le
    rw [ms_mem_qMinus_iff, h1, h2, add_sub_cancel_right, add_sub_cancel_right]
    simp only [envQuad, mem_ofPred_eq, dot_sub_left, sub_neg]
  rw [hfan]
  constructor
  · rintro ⟨h0, t, ht, hqt⟩
    exact ⟨h0, t, ht, (hq t ht).1 hqt⟩
  · rintro ⟨h0, t, ht, hqt⟩
    exact ⟨h0, t, ht, (hq t ht).2 hqt⟩

/-- `ρ_A` is bounded below on `[t₃, π/2]`. -/
lemma gn_rhoA_bddBelow (hP : P.IsSolution) : BddBelow (gb_rhoA P '' Icc (π / 2 - P.θ) (π / 2)) := by
  obtain ⟨M, hM⟩ := gb_rhoA_bdd (P := P)
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  refine ⟨-M, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (abs_le.1 (hM t ⟨by linarith [ht.1], ht.2⟩)).1

/-- `ρ_C` is bounded below on `[0, t₂]`. -/
lemma gn_rhoC_bddBelow (hP : P.IsSolution) : BddBelow (gb_rhoC P '' Icc 0 P.θ) := by
  obtain ⟨M, hM⟩ := gb_rhoC_bdd (P := P)
  obtain ⟨o1, o2, o3, o4, o5⟩ := gb_order hP
  refine ⟨-M, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (abs_le.1 (hM t ⟨ht.1, by linarith [ht.2]⟩)).1

/-- **Theorem 8.4.1 (2)** for Gerver's sofa: the curves `𝐁|_{[t₃, π/2]}`, `𝐱|_{[t₁, t₄]}` and
`𝐃|_{[0, t₂]}` lie on the boundary of the niche, with matching endpoints, and the area of the niche
is `𝒥(𝐱|_{[t₁, t₄]}) - 𝒥(𝐁|_{[t₃, π/2]}) - 𝒥(𝐃|_{[0, t₂]})`. -/
theorem gv_niche (hP : P.IsSolution) (hB : P.Bounds) :
    (∀ t ∈ Icc (π / 2 - P.θ) (π / 2), contactB P.path t ∈
        closure (niche (capOf (gerverSofa P) (π / 2)) (π / 2)) \
          niche (capOf (gerverSofa P) (π / 2)) (π / 2)) ∧
      (∀ t ∈ Icc P.φ (π / 2 - P.φ), P.path t ∈
        closure (niche (capOf (gerverSofa P) (π / 2)) (π / 2)) \
          niche (capOf (gerverSofa P) (π / 2)) (π / 2)) ∧
      (∀ t ∈ Icc 0 P.θ, contactD P.path t ∈
        closure (niche (capOf (gerverSofa P) (π / 2)) (π / 2)) \
          niche (capOf (gerverSofa P) (π / 2)) (π / 2)) ∧
      contactB P.path (π / 2 - P.θ) = P.path P.φ ∧ P.path (π / 2 - P.φ) = contactD P.path P.θ ∧
      (contactD P.path 0).2 = 0 ∧ (contactB P.path (π / 2)).2 = 0 ∧
      area (niche (capOf (gerverSofa P) (π / 2)) (π / 2)) = curveArea P.path P.φ (π / 2 - P.φ) -
        curveArea (contactB P.path) (π / 2 - P.θ) (π / 2) - curveArea (contactD P.path) 0 P.θ := by
  have h := gn_envHyp hP hB
  rw [gn_niche_eq hP hB]
  obtain ⟨c1, c2, c3⟩ := env_mem_closure h
  obtain ⟨n1, n2, n3⟩ := env_not_mem_niche h
  exact ⟨fun t ht => ⟨c2 t ht, n2 t ht⟩, fun t ht => ⟨c1 t ht, n1 t ht⟩,
    fun t ht => ⟨c3 t ht, n3 t ht⟩, gb_B_t₃ hP, (gb_D_t₂ hP).symm, gb_D_end hP, gb_B_end hP,
    env_area h (gn_rhoA_bddBelow hP) (gn_rhoC_bddBelow hP)⟩

/-! ### The cap of Gerver's sofa as the region below its upper boundary -/

variable (P) in
/-- The top edge `s ↦ 𝐀(π/2) + s (𝐂(0) - 𝐀(π/2))`, `s ∈ [0, 1]`, of the cap of Gerver's sofa. -/
noncomputable def gn_seg (s : ℝ) : ℝ × ℝ :=
  contactA P.path (π / 2) + s • (contactC P.path 0 - contactA P.path (π / 2))

/-- Away from the breakpoints, `t` lies in an open phase interval, on which `gb_rhoA`, `gb_rhoC`
are the phase formulas. -/
lemma gn_opiece_of_ne {t : ℝ} (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    ∃ i, gs_opiece P i t ∧ gb_rhoA P t = (P.gs_phase i).ρA t ∧
      gb_rhoC P t = (P.gs_phase i).ρC t := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  unfold gb_rhoA gb_rhoC
  by_cases c1 : t < P.φ
  · simp only [c1, ↓reduceIte]
    exact ⟨0, (show t < P.φ from c1), rfl, rfl⟩
  by_cases c2 : t < P.θ
  · simp only [c1, c2, ↓reduceIte]
    exact ⟨1, (show P.φ < t ∧ t < P.θ from ⟨lt_of_le_of_ne (not_lt.1 c1) (Ne.symm h1), c2⟩),
      rfl, rfl⟩
  by_cases c3 : t ≤ π / 2 - P.θ
  · simp only [c1, c2, c3, ↓reduceIte]
    exact ⟨2, (show P.θ < t ∧ t < π / 2 - P.θ from
      ⟨lt_of_le_of_ne (not_lt.1 c2) (Ne.symm h2), lt_of_le_of_ne c3 h3⟩), rfl, rfl⟩
  by_cases c4 : t ≤ π / 2 - P.φ
  · simp only [c1, c2, c3, c4, ↓reduceIte]
    exact ⟨3, (show π / 2 - P.θ < t ∧ t < π / 2 - P.φ from ⟨not_le.1 c3, lt_of_le_of_ne c4 h4⟩),
      rfl, rfl⟩
  · simp only [c1, c2, c3, c4, ↓reduceIte]
    exact ⟨4, (show π / 2 - P.φ < t from not_le.1 c4), rfl, rfl⟩

/-- `𝐀' = ρ_A v_t` off the breakpoints. -/
lemma gn_A_deriv (hP : P.IsSolution) {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    HasDerivAt (contactA P.path) (gb_rhoA P t • vvec t) t := by
  obtain ⟨i, hi, hA, -⟩ := gn_opiece_of_ne ht
  rw [hA]
  exact gs_hasDerivAt_contactA hP hi

/-- `𝐂' = -ρ_C u_t` off the breakpoints. -/
lemma gn_C_deriv (hP : P.IsSolution) {t : ℝ}
    (ht : t ∉ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ)) :
    HasDerivAt (contactC P.path) (-gb_rhoC P t • uvec t) t := by
  obtain ⟨i, hi, -, hC⟩ := gn_opiece_of_ne ht
  rw [hC]
  exact gs_hasDerivAt_contactC hP hi

/-- `𝐀'` is bounded on `[0, π/2]`. -/
lemma gn_A_bound : ∃ M, ∀ t ∈ Icc 0 (π / 2), ‖gb_rhoA P t • vvec t‖ ≤ M := by
  obtain ⟨M, hM⟩ := gb_rhoA_bdd (P := P)
  refine ⟨M, fun t ht => ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  calc |gb_rhoA P t| * ‖vvec t‖ ≤ M * 1 :=
        mul_le_mul (hM t ht) (env_norm_vvec_le t) (norm_nonneg _) ((abs_nonneg _).trans (hM t ht))
    _ = M := mul_one M

/-- `𝐂'` is bounded on `[0, π/2]`. -/
lemma gn_C_bound : ∃ M, ∀ t ∈ Icc 0 (π / 2), ‖-gb_rhoC P t • uvec t‖ ≤ M := by
  obtain ⟨M, hM⟩ := gb_rhoC_bdd (P := P)
  refine ⟨M, fun t ht => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  calc |gb_rhoC P t| * ‖uvec t‖ ≤ M * 1 :=
        mul_le_mul (hM t ht) (env_norm_uvec_le t) (norm_nonneg _) ((abs_nonneg _).trans (hM t ht))
    _ = M := mul_one M

/-- `𝐀_x` is antitone on `[0, π/2]`. -/
lemma gn_A_anti (hP : P.IsSolution) (hB : P.Bounds) :
    AntitoneOn (fun t => (contactA P.path t).1) (Icc 0 (π / 2)) := by
  intro a ha b hb hab
  have := gs_A_anti hP hB (σ := 0) ha.1 hab hb.2 fun r hr => by
    rw [zero_sub, sin_neg]
    exact neg_nonpos.2 (sin_nonneg_of_nonneg_of_le_pi (ha.1.trans hr.1)
      (by linarith [hr.2, hb.2, pi_pos]))
  simpa only [ms_dot_uvec_zero] using this

/-- `𝐂_x` is antitone on `[0, π/2]`. -/
lemma gn_C_anti (hP : P.IsSolution) (hB : P.Bounds) :
    AntitoneOn (fun t => (contactC P.path t).1) (Icc 0 (π / 2)) := by
  intro a ha b hb hab
  have := gs_C_anti hP hB (σ := 0) ha.1 hab hb.2 fun r hr => by
    rw [sub_zero]
    exact cos_nonneg_of_mem_Icc ⟨by linarith [ha.1, hr.1, pi_pos], by linarith [hr.2, hb.2]⟩
  simpa only [ms_dot_uvec_zero] using this

/-- The top edge starts at `𝐀(π/2)`. -/
lemma gn_seg_zero : P.gn_seg 0 = contactA P.path (π / 2) := by simp [gn_seg]

/-- The top edge ends at `𝐂(0)`. -/
lemma gn_seg_one : P.gn_seg 1 = contactC P.path 0 := by simp [gn_seg]

/-- The abscissa along the top edge. -/
lemma gn_seg_fst (s : ℝ) : (P.gn_seg s).1 =
    (contactA P.path (π / 2)).1 + s * ((contactC P.path 0).1 - (contactA P.path (π / 2)).1) := by
  simp [gn_seg]

/-- The top edge is at height `1`. -/
lemma gn_seg_snd (hP : P.IsSolution) (s : ℝ) : (P.gn_seg s).2 = 1 := by
  simp [gn_seg, gs_A_pi_div_two hP, gs_C_zero hP]

/-- The derivative of the top edge. -/
lemma gn_hasDerivAt_seg (s : ℝ) :
    HasDerivAt P.gn_seg (contactC P.path 0 - contactA P.path (π / 2)) s := by
  have h := ((hasDerivAt_id s).smul_const (contactC P.path 0 - contactA P.path (π / 2))).const_add
    (contactA P.path (π / 2))
  rw [one_smul] at h
  exact h

/-- The top edge goes from right to left: `𝐂(0)_x ≤ 𝐀(π/2)_x`. -/
lemma gn_C_zero_le_A (hP : P.IsSolution) (hB : P.Bounds) :
    (contactC P.path 0).1 ≤ (contactA P.path (π / 2)).1 := by
  rw [gs_C_zero hP, gs_A_pi_div_two hP]
  have := gs_X₀_bounds hP hB
  have := gs_a₁_lo hB
  simp only
  linarith

/-- The abscissa decreases along the top edge. -/
lemma gn_seg_anti (hP : P.IsSolution) (hB : P.Bounds) :
    AntitoneOn (fun s => (P.gn_seg s).1) (Icc 0 1) := by
  intro a _ b _ hab
  simp only [gn_seg_fst]
  nlinarith [gn_C_zero_le_A hP hB]

/-- The top edge lies in `K_G`. -/
lemma gn_seg_mem_K (hP : P.IsSolution) (hB : P.Bounds) {s : ℝ} (hs : s ∈ Icc 0 1) :
    P.gn_seg s ∈ P.gs_K :=
  gs_convex_K.add_smul_sub_mem (gs_A_mem_K hP hB (by linarith [pi_pos]) le_rfl)
    (gs_C_mem_K hP hB le_rfl (by linarith [pi_pos])) hs

/-- A point of the upper half-plane below a point of `K_G` lies in `K_G`. -/
lemma gn_mem_K_of_below {γ q : ℝ × ℝ} (hγ : γ ∈ P.gs_K) (h1 : γ.1 = q.1) (h0 : 0 ≤ q.2)
    (h2 : q.2 ≤ γ.2) : q ∈ P.gs_K := by
  rw [gs_mem_K_iff] at hγ ⊢
  refine ⟨h0, fun σ hσ => ?_⟩
  have h := hγ.2 σ hσ
  have hs : 0 ≤ sin σ := sin_nonneg_of_nonneg_of_le_pi hσ.1 hσ.2
  simp only [dot, uvec] at h ⊢
  rw [← h1]
  nlinarith [mul_le_mul_of_nonneg_right h2 hs]

/-- `K_G` is the region below its upper boundary `𝐀|_{[0, π/2]}`, the top edge, and
`𝐂|_{[0, π/2]}`. -/
lemma gn_K_eq (hP : P.IsSolution) (hB : P.Bounds) :
    P.gs_K = envRegion (contactA P.path) 0 (π / 2) ∪ envRegion P.gn_seg 0 1 ∪
      envRegion (contactC P.path) 0 (π / 2) := by
  have hπ : (0 : ℝ) < π / 2 := by linarith [pi_pos]
  have hA0 := gs_A_zero hP
  have hC0 := gs_C_zero hP
  have hApi := gs_A_pi_div_two hP
  have hCpi := gs_C_pi_div_two hP
  ext q
  constructor
  · intro hq
    obtain ⟨hb1, hb2, hb3, hb4⟩ := gs_K_bounds hP hq
    have hH := (gs_mem_K_iff.1 hq).2
    have hsA : ∀ t ∈ Icc 0 (π / 2), dot q (uvec t) ≤ dot (contactA P.path t) (uvec t) :=
      fun t ht => by
        rw [← gs_H_eq_A ht.2]
        exact hH t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
    have hsC : ∀ t ∈ Icc 0 (π / 2), dot q (vvec t) ≤ dot (contactC P.path t) (vvec t) :=
      fun t ht => by
        have := hH (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
        rwa [gs_H_eq_C hP (by linarith [ht.1]), add_sub_cancel_right,
          uvec_add_pi_div_two] at this
    by_cases h1 : (contactA P.path (π / 2)).1 ≤ q.1
    · -- below `𝐀`
      refine Or.inl (Or.inl ⟨hb3, ?_⟩)
      rcases lt_or_eq_of_le hb2 with hlt | heq
      · obtain ⟨t, ht, hte⟩ : ∃ t ∈ Icc 0 (π / 2), (contactA P.path t).1 = q.1 :=
          intermediate_value_Icc' hπ.le (gs_continuous_contactA hP).fst.continuousOn
            ⟨h1, by rw [hA0]; exact hlt.le⟩
        have ht0 : 0 < t := by
          rcases ht.1.lt_or_eq with h | h
          · exact h
          · rw [← h, hA0] at hte
            simp only at hte
            linarith
        have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith [ht.2, pi_pos])
        refine ⟨t, ht, hte, ?_⟩
        have h := hsA t ht
        simp only [dot, uvec] at h
        rw [hte] at h
        exact le_of_mul_le_mul_right (by linarith) hsin
      · -- `q₁ = 1 = 𝐀(0)_x`: `q₂ ≤ 𝐀(σ)_y` for `σ ∈ (0, π/2)`, and `𝐀(σ)_y → 0`
        refine ⟨0, ⟨le_rfl, hπ.le⟩, by rw [hA0, heq], ?_⟩
        have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), q.2 ≤ (contactA P.path σ).2 := by
          filter_upwards [Ioo_mem_nhdsGT hπ] with σ hσ
          have hsin : 0 < sin σ := sin_pos_of_pos_of_lt_pi hσ.1 (by linarith [hσ.2, pi_pos])
          have hcos : 0 < cos σ := cos_pos_of_mem_Ioo ⟨by linarith [hσ.1, pi_pos], hσ.2⟩
          have hm := gn_A_anti hP hB ⟨le_rfl, hπ.le⟩ ⟨hσ.1.le, hσ.2.le⟩ hσ.1.le
          simp only [hA0] at hm
          have h := hsA σ ⟨hσ.1.le, hσ.2.le⟩
          simp only [dot, uvec] at h
          have h3 : (contactA P.path σ).1 * cos σ ≤ q.1 * cos σ := by
            rw [heq]; nlinarith
          exact le_of_mul_le_mul_right (by linarith) hsin
        exact ge_of_tendsto
          (((gs_continuous_contactA hP).snd.tendsto 0).mono_left nhdsWithin_le_nhds) hev
    by_cases h2 : (contactC P.path 0).1 ≤ q.1
    · -- below the top edge
      push Not at h1
      refine Or.inl (Or.inr ⟨hb3, ?_⟩)
      have hca : (contactC P.path 0).1 < (contactA P.path (π / 2)).1 := lt_of_le_of_lt h2 h1
      refine ⟨((contactA P.path (π / 2)).1 - q.1) /
          ((contactA P.path (π / 2)).1 - (contactC P.path 0).1),
        ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩,
        ?_, by rw [gn_seg_snd hP]; exact hb4⟩
      rw [gn_seg_fst]
      have hne : (contactA P.path (π / 2)).1 - (contactC P.path 0).1 ≠ 0 := (sub_pos.2 hca).ne'
      field_simp
      ring
    · -- below `𝐂`
      push Not at h1 h2
      refine Or.inr ⟨hb3, ?_⟩
      have hb1' : (contactC P.path (π / 2)).1 ≤ q.1 := by rw [hCpi]; exact hb1
      rcases lt_or_eq_of_le hb1' with hlt | heq
      · obtain ⟨t, ht, hte⟩ : ∃ t ∈ Icc 0 (π / 2), (contactC P.path t).1 = q.1 :=
          intermediate_value_Icc' hπ.le (gs_continuous_contactC hP).fst.continuousOn
            ⟨hlt.le, h2.le⟩
        have ht1 : t < π / 2 := by
          rcases ht.2.lt_or_eq with h | h
          · exact h
          · rw [h] at hte
            linarith
        have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht1⟩
        refine ⟨t, ht, hte, ?_⟩
        have h := hsC t ht
        simp only [dot, vvec] at h
        rw [hte] at h
        exact le_of_mul_le_mul_right (by linarith) hcos
      · -- `q₁ = 𝐂(π/2)_x`: `q₂ ≤ 𝐂(σ)_y` for `σ ∈ (0, π/2)`, and `𝐂(σ)_y → 0`
        refine ⟨π / 2, ⟨hπ.le, le_rfl⟩, heq, ?_⟩
        have hev : ∀ᶠ σ in 𝓝[<] (π / 2), q.2 ≤ (contactC P.path σ).2 := by
          filter_upwards [Ioo_mem_nhdsLT hπ] with σ hσ
          have hsin : 0 < sin σ := sin_pos_of_pos_of_lt_pi hσ.1 (by linarith [hσ.2, pi_pos])
          have hcos : 0 < cos σ := cos_pos_of_mem_Ioo ⟨by linarith [hσ.1, pi_pos], hσ.2⟩
          have hm := gn_C_anti hP hB ⟨hσ.1.le, hσ.2.le⟩ ⟨hπ.le, le_rfl⟩ hσ.2.le
          have h := hsC σ ⟨hσ.1.le, hσ.2.le⟩
          simp only [dot, vvec] at h
          have h3 : -(contactC P.path σ).1 * sin σ ≤ -q.1 * sin σ := by
            rw [← heq]; nlinarith
          exact le_of_mul_le_mul_right (by linarith) hcos
        exact ge_of_tendsto
          (((gs_continuous_contactC hP).snd.tendsto (π / 2)).mono_left nhdsWithin_le_nhds) hev
  · rintro ((⟨h0, t, ht, h1, h2⟩ | ⟨h0, s, hs, h1, h2⟩) | ⟨h0, t, ht, h1, h2⟩)
    · exact gn_mem_K_of_below (gs_A_mem_K hP hB ht.1 ht.2) h1 h0 h2
    · exact gn_mem_K_of_below (gn_seg_mem_K hP hB hs) h1 h0 h2
    · exact gn_mem_K_of_below (gs_C_mem_K hP hB ht.1 ht.2) h1 h0 h2

/-- **The area of the cap of Gerver's sofa**: `|K| = 𝒥(𝐀) + 𝒥(𝐂) + 𝒥(𝐀(π/2), 𝐂(0))`. -/
theorem gv_cap_area (hP : P.IsSolution) (hB : P.Bounds) :
    area (capOf (gerverSofa P) (π / 2)) = curveArea (contactA P.path) 0 (π / 2) +
      curveArea (contactC P.path) 0 (π / 2) +
        segArea (contactA P.path (π / 2)) (contactC P.path 0) := by
  have hπ : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  have hS := (env_bp_finite P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ)).countable
  -- the curve `𝐀`
  obtain ⟨MA, hAM⟩ := gn_A_bound (P := P)
  have hAc : ContinuousOn (contactA P.path) (Icc 0 (π / 2)) :=
    (gs_continuous_contactA hP).continuousOn
  have hAd : ∀ t ∈ Ioo 0 (π / 2) \ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ),
      HasDerivAt (contactA P.path) (gb_rhoA P t • vvec t) t := fun t ht => gn_A_deriv hP ht.2
  have hAn : ∀ t ∈ Icc 0 (π / 2), 0 ≤ (contactA P.path t).2 :=
    fun t ht => gs_A_snd_nonneg hP hB ht.1 ht.2
  obtain ⟨hA1, -, hA3⟩ := env_volume_region_of_antitoneOn hπ hS hAc hAd hAM hAn (gn_A_anti hP hB)
  -- the top edge
  have hsc : ContinuousOn P.gn_seg (Icc 0 1) :=
    fun s _ => (gn_hasDerivAt_seg s).continuousAt.continuousWithinAt
  have hsd : ∀ s ∈ Ioo (0 : ℝ) 1 \ (∅ : Set ℝ),
      HasDerivAt P.gn_seg ((fun _ => contactC P.path 0 - contactA P.path (π / 2)) s) s :=
    fun s _ => gn_hasDerivAt_seg s
  have hsM : ∀ s ∈ Icc (0 : ℝ) 1, ‖(fun _ => contactC P.path 0 - contactA P.path (π / 2)) s‖ ≤
      ‖contactC P.path 0 - contactA P.path (π / 2)‖ := fun _ _ => le_rfl
  have hsn : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (P.gn_seg s).2 := fun s _ => by
    rw [gn_seg_snd hP]; exact zero_le_one
  obtain ⟨hs1, -, hs3⟩ :=
    env_volume_region_of_antitoneOn zero_le_one countable_empty hsc hsd hsM hsn (gn_seg_anti hP hB)
  -- the curve `𝐂`
  obtain ⟨MC, hCM⟩ := gn_C_bound (P := P)
  have hCc : ContinuousOn (contactC P.path) (Icc 0 (π / 2)) :=
    (gs_continuous_contactC hP).continuousOn
  have hCd : ∀ t ∈ Ioo 0 (π / 2) \ ({P.φ, P.θ, π / 2 - P.θ, π / 2 - P.φ} : Set ℝ),
      HasDerivAt (contactC P.path) (-gb_rhoC P t • uvec t) t := fun t ht => gn_C_deriv hP ht.2
  have hCn : ∀ t ∈ Icc 0 (π / 2), 0 ≤ (contactC P.path t).2 :=
    fun t ht => gs_C_snd_nonneg hP hB ht.1 ht.2
  obtain ⟨hC1, -, hC3⟩ := env_volume_region_of_antitoneOn hπ hS hCc hCd hCM hCn (gn_C_anti hP hB)
  -- null measurability, and the separation of the three regions by two vertical lines
  have hs4 := (env_nullMeasurableSet_region countable_empty hsc hsd hsM hsn
    (Or.inr (gn_seg_anti hP hB))).1
  have hC4 := (env_nullMeasurableSet_region hS hCc hCd hCM hCn (Or.inr (gn_C_anti hP hB))).1
  have hA_fst : ∀ q ∈ envRegion (contactA P.path) 0 (π / 2), (contactA P.path (π / 2)).1 ≤ q.1 :=
    fun q hq => (env_region_fst_mem_of_antitoneOn (gn_A_anti hP hB) hq).1
  have hs_fst : ∀ q ∈ envRegion P.gn_seg 0 1,
      q.1 ∈ Icc (contactC P.path 0).1 (contactA P.path (π / 2)).1 := fun q hq => by
    have := env_region_fst_mem_of_antitoneOn (gn_seg_anti hP hB) hq
    rwa [gn_seg_one, gn_seg_zero] at this
  have hC_fst : ∀ q ∈ envRegion (contactC P.path) 0 (π / 2), q.1 ≤ (contactC P.path 0).1 :=
    fun q hq => (env_region_fst_mem_of_antitoneOn (gn_C_anti hP hB) hq).2
  have hvol : volume P.gs_K = volume (envRegion (contactA P.path) 0 (π / 2)) +
      volume (envRegion P.gn_seg 0 1) + volume (envRegion (contactC P.path) 0 (π / 2)) := by
    rw [gn_K_eq hP hB,
      env_volume_union_of_sep (contactC P.path 0).1 hC4 (Or.inr ⟨fun q hq => ?_, hC_fst⟩),
      env_volume_union_of_sep (contactA P.path (π / 2)).1 hs4
        (Or.inr ⟨hA_fst, fun q hq => (hs_fst q hq).2⟩)]
    rcases hq with hq | hq
    · exact (gn_C_zero_le_A hP hB).trans (hA_fst q hq)
    · exact (hs_fst q hq).1
  -- the boundary terms cancel
  have hseg : curveArea P.gn_seg 0 1 = segArea (contactA P.path (π / 2)) (contactC P.path 0) :=
    proposition7_2_4 _ _
  have e1 : (contactA P.path (π / 2)).2 = 1 := by rw [gs_A_pi_div_two hP]
  have e2 : (contactA P.path 0).1 = 1 := by rw [gs_A_zero hP]
  have e3 : (contactA P.path 0).2 = 0 := by rw [gs_A_zero hP]
  have e4 : (contactC P.path 0).2 = 1 := by rw [gs_C_zero hP]
  have e5 : (contactC P.path (π / 2)).2 = 0 := by rw [gs_C_pi_div_two hP]
  rw [(gs_monotone_K hP hB).2, area, hvol, hA1, hs1, hC1, ← ENNReal.ofReal_add hA3 hs3,
    ← ENNReal.ofReal_add (add_nonneg hA3 hs3) hC3,
    ENNReal.toReal_ofReal (add_nonneg (add_nonneg hA3 hs3) hC3), hseg, gn_seg_one, gn_seg_zero,
    e1, e2, e3, e4, e5]
  ring

/-- The niche of a rotation path is measurable. -/
lemma gn_measurableSet_envNiche (x : ℝ → ℝ × ℝ) : MeasurableSet (envNiche x) := by
  refine (isClosed_le continuous_const continuous_snd).measurableSet.inter ?_
  refine (isOpen_biUnion fun s _ => ?_).measurableSet
  have hc : ∀ w : ℝ × ℝ, Continuous fun q : ℝ × ℝ => dot (q - x s) w := fun w => by
    unfold dot; fun_prop
  exact (isOpen_lt (hc _) continuous_const).inter (isOpen_lt (hc _) continuous_const)

/-- **Gerver's sofa has area at least `2.2`.** -/
theorem gv_area (hP : P.IsSolution) (hB : P.Bounds) : 2.2 ≤ area (gerverSofa P) := by
  have hK := gs_isConvexBody_K hP hB
  have hcapK := (gs_monotone_K hP hB).2
  have hN : niche P.gs_K (π / 2) ⊆ P.gs_K := gs_niche_subset hP hB
  have hNm : MeasurableSet (niche P.gs_K (π / 2)) := by
    rw [← hcapK, gn_niche_eq hP hB]; exact gn_measurableSet_envNiche _
  have hKfin : volume P.gs_K ≠ ⊤ := hK.2.1.measure_lt_top.ne
  have hNfin : volume (niche P.gs_K (π / 2)) ≠ ⊤ := ne_top_of_le_ne_top hKfin (measure_mono hN)
  have harea : area (gerverSofa P) = area P.gs_K - area (niche P.gs_K (π / 2)) := by
    rw [gs_gerverSofa_eq hP hB, area, measure_sdiff hN hNm.nullMeasurableSet hNfin,
      ENNReal.toReal_sub_of_le (measure_mono hN) hKfin]
    rfl
  have hcap := gv_cap_area hP hB
  have hniche := (gv_niche hP hB).2.2.2.2.2.2.2
  rw [hcapK] at hcap hniche
  rw [harea, hcap, hniche]
  linarith [ga_area_lower hP hB]

end MovingSofa.GerverParams
