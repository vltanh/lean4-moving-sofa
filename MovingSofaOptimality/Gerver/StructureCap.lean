module

public import MovingSofaOptimality.Gerver.Frame
public import MovingSofaOptimality.Monotone.CapContainsNiche
public import MovingSofaOptimality.Injectivity.ArmLengths

/-!
# The cap of Gerver's sofa

Part of the verification of the structure of Gerver's sofa, for a solution `P` of Romik's system
satisfying the enclosures `P.Bounds`.

* `gs_A_le_H`, `gs_C_le_H`: the outer curves `𝐀, 𝐂` satisfy `Ω(τ) · u_σ ≤ H(σ)` for
  `τ ∈ [0, π/2]`, `σ ∈ [0, π]`, where `H(σ) = 𝐱(σ) · u_σ + 1` (`σ ≤ π/2`) and
  `H(σ) = 𝐱(σ - π/2) · v_{σ - π/2} + 1` (`σ > π/2`) (`gs_H`): `τ ↦ 𝐀(τ) · u_σ` has right derivative
  `ρ_A(τ) sin(σ - τ)` with `ρ_A ≥ 0`, similarly for `𝐂`, and the top edge `𝐀(π/2) → 𝐂(0)` is
  horizontal, pointing left.
* `gs_K = {p_y ≥ 0} ∩ ⋂_{σ ∈ [0, π]} H₋(σ, H(σ))` is a cap with rotation angle `π/2`
  (`gs_isCap_K`) and support function `H` on `[0, π]` (`gs_supp_K`); its inner corner is the
  rotation path (`gs_innerCorner_K`).
* The points of the rotation path above the `x`-axis lie in `gs_K` (`gs_path_mem_K`): `𝐱_x`
  decreases from `0` to `𝐱(π/2)_x`, `𝐱_y ≤ 1`, and the top edge contains `(0, 1)` and
  `(𝐱(π/2)_x, 1)`. Hence `gs_K` contains its niche (Theorem 2.5.8) and Gerver's sofa
  `= gs_K \ 𝒩(gs_K)` is a monotone sofa with cap `gs_K` (Theorems 2.5.9 and 2.4.3;
  `gs_monotone_K`).
* Vertices: `v⁻(t) = 𝐀(t)` on `[0, π/2]`, `v⁺(t) = 𝐀(t)` on `[0, π/2)`, `v⁺(t + π/2) = 𝐂(t)` on
  `[0, π/2]` (one-sided derivatives of the support function, and the lowest points of the edges at
  `0` and `π`).
* The injectivity condition (`gs_InjCond1/2/3`): `σ_K = ρ_A dt` on `[0, π/2)` and
  `σ_K = ρ_C(t - π/2) dt` on `(π/2, π]`, from the distribution function of `σ_K`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace MovingSofaOptimality

/-! ### Calculus helpers -/

/-! ### Support functions and vertices -/

namespace GerverParams

variable {P : GerverParams}

/-- The right derivative of `τ ↦ 𝐀(τ) · u_σ`. -/
lemma gs_hasDerivWithinAt_A_dot (hP : P.IsSolution) (σ τ : ℝ) :
    HasDerivWithinAt (fun r => dot (contactA P.path r) (uvec σ))
      ((P.gs_phase (P.gs_ridx τ)).ρA τ * sin (σ - τ)) (Ici τ) τ := by
  have := hasDerivWithinAt_dot (gs_hasDerivWithinAt_contactA hP (gs_rpiece_ridx τ)) (uvec σ)
  rwa [dot_smul_left, dot_vvec_uvec'] at this

/-- The right derivative of `τ ↦ 𝐂(τ) · u_σ`. -/
lemma gs_hasDerivWithinAt_C_dot (hP : P.IsSolution) (σ τ : ℝ) :
    HasDerivWithinAt (fun r => dot (contactC P.path r) (uvec σ))
      (-(P.gs_phase (P.gs_ridx τ)).ρC τ * cos (τ - σ)) (Ici τ) τ := by
  have := hasDerivWithinAt_dot (gs_hasDerivWithinAt_contactC hP (gs_rpiece_ridx τ)) (uvec σ)
  rwa [dot_smul_left, dot_uvec_uvec] at this

/-- `τ ↦ 𝐀(τ) · u_σ` is nondecreasing on `[τ₁, τ₂] ⊆ [0, π/2]` when `sin (σ - τ) ≥ 0` there (its
right derivative is `ρ_A(τ) sin (σ - τ)` with `ρ_A ≥ 0`); `gs_A_anti`, `gs_C_mono`, `gs_C_anti`
are the analogous statements. -/
lemma gs_A_mono (hP : P.IsSolution) (hB : P.Bounds) {σ τ₁ τ₂ : ℝ} (h0 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂)
    (h2 : τ₂ ≤ π / 2) (hs : ∀ r ∈ Ico τ₁ τ₂, 0 ≤ sin (σ - r)) :
    dot (contactA P.path τ₁) (uvec σ) ≤ dot (contactA P.path τ₂) (uvec σ) := by
  refine le_of_right_deriv_nonneg h12 ?_ (fun x _ => gs_hasDerivWithinAt_A_dot hP σ x) ?_
  · exact ((continuous_dot _).comp (gs_continuous_contactA hP)).continuousOn
  · intro x hx
    exact mul_nonneg (gs_ρ_nonneg hP hB (gs_rpiece_ridx x) (h0.trans hx.1) (by linarith [hx.2])).1
      (hs x hx)

lemma gs_A_anti (hP : P.IsSolution) (hB : P.Bounds) {σ τ₁ τ₂ : ℝ} (h0 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂)
    (h2 : τ₂ ≤ π / 2) (hs : ∀ r ∈ Ico τ₁ τ₂, sin (σ - r) ≤ 0) :
    dot (contactA P.path τ₂) (uvec σ) ≤ dot (contactA P.path τ₁) (uvec σ) := by
  refine le_of_right_deriv_nonpos h12 ?_ (fun x _ => gs_hasDerivWithinAt_A_dot hP σ x) ?_
  · exact ((continuous_dot _).comp (gs_continuous_contactA hP)).continuousOn
  · intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos
      (gs_ρ_nonneg hP hB (gs_rpiece_ridx x) (h0.trans hx.1) (by linarith [hx.2])).1 (hs x hx)

lemma gs_C_mono (hP : P.IsSolution) (hB : P.Bounds) {σ τ₁ τ₂ : ℝ} (h0 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂)
    (h2 : τ₂ ≤ π / 2) (hs : ∀ r ∈ Ico τ₁ τ₂, cos (r - σ) ≤ 0) :
    dot (contactC P.path τ₁) (uvec σ) ≤ dot (contactC P.path τ₂) (uvec σ) := by
  refine le_of_right_deriv_nonneg h12 ?_ (fun x _ => gs_hasDerivWithinAt_C_dot hP σ x) ?_
  · exact ((continuous_dot _).comp (gs_continuous_contactC hP)).continuousOn
  · intro x hx
    have := mul_nonpos_of_nonneg_of_nonpos
      (gs_ρ_nonneg hP hB (gs_rpiece_ridx x) (h0.trans hx.1) (by linarith [hx.2])).2 (hs x hx)
    linarith

lemma gs_C_anti (hP : P.IsSolution) (hB : P.Bounds) {σ τ₁ τ₂ : ℝ} (h0 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂)
    (h2 : τ₂ ≤ π / 2) (hs : ∀ r ∈ Ico τ₁ τ₂, 0 ≤ cos (r - σ)) :
    dot (contactC P.path τ₂) (uvec σ) ≤ dot (contactC P.path τ₁) (uvec σ) := by
  refine le_of_right_deriv_nonpos h12 ?_ (fun x _ => gs_hasDerivWithinAt_C_dot hP σ x) ?_
  · exact ((continuous_dot _).comp (gs_continuous_contactC hP)).continuousOn
  · intro x hx
    have := mul_nonneg
      (gs_ρ_nonneg hP hB (gs_rpiece_ridx x) (h0.trans hx.1) (by linarith [hx.2])).2 (hs x hx)
    linarith

variable (P) in
/-- The support function `H` of the cap of Gerver's sofa on `[0, π]`:
`H(σ) = 𝐱(σ) · u_σ + 1` for `σ ≤ π/2` and `H(σ) = 𝐱(σ - π/2) · v_{σ - π/2} + 1` for `σ > π/2`. -/
noncomputable def gs_H (σ : ℝ) : ℝ :=
  if σ ≤ π / 2 then dot (P.path σ) (uvec σ) + 1
  else dot (P.path (σ - π / 2)) (vvec (σ - π / 2)) + 1

variable (P) in
/-- The cap `K_G = {p_y ≥ 0} ∩ ⋂_{σ ∈ [0, π]} H₋(σ, H(σ))` of Gerver's sofa. -/
def gs_K : Set (ℝ × ℝ) := {p | 0 ≤ p.2} ∩ ⋂ σ ∈ Icc 0 π, halfMinus σ (P.gs_H σ)

/-- For `σ ≤ π/2`, `H(σ) = 𝐀(σ) · u_σ`. -/
lemma gs_H_eq_A {σ : ℝ} (hσ : σ ≤ π / 2) : P.gs_H σ = dot (contactA P.path σ) (uvec σ) := by
  rw [gs_H, ite_eq_left hσ, gs_contactA_eq']
  simp only [dot_add_left, dot_smul_left, dot_vvec_uvec, dot_uvec_self]; ring

/-- `𝐂(s) · u_{s + π/2} = 𝐱(s) · v_s + 1`. -/
lemma gs_dot_contactC_eq (s : ℝ) :
    dot (contactC P.path s) (uvec (s + π / 2)) = dot (P.path s) (vvec s) + 1 := by
  rw [gs_contactC_eq', uvec_add_pi_div_two]
  simp only [dot_add_left, dot_sub_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self]; ring

/-- For `σ ≥ π/2`, `H(σ) = 𝐂(σ - π/2) · u_σ`. -/
lemma gs_H_eq_C (hP : P.IsSolution) {σ : ℝ} (hσ : π / 2 ≤ σ) :
    P.gs_H σ = dot (contactC P.path (σ - π / 2)) (uvec σ) := by
  have e := gs_dot_contactC_eq (P := P) (σ - π / 2)
  rw [sub_add_cancel] at e
  rw [e, gs_H]
  rcases hσ.lt_or_eq with h | rfl
  · rw [ite_eq_right (not_le.2 h)]
  · rw [ite_eq_left le_rfl, sub_self, gs_path_zero hP, dot_uvec_pi_div_two,
      gs_path_pi_div_two_snd hP]
    simp

/-! ### The endpoints of the outer curves -/

lemma gs_path_pi_div_two_fst (hP : P.IsSolution) : (P.path (π / 2)).1 = 1 - P.a₁ + P.κ₅.1 := by
  have hO := gs_ord hP
  rw [gs_path_eq_phase hP (gs_piece₄ (by linarith [hO.1]))]
  simp only [gs_phase, gs_Phase.X, gs_ph5, rot, Prod.fst_add, sin_pi_div_two, cos_pi_div_two,
    gs_e₁ hP]
  ring

lemma gs_α_pi_div_two (hP : P.IsSolution) : P.gs_α (π / 2) = 1 - 2 * P.a₁ := by
  have hO := gs_ord hP
  rw [gs_α_eq hP (gs_piece₄ (by linarith [hO.1])), show π / 2 = π / 2 - 0 by ring,
    gs_α₅_eq hP]; simp

/-- `𝐀(0) = (1, 0)`. -/
lemma gs_A_zero (hP : P.IsSolution) : contactA P.path 0 = (1, 0) := by
  rw [gs_contactA_eq', gs_path_zero hP, gs_α_zero hP]
  ext <;> simp [uvec, vvec]

/-- `𝐀(π/2) = (X₀ + 2 a₁ - 1, 1)` with `X₀ = 𝐱(π/2)_x`. -/
lemma gs_A_pi_div_two (hP : P.IsSolution) :
    contactA P.path (π / 2) = ((P.path (π / 2)).1 + 2 * P.a₁ - 1, 1) := by
  rw [gs_contactA_eq', gs_α_pi_div_two hP]
  ext
  · simp [uvec, vvec]; ring
  · simp [uvec, vvec, gs_path_pi_div_two_snd hP]

/-- `𝐂(π/2) = (X₀ - 1, 0)` with `X₀ = 𝐱(π/2)_x`. -/
lemma gs_C_pi_div_two (hP : P.IsSolution) :
    contactC P.path (π / 2) = ((P.path (π / 2)).1 - 1, 0) := by
  rw [gs_contactC_eq', gs_β_pi_div_two hP]
  ext
  · simp [uvec, vvec]; ring
  · simp [uvec, vvec, gs_path_pi_div_two_snd hP]

/-- The `x`-coordinate `X₀ = 𝐱(π/2)_x` of the end of the rotation path. -/
lemma gs_X₀_bounds (hP : P.IsSolution) (hB : P.Bounds) :
    -1.2276 ≤ (P.path (π / 2)).1 ∧ (P.path (π / 2)).1 ≤ -1.2274 := by
  rw [gs_path_pi_div_two_fst hP]
  have := gs_a₁_lo hB
  have := gs_a₁_hi hB
  have := hB.κ₅₁_mem
  constructor <;> linarith [this.1, this.2]

/-! ### Monotonicity of the outer curves: `Ω(τ) · u_σ ≤ H(σ)` -/

lemma gs_sin_nonneg' {σ r : ℝ} (h1 : r ≤ σ) (h2 : σ - r ≤ π) : 0 ≤ sin (σ - r) :=
  sin_nonneg_of_nonneg_of_le_pi (by linarith) h2

lemma gs_sin_nonpos' {σ r : ℝ} (h1 : σ ≤ r) (h2 : r - σ ≤ π) : sin (σ - r) ≤ 0 :=
  sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)

/-- The outer curve `𝐀` lies in every half-plane `H₋(σ, H(σ))`, `σ ∈ [0, π]`. -/
lemma gs_A_le_H (hP : P.IsSolution) (hB : P.Bounds) {σ τ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ π)
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ π / 2) : dot (contactA P.path τ) (uvec σ) ≤ P.gs_H σ := by
  rcases le_or_gt σ (π / 2) with hσ | hσ
  · rw [gs_H_eq_A hσ]
    rcases le_total τ σ with h | h
    · exact gs_A_mono hP hB hτ₀ h hσ fun r hr => gs_sin_nonneg' hr.2.le (by linarith [hr.1])
    · exact gs_A_anti hP hB hσ₀ h hτ₁ fun r hr => gs_sin_nonpos' hr.1 (by linarith [hr.2])
  · rw [gs_H_eq_C hP hσ.le]
    have h1 : dot (contactA P.path τ) (uvec σ) ≤ dot (contactA P.path (π / 2)) (uvec σ) :=
      gs_A_mono hP hB hτ₀ hτ₁ le_rfl fun r hr => gs_sin_nonneg' (by linarith [hr.2])
        (by linarith [hr.1])
    have h2 : dot (contactA P.path (π / 2)) (uvec σ) ≤ dot (contactC P.path 0) (uvec σ) := by
      rw [gs_A_pi_div_two hP, gs_C_zero hP]
      have hc : cos σ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hσ.le (by linarith [pi_pos])
      have := gs_X₀_bounds hP hB
      have := gs_a₁_lo hB
      simp only [dot, uvec]
      nlinarith
    have h3 : dot (contactC P.path 0) (uvec σ) ≤ dot (contactC P.path (σ - π / 2)) (uvec σ) :=
      gs_C_mono hP hB le_rfl (by linarith) (by linarith) fun r hr => by
        rw [← cos_neg]
        exact cos_nonpos_of_pi_div_two_le_of_le (by linarith [hr.2]) (by linarith [hr.1])
    linarith

/-- The outer curve `𝐂` lies in every half-plane `H₋(σ, H(σ))`, `σ ∈ [0, π]`. -/
lemma gs_C_le_H (hP : P.IsSolution) (hB : P.Bounds) {σ τ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ π)
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ π / 2) : dot (contactC P.path τ) (uvec σ) ≤ P.gs_H σ := by
  rcases le_or_gt (π / 2) σ with hσ | hσ
  · rw [gs_H_eq_C hP hσ]
    rcases le_total τ (σ - π / 2) with h | h
    · exact gs_C_mono hP hB hτ₀ h (by linarith) fun r hr => by
        rw [← cos_neg]
        exact cos_nonpos_of_pi_div_two_le_of_le (by linarith [hr.2]) (by linarith [hr.1])
    · exact gs_C_anti hP hB (by linarith) h hτ₁ fun r hr =>
        cos_nonneg_of_mem_Icc ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · rw [gs_H_eq_A hσ.le]
    have h1 : dot (contactC P.path τ) (uvec σ) ≤ dot (contactC P.path 0) (uvec σ) :=
      gs_C_anti hP hB le_rfl hτ₀ hτ₁ fun r hr =>
        cos_nonneg_of_mem_Icc ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h2 : dot (contactC P.path 0) (uvec σ) ≤ dot (contactA P.path (π / 2)) (uvec σ) := by
      rw [gs_A_pi_div_two hP, gs_C_zero hP]
      have hc : 0 ≤ cos σ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hσ.le⟩
      have := gs_X₀_bounds hP hB
      have := gs_a₁_lo hB
      simp only [dot, uvec]
      nlinarith
    have h3 : dot (contactA P.path (π / 2)) (uvec σ) ≤ dot (contactA P.path σ) (uvec σ) :=
      gs_A_anti hP hB hσ₀ hσ.le le_rfl fun r hr => gs_sin_nonpos' hr.1 (by linarith [hr.2])
    linarith

/-- The outer curves `𝐀` and `𝐂` lie in the upper half-plane. -/
lemma gs_A_snd_nonneg (hP : P.IsSolution) (hB : P.Bounds) {τ : ℝ} (hτ₀ : 0 ≤ τ)
    (hτ₁ : τ ≤ π / 2) : 0 ≤ (contactA P.path τ).2 := by
  have := gs_A_mono hP hB (σ := π / 2) le_rfl hτ₀ hτ₁ fun r hr =>
    gs_sin_nonneg' (by linarith [hr.2]) (by linarith [hr.1, pi_pos])
  simpa only [dot_uvec_pi_div_two, gs_A_zero hP] using this

lemma gs_C_snd_nonneg (hP : P.IsSolution) (hB : P.Bounds) {τ : ℝ} (hτ₀ : 0 ≤ τ)
    (hτ₁ : τ ≤ π / 2) : 0 ≤ (contactC P.path τ).2 := by
  have := gs_C_anti hP hB (σ := π / 2) hτ₀ hτ₁ le_rfl fun r hr =>
    cos_nonneg_of_mem_Icc ⟨by linarith [hr.1, pi_pos], by linarith [hr.2, hr.1]⟩
  simpa only [dot_uvec_pi_div_two, gs_C_pi_div_two hP] using this

/-! ### The height of the rotation path -/

/-- The rotation path stays below height `1` on `[0, π/2]`. -/
lemma gs_path_snd_le_one (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ π / 2) : (P.path t).2 ≤ 1 := by
  have hO := gs_ord hP
  rcases gs_cases (P := P) t with h | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | h
  · rw [gs_path_eq_phase hP (gs_piece₀ h)]
    have := gs_ineq_y₁ hB h0 h
    simp only [gs_phase, gs_Phase.X, gs_ph1, rot, Prod.snd_add, gs_a₂ hP, gs_κ₁₂ hP]
    linarith
  · rw [gs_path_eq_phase hP (gs_piece₁ ha.le hb)]
    have := gs_ineq_y₂ hB hP h0 hb
    have := hB.κ₂₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph2, rot, Prod.snd_add]
    linarith
  · rw [gs_path_eq_phase hP (gs_piece₂ ha.le hb)]
    have := gs_ineq_y₃ hB hP ha.le hb
    have := hB.κ₃₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph3, rot, Prod.snd_add]
    linarith
  · rw [gs_path_eq_phase hP (gs_piece₃ ha.le hb)]
    obtain ⟨s, rfl⟩ : ∃ s, t = π / 2 - s := ⟨π / 2 - t, by ring⟩
    have := gs_ineq_y₂ hB hP (s := s) (by linarith [hO.1]) (by linarith)
    have := hB.κ₄₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph4, rot, Prod.snd_add, sin_pi_div_two_sub,
      cos_pi_div_two_sub, gs_d₁ hP, gs_d₂ hP]
    nlinarith
  · rw [gs_path_eq_phase hP (gs_piece₄ h.le)]
    obtain ⟨s, rfl⟩ : ∃ s, t = π / 2 - s := ⟨π / 2 - t, by ring⟩
    have := gs_ineq_y₁ hB (s := s) (by linarith) (by linarith)
    have := hB.κ₅₂_mem.2
    simp only [gs_phase, gs_Phase.X, gs_ph5, rot, Prod.snd_add, sin_pi_div_two_sub,
      cos_pi_div_two_sub, gs_e₁ hP, gs_e₂ hP, gs_a₂ hP]
    nlinarith

/-! ### The abscissa of the rotation path is decreasing -/

/-- `(𝐱_x)' = α cos t - β sin t`. -/
lemma gs_hasDerivAt_path_fst (hP : P.IsSolution) (t : ℝ) :
    HasDerivAt (fun s => (P.path s).1) (P.gs_α t * cos t - P.gs_β t * sin t) t :=
  (hasDerivAt_fst (gs_hasDerivAt_path' hP t)).congr_deriv (by simp [uvec, vvec]; ring)

/-- `𝐱_x` is antitone on `[0, π/2]`, since `α < 0 < β` there. -/
lemma gs_antitoneOn_path_fst (hP : P.IsSolution) (hB : P.Bounds) :
    AntitoneOn (fun s => (P.path s).1) (Icc 0 (π / 2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact fun t _ => (gs_hasDerivAt_path_fst hP t).continuousAt.continuousWithinAt
  · exact fun t _ => (gs_hasDerivAt_path_fst hP t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(gs_hasDerivAt_path_fst hP t).deriv]
    have h1 := gs_α_neg hP hB ht.1 ht.2.le
    have h2 := gs_β_pos hP hB ht.1.le ht.2
    have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2.le⟩
    have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, pi_pos])
    nlinarith

/-- `𝐱(π/2)_x ≤ 𝐱(t)_x ≤ 0` on `[0, π/2]`. -/
lemma gs_path_fst_le (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ π / 2) : (P.path (π / 2)).1 ≤ (P.path t).1 ∧ (P.path t).1 ≤ 0 := by
  have hπ : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  have ha := gs_antitoneOn_path_fst hP hB ⟨h0, h1⟩ ⟨hπ, le_rfl⟩ h1
  have hb := gs_antitoneOn_path_fst hP hB ⟨le_rfl, hπ⟩ ⟨h0, h1⟩ h0
  simp only [gs_path_zero hP, Prod.fst_zero] at hb
  exact ⟨ha, hb⟩

/-! ### Basic properties of `K_G` -/

lemma gs_mem_K_iff {p : ℝ × ℝ} :
    p ∈ P.gs_K ↔ 0 ≤ p.2 ∧ ∀ σ ∈ Icc 0 π, dot p (uvec σ) ≤ P.gs_H σ := by
  simp [gs_K, halfMinus]

lemma gs_A_mem_K (hP : P.IsSolution) (hB : P.Bounds) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ π / 2) :
    contactA P.path τ ∈ P.gs_K :=
  gs_mem_K_iff.2 ⟨gs_A_snd_nonneg hP hB h0 h1, fun _ hσ => gs_A_le_H hP hB hσ.1 hσ.2 h0 h1⟩

lemma gs_C_mem_K (hP : P.IsSolution) (hB : P.Bounds) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ π / 2) :
    contactC P.path τ ∈ P.gs_K :=
  gs_mem_K_iff.2 ⟨gs_C_snd_nonneg hP hB h0 h1, fun _ hσ => gs_C_le_H hP hB hσ.1 hσ.2 h0 h1⟩

lemma gs_H_zero (hP : P.IsSolution) : P.gs_H 0 = 1 := by
  rw [gs_H, ite_eq_left (by linarith [pi_pos]), gs_path_zero hP]; simp

lemma gs_H_pi_div_two (hP : P.IsSolution) : P.gs_H (π / 2) = 1 := by
  rw [gs_H, ite_eq_left le_rfl, dot_uvec_pi_div_two, gs_path_pi_div_two_snd hP]; simp

lemma gs_H_pi : P.gs_H π = 1 - (P.path (π / 2)).1 := by
  rw [gs_H, ite_eq_right (by linarith [pi_pos]), show π - π / 2 = π / 2 by ring]
  simp [dot, vvec]; ring

/-- `K_G` lies in the box `[𝐱(π/2)_x - 1, 1] × [0, 1]`. -/
lemma gs_K_bounds (hP : P.IsSolution) {p : ℝ × ℝ} (hp : p ∈ P.gs_K) :
    (P.path (π / 2)).1 - 1 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [gs_mem_K_iff] at hp
  have h0 := hp.2 0 ⟨le_rfl, pi_pos.le⟩
  have h1 := hp.2 (π / 2) ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have h2 := hp.2 π ⟨pi_pos.le, le_rfl⟩
  rw [gs_H_zero hP, dot_uvec_zero] at h0
  rw [gs_H_pi_div_two hP, dot_uvec_pi_div_two] at h1
  rw [gs_H_pi] at h2
  simp [dot, uvec] at h2
  exact ⟨by linarith, h0, hp.1, h1⟩

/-- `K_G` as an intersection of closed half-planes. -/
lemma gs_K_eq : P.gs_K = halfMinus (3 * π / 2) 0 ∩ ⋂ σ ∈ Icc 0 π, halfMinus σ (P.gs_H σ) := by
  ext p
  simp only [gs_K, mem_inter_iff, mem_ofPred_eq, halfMinus, dot_uvec_three_pi_div_two]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

lemma gs_isClosed_K : IsClosed P.gs_K := by
  rw [gs_K_eq]
  exact (isClosed_halfMinus _ _).inter (isClosed_biInter fun σ _ => isClosed_halfMinus _ _)

lemma gs_convex_K : Convex ℝ P.gs_K := by
  rw [gs_K_eq]
  exact (convex_halfMinus _ _).inter (convex_iInter₂ fun σ _ => convex_halfMinus _ _)

/-- `K_G` is a convex body. -/
lemma gs_isConvexBody_K (hP : P.IsSolution) (hB : P.Bounds) : IsConvexBody P.gs_K := by
  refine ⟨⟨_, gs_A_mem_K hP hB le_rfl (by linarith [pi_pos])⟩, ?_, gs_convex_K⟩
  exact Metric.isCompact_of_isClosed_isBounded gs_isClosed_K
    (ms_isBounded_of_bounds _ _ _ _ fun p hp => gs_K_bounds hP hp)

/-- The support function of `K_G` on `[0, π]` is `H`. -/
lemma gs_supp_K (hP : P.IsSolution) (hB : P.Bounds) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ π) :
    supp P.gs_K σ = P.gs_H σ := by
  have hK := gs_isConvexBody_K hP hB
  refine le_antisymm (supp_le_of_forall hK.1 fun p hp => (gs_mem_K_iff.1 hp).2 σ ⟨h0, h1⟩) ?_
  rcases le_or_gt σ (π / 2) with h | h
  · rw [gs_H_eq_A h]
    exact dot_le_supp hK.2.1 (gs_A_mem_K hP hB h0 h) σ
  · rw [gs_H_eq_C hP h.le]
    exact dot_le_supp hK.2.1 (gs_C_mem_K hP hB (by linarith) (by linarith)) σ

/-- `h_{K_G}(3π/2) = 0`: the lowest points of `K_G` lie on the `x`-axis. -/
lemma gs_supp_K_three_pi_div_two (hP : P.IsSolution) (hB : P.Bounds) :
    supp P.gs_K (3 * π / 2) = 0 := by
  have hK := gs_isConvexBody_K hP hB
  refine le_antisymm (supp_le_of_forall hK.1 fun p hp => ?_) ?_
  · rw [dot_uvec_three_pi_div_two]; linarith [(gs_mem_K_iff.1 hp).1]
  · have := dot_le_supp hK.2.1 (gs_A_mem_K hP hB le_rfl (by linarith [pi_pos])) (3 * π / 2)
    rwa [dot_uvec_three_pi_div_two, gs_A_zero hP, neg_zero] at this

/-- `K_G` is a cap with rotation angle `π/2`. -/
lemma gs_isCap_K (hP : P.IsSolution) (hB : P.Bounds) : IsCap P.gs_K (π / 2) := by
  have hK := gs_isConvexBody_K hP hB
  have h12 : supp P.gs_K (π / 2) = 1 := by
    rw [gs_supp_K hP hB (by linarith [pi_pos]) (by linarith [pi_pos]), gs_H_pi_div_two hP]
  refine ⟨⟨by linarith [pi_pos], le_rfl⟩, hK, h12, h12, ?_, gs_supp_K_three_pi_div_two hP hB, ?_⟩
  · rw [show π / 2 + π = 3 * π / 2 by ring]; exact gs_supp_K_three_pi_div_two hP hB
  · refine ⟨Option (Icc (0 : ℝ) π), fun i => i.elim (3 * π / 2) (fun σ => σ.1),
      fun i => i.elim 0 (fun σ => P.gs_H σ.1), fun i => ?_, ?_⟩
    · rcases i with _ | ⟨σ, hσ⟩
      · exact Or.inr (Or.inr rfl)
      · rcases le_or_gt σ (π / 2) with h | h
        · exact Or.inl (Or.inl ⟨hσ.1, h⟩)
        · exact Or.inl (Or.inr ⟨h.le, show σ ≤ π / 2 + π / 2 by linarith [hσ.2]⟩)
    · rw [gs_K_eq]
      ext p
      simp only [mem_inter_iff, mem_iInter, Option.forall, Option.elim, Subtype.forall]

lemma gs_H_add_pi_div_two (hP : P.IsSolution) {t : ℝ} (h0 : 0 ≤ t) :
    P.gs_H (t + π / 2) = dot (P.path t) (vvec t) + 1 := by
  rw [gs_H_eq_C hP (by linarith), add_sub_cancel_right, gs_dot_contactC_eq]

lemma gs_H_of_le {σ : ℝ} (h : σ ≤ π / 2) : P.gs_H σ = dot (P.path σ) (uvec σ) + 1 := by
  rw [gs_H, ite_eq_left h]

/-- The inner corner of `K_G` is the rotation path. -/
lemma gs_innerCorner_K (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ π / 2) : innerCorner P.gs_K t = P.path t := by
  rw [proposition2_2_2_innerCorner, gs_supp_K hP hB h0 (by linarith [pi_pos]),
    gs_supp_K hP hB (by linarith [pi_pos]) (by linarith), gs_H_of_le h1,
    gs_H_add_pi_div_two hP h0, add_sub_cancel_right, add_sub_cancel_right]
  exact (eq_dot_uvec_smul_add _ t).symm

/-- The points of the rotation path above the `x`-axis lie in `K_G`. -/
lemma gs_path_mem_K (hP : P.IsSolution) (hB : P.Bounds) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ π / 2)
    (hy : 0 ≤ (P.path s).2) : P.path s ∈ P.gs_K := by
  have hx := gs_path_fst_le hP hB h0 h1
  have hy1 := gs_path_snd_le_one hP hB h0 h1
  have hX := gs_X₀_bounds hP hB
  have ha := gs_a₁_lo hB
  have ha' := gs_a₁_hi hB
  refine gs_mem_K_iff.2 ⟨hy, fun σ hσ => ?_⟩
  rcases le_or_gt σ (π / 2) with h | h
  · have hA := gs_A_le_H hP hB hσ.1 hσ.2 (τ := π / 2) (by linarith [pi_pos]) le_rfl
    rw [gs_A_pi_div_two hP] at hA
    have hc : 0 ≤ cos σ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hσ.1], h⟩
    have hsn : 0 ≤ sin σ := sin_nonneg_of_nonneg_of_le_pi hσ.1 hσ.2
    simp only [dot, uvec] at hA ⊢
    nlinarith
  · have hC := gs_C_le_H hP hB hσ.1 hσ.2 (τ := 0) le_rfl (by linarith [pi_pos])
    rw [gs_C_zero hP] at hC
    have hc : cos σ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le h.le (by linarith [pi_pos, hσ.2])
    have hsn : 0 ≤ sin σ := sin_nonneg_of_nonneg_of_le_pi hσ.1 hσ.2
    simp only [dot, uvec] at hC ⊢
    nlinarith

/-- `K_G` contains its niche (Theorem 2.5.8, (3) ⇒ (1)). -/
lemma gs_niche_subset (hP : P.IsSolution) (hB : P.Bounds) :
    niche P.gs_K (π / 2) ⊆ P.gs_K := by
  refine ((theorem2_5_8 (gs_isCap_K hP hB)).out 3 1).1 fun t ht => ?_
  rw [gs_innerCorner_K hP hB ht.1.le ht.2.le]
  by_cases hy : 0 ≤ (P.path t).2
  · exact Or.inr (gs_path_mem_K hP hB ht.1.le ht.2.le hy)
  · refine Or.inl fun hint => hy ?_
    have := (interior_subset hint).1
    simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two] at this
    exact this

/-- The hallway map of `K_G` at angle `t` is `p ↦ 𝐱(t) + R_t p`. -/
lemma gs_hallwayMap_K (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    hallwayMap P.gs_K t = fun p => P.path t + rot t p := by
  funext p
  rw [← gs_innerCorner_K hP hB h0 h1, proposition2_2_2_innerCorner, hallwayMap]
  rw [add_comm]; abel

lemma gs_mem_suppHallway_K (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ π / 2) (p : ℝ × ℝ) :
    p ∈ (fun q => P.path t + rot t q) '' hallway ↔ p ∈ suppHallway P.gs_K t := by
  rw [suppHallway, gs_hallwayMap_K hP hB h0 h1]

/-- Gerver's sofa is `K_G \ 𝒩(K_G)`. -/
lemma gs_gerverSofa_eq (hP : P.IsSolution) (hB : P.Bounds) :
    gerverSofa P = P.gs_K \ niche P.gs_K (π / 2) := by
  have hK := gs_isConvexBody_K hP hB
  have hπ : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  have hs2 : supp P.gs_K (π / 2) = 1 := by
    rw [gs_supp_K hP hB hπ (by linarith [pi_pos]), gs_H_pi_div_two hP]
  ext p
  simp only [gerverSofa, shapeOfPath, mem_inter_iff, mem_iInter₂, Set.mem_sdiff]
  constructor
  · -- `G ⊆ K_G \ 𝒩(K_G)`: the hallway `𝐱(t) + R_t(L)` is `Q⁺(t) \ Q⁻(t)` for `K_G`.
    rintro ⟨⟨hH, hL⟩, -⟩
    have hL' : ∀ t ∈ Icc 0 (π / 2), p ∈ qPlus P.gs_K t \ qMinus P.gs_K t := fun t ht => by
      rw [← proposition2_2_2_hallway, ← gs_mem_suppHallway_K hP hB ht.1 ht.2]; exact hL t ht
    refine ⟨gs_mem_K_iff.2 ⟨hH.2.1, fun σ hσ => ?_⟩, ?_⟩
    · -- `p ∈ K_G`: the support inequality at `σ` comes from `Q⁺(σ)` or `Q⁺(σ - π/2)`.
      rcases le_or_gt σ (π / 2) with h | h
      · have := ((ms_mem_qPlus_iff _ _ _).1 (hL' σ ⟨hσ.1, h⟩).1).1
        rwa [gs_supp_K hP hB hσ.1 hσ.2] at this
      · have := ((ms_mem_qPlus_iff _ _ _).1
          (hL' (σ - π / 2) ⟨by linarith, by linarith [hσ.2]⟩).1).2
        rwa [sub_add_cancel, gs_supp_K hP hB hσ.1 hσ.2, ← uvec_add_pi_div_two,
          sub_add_cancel] at this
    · -- `p ∉ 𝒩(K_G)`: `p` avoids every `Q⁻(t)`.
      rintro ⟨-, hU⟩
      obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hU
      exact (hL' t (Ioo_subset_Icc_self ht)).2 hq
  · -- `K_G \ 𝒩(K_G) ⊆ G`.
    rintro ⟨hp, hN⟩
    have hb := gs_K_bounds hP hp
    refine ⟨⟨⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩, fun t ht => ?_⟩, ?_⟩
    · -- `p` lies in the hallway at `t`: in `Q⁺(t)` as `p ∈ K_G`, and not in `Q⁻(t)`, by
      -- `p ∉ 𝒩(K_G)` for `0 < t < π/2` and by `0 ≤ p_y ≤ 1` for `t = 0, π/2`.
      rw [gs_mem_suppHallway_K hP hB ht.1 ht.2, proposition2_2_2_hallway]
      refine ⟨(ms_mem_qPlus_iff _ _ _).2 ⟨dot_le_supp hK.2.1 hp t, ?_⟩, fun hq => ?_⟩
      · rw [← uvec_add_pi_div_two]; exact dot_le_supp hK.2.1 hp _
      · rw [ms_mem_qMinus_iff] at hq
        rcases ht.1.lt_or_eq with h0 | rfl
        · rcases ht.2.lt_or_eq with h1 | rfl
          · have hp2 : 0 ≤ dot p (uvec (π / 2)) := by rw [dot_uvec_pi_div_two]; exact hb.2.2.1
            exact hN ⟨⟨hp2, hp2⟩, mem_iUnion₂.2 ⟨t, ⟨h0, h1⟩, (ms_mem_qMinus_iff _ _ _).2 hq⟩⟩
          · rw [hs2, dot_uvec_pi_div_two] at hq; linarith [hq.1]
        · rw [zero_add, hs2] at hq
          have : dot p (vvec 0) = p.2 := by simp [dot, vvec]
          linarith [hq.2]
    · -- `p` lies in the vertical side `𝐱(π/2) + R_{π/2}(V_L)`.
      have e : (fun q => P.path (π / 2) + rot (π / 2) q) =
          fun q => rot (π / 2) q + P.path (π / 2) := funext fun q => add_comm _ _
      rw [e, ms_mem_image_iff]
      simp only [vertSide, mem_ofPred_eq, dot_sub_left, dot_uvec_pi_div_two]
      have hv : ∀ q : ℝ × ℝ, dot q (vvec (π / 2)) = -q.1 := fun q => by simp [dot, vvec]
      rw [hv, hv, Prod.snd_sub, gs_path_pi_div_two_snd hP, sub_zero]
      exact ⟨hb.2.2.1, hb.2.2.2, by linarith [hb.1]⟩

/-- Gerver's sofa is a monotone sofa with cap `K_G`. -/
lemma gs_monotone_K (hP : P.IsSolution) (hB : P.Bounds) :
    IsMonotoneSofa (gerverSofa P) (π / 2) ∧ capOf (gerverSofa P) (π / 2) = P.gs_K := by
  obtain ⟨S, hS, hcap⟩ := (theorem2_5_9 (gs_isCap_K hP hB)).2 (gs_niche_subset hP hB)
  have h := theorem2_4_3 hS
  rw [hcap] at h
  have hG : gerverSofa P = S := (gs_gerverSofa_eq hP hB).trans h.symm
  rw [hG]
  exact ⟨hS, hcap⟩

/-- The derivative of `σ ↦ 𝐱(σ) · u_σ + 1` (the support function on `[0, π/2]`) is `𝐀(σ) · v_σ`. -/
lemma gs_hasDerivAt_G₁ (hP : P.IsSolution) (σ : ℝ) :
    HasDerivAt (fun s => dot (P.path s) (uvec s) + 1) (dot (contactA P.path σ) (vvec σ)) σ := by
  refine ((hasDerivAt_dot' (gs_hasDerivAt_path hP σ) (hasDerivAt_uvec σ)).add_const
    1).congr_deriv ?_
  rw [gs_contactA_eq', ← gs_deriv_path hP]
  simp only [dot_add_left, dot_smul_left, dot_vvec_self, dot_uvec_vvec, gs_α]; ring

/-- The derivative of `σ ↦ 𝐱(σ - π/2) · v_{σ - π/2} + 1` (the support function on `[π/2, π]`)
is `𝐂(σ - π/2) · v_σ`. -/
lemma gs_hasDerivAt_G₂ (hP : P.IsSolution) (σ : ℝ) :
    HasDerivAt (fun s => dot (P.path (s - π / 2)) (vvec (s - π / 2)) + 1)
      (dot (contactC P.path (σ - π / 2)) (vvec σ)) σ := by
  have hs : HasDerivAt (fun s : ℝ => s - π / 2) 1 σ := (hasDerivAt_id σ).sub_const _
  have h1 := (gs_hasDerivAt_path hP (σ - π / 2)).scomp σ hs
  have h2 := (hasDerivAt_vvec (σ - π / 2)).scomp σ hs
  refine ((hasDerivAt_dot' h1 h2).add_const 1).congr_deriv ?_
  have hv : vvec σ = -uvec (σ - π / 2) := by rw [← vvec_add_pi_div_two, sub_add_cancel]
  rw [one_smul, one_smul, gs_contactC_eq', ← gs_deriv_path hP, hv]
  simp only [Function.comp_apply, dot_add_left, dot_sub_left, dot_smul_left, dot_neg_right,
    dot_uvec_self, dot_vvec_uvec, gs_β]
  ring

/-- `v_{K_G}⁻(t) = 𝐀(t)` on `[0, π/2]`. -/
lemma gs_vminus_K (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    vminus P.gs_K t = contactA P.path t := by
  have hK := gs_isConvexBody_K hP hB
  have hu : dot (vminus P.gs_K t) (uvec t) = dot (contactA P.path t) (uvec t) := by
    rw [dot_vminus_uvec, gs_supp_K hP hB h0 (by linarith [pi_pos]), gs_H_eq_A h1]
  refine eq_of_dot_frame hu ?_
  rcases h0.lt_or_eq with h0 | rfl
  · refine dot_vminus_vvec_of_hasDerivAt hK (gs_hasDerivAt_G₁ hP t) ?_ ?_
    · filter_upwards [Ioc_mem_nhdsLE h0] with s hs
      rw [gs_supp_K hP hB hs.1.le (by linarith [hs.2, pi_pos]), gs_H_of_le (hs.2.trans h1)]
    · rw [gs_supp_K hP hB h0.le (by linarith [pi_pos]), gs_H_of_le h1]
  · -- at `t = 0`, `v⁻` is the lowest point of the edge, and `𝐀(0) = (1, 0)`
    have hA : contactA P.path 0 ∈ edge P.gs_K 0 :=
      ⟨gs_A_mem_K hP hB le_rfl (by linarith [pi_pos]), by
        simp only [suppLine, line, mem_ofPred_eq]; rw [← dot_vminus_uvec, hu]⟩
    have h1 := dot_vminus_le_dot hK.2.1 hA
    have h2 := (gs_mem_K_iff.1 (vminus_mem_edge hK 0).1).1
    have e : ∀ q : ℝ × ℝ, dot q (vvec 0) = q.2 := fun q => by simp [dot, vvec]
    rw [e, e, gs_A_zero hP] at *
    simp only at h1 ⊢
    linarith

/-- `v_{K_G}⁺(t) = 𝐀(t)` on `[0, π/2)`. -/
lemma gs_vplus_K (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < π / 2) :
    vplus P.gs_K t = contactA P.path t := by
  have hK := gs_isConvexBody_K hP hB
  have hu : dot (vplus P.gs_K t) (uvec t) = dot (contactA P.path t) (uvec t) := by
    rw [dot_vplus_uvec, gs_supp_K hP hB h0 (by linarith [pi_pos]), gs_H_eq_A h1.le]
  refine eq_of_dot_frame hu (dot_vplus_vvec_of_hasDerivAt hK (gs_hasDerivAt_G₁ hP t) ?_ ?_)
  · filter_upwards [Ico_mem_nhdsGE h1] with s hs
    rw [gs_supp_K hP hB (h0.trans hs.1) (by linarith [hs.2, pi_pos]), gs_H_of_le hs.2.le]
  · rw [gs_supp_K hP hB h0 (by linarith [pi_pos]), gs_H_of_le h1.le]

/-- `v_{K_G}⁺(t + π/2) = 𝐂(t)` on `[0, π/2]`. -/
lemma gs_vplus_K' (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    vplus P.gs_K (t + π / 2) = contactC P.path t := by
  have hK := gs_isConvexBody_K hP hB
  have hu : dot (vplus P.gs_K (t + π / 2)) (uvec (t + π / 2)) =
      dot (contactC P.path t) (uvec (t + π / 2)) := by
    rw [dot_vplus_uvec, gs_supp_K hP hB (by linarith [pi_pos]) (by linarith),
      gs_H_eq_C hP (by linarith), add_sub_cancel_right]
  refine eq_of_dot_frame hu ?_
  rcases h1.lt_or_eq with h1 | rfl
  · have := dot_vplus_vvec_of_hasDerivAt hK (gs_hasDerivAt_G₂ hP (t + π / 2)) ?_ ?_
    · rwa [add_sub_cancel_right] at this
    · filter_upwards [Ico_mem_nhdsGE (show t + π / 2 < π by linarith)] with s hs
      rw [gs_supp_K hP hB (by linarith [hs.1, pi_pos]) hs.2.le,
        gs_H_eq_C hP (by linarith [hs.1]), ← gs_dot_contactC_eq, sub_add_cancel]
    · rw [gs_supp_K hP hB (by linarith [pi_pos]) (by linarith), gs_H_eq_C hP (by linarith),
        ← gs_dot_contactC_eq, sub_add_cancel]
  · -- at `t = π/2`, `v⁺(π)` is the lowest point of the edge, and `𝐂(π/2) = (X₀ - 1, 0)`
    have hC : contactC P.path (π / 2) ∈ edge P.gs_K (π / 2 + π / 2) :=
      ⟨gs_C_mem_K hP hB (by linarith [pi_pos]) le_rfl, by
        simp only [suppLine, line, mem_ofPred_eq]; rw [← dot_vplus_uvec, hu]⟩
    have h1 := dot_le_dot_vplus hK.2.1 hC
    have h2 := (gs_mem_K_iff.1 (vplus_mem_edge hK (π / 2 + π / 2)).1).1
    have e : ∀ q : ℝ × ℝ, dot q (vvec (π / 2 + π / 2)) = -q.2 := fun q => by
      rw [show π / 2 + π / 2 = π by ring]; simp [dot, vvec]
    rw [e, e, gs_C_pi_div_two hP] at *
    simp only at h1 ⊢
    linarith

/-- `h_{K_G}(t) = 𝐱(t) · u_t + 1` and `h_{K_G}(t + π/2) = 𝐱(t) · v_t + 1` on `[0, π/2]`. -/
lemma gs_supp_K_eq (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    supp P.gs_K t = dot (P.path t) (uvec t) + 1 ∧
      supp P.gs_K (t + π / 2) = dot (P.path t) (vvec t) + 1 := by
  rw [gs_supp_K hP hB h0 (by linarith [pi_pos]), gs_supp_K hP hB (by linarith [pi_pos])
    (by linarith), gs_H_of_le h1, gs_H_add_pi_div_two hP h0]
  exact ⟨rfl, rfl⟩

/-- **InjCond2** for `K_G`: its inner corner (the rotation path) is `C¹`. -/
lemma gs_InjCond2 (hP : P.IsSolution) (hB : P.Bounds) : InjCond2 P.gs_K :=
  (gs_contDiff_path hP).contDiffOn.congr fun _ ht => gs_innerCorner_K hP hB ht.1 ht.2

/-- **InjCond3** for `K_G`: `α < 0 < β` on `(0, π/2)`. -/
lemma gs_InjCond3 (hP : P.IsSolution) (hB : P.Bounds) : InjCond3 P.gs_K := by
  intro t ht
  have e : deriv (innerCorner P.gs_K) t = deriv P.path t := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact gs_innerCorner_K hP hB hs.1.le hs.2.le
  rw [e]
  exact ⟨gs_α_neg hP hB ht.1 ht.2.le, gs_β_pos hP hB ht.1.le ht.2⟩

/-! ### Functions selected by the half-open phase intervals -/

/-- A function selected by the half-open phase intervals, as an `if` cascade. -/
lemma gs_ridx_sel (f : ℕ → ℝ → ℝ) (t : ℝ) :
    f (P.gs_ridx t) t = if t < P.φ then f 0 t else if t < P.θ then f 1 t
      else if t < π / 2 - P.θ then f 2 t else if t < π / 2 - P.φ then f 3 t else f 4 t := by
  unfold gs_ridx; split_ifs <;> rfl

/-- Functions selected by the half-open phase intervals from continuous functions are measurable,
and integrable on compact intervals (`gs_integrableOn_sel`, `gs_intervalIntegrable_sel`). -/
lemma gs_measurable_sel {f : ℕ → ℝ → ℝ} (hf : ∀ i, Continuous (f i)) :
    Measurable fun t => f (P.gs_ridx t) t := by
  simp only [gs_ridx_sel]
  exact Measurable.ite measurableSet_Iio (hf 0).measurable <| Measurable.ite measurableSet_Iio
    (hf 1).measurable <| Measurable.ite measurableSet_Iio (hf 2).measurable <|
    Measurable.ite measurableSet_Iio (hf 3).measurable (hf 4).measurable

lemma gs_integrableOn_sel {f : ℕ → ℝ → ℝ} (hf : ∀ i, Continuous (f i)) (a b : ℝ) :
    IntegrableOn (fun t => f (P.gs_ridx t) t) (Icc a b) := by
  obtain ⟨M, hM⟩ := gs_exists_bound_of_sel hf (fun t => ⟨P.gs_ridx t, gs_ridx_lt t, rfl⟩) a b
  exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (gs_measurable_sel hf).aestronglyMeasurable (M := M)
    (ae_restrict_of_forall_mem measurableSet_Icc hM)

lemma gs_intervalIntegrable_sel {f : ℕ → ℝ → ℝ} (hf : ∀ i, Continuous (f i)) (a b : ℝ) :
    IntervalIntegrable (fun t => f (P.gs_ridx t) t) volume a b :=
  (gs_integrableOn_sel hf (min a b) (max a b)).intervalIntegrable

variable (P) in
/-- The density of `σ_{K_G}` on `[0, π/2)`: `ρ_A` on the half-open phase intervals. -/
noncomputable def gs_rA (t : ℝ) : ℝ := max ((P.gs_phase (P.gs_ridx t)).ρA t) 0

variable (P) in
/-- The density of `σ_{K_G}` on `(π/2, π]`, as a function of `t - π/2`: `ρ_C`. -/
noncomputable def gs_rC (t : ℝ) : ℝ := max ((P.gs_phase (P.gs_ridx t)).ρC t) 0

lemma gs_rA_nonneg (t : ℝ) : 0 ≤ P.gs_rA t := le_max_right _ _
lemma gs_rC_nonneg (t : ℝ) : 0 ≤ P.gs_rC t := le_max_right _ _

lemma gs_measurable_rA : Measurable P.gs_rA :=
  gs_measurable_sel (f := fun i t => max ((P.gs_phase i).ρA t) 0)
    fun i => (gs_continuous_ρA i).max continuous_const

lemma gs_measurable_rC : Measurable P.gs_rC :=
  gs_measurable_sel (f := fun i t => max ((P.gs_phase i).ρC t) 0)
    fun i => (gs_continuous_ρC i).max continuous_const

lemma gs_intervalIntegrable_rA (a b : ℝ) : IntervalIntegrable P.gs_rA volume a b :=
  gs_intervalIntegrable_sel (f := fun i t => max ((P.gs_phase i).ρA t) 0)
    (fun i => (gs_continuous_ρA i).max continuous_const) a b

lemma gs_intervalIntegrable_rC (a b : ℝ) : IntervalIntegrable P.gs_rC volume a b :=
  gs_intervalIntegrable_sel (f := fun i t => max ((P.gs_phase i).ρC t) 0)
    (fun i => (gs_continuous_ρC i).max continuous_const) a b

lemma gs_intervalIntegrable_rC' (a b : ℝ) :
    IntervalIntegrable (fun x => P.gs_rC (x - π / 2)) volume a b := by
  simpa using (gs_intervalIntegrable_rC (P := P) (a - π / 2) (b - π / 2)).comp_sub_right (π / 2)

/-! ### The distribution function of `σ_{K_G}` -/

lemma gs_continuous_supp_K (hP : P.IsSolution) (hB : P.Bounds) : Continuous (supp P.gs_K) :=
  continuous_supp (gs_isConvexBody_K hP hB).2.1

/-- `t ↦ ∫₀ᵗ h_{K_G}` is differentiable, with derivative `h_{K_G}`. -/
lemma gs_hasDerivAt_primitive (hP : P.IsSolution) (hB : P.Bounds) (t : ℝ) :
    HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, supp P.gs_K x) (supp P.gs_K t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((gs_continuous_supp_K hP hB).intervalIntegrable _ _)
    ((gs_continuous_supp_K hP hB).stronglyMeasurableAtFilter _ _)
    (gs_continuous_supp_K hP hB).continuousAt

lemma gs_continuous_primitive (hP : P.IsSolution) (hB : P.Bounds) :
    Continuous fun u => ∫ x in (0 : ℝ)..u, supp P.gs_K x :=
  continuous_iff_continuousAt.2 fun t => (gs_hasDerivAt_primitive hP hB t).continuousAt

variable (P) in
/-- `G₁(t) = 𝐀(t) · v_t + ∫₀ᵗ h_K`, the distribution function of `σ_K` on `[0, π/2]` (without the
jump at `π/2`). -/
noncomputable def gs_G₁ (t : ℝ) : ℝ :=
  dot (contactA P.path t) (vvec t) + ∫ x in (0 : ℝ)..t, supp P.gs_K x

variable (P) in
/-- `G₂(σ) = 𝐂(σ - π/2) · v_σ + ∫₀^σ h_K`, the distribution function of `σ_K` on `[π/2, π]`. -/
noncomputable def gs_G₂ (σ : ℝ) : ℝ :=
  dot (contactC P.path (σ - π / 2)) (vvec σ) + ∫ x in (0 : ℝ)..σ, supp P.gs_K x

/-- The right derivative of `G₁` on `[0, π/2)` is the density `ρ_A`. -/
lemma gs_hasDerivWithinAt_G₁ (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t < π / 2) : HasDerivWithinAt P.gs_G₁ (P.gs_rA t) (Ici t) t := by
  have hA := gs_hasDerivWithinAt_contactA hP (gs_rpiece_ridx (P := P) t)
  have hv := (hasDerivAt_vvec t).hasDerivWithinAt (s := Ici t)
  have := (hasDerivWithinAt_dot' hA hv).add (gs_hasDerivAt_primitive hP hB t).hasDerivWithinAt
  refine this.congr_deriv ?_
  rw [gs_supp_K hP hB h0 (by linarith [pi_pos]), gs_H_eq_A h1.le, gs_rA,
    max_eq_left (gs_ρ_nonneg hP hB (gs_rpiece_ridx t) h0 h1.le).1]
  simp only [dot_smul_left, dot_vvec_self, dot_neg_right]; ring

/-- The right derivative of `G₂` on `[π/2, π)` is the density `ρ_C(σ - π/2)`. -/
lemma gs_hasDerivWithinAt_G₂ (hP : P.IsSolution) (hB : P.Bounds) {σ : ℝ} (h0 : π / 2 ≤ σ)
    (h1 : σ < π) : HasDerivWithinAt P.gs_G₂ (P.gs_rC (σ - π / 2)) (Ici σ) σ := by
  have hs : HasDerivWithinAt (fun x : ℝ => x - π / 2) 1 (Ici σ) σ :=
    ((hasDerivAt_id σ).sub_const _).hasDerivWithinAt
  have hC := (gs_hasDerivWithinAt_contactC hP (gs_rpiece_ridx (P := P) (σ - π / 2))).scomp σ hs
    (fun x hx => by simp only [mem_Ici] at hx ⊢; linarith)
  have hv := (hasDerivAt_vvec σ).hasDerivWithinAt (s := Ici σ)
  have := (hasDerivWithinAt_dot' hC hv).add (gs_hasDerivAt_primitive hP hB σ).hasDerivWithinAt
  refine this.congr_deriv ?_
  have hvv : vvec σ = -uvec (σ - π / 2) := by rw [← vvec_add_pi_div_two, sub_add_cancel]
  rw [gs_supp_K hP hB (by linarith [pi_pos]) h1.le, gs_H_eq_C hP h0, gs_rC,
    max_eq_left (gs_ρ_nonneg hP hB (gs_rpiece_ridx _) (by linarith) (by linarith)).2]
  simp only [Function.comp_apply, one_smul, dot_smul_left, dot_neg_right]
  rw [hvv]
  simp only [dot_neg_right, dot_uvec_self]; ring

lemma gs_continuous_G₁ (hP : P.IsSolution) (hB : P.Bounds) : Continuous P.gs_G₁ :=
  (continuous_dot_pair.comp ((gs_continuous_contactA hP).prodMk continuous_vvec)).add
    (gs_continuous_primitive hP hB)

lemma gs_continuous_G₂ (hP : P.IsSolution) (hB : P.Bounds) : Continuous P.gs_G₂ :=
  (continuous_dot_pair.comp (((gs_continuous_contactC hP).comp
    (continuous_id.sub continuous_const)).prodMk continuous_vvec)).add
    (gs_continuous_primitive hP hB)

/-- `G₁(b) - G₁(a) = ∫_a^b ρ_A` on `[0, π/2]`. -/
lemma gs_G₁_sub (hP : P.IsSolution) (hB : P.Bounds) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) : P.gs_G₁ b - P.gs_G₁ a = ∫ x in a..b, P.gs_rA x :=
  (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (gs_continuous_G₁ hP hB).continuousOn
    (fun _ hx => (gs_hasDerivWithinAt_G₁ hP hB (ha.trans hx.1.le) (hx.2.trans_le hb)).mono
      Ioi_subset_Ici_self) (gs_intervalIntegrable_rA a b)).symm

/-- `G₂(b) - G₂(a) = ∫_a^b ρ_C(x - π/2) dx` on `[π/2, π]`. -/
lemma gs_G₂_sub (hP : P.IsSolution) (hB : P.Bounds) {a b : ℝ} (ha : π / 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π) : P.gs_G₂ b - P.gs_G₂ a = ∫ x in a..b, P.gs_rC (x - π / 2) :=
  (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (gs_continuous_G₂ hP hB).continuousOn
    (fun _ hx => (gs_hasDerivWithinAt_G₂ hP hB (ha.trans hx.1.le) (hx.2.trans_le hb)).mono
      Ioi_subset_Ici_self) (gs_intervalIntegrable_rC' a b)).symm

/-- On `[0, π/2]`, the distribution function of `σ_{K_G}` is `G₁` plus the atom at `t`. -/
lemma gs_sigmaFun_eq₁ (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    sigmaFun P.gs_K t = P.gs_G₁ t + sigmaAt P.gs_K t := by
  have hK := gs_isConvexBody_K hP hB
  have h := (proposition2_1_2 hK t).2
  rw [gs_vminus_K hP hB h0 h1] at h
  rw [sigmaFun, gs_G₁, h, dot_add_left, dot_smul_left, dot_vvec_self]; ring

/-- `σ_{K_G}` has no atoms on `[0, π/2)`. -/
lemma gs_sigmaAt_eq_zero (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t < π / 2) : sigmaAt P.gs_K t = 0 := by
  have hK := gs_isConvexBody_K hP hB
  have h := congrArg (fun p => dot p (vvec t)) (proposition2_1_2 hK t).2
  simp only [gs_vminus_K hP hB h0 h1.le, gs_vplus_K hP hB h0 h1, dot_add_left, dot_smul_left,
    dot_vvec_self] at h
  linarith

/-- On `[π/2, π]`, the distribution function of `σ_{K_G}` is `G₂`. -/
lemma gs_sigmaFun_eq₂ (hP : P.IsSolution) (hB : P.Bounds) {σ : ℝ} (h0 : π / 2 ≤ σ)
    (h1 : σ ≤ π) : sigmaFun P.gs_K σ = P.gs_G₂ σ := by
  have h := gs_vplus_K' hP hB (t := σ - π / 2) (by linarith) (by linarith)
  rw [sub_add_cancel] at h
  rw [sigmaFun, gs_G₂, h]

lemma gs_sigma_singleton (t : ℝ) :
    sigma P.gs_K {t} = ENNReal.ofReal (sigmaAt P.gs_K t) := by
  rw [sigmaAt, ENNReal.ofReal_toReal (isCompact_singleton.measure_lt_top).ne]

/-- `σ_{K_G}(Ico a b) = ∫_a^b ρ_A` for `0 ≤ a ≤ b ≤ π/2`. -/
lemma gs_sigma_Ico (hP : P.IsSolution) (hB : P.Bounds) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) : sigma P.gs_K (Ico a b) = ENNReal.ofReal (∫ x in a..b, P.gs_rA x) := by
  have hK := gs_isConvexBody_K hP hB
  rcases hab.lt_or_eq with hab | rfl
  swap
  · simp
  have ha' : a < π / 2 := hab.trans_le hb
  have hI := sigma_Ioc hK a b
  rw [gs_sigmaFun_eq₁ hP hB ha ha'.le, gs_sigmaFun_eq₁ hP hB (ha.trans hab.le) hb,
    gs_sigmaAt_eq_zero hP hB ha ha'] at hI
  have hpos : 0 ≤ ∫ x in a..b, P.gs_rA x :=
    intervalIntegral.integral_nonneg hab.le fun x _ => gs_rA_nonneg x
  have hσ : 0 ≤ sigmaAt P.gs_K b := ENNReal.toReal_nonneg
  rw [show P.gs_G₁ b + sigmaAt P.gs_K b - (P.gs_G₁ a + 0) =
      (∫ x in a..b, P.gs_rA x) + sigmaAt P.gs_K b by rw [← gs_G₁_sub hP hB ha hab.le hb]; ring,
    ENNReal.ofReal_add hpos hσ, ← gs_sigma_singleton] at hI
  have hIoc : Ioc a b = Ioo a b ∪ {b} := by
    rw [← Ioo_insert_right hab, insert_eq, union_comm]
  rw [hIoc, measure_union (by simp) (measurableSet_singleton b),
    ENNReal.add_left_inj (isCompact_singleton.measure_lt_top).ne] at hI
  have hIco : Ico a b = {a} ∪ Ioo a b := by rw [← Ioo_insert_left hab, insert_eq]
  rw [hIco, measure_union (by simp) measurableSet_Ioo, hI, gs_sigma_singleton,
    gs_sigmaAt_eq_zero hP hB ha ha', ENNReal.ofReal_zero, zero_add]

/-- `σ_{K_G}(Ioc a b) = ∫_a^b ρ_C(x - π/2) dx` for `π/2 ≤ a ≤ b ≤ π`. -/
lemma gs_sigma_Ioc (hP : P.IsSolution) (hB : P.Bounds) {a b : ℝ} (ha : π / 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π) :
    sigma P.gs_K (Ioc a b) = ENNReal.ofReal (∫ x in a..b, P.gs_rC (x - π / 2)) := by
  rw [sigma_Ioc (gs_isConvexBody_K hP hB), gs_sigmaFun_eq₂ hP hB (ha.trans hab) hb,
    gs_sigmaFun_eq₂ hP hB ha (hab.trans hb), gs_G₂_sub hP hB ha hab hb]

/-- The lower integral of `ofReal ∘ f` over a set a.e. equal to `(a, b]` is `ofReal (∫_a^b f)`. -/
lemma gs_lintegral_eq {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable f volume a b) (s : Set ℝ) (hs : s =ᵐ[volume] Ioc a b) :
    ∫⁻ x in s, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set hs,
    ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hi)
      (Eventually.of_forall hf)]

/-- **InjCond1** for `K_G`. -/
lemma gs_InjCond1 (hP : P.IsSolution) (hB : P.Bounds) : InjCond1 P.gs_K := by
  have hπ : (0 : ℝ) < π / 2 := by linarith [pi_pos]
  refine ⟨P.gs_rA, P.gs_rC, gs_measurable_rA, gs_measurable_rC, gs_rA_nonneg, gs_rC_nonneg, ?_, ?_⟩
  · refine Measure.ext_of_Ico _ _ fun a b _ => ?_
    rw [Measure.restrict_apply measurableSet_Ico, withDensity_apply _ measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico, Ico_inter_Ico]
    rcases le_or_gt (min b (π / 2)) (max a 0) with h | h
    · rw [Ico_eq_empty (not_lt.2 h)]; simp
    · rw [gs_sigma_Ico hP hB (le_max_right _ _) h.le (min_le_right _ _)]
      exact (gs_lintegral_eq gs_rA_nonneg h.le (gs_intervalIntegrable_rA _ _) _
        Ico_ae_eq_Ioc).symm
  · refine Measure.ext_of_Ioc _ _ fun a b _ => ?_
    rw [Measure.restrict_apply measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
    rcases le_or_gt (min b π) (max a (π / 2)) with h | h
    · rw [Ioc_eq_empty (not_lt.2 h)]; simp
    · rw [gs_sigma_Ioc hP hB (le_max_right _ _) h.le (min_le_right _ _)]
      exact (gs_lintegral_eq (fun x => gs_rC_nonneg _) h.le (gs_intervalIntegrable_rC' _ _) _
        ae_eq_rfl).symm

end GerverParams

end MovingSofaOptimality
