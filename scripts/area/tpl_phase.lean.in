
/-! ### The contact curves on one phase -/

variable {P : GerverParams}

lemma ga_continuous_uvec : Continuous uvec := continuous_cos.prodMk continuous_sin
lemma ga_continuous_vvec : Continuous vvec := continuous_sin.neg.prodMk continuous_cos

lemma ga_continuous_ρA₀ : Continuous (P.gs_phase 0).ρA := by
  unfold gs_Phase.ρA; simp only [gs_phase, gs_ph1]; fun_prop
lemma ga_continuous_ρA₁ : Continuous (P.gs_phase 1).ρA := by
  unfold gs_Phase.ρA; simp only [gs_phase, gs_ph2]; fun_prop
lemma ga_continuous_ρA₂ : Continuous (P.gs_phase 2).ρA := by
  unfold gs_Phase.ρA; simp only [gs_phase, gs_ph3]; fun_prop
lemma ga_continuous_ρA₃ : Continuous (P.gs_phase 3).ρA := by
  unfold gs_Phase.ρA; simp only [gs_phase, gs_ph4]; fun_prop
lemma ga_continuous_ρA₄ : Continuous (P.gs_phase 4).ρA := by
  unfold gs_Phase.ρA; simp only [gs_phase, gs_ph5]; fun_prop
lemma ga_continuous_ρC₀ : Continuous (P.gs_phase 0).ρC := by
  unfold gs_Phase.ρC; simp only [gs_phase, gs_ph1]; fun_prop
lemma ga_continuous_ρC₁ : Continuous (P.gs_phase 1).ρC := by
  unfold gs_Phase.ρC; simp only [gs_phase, gs_ph2]; fun_prop
lemma ga_continuous_ρC₂ : Continuous (P.gs_phase 2).ρC := by
  unfold gs_Phase.ρC; simp only [gs_phase, gs_ph3]; fun_prop
lemma ga_continuous_ρC₃ : Continuous (P.gs_phase 3).ρC := by
  unfold gs_Phase.ρC; simp only [gs_phase, gs_ph4]; fun_prop
lemma ga_continuous_ρC₄ : Continuous (P.gs_phase 4).ρC := by
  unfold gs_Phase.ρC; simp only [gs_phase, gs_ph5]; fun_prop

/-- `𝒥(𝐀|[a, b])` on a phase interval, from an antiderivative of `𝐀 × 𝐀'`. -/
lemma ga_phase_A (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hab : a < b)
    (hρ : Continuous (P.gs_phase i).ρA) (hpc : ∀ t ∈ Icc a b, gs_piece P i t) (K : ga_TP)
    (hK : ∀ t, cross ((P.gs_phase i).A t) ((P.gs_phase i).ρA t • vvec t) =
      K.dF t (cos t) (sin t)) :
    curveArea (contactA P.path) a b = 1 / 2 * (K.F b (cos b) (sin b) - K.F a (cos a) (sin a)) := by
  rw [ga_curveArea_eq hab (gs_Phase.hasDerivAt_A (gs_valid i)) (hρ.smul ga_continuous_vvec)
    (fun t ht => gs_contactA_eq hP (hpc t ht)), ← K.integral]
  simp only [hK]

/-- `𝒥(𝐁|[a, b])` on a phase interval, from an antiderivative of `𝐁 × 𝐁'`. -/
lemma ga_phase_B (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hab : a < b)
    (hρ : Continuous (P.gs_phase i).ρA) (hpc : ∀ t ∈ Icc a b, gs_piece P i t) (K : ga_TP)
    (hK : ∀ t, cross ((P.gs_phase i).B t) (((P.gs_phase i).ρA t - 1) • vvec t) =
      K.dF t (cos t) (sin t)) :
    curveArea (contactB P.path) a b = 1 / 2 * (K.F b (cos b) (sin b) - K.F a (cos a) (sin a)) := by
  rw [ga_curveArea_eq hab (gs_Phase.hasDerivAt_B (gs_valid i))
    ((hρ.sub continuous_const).smul ga_continuous_vvec)
    (fun t ht => gs_contactB_eq hP (hpc t ht)), ← K.integral]
  simp only [hK]

/-- `𝒥(𝐂|[a, b])` on a phase interval, from an antiderivative of `𝐂 × 𝐂'`. -/
lemma ga_phase_C (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hab : a < b)
    (hρ : Continuous (P.gs_phase i).ρC) (hpc : ∀ t ∈ Icc a b, gs_piece P i t) (K : ga_TP)
    (hK : ∀ t, cross ((P.gs_phase i).C t) (-(P.gs_phase i).ρC t • uvec t) =
      K.dF t (cos t) (sin t)) :
    curveArea (contactC P.path) a b = 1 / 2 * (K.F b (cos b) (sin b) - K.F a (cos a) (sin a)) := by
  rw [ga_curveArea_eq hab (gs_Phase.hasDerivAt_C (gs_valid i)) (hρ.neg.smul ga_continuous_uvec)
    (fun t ht => gs_contactC_eq hP (hpc t ht)), ← K.integral]
  simp only [hK]

/-- `𝒥(𝐃|[a, b])` on a phase interval, from an antiderivative of `𝐃 × 𝐃'`. -/
lemma ga_phase_D (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hab : a < b)
    (hρ : Continuous (P.gs_phase i).ρC) (hpc : ∀ t ∈ Icc a b, gs_piece P i t) (K : ga_TP)
    (hK : ∀ t, cross ((P.gs_phase i).D t) ((1 - (P.gs_phase i).ρC t) • uvec t) =
      K.dF t (cos t) (sin t)) :
    curveArea (contactD P.path) a b = 1 / 2 * (K.F b (cos b) (sin b) - K.F a (cos a) (sin a)) := by
  rw [ga_curveArea_eq hab (gs_Phase.hasDerivAt_D (gs_valid i))
    ((continuous_const.sub hρ).smul ga_continuous_uvec)
    (fun t ht => gs_contactD_eq hP (hpc t ht)), ← K.integral]
  simp only [hK]

/-- `𝒥(𝐱|[a, b])` on a phase interval, from an antiderivative of `𝐱 × 𝐱'`. -/
lemma ga_phase_X (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hab : a < b)
    (hpc : ∀ t ∈ Icc a b, gs_piece P i t) (K : ga_TP)
    (hK : ∀ t, cross ((P.gs_phase i).X t) ((P.gs_phase i).X' t) = K.dF t (cos t) (sin t)) :
    curveArea P.path a b = 1 / 2 * (K.F b (cos b) (sin b) - K.F a (cos a) (sin a)) := by
  rw [ga_curveArea_eq hab (gs_Phase.hasDerivAt_X (gs_valid i))
    (gs_Phase.continuous_X' (gs_valid i)) (fun t ht => gs_path_eq_phase hP (hpc t ht)),
    ← K.integral]
  simp only [hK]

/-! ### The contact curves are of class `C^BV` -/

lemma ga_isCBV_A_piece (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hρ : Continuous (P.gs_phase i).ρA)
    (hpc : ∀ t ∈ Icc a b, gs_piece P i t) : IsCBV (contactA P.path) a b :=
  ga_isCBV_of_eqOn (gs_Phase.hasDerivAt_A (gs_valid i)) (hρ.smul ga_continuous_vvec)
    (fun t ht => gs_contactA_eq hP (hpc t ht))

lemma ga_isCBV_B_piece (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hρ : Continuous (P.gs_phase i).ρA)
    (hpc : ∀ t ∈ Icc a b, gs_piece P i t) : IsCBV (contactB P.path) a b :=
  ga_isCBV_of_eqOn (gs_Phase.hasDerivAt_B (gs_valid i))
    ((hρ.sub continuous_const).smul ga_continuous_vvec) (fun t ht => gs_contactB_eq hP (hpc t ht))

lemma ga_isCBV_C_piece (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hρ : Continuous (P.gs_phase i).ρC)
    (hpc : ∀ t ∈ Icc a b, gs_piece P i t) : IsCBV (contactC P.path) a b :=
  ga_isCBV_of_eqOn (gs_Phase.hasDerivAt_C (gs_valid i)) (hρ.neg.smul ga_continuous_uvec)
    (fun t ht => gs_contactC_eq hP (hpc t ht))

lemma ga_isCBV_D_piece (hP : P.IsSolution) {i : ℕ} {a b : ℝ} (hρ : Continuous (P.gs_phase i).ρC)
    (hpc : ∀ t ∈ Icc a b, gs_piece P i t) : IsCBV (contactD P.path) a b :=
  ga_isCBV_of_eqOn (gs_Phase.hasDerivAt_D (gs_valid i))
    ((continuous_const.sub hρ).smul ga_continuous_uvec) (fun t ht => gs_contactD_eq hP (hpc t ht))

lemma ga_isCBV_X_piece (hP : P.IsSolution) {i : ℕ} {a b : ℝ}
    (hpc : ∀ t ∈ Icc a b, gs_piece P i t) : IsCBV P.path a b :=
  ga_isCBV_of_eqOn (gs_Phase.hasDerivAt_X (gs_valid i)) (gs_Phase.continuous_X' (gs_valid i))
    (fun t ht => gs_path_eq_phase hP (hpc t ht))

/-- A curve of class `C^BV` on the five phase intervals is of class `C^BV` on `[0, π/2]`. -/
lemma ga_isCBV_five (hP : P.IsSolution) {Z : ℝ → ℝ × ℝ} (h₀ : IsCBV Z 0 P.φ)
    (h₁ : IsCBV Z P.φ P.θ) (h₂ : IsCBV Z P.θ (π / 2 - P.θ))
    (h₃ : IsCBV Z (π / 2 - P.θ) (π / 2 - P.φ)) (h₄ : IsCBV Z (π / 2 - P.φ) (π / 2)) :
    IsCBV Z 0 (π / 2) := by
  have hO := gs_ord hP
  have o1 := hO.φ_pos
  have o2 := hO.φ_lt_θ
  have o3 := hO.θ_lt
  have o4 := hO.lt_φ'
  refine ga_isCBV_append o1.le (by linarith) h₀ ?_
  refine ga_isCBV_append o2.le (by linarith) h₁ ?_
  refine ga_isCBV_append o3.le (by linarith) h₂ ?_
  exact ga_isCBV_append o4.le (by linarith) h₃ h₄

lemma ga_isCBV_A (hP : P.IsSolution) : IsCBV (contactA P.path) 0 (π / 2) :=
  ga_isCBV_five hP (ga_isCBV_A_piece hP ga_continuous_ρA₀ fun _ ht => gs_piece₀ ht.2)
    (ga_isCBV_A_piece hP ga_continuous_ρA₁ fun _ ht => gs_piece₁ ht.1 ht.2)
    (ga_isCBV_A_piece hP ga_continuous_ρA₂ fun _ ht => gs_piece₂ ht.1 ht.2)
    (ga_isCBV_A_piece hP ga_continuous_ρA₃ fun _ ht => gs_piece₃ ht.1 ht.2)
    (ga_isCBV_A_piece hP ga_continuous_ρA₄ fun _ ht => gs_piece₄ ht.1)

lemma ga_isCBV_C (hP : P.IsSolution) : IsCBV (contactC P.path) 0 (π / 2) :=
  ga_isCBV_five hP (ga_isCBV_C_piece hP ga_continuous_ρC₀ fun _ ht => gs_piece₀ ht.2)
    (ga_isCBV_C_piece hP ga_continuous_ρC₁ fun _ ht => gs_piece₁ ht.1 ht.2)
    (ga_isCBV_C_piece hP ga_continuous_ρC₂ fun _ ht => gs_piece₂ ht.1 ht.2)
    (ga_isCBV_C_piece hP ga_continuous_ρC₃ fun _ ht => gs_piece₃ ht.1 ht.2)
    (ga_isCBV_C_piece hP ga_continuous_ρC₄ fun _ ht => gs_piece₄ ht.1)

lemma ga_isCBV_X (hP : P.IsSolution) : IsCBV P.path P.φ (π / 2 - P.φ) := by
  have hO := gs_ord hP
  refine ga_isCBV_append hO.φ_lt_θ.le (by linarith [hO.θ_lt, hO.lt_φ'])
    (ga_isCBV_X_piece hP fun _ ht => gs_piece₁ ht.1 ht.2) ?_
  exact ga_isCBV_append hO.θ_lt.le hO.lt_φ'.le (ga_isCBV_X_piece hP fun _ ht => gs_piece₂ ht.1 ht.2)
    (ga_isCBV_X_piece hP fun _ ht => gs_piece₃ ht.1 ht.2)

lemma ga_isCBV_B (hP : P.IsSolution) : IsCBV (contactB P.path) (π / 2 - P.θ) (π / 2) := by
  have hO := gs_ord hP
  exact ga_isCBV_append hO.lt_φ'.le (by linarith [hO.φ_pos])
    (ga_isCBV_B_piece hP ga_continuous_ρA₃ fun _ ht => gs_piece₃ ht.1 ht.2)
    (ga_isCBV_B_piece hP ga_continuous_ρA₄ fun _ ht => gs_piece₄ ht.1)

lemma ga_isCBV_D (hP : P.IsSolution) : IsCBV (contactD P.path) 0 P.θ := by
  have hO := gs_ord hP
  exact ga_isCBV_append hO.φ_pos.le hO.φ_lt_θ.le
    (ga_isCBV_D_piece hP ga_continuous_ρC₀ fun _ ht => gs_piece₀ ht.2)
    (ga_isCBV_D_piece hP ga_continuous_ρC₁ fun _ ht => gs_piece₁ ht.1 ht.2)

/-! ### The phases on which a contact curve is constant -/

/-- `𝐀` is constant on the first phase (`ρ_A = 0`). -/
lemma ga_A1 (hP : P.IsSolution) : curveArea (contactA P.path) 0 P.φ = 0 := by
  have hO := gs_ord hP
  rw [ga_phase_A hP hO.φ_pos ga_continuous_ρA₀ (fun t ht => gs_piece₀ ht.2) ga_TP.zero fun t => by
    rw [ga_cross_A]; simp only [gs_phase, gs_ph1, gs_Phase.ρA, ga_TP.dF, ga_TP.zero]; ring]
  simp only [ga_TP.zero_F, sub_self, mul_zero]

/-- `𝐂` is constant on the last phase (`ρ_C = 0`). -/
lemma ga_C5 (hP : P.IsSolution) : curveArea (contactC P.path) (π / 2 - P.φ) (π / 2) = 0 := by
  have hO := gs_ord hP
  rw [ga_phase_C hP (by linarith [hO.φ_pos]) ga_continuous_ρC₄ (fun t ht => gs_piece₄ ht.1)
    ga_TP.zero fun t => by
      rw [ga_cross_C]; simp only [gs_phase, gs_ph5, gs_Phase.ρC, ga_TP.dF, ga_TP.zero]; ring]
  simp only [ga_TP.zero_F, sub_self, mul_zero]

/-! ### The segment from `𝐀(π/2)` to `𝐂(0)` -/

lemma ga_contactA_pi_div_two (hP : P.IsSolution) :
    contactA P.path (π / 2) = (P.a₁ + P.κ₅.1, 3 / 4 + P.κ₅.2) := by
  have hO := gs_ord hP
  rw [gs_contactA_eq hP (gs_piece₄ (by linarith [hO.φ_pos] : π / 2 - P.φ ≤ π / 2))]
  simp only [gs_phase, gs_ph5, gs_Phase.A, rot, cos_pi_div_two, sin_pi_div_two, gs_e₁ hP,
    gs_e₂ hP, gs_a₂ hP]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

lemma ga_contactC_zero (hP : P.IsSolution) : contactC P.path 0 = (1 - 2 * P.a₁, 1) := by
  rw [gs_contactC_eq hP (gs_piece₀ (gs_ord hP).φ_pos.le)]
  simp only [gs_phase, gs_ph1, gs_Phase.C, rot, cos_zero, sin_zero, gs_a₂ hP]
  ext
  · simp only [Prod.fst_add, gs_κ₁₁ hP]; ring
  · simp only [Prod.snd_add, gs_κ₁₂ hP]; ring

lemma ga_segArea_eq (hP : P.IsSolution) :
    segArea (contactA P.path (π / 2)) (contactC P.path 0) =
      ((P.a₁ + P.κ₅.1) - ((3 / 4) + P.κ₅.2) * (1 - 2 * P.a₁)) / 2 := by
  rw [ga_contactA_pi_div_two hP, ga_contactC_zero hP, segArea, cross]
  ring

