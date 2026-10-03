module

public import MovingSofaOptimality.Gerver.Properties

/-!
# Proposition 6: Gerver's sofa is the closure of its interior

Gerver's sofa is its cap minus the region below the envelope of the inner corner. The rotation path
stays strictly below the top of the cap (`path_snd_lt_one`), so every point of the sofa is a limit
of interior points (`gerver_regularClosed`).
-/

@[expose] public section
noncomputable section

/-!
## Gerver's rotation path stays below height one

On the five phases of Gerver's motion, the height estimates of the optimality library
(`gs_ineq_y₁`, `gs_ineq_y₂`, `gs_ineq_y₃`) and the bounds on the translations of the phases bound
the height of the rotation path by `0.95`, `0.99240672`, `0.88962658`, `0.99240672` and
`0.9500001`. So the path
has height less than one on `[0, π/2]` (`path_snd_lt_one`), a strict form of `gs_path_snd_le_one`.
-/

section

open Real Set

namespace MovingSofaOptimality.GerverParams

variable {P : GerverParams}

/-- Gerver's rotation path has height less than one on `[0, π/2]`, a strict form of
`gs_path_snd_le_one`. -/
theorem path_snd_lt_one (hP : P.IsSolution) (hB : P.Bounds) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ π / 2) : (P.path t).2 < 1 := by
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

end MovingSofaOptimality.GerverParams

end

/-!
## The envelope of the inner corner

Under the hypotheses `EnvHyp`, the envelope `envCurve` is the union of the curve `D`, the rotation
path `x` and the curve `B`. It is compact (`envelope_isCompact`), and its ends and junctions `D(0)`,
`x(t₄)`, `x(t₁)` and `B(π/2)` have increasing abscissas (`envelope_endpoint_order`). If the path
stays below height one, every point of the envelope has abscissa between those of `D(0)` and
`B(π/2)` and height in `[0, 1)` (`envelope_bounds_of_path_height`).
-/

section

open Real Set MovingSofaOptimality

namespace MovingSofaUniqueness

variable {t₁ t₂ t₃ t₄ sA sC : ℝ}
variable {x : ℝ → ℝ × ℝ} {α β ρA ρC : ℝ → ℝ}

/-- The abscissas of `D(0)`, `x(t₄)`, `x(t₁)` and `B(π/2)` increase strictly. -/
theorem envelope_endpoint_order (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    (envD x β 0).1 < (x t₄).1 ∧ (x t₄).1 < (x t₁).1 ∧
      (x t₁).1 < (envB x α (π / 2)).1 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hd := env_D₁_strictMono h
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : (0 : ℝ) < t₂)
  simp only at hd
  rw [h.D_t₂] at hd
  have hx := env_x₁_strictAnti h
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t₁ < t₄)
  simp only at hx
  have hb := env_B₁_strictMono h
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t₃ < π / 2)
  simp only at hb
  rw [h.B_t₃] at hb
  exact ⟨hd, hx, hb⟩

theorem envelope_isCompact (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) :
    IsCompact (envCurve t₁ t₂ t₃ t₄ x α β) := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  unfold envCurve
  apply IsCompact.union
  · apply IsCompact.union
    · exact isCompact_Icc.image_of_continuousOn
        ((env_B_cont h).mono (Icc_subset_Icc (by linarith) le_rfl))
    · exact isCompact_Icc.image_of_continuousOn
        (h.x_cont.mono (Icc_subset_Icc h1.le h4.le))
  · exact isCompact_Icc.image_of_continuousOn
      ((env_D_cont h).mono (Icc_subset_Icc le_rfl (by linarith)))

/-- If the path has height less than one, every point of the envelope has abscissa between those of
`D(0)` and `B(π/2)` and height in `[0, 1)`. -/
theorem envelope_bounds_of_path_height
    (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)
    (hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (x t).2 < 1) :
    ∀ p ∈ envCurve t₁ t₂ t₃ t₄ x α β,
      p.1 ∈ Icc (envD x β 0).1 (envB x α (π / 2)).1 ∧
        p.2 ∈ Ico (0 : ℝ) 1 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨ha, hm, hb⟩ := envelope_endpoint_order h
  have hBstart : t₃ ∈ Icc t₃ (π / 2) := ⟨le_rfl, by linarith⟩
  have hBend : π / 2 ∈ Icc t₃ (π / 2) := ⟨by linarith, le_rfl⟩
  have hxstart : t₁ ∈ Icc t₁ t₄ := ⟨le_rfl, by linarith⟩
  have hxend : t₄ ∈ Icc t₁ t₄ := ⟨by linarith, le_rfl⟩
  have hDstart : (0 : ℝ) ∈ Icc 0 t₂ := ⟨le_rfl, by linarith⟩
  have hDend : t₂ ∈ Icc 0 t₂ := ⟨by linarith, le_rfl⟩
  intro p hp
  rcases hp with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · have hxlo := (env_B₁_strictMono h).monotoneOn hBstart ht ht.1
    have hxhi := (env_B₁_strictMono h).monotoneOn ht hBend ht.2
    have hylo := (env_B₂_strictAnti h).antitoneOn ht hBend ht.2
    have hyhi := (env_B₂_strictAnti h).antitoneOn hBstart ht ht.1
    rw [h.B_t₃] at hxlo hyhi
    rw [h.B_end] at hylo
    have htopy := hheight t₁ ⟨h1.le, by linarith⟩
    exact ⟨⟨(ha.trans hm).le.trans hxlo, hxhi⟩, hylo, hyhi.trans_lt htopy⟩
  · have hxlo := (env_x₁_strictAnti h).antitoneOn ht hxend ht.2
    have hxhi := (env_x₁_strictAnti h).antitoneOn hxstart ht ht.1
    have hyhi := hheight t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨⟨ha.le.trans hxlo, hxhi.trans hb.le⟩, (h.x_pos t ht).le, hyhi⟩
  · have hxlo := (env_D₁_strictMono h).monotoneOn hDstart ht ht.1
    have hxhi := (env_D₁_strictMono h).monotoneOn ht hDend ht.2
    have hylo := (env_D₂_strictMono h).monotoneOn hDstart ht ht.1
    have hyhi := (env_D₂_strictMono h).monotoneOn ht hDend ht.2
    rw [h.D_t₂] at hxhi hyhi
    rw [h.D_end] at hylo
    have htopy := hheight t₄ ⟨by linarith, h4.le⟩
    exact ⟨⟨hxlo, hxhi.trans (hm.trans hb).le⟩, hylo, hyhi.trans_lt htopy⟩

end MovingSofaUniqueness

end

/-!
## Removing the region under an envelope

Let `K` be a regular closed set in the strip `0 ≤ y ≤ 1` that contains the rectangle
`[a, b] × [0, 1]`, and let `Γ` be a compact set of points with abscissa in `[a, b]` and height in
`[0, 1]`, at most one of height one. If `K` minus the region strictly under `Γ` is closed, it is
regular closed (`regularClosed_cap_sdiff_envelope`). Its points outside the closed region under `Γ`,
which is compact (`isCompact_envUnder`), are limits of its interior points because `K` is regular
closed; its other points lie on `Γ` and are limits of points above them or, at height one, of points
of the top edge.
-/

section

open Real Set MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The closed region under a compact nonnegative envelope is compact. -/
theorem isCompact_envUnder {Γ : Set (ℝ × ℝ)} (hΓ : IsCompact Γ)
    (hΓ0 : ∀ p ∈ Γ, 0 ≤ p.2) : IsCompact (envUnder Γ) := by
  let F : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun q => (q.1.1, q.2 * q.1.2)
  have hF : Continuous F := by unfold F; fun_prop
  have he : envUnder Γ = F '' (Γ ×ˢ Icc (0 : ℝ) 1) := by
    ext p
    constructor
    · rintro ⟨hp0, γ, hγ, hγx, hpγ⟩
      by_cases hγ0 : γ.2 = 0
      · have hp2 : p.2 = 0 := by linarith
        refine ⟨(γ, 0), ⟨hγ, le_rfl, zero_le_one⟩, ?_⟩
        ext <;> simp [F, hγx, hp2]
      · have hγpos : 0 < γ.2 := lt_of_le_of_ne (hΓ0 γ hγ) (Ne.symm hγ0)
        refine ⟨(γ, p.2 / γ.2), ⟨hγ, div_nonneg hp0 hγpos.le,
          (div_le_one hγpos).mpr hpγ⟩, ?_⟩
        ext
        · exact hγx
        · exact div_mul_cancel₀ _ hγ0
    · rintro ⟨⟨γ, t⟩, ⟨hγ, ht0, ht1⟩, rfl⟩
      refine ⟨mul_nonneg ht0 (hΓ0 γ hγ), γ, hγ, rfl, ?_⟩
      dsimp [F]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (hΓ0 γ hγ)
  rw [he]
  exact (hΓ.prod isCompact_Icc).image hF

/-- If a continuous path `q` lies in a closed set for `t ∈ (0, 1)`, so does `q 0`. -/
theorem mem_closed_of_positive_path {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (q : ℝ → X) (hq : Continuous q)
    (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ A) : q 0 ∈ A := by
  have hsub : Ioo (0 : ℝ) 1 ⊆ q ⁻¹' A := fun t ht => hmem t ht
  have h := closure_minimal hsub (hA.preimage hq)
  apply h
  rw [closure_Ioo zero_ne_one]
  exact ⟨le_rfl, zero_le_one⟩

/-- If `K` is regular closed and `N ⊆ U` with `U` closed, every point of `K \ U` is a limit of
interior points of `K \ N`. -/
theorem outside_closed_envelope_subset {X : Type*} [TopologicalSpace X]
    {K U N : Set X} (hK : closure (interior K) = K) (hU : IsClosed U)
    (hNU : N ⊆ U) : K \ U ⊆ closure (interior (K \ N)) := by
  intro p hp
  have hnear : p ∈ Uᶜ ∩ closure (interior K) := by
    exact ⟨hp.2, by rw [hK]; exact hp.1⟩
  have hcl : p ∈ closure (Uᶜ ∩ interior K) := hU.isOpen_compl.inter_closure hnear
  have hsub : Uᶜ ∩ interior K ⊆ interior (K \ N) := by
    apply interior_maximal
    · intro q hq
      exact ⟨interior_subset hq.2, fun hqN => hq.1 (hNU hqN)⟩
    · exact hU.isOpen_compl.inter isOpen_interior
  exact closure_mono hsub hcl

/-- Removing the region strictly under a compact set `Γ` from a regular closed set `K` in the strip
`0 ≤ y ≤ 1` leaves a regular closed set, if the difference is closed, `K` contains
`[a, b] × [0, 1]`, and the points of `Γ` have abscissa in `[a, b]` and height in `[0, 1]`, at most
one of them of height one. -/
theorem regularClosed_cap_sdiff_envelope {K Γ : Set (ℝ × ℝ)} {a b : ℝ}
    (hab : a < b) (hK : closure (interior K) = K)
    (hKstrip : ∀ p ∈ K, 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1, (x, y) ∈ K)
    (hΓ : IsCompact Γ)
    (hΓbounds : ∀ p ∈ Γ, p.1 ∈ Icc a b ∧ p.2 ∈ Icc (0 : ℝ) 1)
    (hΓtop : ∀ p ∈ Γ, ∀ q ∈ Γ, p.2 = 1 → q.2 = 1 → p = q)
    (hclosed : IsClosed (K \ envUnderStrict Γ)) :
    closure (interior (K \ envUnderStrict Γ)) = K \ envUnderStrict Γ := by
  let C := closure (interior (K \ envUnderStrict Γ))
  have hCclosed : IsClosed C := isClosed_closure
  have hUclosed : IsClosed (envUnder Γ) :=
    (isCompact_envUnder hΓ (fun p hp => (hΓbounds p hp).2.1)).isClosed
  have hNU : envUnderStrict Γ ⊆ envUnder Γ := by
    rintro p ⟨hp0, γ, hγ, hγx, hpγ⟩
    exact ⟨hp0, γ, hγ, hγx, hpγ.le⟩
  have hout : K \ envUnder Γ ⊆ C :=
    outside_closed_envelope_subset hK hUclosed hNU
  apply Set.Subset.antisymm (closure_minimal interior_subset hclosed)
  intro p hp
  by_cases hpU : p ∈ envUnder Γ
  · obtain ⟨hp0, γ, hγ, hγx, hpγ⟩ := hpU
    have hpI : p.1 ∈ Icc a b := by rw [← hγx]; exact (hΓbounds γ hγ).1
    obtain ⟨hpy0, hpy1⟩ := hKstrip p hp.1
    rcases lt_or_eq_of_le hpy1 with hplt | hpone
    · let q : ℝ → ℝ × ℝ := fun t => (p.1, (1 - t) * p.2 + t)
      have hq : Continuous q := by unfold q; fun_prop
      have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ C := by
        intro t ht
        have hygt : p.2 < (q t).2 := by
          dsimp [q]; nlinarith [mul_pos ht.1 (sub_pos.mpr hplt)]
        have hylo : 0 ≤ (q t).2 := hpy0.trans hygt.le
        have hyhi : (q t).2 ≤ 1 := by
          dsimp [q]; nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hpy1)]
        apply hout
        refine ⟨hrect _ hpI _ ⟨hylo, hyhi⟩, ?_⟩
        rintro ⟨_, δ, hδ, hδx, hqδ⟩
        apply hp.2
        exact ⟨hpy0, δ, hδ, hδx, hygt.trans_le hqδ⟩
      have h := mem_closed_of_positive_path hCclosed q hq hmem
      simpa [q] using h
    · have hγone : γ.2 = 1 := le_antisymm (hΓbounds γ hγ).2.2 (by linarith)
      have hγp : γ = p := by
        apply Prod.ext hγx
        exact hγone.trans hpone.symm
      have hpΓ : p ∈ Γ := hγp ▸ hγ
      obtain ⟨v, hv, hvne⟩ : ∃ v ∈ Icc a b, v ≠ p.1 := by
        by_cases ha : a = p.1
        · exact ⟨b, ⟨hab.le, le_rfl⟩, by rw [← ha]; exact ne_of_gt hab⟩
        · exact ⟨a, ⟨le_rfl, hab.le⟩, ha⟩
      let q : ℝ → ℝ × ℝ := fun t => ((1 - t) * p.1 + t * v, 1)
      have hq : Continuous q := by unfold q; fun_prop
      have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ C := by
        intro t ht
        have h1t : 0 ≤ 1 - t := by linarith [ht.2]
        have hxlo : a ≤ (q t).1 := by
          calc
            a = (1 - t) * a + t * a := by ring
            _ ≤ (1 - t) * p.1 + t * v :=
              add_le_add (mul_le_mul_of_nonneg_left hpI.1 h1t)
                (mul_le_mul_of_nonneg_left hv.1 ht.1.le)
        have hxhi : (q t).1 ≤ b := by
          calc
            (1 - t) * p.1 + t * v ≤ (1 - t) * b + t * b :=
              add_le_add (mul_le_mul_of_nonneg_left hpI.2 h1t)
                (mul_le_mul_of_nonneg_left hv.2 ht.1.le)
            _ = b := by ring
        apply hout
        refine ⟨hrect _ ⟨hxlo, hxhi⟩ 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
        rintro ⟨_, δ, hδ, hδx, hqδ⟩
        have hδone : δ.2 = 1 := le_antisymm (hΓbounds δ hδ).2.2 hqδ
        have hδp := hΓtop δ hδ p hpΓ hδone hpone
        have hx : (1 - t) * p.1 + t * v = p.1 := by
          calc
            _ = δ.1 := hδx.symm
            _ = p.1 := congrArg Prod.fst hδp
        have hprod : t * (v - p.1) = 0 := by nlinarith
        exact hvne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ht.1.ne'))
      have h := mem_closed_of_positive_path hCclosed q hq hmem
      have hq0 : q 0 = p := by
        ext
        · simp [q]
        · simp [q, hpone]
      rw [hq0] at h
      exact h
  · exact hout ⟨hp.1, hpU⟩

end MovingSofaUniqueness

end

/-!
## Gerver's sofa is regular closed

Gerver's sofa is its cap minus the region strictly under the envelope `Γ` of the inner corner. The
points `(a, 1)` and `(b, 1)` above the ends of `Γ` are contact points of the cap, so convexity and
downward closure put the rectangle `[a, b] × [0, 1]` in the cap; in particular the convex cap has
nonempty interior and is regular closed. Since the rotation path stays below height one, every point
of `Γ` has height less than one, and `regularClosed_cap_sdiff_envelope` gives Proposition 6 of
note 20 (`gerver_regularClosed`).
-/

section

open Real Set MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniqueness

/-- Proposition 6 of note 20: Gerver's sofa is the closure of its interior. -/
theorem gerver_regularClosed {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    closure (interior (gerverSofa P)) = gerverSofa P := by
  have hB := GerverParams.romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  let Γ := envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ)
    P.path P.gs_α P.gs_β
  let a := (envD P.path P.gs_β 0).1
  let b := (envB P.path P.gs_α (π / 2)).1
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hΓc : IsCompact Γ := envelope_isCompact henv
  have hΓbounds : ∀ p ∈ Γ, p.1 ∈ Icc a b ∧ p.2 ∈ Ico (0 : ℝ) 1 :=
    envelope_bounds_of_path_height henv hheight
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hab : a < b := ho1.trans (ho2.trans ho3)
  have hcap : IsCap P.gs_K (π / 2) := gs_isCap_K hP hB
  have hconv : Convex ℝ P.gs_K := gs_convex_K
  have hleft : (a, 1) ∈ P.gs_K := by
    have hmem := gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
    have he : contactC P.path 0 = (a, 1) := by
      change envD P.path P.gs_β 0 + vvec 0 = (a, 1)
      apply Prod.ext
      · simp [a, vvec]
      · simp [vvec, henv.D_end]
    rwa [he] at hmem
  have hright : (b, 1) ∈ P.gs_K := by
    have hmem := gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
    have he : contactA P.path (π / 2) = (b, 1) := by
      change envB P.path P.gs_α (π / 2) + uvec (π / 2) = (b, 1)
      apply Prod.ext
      · simp [b, uvec]
      · simp [uvec, henv.B_end]
    rwa [he] at hmem
  have hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1, (x, y) ∈ P.gs_K := by
    intro x hx y hy
    let c := (x - a) / (b - a)
    have hba : 0 < b - a := sub_pos.mpr hab
    have hc : c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hx.1) hba.le,
        (div_le_one hba).mpr (by linarith [hx.2])⟩
    have htop := hconv.add_smul_sub_mem hleft hright hc
    have he : (a, (1 : ℝ)) + c • ((b, 1) - (a, 1)) = (x, 1) := by
      apply Prod.ext
      · dsimp [c]
        field_simp
        ring
      · simp
    rw [he] at htop
    exact opt_cap_down hcap htop hy.1 hy.2
  have hKreg : closure (interior P.gs_K) = P.gs_K := by
    have hsub : Ioo a b ×ˢ Ioo (0 : ℝ) 1 ⊆ P.gs_K := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact hrect x ⟨hx.1.le, hx.2.le⟩ y ⟨hy.1.le, hy.2.le⟩
    have hint := interior_maximal hsub (isOpen_Ioo.prod isOpen_Ioo)
    have hne : (interior P.gs_K).Nonempty := by
      refine ⟨((a + b) / 2, 1 / 2), hint ?_⟩
      constructor <;> constructor <;> dsimp <;> linarith
    calc
      closure (interior P.gs_K) = closure P.gs_K :=
        hconv.closure_interior_eq_closure_of_nonempty_interior hne
      _ = P.gs_K := gs_isClosed_K.closure_eq
  have hn : niche P.gs_K (π / 2) = envUnderStrict Γ := by
    calc
      niche P.gs_K (π / 2) = niche (capOf (gerverSofa P) (π / 2)) (π / 2) := by
        rw [(gs_monotone_K hP hB).2]
      _ = envNiche P.path := gn_niche_eq hP hB
      _ = envUnderStrict Γ := env_niche_eq henv
  have hG : gerverSofa P = P.gs_K \ envUnderStrict Γ := by
    rw [gs_gerverSofa_eq hP hB, hn]
  have hclosed : IsClosed (P.gs_K \ envUnderStrict Γ) := by
    rw [← hG]
    exact (gm_movingSofa_std hP hbox).1.1
  have hfinal := regularClosed_cap_sdiff_envelope hab hKreg
    (fun p hp => (gs_K_bounds hP hp).2.2) hrect hΓc
    (fun p hp => ⟨(hΓbounds p hp).1,
      (hΓbounds p hp).2.1, (hΓbounds p hp).2.2.le⟩)
    (fun p hp q hq hpone hqone => False.elim ((hΓbounds p hp).2.2.ne hpone))
    hclosed
  simpa only [← hG] using hfinal

end MovingSofaUniqueness

end
