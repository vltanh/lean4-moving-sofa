module

public import MovingSofaOptimality.Gerver.Properties

/-!
# Proposition 6: Gerver's sofa is the closure of its interior

Gerver's sofa is its cap minus the region below the envelope of the inner corner. The rotation path
stays strictly below the top of the cap (`path_snd_lt_one`), so every point of the sofa is a limit
of interior points (`gerver_regularClosed`). The same description shows that the width of Gerver's
sofa exceeds one in every direction other than the vertical (`gerver_width_gt_one`).
-/

@[expose] public section
noncomputable section

/-!
## Gerver's rotation path stays below height one

On the five phases of Gerver's motion, the height estimates of the optimality library
(`gs_ineq_y₁`, `gs_ineq_y₂`, `gs_ineq_y₃`) and the bounds on the translations of the phases bound
the height of the rotation path by `0.95`, `0.99240672`, `0.88962658`, `0.99240672` and
`0.9500001`. So the path has height less than one on `[0, π/2]` (`path_snd_lt_one`), a strict form
of `gs_path_snd_le_one`.
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
`B(π/2)` and height in `[0, 1)` (`envelope_bounds_of_path_height`). A point strictly under the
envelope has abscissa strictly between those of `D(0)` and `B(π/2)`, which have height zero
(`envUnderStrict_fst_mem_Ioo`).
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

/-- The envelope is compact: it is the union of three continuous images of closed intervals. -/
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

/-- A point strictly under the envelope has abscissa strictly between those of `D(0)` and
`B(π/2)`: it lies below a point of the envelope of positive height, and the points of the envelope
with these abscissas are `D(0)` and `B(π/2)`, of height zero. -/
theorem envUnderStrict_fst_mem_Ioo (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC) {q : ℝ × ℝ}
    (hq : q ∈ envUnderStrict (envCurve t₁ t₂ t₃ t₄ x α β)) :
    q.1 ∈ Ioo (envD x β 0).1 (envB x α (π / 2)).1 := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  obtain ⟨ha, hm, hb⟩ := envelope_endpoint_order h
  obtain ⟨hq0, γ, hγ, hγx, hqγ⟩ := hq
  have hγpos : 0 < γ.2 := hq0.trans_lt hqγ
  rw [← hγx]
  rcases hγ with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · -- `γ = B(t)` with `t ∈ [t₃, π/2)`, as `B(π/2)` has height zero.
    have hBstart : t₃ ∈ Icc t₃ (π / 2) := ⟨le_rfl, by linarith⟩
    have hBend : π / 2 ∈ Icc t₃ (π / 2) := ⟨by linarith, le_rfl⟩
    have htlt : t < π / 2 := by
      refine lt_of_le_of_ne ht.2 fun he => ?_
      rw [he, h.B_end] at hγpos
      exact lt_irrefl _ hγpos
    have hlo := (env_B₁_strictMono h).monotoneOn hBstart ht ht.1
    have hhi := env_B₁_strictMono h ht hBend htlt
    simp only at hlo hhi
    rw [h.B_t₃] at hlo
    exact ⟨(ha.trans hm).trans_le hlo, hhi⟩
  · -- `γ = x(t)` with `t ∈ [t₁, t₄]`.
    have hxstart : t₁ ∈ Icc t₁ t₄ := ⟨le_rfl, by linarith⟩
    have hxend : t₄ ∈ Icc t₁ t₄ := ⟨by linarith, le_rfl⟩
    have hlo := (env_x₁_strictAnti h).antitoneOn ht hxend ht.2
    have hhi := (env_x₁_strictAnti h).antitoneOn hxstart ht ht.1
    exact ⟨ha.trans_le hlo, hhi.trans_lt hb⟩
  · -- `γ = D(t)` with `t ∈ (0, t₂]`, as `D(0)` has height zero.
    have hDstart : (0 : ℝ) ∈ Icc 0 t₂ := ⟨le_rfl, by linarith⟩
    have hDend : t₂ ∈ Icc 0 t₂ := ⟨by linarith, le_rfl⟩
    have htpos : 0 < t := by
      refine lt_of_le_of_ne ht.1 fun he => ?_
      rw [← he, h.D_end] at hγpos
      exact lt_irrefl _ hγpos
    have hlo := env_D₁_strictMono h hDstart ht htpos
    have hhi := (env_D₁_strictMono h).monotoneOn ht hDend ht.2
    simp only at hlo hhi
    rw [h.D_t₂] at hhi
    exact ⟨hlo, hhi.trans_lt (hm.trans hb)⟩

end MovingSofaUniqueness

end

/-!
## Removing the region under an envelope

Let `K` be a regular closed set that contains the rectangle `[a, b] × [0, 1]`, and let `Γ` be a
compact set of points with abscissa in `[a, b]` and height in `[0, 1)`. If `K` minus the region
strictly under `Γ` is closed, it is regular closed (`regularClosed_cap_sdiff_envelope`). Its points
outside the closed region under `Γ`, which is compact (`isCompact_envUnder`), are limits of its
interior points because `K` is regular closed; its other points lie on `Γ`, below height one, and
are limits of the points of the rectangle just above them.
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
  have h : closure (Ioo (0 : ℝ) 1) ⊆ q ⁻¹' A := (hA.preimage hq).closure_subset_iff.mpr hmem
  exact h (by rw [closure_Ioo zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩)

/-- If `K` is regular closed and `N ⊆ U` with `U` closed, every point of `K \ U` is a limit of
interior points of `K \ N`. -/
theorem outside_closed_envelope_subset {X : Type*} [TopologicalSpace X]
    {K U N : Set X} (hK : closure (interior K) = K) (hU : IsClosed U)
    (hNU : N ⊆ U) : K \ U ⊆ closure (interior (K \ N)) := by
  intro p hp
  have hcl : p ∈ closure (Uᶜ ∩ interior K) :=
    hU.isOpen_compl.inter_closure ⟨hp.2, by rw [hK]; exact hp.1⟩
  refine closure_mono (interior_maximal ?_ (hU.isOpen_compl.inter isOpen_interior)) hcl
  exact fun q hq => ⟨interior_subset hq.2, fun hqN => hq.1 (hNU hqN)⟩

/-- Removing the region strictly under a compact set `Γ` from a regular closed set `K` leaves a
regular closed set, if the difference is closed, `K` contains `[a, b] × [0, 1]`, and the points of
`Γ` have abscissa in `[a, b]` and height in `[0, 1)`. -/
theorem regularClosed_cap_sdiff_envelope {K Γ : Set (ℝ × ℝ)} {a b : ℝ}
    (hK : closure (interior K) = K)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1, (x, y) ∈ K)
    (hΓ : IsCompact Γ)
    (hΓbounds : ∀ p ∈ Γ, p.1 ∈ Icc a b ∧ p.2 ∈ Ico (0 : ℝ) 1)
    (hclosed : IsClosed (K \ envUnderStrict Γ)) :
    closure (interior (K \ envUnderStrict Γ)) = K \ envUnderStrict Γ := by
  set C := closure (interior (K \ envUnderStrict Γ))
  -- The points outside the closed region under `Γ` are limits of interior points.
  have hout : K \ envUnder Γ ⊆ C := by
    refine outside_closed_envelope_subset hK
      (isCompact_envUnder hΓ fun p hp => (hΓbounds p hp).2.1).isClosed ?_
    rintro p ⟨hp0, γ, hγ, hγx, hpγ⟩
    exact ⟨hp0, γ, hγ, hγx, hpγ.le⟩
  refine Set.Subset.antisymm (closure_minimal interior_subset hclosed) fun p hp => ?_
  by_cases hpU : p ∈ envUnder Γ
  swap
  · exact hout ⟨hp.1, hpU⟩
  -- A point `p` on or below a point `γ` of `Γ` has height `p.2 ≤ γ.2 < 1`. The points just above
  -- `p` lie in the rectangle, outside the region under `Γ`, and tend to `p`.
  obtain ⟨hp0, γ, hγ, hγx, hpγ⟩ := hpU
  have hpI : p.1 ∈ Icc a b := by rw [← hγx]; exact (hΓbounds γ hγ).1
  have hp1 : p.2 < 1 := hpγ.trans_lt (hΓbounds γ hγ).2.2
  let q : ℝ → ℝ × ℝ := fun t => (p.1, (1 - t) * p.2 + t)
  have hq : Continuous q := by unfold q; fun_prop
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ C := by
    intro t ht
    have hygt : p.2 < (q t).2 := by
      dsimp [q]; nlinarith [mul_pos ht.1 (sub_pos.mpr hp1)]
    have hyle : (q t).2 ≤ 1 := by
      dsimp [q]; nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hp1.le)]
    refine hout ⟨hrect _ hpI _ ⟨hp0.trans hygt.le, hyle⟩, ?_⟩
    rintro ⟨-, δ, hδ, hδx, hqδ⟩
    exact hp.2 ⟨hp0, δ, hδ, hδx, hygt.trans_le hqδ⟩
  simpa [q] using mem_closed_of_positive_path isClosed_closure q hq hmem

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

The points of the niche have abscissa strictly between `a` and `b` (`envUnderStrict_fst_mem_Ioo`).
So the ends `(a, 1)`, `(b, 1)` of the top edge of the cap and the ends `(x₋, 0)`, `(1, 0)` of its
floor lie in Gerver's sofa (`gerver_corner_points`), and with `a < 0` and `b - x₋ > 1` they show that
the width of Gerver's sofa exceeds one in every direction `u_r`, `r ∈ [0, π]`, `r ≠ π/2`
(`gerver_width_gt_one`): `lem:gerver-width` of the manuscript `docs/paper`.
-/

section

open Real Set MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniqueness

/-- The niche of Gerver's cap is the region strictly under the envelope `Γ` of the inner corner. -/
theorem gerver_niche_eq_envUnderStrict {P : GerverParams} (hP : P.IsSolution) (hB : P.Bounds) :
    niche P.gs_K (π / 2) =
      envUnderStrict (envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ) P.path P.gs_α P.gs_β) := by
  calc
    niche P.gs_K (π / 2) = niche (capOf (gerverSofa P) (π / 2)) (π / 2) := by
      rw [(gs_monotone_K hP hB).2]
    _ = envNiche P.path := gn_niche_eq hP hB
    _ = _ := env_niche_eq (gn_envHyp hP hB)

/-- The left end of the top edge of Gerver's cap is `𝐂(0) = 𝐃(0) + v_0 = (a, 1)`, with
`a = 𝐃(0)_x`. -/
theorem gerver_contactC_zero {P : GerverParams} (hP : P.IsSolution) (hB : P.Bounds) :
    contactC P.path 0 = ((envD P.path P.gs_β 0).1, 1) := by
  change envD P.path P.gs_β 0 + vvec 0 = _
  apply Prod.ext
  · simp [vvec]
  · simp [vvec, (gn_envHyp hP hB).D_end]

/-- The right end of the top edge of Gerver's cap is `𝐀(π/2) = 𝐁(π/2) + u_{π/2} = (b, 1)`, with
`b = 𝐁(π/2)_x`. -/
theorem gerver_contactA_pi_div_two {P : GerverParams} (hP : P.IsSolution) (hB : P.Bounds) :
    contactA P.path (π / 2) = ((envB P.path P.gs_α (π / 2)).1, 1) := by
  change envB P.path P.gs_α (π / 2) + uvec (π / 2) = _
  apply Prod.ext
  · simp [uvec]
  · simp [uvec, (gn_envHyp hP hB).B_end]

/-- Proposition 6 of note 20: Gerver's sofa is the closure of its interior. -/
theorem gerver_regularClosed {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    closure (interior (gerverSofa P)) = gerverSofa P := by
  have hB := GerverParams.romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  -- Step 1: the envelope `Γ` is compact, with abscissas in `[a, b]` and heights in `[0, 1)`.
  let Γ := envCurve P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ) P.path P.gs_α P.gs_β
  let a := (envD P.path P.gs_β 0).1
  let b := (envB P.path P.gs_α (π / 2)).1
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hΓc : IsCompact Γ := envelope_isCompact henv
  have hΓbounds : ∀ p ∈ Γ, p.1 ∈ Icc a b ∧ p.2 ∈ Ico (0 : ℝ) 1 :=
    envelope_bounds_of_path_height henv hheight
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hab : a < b := ho1.trans (ho2.trans ho3)
  -- Step 2: `(a, 1)` and `(b, 1)` are contact points of the cap, so the cap contains the segment
  -- between them and the rectangle `[a, b] × [0, 1]` below it.
  have hcap : IsCap P.gs_K (π / 2) := gs_isCap_K hP hB
  have hconv : Convex ℝ P.gs_K := gs_convex_K
  have hleft : (a, 1) ∈ P.gs_K := by
    have hmem := gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
    rwa [gerver_contactC_zero hP hB] at hmem
  have hright : (b, 1) ∈ P.gs_K := by
    have hmem := gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
    rwa [gerver_contactA_pi_div_two hP hB] at hmem
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
  -- Step 3: the convex cap has nonempty interior, so it is regular closed.
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
  -- Step 4: Gerver's sofa is the closed set obtained by removing the region under `Γ` from the cap.
  have hG : gerverSofa P = P.gs_K \ envUnderStrict Γ := by
    rw [gs_gerverSofa_eq hP hB, gerver_niche_eq_envUnderStrict hP hB]
  have hclosed : IsClosed (P.gs_K \ envUnderStrict Γ) := by
    rw [← hG]
    exact (gm_movingSofa_std hP hbox).1.1
  simpa only [← hG] using regularClosed_cap_sdiff_envelope hKreg hrect hΓc hΓbounds hclosed

/-- The ends `(a, 1)` and `(b, 1)` of the top edge of Gerver's cap and the ends `(x₋, 0)` and
`(1, 0)` of its floor lie in Gerver's sofa, with `a < 0` and `b - x₋ > 1`. Here `a = 𝐃(0)_x`,
`b = 𝐁(π/2)_x` and `x₋ = 𝐱(π/2)_x - 1` (`xm` in the statement); the four points are `𝐂(0)`,
`𝐀(π/2)`, `𝐂(π/2)` and `𝐀(0)`. The points of the niche have abscissa in `(a, b)`, and
`x₋ ≤ a < b ≤ 1`, so the four points lie outside the niche. -/
theorem gerver_corner_points {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ a b xm : ℝ, (a, 1) ∈ gerverSofa P ∧ (b, 1) ∈ gerverSofa P ∧ (xm, 0) ∈ gerverSofa P ∧
      ((1 : ℝ), (0 : ℝ)) ∈ gerverSofa P ∧ a < 0 ∧ 1 < b - xm := by
  have hB := GerverParams.romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  obtain ⟨h1, h12, h23, h34, h4⟩ := henv.ht
  set a := (envD P.path P.gs_β 0).1
  set b := (envB P.path P.gs_α (π / 2)).1
  set xm := (P.path (π / 2)).1 - 1 with hxm
  -- Step 1: the four points are contact points of the cap.
  have hC0 := gs_C_mem_K hP hB (τ := 0) le_rfl (by positivity)
  have hA1 := gs_A_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
  have hC1 := gs_C_mem_K hP hB (τ := π / 2) (by positivity) le_rfl
  have hA0 := gs_A_mem_K hP hB (τ := 0) le_rfl (by positivity)
  rw [gerver_contactC_zero hP hB] at hC0
  rw [gerver_contactA_pi_div_two hP hB] at hA1
  rw [gs_C_pi_div_two hP] at hC1
  rw [gs_A_zero hP] at hA0
  -- Step 2: the points of the niche have abscissa in `(a, b)`, so a point of the cap with another
  -- abscissa lies in the sofa; and `xm ≤ a < b ≤ 1`, as `(a, 1)` and `(b, 1)` lie in the cap.
  have hsofa : ∀ p ∈ P.gs_K, p.1 ∉ Ioo a b → p ∈ gerverSofa P := by
    intro p hp hpx
    rw [gs_gerverSofa_eq hP hB, gerver_niche_eq_envUnderStrict hP hB]
    exact ⟨hp, fun hn => hpx (envUnderStrict_fst_mem_Ioo henv hn)⟩
  have hxa : xm ≤ a := (gs_K_bounds hP hC0).1
  have hb1 : b ≤ 1 := (gs_K_bounds hP hA1).2.1
  -- Step 3: `a < 𝐱(t₄)_x < 𝐱(t₁)_x ≤ 𝐱(0)_x = 0`, and `b > 𝐱(t₁)_x > 𝐱(t₄)_x ≥ 𝐱(π/2)_x = xm + 1`.
  obtain ⟨ho1, ho2, ho3⟩ := envelope_endpoint_order henv
  have hx₁ := (gs_path_fst_le hP hB h1.le (by linarith)).2
  have hx₄ := (gs_path_fst_le hP hB (by linarith) h4.le).1
  refine ⟨a, b, xm, hsofa _ hC0 fun h => lt_irrefl _ h.1, hsofa _ hA1 fun h => lt_irrefl _ h.2,
    hsofa _ hC1 fun h => ?_, hsofa _ hA0 fun h => ?_, by linarith, by linarith⟩
  · exact absurd h.1 (not_lt.mpr hxa)
  · exact absurd h.2 (not_lt.mpr hb1)

/-- The width of Gerver's sofa in every direction `u_r`, `r ∈ [0, π]`, `r ≠ π/2`, exceeds one: for
`r < π/2` the points `(b, 1)` and `(x₋, 0)` of `gerver_corner_points` have
`((b, 1) - (x₋, 0)) · u_r = (b - x₋) cos r + sin r > cos r + sin r ≥ 1`, and for `r > π/2` the
points `(a, 1)` and `(1, 0)` have `((a, 1) - (1, 0)) · u_r = (1 - a) |cos r| + sin r > 1`. -/
theorem gerver_width_gt_one {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) {r : ℝ}
    (hr : r ∈ Icc 0 π) (hr2 : r ≠ π / 2) :
    ∃ p ∈ gerverSofa P, ∃ q ∈ gerverSofa P, 1 < dot (p - q) (uvec r) := by
  obtain ⟨a, b, xm, ha1, hb1, hx0, h10, ha, hbx⟩ := gerver_corner_points hP hbox
  have hs : 0 ≤ sin r := sin_nonneg_of_nonneg_of_le_pi hr.1 hr.2
  have hs1 : sin r * sin r ≤ sin r := mul_le_of_le_one_left hs (sin_le_one r)
  have hsc := sin_sq_add_cos_sq r
  rcases lt_or_gt_of_ne hr2 with hlt | hgt
  · -- `r < π/2`: the points `(b, 1)` and `(xm, 0)`.
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hlt⟩
    have hc1 : cos r * cos r ≤ cos r := mul_le_of_le_one_left hc.le (cos_le_one r)
    refine ⟨(b, 1), hb1, (xm, 0), hx0, ?_⟩
    have hdot : dot ((b, 1) - (xm, 0)) (uvec r) = (b - xm) * cos r + sin r := by
      simp only [dot, uvec, Prod.mk_sub_mk]
      ring
    rw [hdot]
    nlinarith [mul_lt_mul_of_pos_right hbx hc]
  · -- `r > π/2`: the points `(a, 1)` and `(1, 0)`.
    have hc : cos r < 0 := cos_neg_of_pi_div_two_lt_of_lt hgt (by linarith [hr.2, pi_pos])
    have hc1 : cos r * cos r ≤ -cos r := by nlinarith [neg_one_le_cos r]
    refine ⟨(a, 1), ha1, (1, 0), h10, ?_⟩
    have hdot : dot ((a, 1) - (1, 0)) (uvec r) = (1 - a) * -cos r + sin r := by
      simp only [dot, uvec, Prod.mk_sub_mk]
      ring
    rw [hdot]
    nlinarith [mul_lt_mul_of_pos_right (show 1 < 1 - a by linarith) (neg_pos.mpr hc)]

/-- If Gerver's sofa has width at most one in the direction of a unit vector `w`, then `w` is
vertical: `w` or `-w` is `u_r` with `r = arccos (±w.1) ∈ [0, π]`, and `r = π/2` by
`gerver_width_gt_one`. -/
theorem fst_eq_zero_of_gerver_width_le_one {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {w : ℝ × ℝ} (hw : w.1 ^ 2 + w.2 ^ 2 = 1)
    (hwidth : ∀ p ∈ gerverSofa P, ∀ q ∈ gerverSofa P, dot (p - q) w ≤ 1) : w.1 = 0 := by
  -- Step 1: for `w.2 ≥ 0`, `w = u_r` with `r = arccos w.1 ∈ [0, π]`, so `r = π/2`.
  have hupper : ∀ w : ℝ × ℝ, w.1 ^ 2 + w.2 ^ 2 = 1 → 0 ≤ w.2 →
      (∀ p ∈ gerverSofa P, ∀ q ∈ gerverSofa P, dot (p - q) w ≤ 1) → w.1 = 0 := by
    intro w hw hw2 hwidth
    have hlo : -1 ≤ w.1 := by nlinarith [sq_nonneg w.2]
    have hhi : w.1 ≤ 1 := by nlinarith [sq_nonneg w.2]
    have hu : uvec (arccos w.1) = w := by
      apply Prod.ext
      · exact cos_arccos hlo hhi
      · rw [uvec_snd, sin_arccos, show 1 - w.1 ^ 2 = w.2 ^ 2 by linarith, sqrt_sq hw2]
    by_contra hne
    have hr : arccos w.1 ≠ π / 2 := fun h =>
      hne (by rw [← cos_arccos hlo hhi, h, cos_pi_div_two])
    obtain ⟨p, hp, q, hq, hlt⟩ :=
      gerver_width_gt_one hP hbox ⟨arccos_nonneg _, arccos_le_pi _⟩ hr
    rw [hu] at hlt
    linarith [hwidth p hp q hq]
  -- Step 2: for `w.2 < 0`, apply Step 1 to `-w`, as `(p - q) · (-w) = (q - p) · w`.
  rcases le_or_gt 0 w.2 with h2 | h2
  · exact hupper w hw h2 hwidth
  · have h := hupper (-w) (by simpa using hw) (by simp only [Prod.snd_neg]; linarith)
      fun p hp q hq => by
        rw [dot_neg_right, ← dot_neg_left, neg_sub]
        exact hwidth q hq p hp
    simpa using h

end MovingSofaUniqueness

end
