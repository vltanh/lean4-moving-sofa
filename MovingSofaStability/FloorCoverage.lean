module

public import MovingSofaStability.LocalUpperBound

/-!
# The interior niche floor is already removed before the terminal angle

A directed compact-cover argument supplies a uniform strict slack and an angle
bounded away from pi/2. The fixed floor interval is chosen first; no unsupported
rate of compactness is used.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Gerver's roof has positive height at every abscissa strictly between its endpoints. -/
theorem gerver_floor_mem_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : ℝ} (hx : x ∈ Ioo (gerverRoofLeft P) (gerverRoofRight P)) :
    (x, 0) ∈ niche P.cap (π / 2) := by
  have h := gn_envHyp hP (romik_bounds hP hbox)
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hBcont : ContinuousOn (envB P.path P.gs_α) (Icc 0 (π / 2)) :=
    h.x_cont.add (h.α_cont.smul continuous_vvec.continuousOn)
  have hDcont : ContinuousOn (envD P.path P.gs_β) (Icc 0 (π / 2)) :=
    h.x_cont.sub (h.β_cont.smul continuous_uvec.continuousOn)
  have hBanti : StrictAntiOn (fun t => (envB P.path P.gs_α t).2)
      (Icc (π / 2 - P.θ) (π / 2)) := by
    apply env_strictAntiOn (env_bp_finite P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ))
      (hBcont.snd.mono (Icc_subset_Icc (by linarith) le_rfl))
      (f' := fun t => (gb_rhoA P t - 1) * cos t)
    · intro t ht hne
      simpa only [Prod.smul_snd, smul_eq_mul, vvec_snd] using
        hasDerivAt_snd (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ hne)
    · intro t ht hne
      exact mul_neg_of_neg_of_pos (sub_neg.mpr (h.ρA_lt t ⟨ht.1.le, ht.2.le⟩))
        (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩)
  have hDmono : StrictMonoOn (fun t => (envD P.path P.gs_β t).2) (Icc 0 P.θ) := by
    apply env_strictMonoOn (env_bp_finite P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ))
      (hDcont.snd.mono (Icc_subset_Icc le_rfl (by linarith)))
      (f' := fun t => (1 - gb_rhoC P t) * sin t)
    · intro t ht hne
      simpa only [Prod.smul_snd, smul_eq_mul, uvec_snd] using
        hasDerivAt_snd (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ hne)
    · intro t ht hne
      exact mul_pos (sub_pos.mpr (h.ρC_lt t ⟨ht.1.le, ht.2.le⟩))
        (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]))
  obtain ⟨q, hq, hqx⟩ := env_exists_curve_fst h ⟨hx.1.le, hx.2.le⟩
  have hqy : 0 < q.2 := by
    rcases hq with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · have htv : t < π / 2 := lt_of_le_of_ne ht.2 (by
        intro he
        subst t
        change gerverRoofRight P = x at hqx
        exact (ne_of_lt hx.2) hqx.symm)
      have he : (envB P.path P.gs_α (π / 2)).2 < (envB P.path P.gs_α t).2 :=
        hBanti ht ⟨by linarith, le_rfl⟩ htv
      rwa [h.B_end] at he
    · exact h.x_pos t ht
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
        intro he
        subst t
        change gerverRoofLeft P = x at hqx
        exact (ne_of_lt hx.1) hqx)
      have he : (envD P.path P.gs_β 0).2 < (envD P.path P.gs_β t).2 :=
        hDmono ⟨le_rfl, by linarith⟩ ht ht0
      rwa [h.D_end] at he
  rw [gerver_niche_envelope hP hbox]
  exact ⟨le_rfl, q, hq, hqx, hqy⟩

/-- Compact sets of floor points in the reference niche have uniform strict
witnesses whose angles stay away from both endpoints. -/
theorem compact_floor_witnesses {K₀ : Set Point} {I : Set ℝ} (hI : IsCompact I)
    (hfloor : ∀ x ∈ I, (x, 0) ∈ niche K₀ (π / 2)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ I, ∃ t ∈ Ioo e (π / 2 - e),
      innerSlackU K₀ t (x, 0) < -e ∧ innerSlackV K₀ t (x, 0) < -e := by
  classical
  let J := {e : ℝ // 0 < e}
  let U : J → Set ℝ := fun e => ⋃ t ∈ Ioo e.1 (π / 2 - e.1),
    {x | innerSlackU K₀ t (x, 0) < -e.1 ∧ innerSlackV K₀ t (x, 0) < -e.1}
  have : Nonempty J := ⟨⟨1, by norm_num⟩⟩
  have ho : ∀ e, IsOpen (U e) := by
    intro e
    apply isOpen_iUnion
    intro t
    apply isOpen_iUnion
    intro ht
    exact (isOpen_lt (f := fun x : ℝ => innerSlackU K₀ t (x, 0))
      (by unfold innerSlackU dot; fun_prop) continuous_const).inter
      (isOpen_lt (f := fun x : ℝ => innerSlackV K₀ t (x, 0))
        (by unfold innerSlackV dot; fun_prop) continuous_const)
  have hcover : I ⊆ ⋃ e, U e := by
    intro x hx
    obtain ⟨-, t, ht, hU, hV⟩ := (mem_niche_iff_slacks K₀ (x, 0)).1 (hfloor x hx)
    let e := min t (min (π / 2 - t) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0)))) / 2
    have he : 0 < e := half_pos (lt_min ht.1
      (lt_min (sub_pos.mpr ht.2) (lt_min (neg_pos.mpr hU) (neg_pos.mpr hV))))
    have hr := min_le_right t
      (min (π / 2 - t) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0))))
    have e1 : e < t := by
      have hm := min_le_left t
        (min (π / 2 - t) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0))))
      dsimp [e] at *
      linarith
    have e2 : e < π / 2 - t := by
      have hm := hr.trans (min_le_left _ _)
      dsimp [e] at *
      linarith
    have e3 : e < -innerSlackU K₀ t (x, 0) := by
      have hm := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
      dsimp [e] at *
      linarith
    have e4 : e < -innerSlackV K₀ t (x, 0) := by
      have hm := hr.trans ((min_le_right _ _).trans (min_le_right _ _))
      dsimp [e] at *
      linarith
    exact mem_iUnion.mpr ⟨⟨e, he⟩, mem_iUnion₂.mpr ⟨t, ⟨e1, by linarith⟩, by linarith, by linarith⟩⟩
  have hd : Directed (· ⊆ ·) U := by
    intro e f
    let g : J := ⟨min e.1 f.1, lt_min e.2 f.2⟩
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      obtain ⟨t, ht, hU, hV⟩ := mem_iUnion₂.mp hx
      have hge : g.1 ≤ e.1 := min_le_left _ _
      exact mem_iUnion₂.mpr ⟨t, ⟨hge.trans_lt ht.1, by linarith [ht.2]⟩, by linarith, by linarith⟩
    · intro x hx
      obtain ⟨t, ht, hU, hV⟩ := mem_iUnion₂.mp hx
      have hgf : g.1 ≤ f.1 := min_le_right _ _
      exact mem_iUnion₂.mpr ⟨t, ⟨hgf.trans_lt ht.1, by linarith [ht.2]⟩, by linarith, by linarith⟩
  obtain ⟨e, he⟩ := hI.elim_directed_cover U ho hcover hd
  refine ⟨e.1, e.2, fun x hx => ?_⟩
  obtain ⟨t, ht, hx'⟩ := mem_iUnion₂.mp (he hx)
  exact ⟨t, ht, hx'⟩

/-- A fixed interior floor slab is removed by angles uniformly below pi/2,
even after a sufficiently small perturbation of the cap support. -/
theorem gerver_floor_slab_covered {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {l r : ℝ} (hl : gerverRoofLeft P < l) (hr : r < gerverRoofRight P) :
    ∃ e δ : ℝ, 0 < e ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, UpperSupportClose δ K P.cap →
      ∀ p ∈ Icc l r ×ˢ Icc (0 : ℝ) δ,
        ∃ t ∈ Ioo (0 : ℝ) (π / 2 - e),
          innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  obtain ⟨e, he, hw⟩ := compact_floor_witnesses isCompact_Icc
    (fun x hx => gerver_floor_mem_niche hP hbox ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩)
  let δ := min 1 (e / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδe : δ ≤ e / 4 := min_le_right _ _
  refine ⟨e, δ, he, hδ, min_le_left _ _, ?_⟩
  intro K hclose p hp
  obtain ⟨t, ht, hU, hV⟩ := hw p.1 hp.1
  have htv : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨he.trans ht.1, by linarith [ht.2]⟩
  have hs1 := (abs_le.mp (hclose t ⟨htv.1.le, by linarith [htv.2, pi_pos]⟩)).1
  have hs2 := (abs_le.mp (hclose (t + π / 2) ⟨by linarith [htv.1, pi_pos], by linarith [htv.2]⟩)).1
  have hu : p.2 * sin t ≤ δ := (mul_le_mul_of_nonneg_left (sin_le_one t) hp.2.1).trans
    (by simpa only [mul_one] using hp.2.2)
  have hv : p.2 * cos t ≤ δ := (mul_le_mul_of_nonneg_left (cos_le_one t) hp.2.1).trans
    (by simpa only [mul_one] using hp.2.2)
  refine ⟨t, ⟨htv.1, ht.2⟩, ?_, ?_⟩
  · simp only [innerSlackU, dot, uvec] at hU ⊢
    nlinarith
  · simp only [innerSlackV, dot, vvec] at hV ⊢
    nlinarith

end MovingSofaStability
