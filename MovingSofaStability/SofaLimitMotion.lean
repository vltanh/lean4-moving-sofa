module

public import MovingSofaStability.SofaBounds

/-!
# Closed supporting constraints give a genuine motion of the limit

Uncompiled proof source. The original movement paths are not assumed to have
a convergent subsequence. The limit motion is constructed directly from the
limit set's support function and its terminal width. Compact support continuity
is used directly; the actual sofa is not required to be convex.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem compact_innerCorner_continuous {S : Set Point} (hS : IsCompact S) :
    Continuous (innerCorner S) := by
  have hs := continuous_supp hS
  have he : innerCorner S = fun t => (supp S t - 1) • uvec t +
      (supp S (t + π / 2) - 1) • vvec t := by
    funext t
    exact proposition2_2_2_innerCorner S t
  rw [he]
  exact ((hs.sub continuous_const).smul continuous_uvec).add
    (((hs.comp (continuous_id.add continuous_const)).sub continuous_const).smul continuous_vvec)

/-- Canonical placement coordinates equal the two inner-wall slacks. -/
theorem canonical_placement_coordinates (S : Set Point) (t : ℝ) (p : Point) :
    (rot (-t) (p - innerCorner S t)).1 = innerSlackU S t p ∧
    (rot (-t) (p - innerCorner S t)).2 = innerSlackV S t p := by
  rw [ms_rot_neg_fst, ms_rot_neg_snd, dot_sub_left, dot_sub_left,
    (cn_innerCorner_dot S t).1, opt_innerCorner_dot_v]
  constructor <;> unfold innerSlackU innerSlackV <;> ring

/-- Closed canonical-hallway inequalities and terminal width define a movement. -/
theorem moving_of_supporting_constraints {S : Set Point} {ω : ℝ}
    (hS : IsCompact S) (hc : IsConnected S) (hω : 0 ≤ ω)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    (hwidth : supp S ω + supp S (ω + π) ≤ 1)
    (hslack : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    IsMovingSofaWithAngle S ω := by
  let θ : ℝ → ℝ := fun s => -(s * ω)
  let c : ℝ → Point := fun s => -rot (-(s * ω)) (innerCorner S (s * ω))
  have hcorner := compact_innerCorner_continuous hS
  have hplace (s : ℝ) (p : Point) :
      rot (θ s) p + c s = rot (-(s * ω)) (p - innerCorner S (s * ω)) := by
    simp only [θ, c, rot_sub_vec, sub_eq_add_neg]
  refine ⟨hS.isClosed, hc, θ, c, ?_⟩
  refine ⟨by fun_prop, ?_, by simp [θ], by simp [θ], ?_, ?_, ?_⟩
  · have hpath : Continuous (fun s => innerCorner S (s * ω)) := hcorner.comp (by fun_prop)
    unfold c rot
    fun_prop
  · intro p hp
    rw [hplace]
    simp only [zero_mul, neg_zero, rot_zero]
    change (p - innerCorner S 0).1 ≤ 1 ∧ 0 ≤ (p - innerCorner S 0).2 ∧
      (p - innerCorner S 0).2 ≤ 1
    have he := canonical_placement_coordinates S 0 p
    simp only [neg_zero, rot_zero] at he
    rw [he.1, he.2]
    have hU := dot_le_supp hS hp 0
    have hV : innerSlackV S 0 p = p.2 := by
      simp only [innerSlackV, vvec_zero, dot, zero_add, htop]
      ring
    rw [hV]
    exact ⟨by unfold innerSlackU; linarith, (hstrip hp).1, (hstrip hp).2⟩
  · intro s hs p hp
    let t := s * ω
    have ht : t ∈ Icc (0 : ℝ) ω :=
      ⟨mul_nonneg hs.1 hω, by dsimp [t]; nlinarith [hs.2]⟩
    have hu : innerSlackU S t p ≤ 1 := by
      have he := dot_le_supp hS hp t
      unfold innerSlackU
      linarith
    have hv : innerSlackV S t p ≤ 1 := by
      have he := dot_le_supp hS hp (t + π / 2)
      rw [uvec_add_pi_div_two] at he
      unfold innerSlackV
      linarith
    have hm := hslack p hp t ht
    rw [hplace, ms_mem_hallway_iff]
    change (rot (-t) (p - innerCorner S t)).1 ≤ 1 ∧
      (rot (-t) (p - innerCorner S t)).2 ≤ 1 ∧
      (0 ≤ (rot (-t) (p - innerCorner S t)).1 ∨ 0 ≤ (rot (-t) (p - innerCorner S t)).2)
    rw [(canonical_placement_coordinates S t p).1, (canonical_placement_coordinates S t p).2]
    exact ⟨hu, hv, le_max_iff.mp hm⟩
  · intro p hp
    have hu := dot_le_supp hS hp ω
    have hl := dot_le_supp hS hp (ω + π)
    rw [dot_uvec_add_pi] at hl
    have hv := dot_le_supp hS hp (ω + π / 2)
    rw [uvec_add_pi_div_two] at hv
    rw [hplace]
    simp only [one_mul]
    change 0 ≤ (rot (-ω) (p - innerCorner S ω)).1 ∧
      (rot (-ω) (p - innerCorner S ω)).1 ≤ 1 ∧ (rot (-ω) (p - innerCorner S ω)).2 ≤ 1
    rw [(canonical_placement_coordinates S ω p).1, (canonical_placement_coordinates S ω p).2]
    simp only [innerSlackU, innerSlackV]
    exact ⟨by linarith, by linarith, by linarith⟩

/-- Both slacks pass to limits of compact sets, points, and hallway angles. -/
theorem compactShape_slack_limits {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {p : ℕ → Point} {q : Point}
    (hp : Tendsto p atTop (𝓝 q)) {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto (fun n => innerSlackU (K n : Set Point) (t n) (p n)) atTop
      (𝓝 (innerSlackU (L : Set Point) a q)) ∧
    Tendsto (fun n => innerSlackV (K n : Set Point) (t n) (p n)) atTop
      (𝓝 (innerSlackV (L : Set Point) a q)) := by
  have hu := continuous_uvec.continuousAt.tendsto.comp ht
  have hv := continuous_vvec.continuousAt.tendsto.comp ht
  have hdu := continuous_dot_pair.continuousAt.tendsto.comp (hp.prodMk_nhds hu)
  have hdv := continuous_dot_pair.continuousAt.tendsto.comp (hp.prodMk_nhds hv)
  have hsu := compactShape_support_tendsto hK ht
  have hsv := compactShape_support_tendsto hK (ht.add_const (π / 2))
  exact ⟨(hdu.sub hsu).add_const 1, (hdv.sub hsv).add_const 1⟩

/-- The class with a reduced angle, fixed supports and an actual movement is
closed under compact-set convergence. -/
theorem normalized_moving_limit {P : GerverParams} {K : ℕ → CompactShape} {L : CompactShape}
    {ωn : ℕ → ℝ} {ω : ℝ} (hK : Tendsto K atTop (𝓝 L)) (hωn : Tendsto ωn atTop (𝓝 ω))
    (hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ωn n))
    (hangles : ∀ n, ωn n ∈ Icc (arccos (5 / 11)) (π / 2))
    (htops : ∀ n, supp (K n : Set Point) (π / 2) = 1)
    (hlefts : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π) :
    IsMovingSofaWithAngle (L : Set Point) ω ∧
      ω ∈ Icc (arccos (5 / 11)) (π / 2) ∧
      supp (L : Set Point) (π / 2) = 1 ∧ supp (L : Set Point) π = supp (gerverSofa P) π := by
  have hω : ω ∈ Icc (arccos (5 / 11)) (π / 2) :=
    isClosed_Icc.mem_of_tendsto hωn (Eventually.of_forall hangles)
  have hωpos : 0 < ω := lt_of_lt_of_le (by positivity : (0 : ℝ) < π / 4)
    (quarter_le_reduced_angle.trans hω.1)
  have htop : supp (L : Set Point) (π / 2) = 1 :=
    tendsto_nhds_unique (compactShape_support_tendsto hK tendsto_const_nhds)
      (by simpa only [htops] using tendsto_const_nhds)
  have hleft : supp (L : Set Point) π = supp (gerverSofa P) π :=
    tendsto_nhds_unique (compactShape_support_tendsto hK tendsto_const_nhds)
      (by simpa only [hlefts] using tendsto_const_nhds)
  have hconn := compactShape_connected_limit hK (fun n => (hmove n).2.1)
  have hstrip : (L : Set Point) ⊆ hStrip := compactShape_subset_limit hK
    ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const))
    (fun n => moving_strip_of_top ⟨ωn n, hmove n⟩ (htops n))
  have hwidth : supp (L : Set Point) ω + supp (L : Set Point) (ω + π) ≤ 1 :=
    le_of_tendsto ((compactShape_support_tendsto hK hωn).add
      (compactShape_support_tendsto hK (hωn.add_const π)))
      (Eventually.of_forall fun n => moving_terminal_width (hmove n))
  have hslack : ∀ p ∈ (L : Set Point), ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU (L : Set Point) t p) (innerSlackV (L : Set Point) t p) := by
    intro p hp t ht
    obtain ⟨pn, hpn, hpt⟩ := compactShape_approximate_point hK hp
    let s := t / ω
    have hs : s ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hωpos.le, (div_le_one hωpos).2 ht.2⟩
    have he : s * ω = t := div_mul_cancel₀ _ hωpos.ne'
    have htn : Tendsto (fun n => s * ωn n) atTop (𝓝 t) := by
      simpa only [he] using tendsto_const_nhds.mul hωn
    obtain ⟨hU, hV⟩ := compactShape_slack_limits hK hpt htn
    apply ge_of_tendsto (hU.max hV)
    exact Eventually.of_forall fun n => moving_hallway_slacks (hmove n) (hpn n)
      ⟨mul_nonneg hs.1 (arccos_nonneg _ |>.trans (hangles n).1),
        by nlinarith [hs.2, (hangles n).1, arccos_nonneg (5 / 11 : ℝ)]⟩
  exact ⟨moving_of_supporting_constraints L.isCompact hconn hωpos.le hstrip htop hwidth hslack,
    hω, htop, hleft⟩

end MovingSofaStability
