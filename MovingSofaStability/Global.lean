module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.MeasureTheory.Measure.Regular
public import MovingSofaExtremal.Main
public import MovingSofaStability.Recovery

/-!
# Compactness, uniqueness, and the stability theorems

Normalized sofas of nearly maximal area lie in a fixed rectangle, and their Hausdorff limits are moving
sofas of maximal area, hence Gerver's sofa by the uniqueness theorem of the coercive route; so every sofa of
small deficit enters the neighborhood of the local estimates (`near_maximizers_enter_neighborhood`), which
gives the two stability theorems (`unrestricted_stability`, `terminal_angle_stability`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## The sign of the deficit
-/

section SofaDeficitNonneg

open MovingSofaOptimality

namespace MovingSofaStability

/-- The deficit of a moving sofa is nonnegative: Gerver's sofa has the largest area, by the
optimality theorem of the coercive route (`MovingSofaExtremal.area_le_gerver`). -/
theorem sofaDeficit_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofa S) : 0 ≤ sofaDeficit P S :=
  sub_nonneg.mpr (MovingSofaExtremal.area_le_gerver hP hbox hS)

end MovingSofaStability

end SofaDeficitNonneg

/-!
## Limits of actual compact sets

The hyperspace here contains all nonempty compact sets, not only convex bodies.
Its ordinary product-metric Hausdorff distance is used only for topology;
Euclidean witnesses are recovered with factor two. Area is upper semicontinuous,
not asserted continuous.
-/

section CompactSetLimits

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev CompactShape := NonemptyCompacts Point

/-- A point of one compact set has a nearest point in the other within their
Hausdorff distance, in the product metric used by the hyperspace. -/
theorem compactShape_near_point (K L : CompactShape) {p : Point} (hp : p ∈ K) :
    ∃ q ∈ L, dist p q ≤ dist K L := by
  obtain ⟨q, hq, he⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty p
  have hb := Metric.infDist_le_hausdorffDist_of_mem hp (show
      Metric.hausdorffEDist (K : Set Point) (L : Set Point) ≠ ⊤ from edist_ne_top K L)
  rw [he] at hb
  exact ⟨q, hq, hb⟩

theorem compactShape_euclideanClose (K L : CompactShape) :
    EuclideanClose (2 * dist K L) (K : Set Point) (L : Set Point) := by
  have forward (A B : CompactShape) : DirectedClose (2 * dist A B) (A : Set Point) (B : Set Point) := by
    intro p hp
    obtain ⟨q, hq, hd⟩ := compactShape_near_point A B hp
    refine ⟨q, hq, ?_⟩
    exact (norm2_le_two_product_norm (p - q)).trans
      (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 by norm_num))
  exact ⟨forward K L, by simpa only [dist_comm L K] using forward L K⟩

/-- Uniform support control holds for nonconvex compact sets as well. -/
theorem compactShape_support_error (K L : CompactShape) (t : ℝ) :
    |supp (K : Set Point) t - supp (L : Set Point) t| ≤ 2 * dist K L :=
  (compactShape_euclideanClose K L).abs_supp_sub_le K.isCompact L.isCompact K.nonempty L.nonempty t

/-- Supports converge even when the normal direction changes with the sequence. -/
theorem compactShape_support_tendsto {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto (fun n => supp (K n : Set Point) (t n)) atTop (𝓝 (supp (L : Set Point) a)) := by
  have hfixed := (continuous_supp L.isCompact).continuousAt.tendsto.comp ht
  apply Metric.tendsto_nhds.2
  intro ε hε
  have h1 := Metric.tendsto_nhds.1 hK (ε / 4) (by positivity)
  have h2 := Metric.tendsto_nhds.1 hfixed (ε / 2) (by positivity)
  filter_upwards [h1, h2] with n hn1 hn2
  have he := compactShape_support_error (K n) L (t n)
  have htri := abs_add_le (supp (K n : Set Point) (t n) - supp (L : Set Point) (t n))
    (supp (L : Set Point) (t n) - supp (L : Set Point) a)
  rw [Real.dist_eq, Function.comp_apply] at hn2
  rw [Real.dist_eq]
  have hsum : supp (K n : Set Point) (t n) - supp (L : Set Point) (t n) +
      (supp (L : Set Point) (t n) - supp (L : Set Point) a) =
      supp (K n : Set Point) (t n) - supp (L : Set Point) a := by ring
  rw [hsum] at htri
  linarith

/-- Every point of the limit is the limit of a sequence of points in the approximants. -/
theorem compactShape_approximate_point {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {p : Point} (hp : p ∈ L) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) := by
  choose q hq hd using fun n => compactShape_near_point L (K n) hp
  refine ⟨q, hq, Metric.tendsto_nhds.2 ?_⟩
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 hK ε hε] with n hn
  rw [dist_comm] at hn
  rw [dist_comm]
  exact (hd n).trans_lt hn

/-- Compact connected sets remain connected under Hausdorff limits. -/
theorem compactShape_connected_limit {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) (hc : ∀ n, IsConnected (K n : Set Point)) :
    IsConnected (L : Set Point) := by
  refine ⟨L.nonempty, (isPreconnected_iff_subset_of_fully_disjoint_closed L.isCompact.isClosed).2 ?_⟩
  intro A B hA hB hcover hdisj
  by_contra hnot
  push Not at hnot
  obtain ⟨p, hp, hpA⟩ := Set.not_subset.mp hnot.1
  obtain ⟨q, hq, hqB⟩ := Set.not_subset.mp hnot.2
  have hpB : p ∈ B := (hcover hp).resolve_left hpA
  have hqA : q ∈ A := (hcover hq).resolve_right hqB
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hdisj
  have evcover : ∀ᶠ n in atTop, (K n : Set Point) ⊆ U ∪ V := hK.eventually
    ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).mem_nhds
      (hcover.trans (union_subset_union hAU hBV)))
  have evU : ∀ᶠ n in atTop, ((K n : Set Point) ∩ U).Nonempty := hK.eventually
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).mem_nhds ⟨q, hq, hAU hqA⟩)
  have evV : ∀ᶠ n in atTop, ((K n : Set Point) ∩ V).Nonempty := hK.eventually
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV).mem_nhds ⟨p, hp, hBV hpB⟩)
  obtain ⟨n, hn, hnU, hnV⟩ := (evcover.and (evU.and evV)).exists
  obtain ⟨x, hxK, hxU, hxV⟩ := (hc n).isPreconnected U V hU hV hn hnU hnV
  exact Set.disjoint_left.mp hUV hxU hxV

/-- Inclusion in a fixed closed set passes to the compact-set limit. -/
theorem compactShape_subset_limit {K : ℕ → CompactShape} {L : CompactShape} {B : Set Point}
    (hK : Tendsto K atTop (𝓝 L)) (hB : IsClosed B) (hsub : ∀ n, (K n : Set Point) ⊆ B) :
    (L : Set Point) ⊆ B :=
  (NonemptyCompacts.isClosed_subsets_of_isClosed hB).mem_of_tendsto hK
    (Eventually.of_forall hsub)

/-- Upper semicontinuity of finite planar area along a convergent compact-set sequence. -/
theorem compactShape_area_limsup {K : ℕ → CompactShape} {L : CompactShape} {M : ℝ}
    (hK : Tendsto K atTop (𝓝 L)) (harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 M)) :
    M ≤ area (L : Set Point) := by
  apply le_of_forall_gt
  intro r hr
  have hL0 : 0 ≤ area (L : Set Point) := ENNReal.toReal_nonneg
  have hr0 : 0 < r := lt_of_le_of_lt hL0 hr
  have hvol : volume (L : Set Point) < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal L.isCompact.measure_lt_top.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 hr
  obtain ⟨U, hLU, hU, hvolU⟩ := (L : Set Point).exists_isOpen_lt_of_lt
    (μ := volume) (ENNReal.ofReal r) hvol
  have hUf : volume U ≠ ⊤ := ne_top_of_lt (hvolU.trans_le le_top)
  have huarea : area U < r := by
    have he := ENNReal.toReal_lt_toReal hUf ENNReal.ofReal_ne_top |>.2 hvolU
    simpa only [area, ENNReal.toReal_ofReal hr0.le] using he
  have ev : ∀ᶠ n in atTop, area (K n : Set Point) ≤ area U := by
    filter_upwards [hK.eventually ((NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hLU)] with n hn
    exact area_mono_of_finite hn hUf
  have hm : M ≤ area U := le_of_tendsto harea ev
  exact hm.trans_lt huarea

end MovingSofaStability

end CompactSetLimits

/-!
## A compact containing rectangle for the original sofa sets

Connectedness bounds a supporting inner corner and the pi/4 hallway bounds
horizontal span. No balancedness is assumed.
-/

section SofaBounds

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Coordinate proof of rotation linearity used in the canonical limit motion. -/
theorem rot_sub_vec (t : ℝ) (p q : Point) : rot t (p - q) = rot t p - rot t q := by
  ext <;> simp only [rot, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem connected_corner_height {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hconn : IsConnected S) (hstrip : S ⊆ hStrip) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2))
    (hslack : ∀ p ∈ S, 0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    (innerCorner S t).2 ≤ 1 := by
  obtain ⟨p, hp, hpu⟩ := exists_dot_eq_supp hS hne t
  obtain ⟨q, hq, hqv⟩ := exists_dot_eq_supp hS hne (t + π / 2)
  let f : Point → ℝ := fun z => innerSlackU S t z - innerSlackV S t z
  have hf : ContinuousOn f S :=
    ((((continuous_dot (uvec t)).sub continuous_const).add continuous_const).sub
      (((continuous_dot (vvec t)).sub continuous_const).add continuous_const)).continuousOn
  have hpu' : innerSlackU S t p = 1 := by unfold innerSlackU; rw [hpu]; ring
  have hqv' : innerSlackV S t q = 1 := by unfold innerSlackV; rw [← uvec_add_pi_div_two, hqv]; ring
  have hpv : innerSlackV S t p ≤ 1 := by
    have he := dot_le_supp hS hp (t + π / 2)
    rw [uvec_add_pi_div_two] at he
    unfold innerSlackV
    linarith
  have hqu : innerSlackU S t q ≤ 1 := by
    have he := dot_le_supp hS hq t
    unfold innerSlackU
    linarith
  have hfq : f q ≤ 0 := by dsimp [f]; rw [hqv']; linarith
  have hfp : 0 ≤ f p := by dsimp [f]; rw [hpu']; linarith
  obtain ⟨z, hz, hfz⟩ := hconn.isPreconnected.intermediate_value hq hp hf ⟨hfq, hfp⟩
  have heq : innerSlackU S t z = innerSlackV S t z := sub_eq_zero.mp hfz
  have hu : 0 ≤ innerSlackU S t z := by simpa only [← heq, max_self] using hslack z hz
  have hv : 0 ≤ innerSlackV S t z := by rwa [← heq]
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc := cos_nonneg_of_mem_Icc (show t ∈ Icc (-(π / 2)) (π / 2) from
    ⟨by linarith [ht.1, pi_pos], ht.2⟩)
  have hpos := add_nonneg (mul_nonneg hu hs) (mul_nonneg hv hc)
  have hid : innerSlackU S t z * sin t + innerSlackV S t z * cos t =
      z.2 - (innerCorner S t).2 := by
    rw [proposition2_2_2_innerCorner]
    simp only [innerSlackU, innerSlackV, dot, uvec, vvec,
      Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have htrig := sin_sq_add_cos_sq t
    nlinarith [show z.2 * (sin t ^ 2 + cos t ^ 2) = z.2 by rw [htrig, mul_one]]
  rw [hid] at hpos
  linarith [(hstrip hz).2]

theorem moving_horizontal_span_le_six {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : π / 4 ≤ ω)
    (htop : supp S (π / 2) = 1) {p q : Point} (hp : p ∈ S) (hq : q ∈ S) :
    p.1 - q.1 ≤ 6 := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  have hstrip := moving_strip_of_top ⟨ω, hS⟩ htop
  have hheight := connected_corner_height hcpt hS.2.1.nonempty hS.2.1 hstrip
    (t := π / 4) ⟨by positivity, by linarith [pi_pos]⟩
    (fun p hp => moving_hallway_slacks hS hp ⟨by positivity, hω⟩)
  have hu := dot_le_supp hcpt hp (π / 4)
  have hv := dot_le_supp hcpt hq (π / 4 + π / 2)
  rw [uvec_add_pi_div_two] at hv
  rw [proposition2_2_2_innerCorner] at hheight
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd,
    sin_pi_div_four, cos_pi_div_four] at hheight
  simp only [dot, uvec, vvec, sin_pi_div_four, cos_pi_div_four] at hu hv
  have hr0 := sqrt_nonneg (2 : ℝ)
  have hr2 : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hrlo : 1 ≤ sqrt (2 : ℝ) := by nlinarith
  have hrhi : sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have hsum := add_le_add hu hv
  have hmul := mul_le_mul_of_nonneg_right hsum hr0
  have hpy := (hstrip hp).1
  have hqy := (hstrip hq).1
  have hy := mul_nonneg (add_nonneg hpy hqy) hr0
  have hp2 : p.1 * (sqrt (2 : ℝ)) ^ 2 = 2 * p.1 := by rw [hr2]; ring
  have hq2 : q.1 * (sqrt (2 : ℝ)) ^ 2 = 2 * q.1 := by rw [hr2]; ring
  have hpy2 : p.2 * (sqrt (2 : ℝ)) ^ 2 = 2 * p.2 := by rw [hr2]; ring
  have hqy2 : q.2 * (sqrt (2 : ℝ)) ^ 2 = 2 * q.2 := by rw [hr2]; ring
  nlinarith

def normalizedBox (P : GerverParams) : Set Point :=
  Icc (-supp (gerverSofa P) π) (-supp (gerverSofa P) π + 6) ×ˢ Icc (0 : ℝ) 1

theorem normalizedBox_compact (P : GerverParams) : IsCompact (normalizedBox P) :=
  isCompact_Icc.prod isCompact_Icc

theorem pinned_sofa_subset_box {P : GerverParams} {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : π / 4 ≤ ω)
    (htop : supp S (π / 2) = 1) (hleft : supp S π = supp (gerverSofa P) π) :
    S ⊆ normalizedBox P := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  obtain ⟨q, hq, he⟩ := exists_dot_eq_supp hcpt hS.2.1.nonempty π
  simp only [dot, uvec_pi] at he
  intro p hp
  have hl := dot_le_supp hcpt hp π
  simp only [dot, uvec_pi, hleft] at hl
  have hw := moving_horizontal_span_le_six hS hω htop hp hq
  rw [hleft] at he
  exact ⟨⟨by linarith, by linarith⟩, moving_strip_of_top ⟨ω, hS⟩ htop hp⟩

theorem quarter_le_reduced_angle : π / 4 ≤ arccos (5 / 11 : ℝ) := by
  have hs0 := sqrt_nonneg (2 : ℝ)
  have hs2 := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcos : (5 / 11 : ℝ) ≤ cos (π / 4) := by rw [cos_pi_div_four]; nlinarith
  have he := arccos_le_arccos hcos
  rwa [arccos_cos (by positivity : (0 : ℝ) ≤ π / 4) (by linarith [pi_pos])] at he


end MovingSofaStability

end SofaBounds

/-!
## Closed supporting constraints give a genuine motion of the limit

The original movement paths are not assumed to have a convergent subsequence.
The limit motion is constructed directly from the limit set's support function
and its terminal width. Compact support continuity is used directly; the actual
sofa is not required to be convex.
-/

section SofaLimitMotion

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
  exact ⟨by unfold innerSlackU; ring, by unfold innerSlackV; ring⟩

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
    simp only [θ, c]
    rw [rot_sub_vec, sub_eq_add_neg]
  refine ⟨hS.isClosed, hc, θ, c, ?_⟩
  refine ⟨by fun_prop, ?_, by simp [θ], by simp [θ], ?_, ?_, ?_⟩
  · have hpath : Continuous (fun s => innerCorner S (s * ω)) := hcorner.comp (by fun_prop)
    have hfst : Continuous (fun s => (innerCorner S (s * ω)).1) := continuous_fst.comp hpath
    have hsnd : Continuous (fun s => (innerCorner S (s * ω)).2) := continuous_snd.comp hpath
    exact Continuous.continuousOn (by unfold c rot; fun_prop)
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
      rw [← he]
      exact tendsto_const_nhds.mul hωn
    obtain ⟨hU, hV⟩ := compactShape_slack_limits hK hpt htn
    apply ge_of_tendsto (hU.max hV)
    exact Eventually.of_forall fun n => moving_hallway_slacks (hmove n) (hpn n)
      ⟨mul_nonneg hs.1 (arccos_nonneg _ |>.trans (hangles n).1),
        by nlinarith [hs.2, (hangles n).1, arccos_nonneg (5 / 11 : ℝ)]⟩
  exact ⟨moving_of_supporting_constraints L.isCompact hconn hωpos.le hstrip htop hwidth hslack,
    hω, htop, hleft⟩

end MovingSofaStability

end SofaLimitMotion

/-!
## Qualitative entry into the quantitative neighborhood

Compactness supplies entry into a fixed neighborhood, not a rate. The limit
motion is constructed from supporting constraints. A limit of normalized sofas
whose areas tend to `|G|` has area `|G|`, so it is Gerver's sofa, by the
optimality and uniqueness theorems of the coercive route
(`MovingSofaExtremal.area_le_gerver`, `pinned_maximizer_eq_gerver`).
-/

section QualitativeEntry

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def compactShapeOfMoving {S : Set Point} (hS : IsMovingSofa S) : CompactShape where
  carrier := S
  isCompact' := isCompact_of_isMovingSofa hS
  nonempty' := hS.choose_spec.2.1.nonempty

def gerverCompactShape {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : CompactShape :=
  compactShapeOfMoving ⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩

theorem maximizing_subsequence {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (K : ℕ → CompactShape) (ωn : ℕ → ℝ)
    (hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ωn n))
    (hangles : ∀ n, ωn n ∈ Icc (arccos (5 / 11)) (π / 2))
    (htops : ∀ n, supp (K n : Set Point) (π / 2) = 1)
    (hlefts : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π)
    (harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 (area (gerverSofa P)))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (K ∘ σ) atTop (𝓝 (gerverCompactShape hP hbox)) ∧
      Tendsto (ωn ∘ σ) atTop (𝓝 (π / 2)) := by
  let B := {L : CompactShape | (L : Set Point) ⊆ normalizedBox P}
  have hB : IsCompact B := NonemptyCompacts.isCompact_subsets_of_isCompact (normalizedBox_compact P)
  have hprod : IsCompact (B ×ˢ Icc (arccos (5 / 11 : ℝ)) (π / 2)) := hB.prod isCompact_Icc
  have hmem : ∀ n, (K n, ωn n) ∈ B ×ˢ Icc (arccos (5 / 11 : ℝ)) (π / 2) := by
    intro n
    exact ⟨pinned_sofa_subset_box (hmove n) (quarter_le_reduced_angle.trans (hangles n).1)
      (htops n) (hlefts n), hangles n⟩
  obtain ⟨⟨L, ω⟩, hLω, σ, hσ, hlim⟩ := hprod.tendsto_subseq hmem
  have hKlim : Tendsto (K ∘ σ) atTop (𝓝 L) := (continuous_fst.tendsto _).comp hlim
  have hωlim : Tendsto (ωn ∘ σ) atTop (𝓝 ω) := (continuous_snd.tendsto _).comp hlim
  obtain ⟨hLmove, hω, htop, hleft⟩ := normalized_moving_limit hKlim hωlim
    (fun n => hmove (σ n)) (fun n => hangles (σ n)) (fun n => htops (σ n)) (fun n => hlefts (σ n))
  have hareaLim := harea.comp hσ.tendsto_atTop
  have hmax : area (L : Set Point) = area (gerverSofa P) := le_antisymm
    (MovingSofaExtremal.area_le_gerver hP hbox ⟨ω, hLmove⟩)
    (compactShape_area_limsup hKlim hareaLim)
  have hset : (L : Set Point) = gerverSofa P := pinned_maximizer_eq_gerver hP hbox
    ⟨ω, hLmove⟩ htop hleft hmax
  have hLeq : L = gerverCompactShape hP hbox := NonemptyCompacts.ext hset
  have hωeq : ω = π / 2 := by
    by_contra hne
    obtain ⟨p, hp, q, hq, hgt⟩ := gerver_width_gt_one hP hbox
      ⟨(arccos_nonneg _).trans hω.1, hω.2.trans (by linarith [pi_pos])⟩ hne
    rw [hset] at hLmove
    have hle := moving_terminal_projection hLmove hq hp
    linarith
  exact ⟨σ, hσ, hLeq ▸ hKlim, hωeq ▸ hωlim⟩

theorem near_maximizers_enter_neighborhood {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {ρ α₀ : ℝ} (hρ : 0 < ρ) (hα₀ : 0 < α₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ S : Set Point, ∀ ω : ℝ,
      IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
      sofaDeficit P S < ε₀ →
      EuclideanClose ρ (normalizedSofa P S) (gerverSofa P) ∧ π / 2 - ω < α₀ := by
  classical
  by_contra hn
  have counter (ε : ℝ) (hε : 0 < ε) :
      ∃ S : Set Point, ∃ ω : ℝ, IsMovingSofaWithAngle S ω ∧
        ω ∈ Icc (arccos (5 / 11)) (π / 2) ∧ sofaDeficit P S < ε ∧
        ¬(EuclideanClose ρ (normalizedSofa P S) (gerverSofa P) ∧ π / 2 - ω < α₀) := by
    by_contra hc
    apply hn
    refine ⟨ε, hε, ?_⟩
    intro S ω hS hω hdef
    by_contra hbad
    exact hc ⟨S, ω, hS, hω, hdef, hbad⟩
  choose S ω hS hω hdef hbad using fun n : ℕ => counter (1 / ((n : ℝ) + 1)) (by positivity)
  let K : ℕ → CompactShape := fun n => compactShapeOfMoving (normalizedSofa_moving P ⟨ω n, hS n⟩)
  have hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ω n) :=
    fun n => normalizedSofa_movingWithAngle P (hS n)
  have htop : ∀ n, supp (K n : Set Point) (π / 2) = 1 := fun n =>
    normalizedSofa_top P (ms_isCompact_of_isMovingSofaWithAngle (hS n)) (hS n).2.1.nonempty
  have hleft : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π := fun n =>
    normalizedSofa_left P (ms_isCompact_of_isMovingSofaWithAngle (hS n)) (hS n).2.1.nonempty
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdef0 : Tendsto (fun n => sofaDeficit P (S n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => sofaDeficit_nonneg hP hbox ⟨ω n, hS n⟩) (fun n => (hdef n).le) hinv
  have harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 (area (gerverSofa P))) := by
    have he := (tendsto_const_nhds (x := area (gerverSofa P))).sub hdef0
    simpa only [K, compactShapeOfMoving, NonemptyCompacts.coe_mk, Compacts.coe_mk, sofaDeficit,
      sub_sub_cancel, sub_zero, area_normalizedSofa] using he
  obtain ⟨σ, hσ, hKlim, hωlim⟩ := maximizing_subsequence hP hbox K ω hmove hω htop hleft harea
  have evK := Metric.tendsto_nhds.1 hKlim (ρ / 2) (by positivity)
  have evω := Metric.tendsto_nhds.1 hωlim α₀ hα₀
  obtain ⟨n, hnK, hnω⟩ := (evK.and evω).exists
  rw [Function.comp_apply] at hnK hnω
  have hclose := compactShape_euclideanClose (K (σ n)) (gerverCompactShape hP hbox)
  have hclose' : EuclideanClose ρ (normalizedSofa P (S (σ n))) (gerverSofa P) :=
    hclose.mono (by linarith)
  have hang : π / 2 - ω (σ n) < α₀ := by
    rw [Real.dist_eq] at hnω
    have he := (abs_lt.mp hnω).1
    linarith
  exact hbad (σ n) ⟨hclose', hang⟩

end MovingSofaStability

end QualitativeEntry

/-!
## Unrestricted stability of Gerver's sofa

The conclusions concern the actual nonconvex sets in the repository's original
moving-sofa definition. All analytic and geometric prerequisites are supplied by
the preceding modules; neither an injective envelope nor a stability estimate is
assumed of the input sofa.

The global constants are existential: no claim is made that they are sharp or
effectively computed.
-/

section GlobalStability

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- An exact maximizer equals Gerver after the prescribed translation. -/
theorem normalizedSofa_eq_gerver_of_zero_deficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Point}
    (hS : IsMovingSofa S) (hzero : sofaDeficit P S = 0) :
    normalizedSofa P S = gerverSofa P := by
  have hc := isCompact_of_isMovingSofa hS
  have hn := hS.choose_spec.2.1.nonempty
  apply pinned_maximizer_eq_gerver hP hbox (normalizedSofa_moving P hS)
    (normalizedSofa_top P hc hn) (normalizedSofa_left P hc hn)
  rw [area_normalizedSofa]
  unfold sofaDeficit at hzero
  linarith

/-- In a reduced angle range Gerver itself must complete the right-angle turn. -/
theorem gerver_reduced_angle_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {ω : ℝ} (hω : ω ∈ Icc (arccos (5 / 11)) (π / 2))
    (hmove : IsMovingSofaWithAngle (gerverSofa P) ω) : ω = π / 2 := by
  by_contra hne
  obtain ⟨p, hp, q, hq, hgt⟩ := gerver_width_gt_one hP hbox
    ⟨(arccos_nonneg _).trans hω.1, by linarith [hω.2, pi_pos]⟩ hne
  have hle := moving_terminal_projection hmove hq hp
  linarith

/-- A single neighborhood and one choice of constants work for every reduced
motion of every sufficiently near-optimal original sofa. -/
theorem reduced_sofa_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ C Carea Cangle ε₀ : ℝ,
      0 < C ∧ 0 < Carea ∧ 0 < Cangle ∧ 0 < ε₀ ∧
      ∀ S : Set Point, ∀ ω : ℝ, IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
        EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
        symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤ Carea * sqrt (sofaDeficit P S) ∧
        0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S := by
  obtain ⟨C, c, δ, α₀, εL, hC, hc, hδ, hδ1, hα₀, hεL, hεL1, hlocal⟩ :=
    local_positive_sofa_hausdorff hP hbox
  obtain ⟨Carea, εA, hCarea, hεA, hεA1, harea⟩ :=
    gerver_symmetricDifference_from_distance hP hbox hC
  obtain ⟨εQ, hεQ, hentry⟩ := near_maximizers_enter_neighborhood hP hbox hδ hα₀
  let ε₀ := min εL (min εA εQ)
  have hε₀ : 0 < ε₀ := lt_min hεL (lt_min hεA hεQ)
  have eL : ε₀ ≤ εL := min_le_left _ _
  have eA : ε₀ ≤ εA := (min_le_right _ _).trans (min_le_left _ _)
  have eQ : ε₀ ≤ εQ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, Carea, 1 / c, ε₀, hC, hCarea, one_div_pos.mpr hc, hε₀, ?_⟩
  intro S ω hS hω hε
  have hSmove : IsMovingSofa S := ⟨ω, hS⟩
  have hdef := sofaDeficit_nonneg hP hbox hSmove
  have hα : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  rcases eq_or_lt_of_le hdef with hzero | hpositive
  · have hz : sofaDeficit P S = 0 := hzero.symm
    have hset := normalizedSofa_eq_gerver_of_zero_deficit hP hbox hSmove hz
    have hGmove := normalizedSofa_movingWithAngle P hS
    rw [hset] at hGmove
    have hωeq := gerver_reduced_angle_eq hP hbox hω hGmove
    rw [hz, sqrt_zero, mul_zero, mul_zero, mul_zero, hset, hωeq, sub_self]
    refine ⟨EuclideanClose.refl _ le_rfl, ?_, le_rfl, le_rfl⟩
    simp [symmetricDifferenceArea, area]
  · have hcompact := ms_isCompact_of_isMovingSofaWithAngle hS
    have hne := hS.2.1.nonempty
    let N := normalizedSofa P S
    have hNmove : IsMovingSofaWithAngle N ω := normalizedSofa_movingWithAngle P hS
    have hNc := ms_isCompact_of_isMovingSofaWithAngle hNmove
    have hNne := hNmove.2.1.nonempty
    have htop : supp N (π / 2) = 1 := normalizedSofa_top P hcompact hne
    have hleft : supp N π = supp (gerverSofa P) π := normalizedSofa_left P hcompact hne
    have hstrip := normalizedSofa_strip P hSmove
    obtain ⟨hclose, hangle⟩ := hentry S ω hS hω (hε.trans_le eQ)
    let K := sofaCap N
    have hK : IsCap K (π / 2) := sofaCap_isCap hNc hNne hstrip htop
    have hKleft : supp K π = supp P.cap π := by
      rw [sofaCap_upper_support hNc hNne hstrip htop ⟨pi_pos.le, le_rfl⟩,
        hleft, gerver_upper_support hP hbox ⟨pi_pos.le, le_rfl⟩]
    have hKclose : UpperSupportClose δ K P.cap :=
      sofaCap_close_to_gerver hP hbox hNc hNne hstrip htop hclose
    have hω' : ω ∈ Icc (0 : ℝ) (π / 2) := ⟨(arccos_nonneg _).trans hω.1, hω.2⟩
    have hconstraints : PartialSofaConstraints K N ω := sofaCap_partial_constraints hNmove hω' htop
    have heq : sofaDeficit P S = area (gerverSofa P) - area N := by
      rw [area_normalizedSofa]
      rfl
    obtain ⟨hd, ha⟩ := hlocal K hK hKleft hKclose N hNc.measurableSet ω hω' hangle.le hconstraints
      (sofaDeficit P S) heq hpositive (hε.trans_le eL)
    have had := harea N hNc (sofaDeficit P S) ⟨hpositive, (hε.trans_le eA).le⟩ heq hd
    refine ⟨hd, had, hα, ?_⟩
    rwa [one_div_mul_eq_div]

/-- The unrestricted actual-set stability theorem, in the precise target
proposition. No geometric certificate is an assumption of this theorem. -/
theorem unrestricted_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P := by
  obtain ⟨C, Carea, Cangle, εR, hC, hCarea, hCangle, hεR, hresult⟩ := reduced_sofa_stability hP hbox
  let gap := area (gerverSofa P) - (2.2 : ℝ)
  have hgap : 0 < gap := by
    have harea := (gerverSofa_area_mem hP hbox).1
    dsimp [gap]
    linarith
  let ε₀ := min εR gap
  refine ⟨C, Carea, ε₀, hC, hCarea, lt_min hεR hgap, ?_⟩
  intro S hS hε
  have h22 : (2.2 : ℝ) ≤ area S := by
    have he := hε.trans_le (min_le_right εR gap)
    dsimp [sofaDeficit, gap] at he
    linarith
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hω' : ω ∈ Icc (arccos (5 / 11 : ℝ)) (π / 2) := by
    have h : (1 / 2.2 : ℝ) = 5 / 11 := by norm_num
    simpa only [arcsec22, h] using hω
  have he := hresult S ω hSω hω' (hε.trans_le (min_le_left _ _))
  exact ⟨he.1, he.2.1⟩

/-- The missing terminal angle is controlled linearly in the original area deficit. -/
theorem terminal_angle_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P := by
  obtain ⟨C, Carea, Cangle, ε₀, hC, hCarea, hCangle, hε₀, hresult⟩ := reduced_sofa_stability hP hbox
  exact ⟨Cangle, ε₀, hCangle, hε₀, fun S ω hS hω hε => (hresult S ω hS hω hε).2.2⟩

end MovingSofaStability

end GlobalStability
