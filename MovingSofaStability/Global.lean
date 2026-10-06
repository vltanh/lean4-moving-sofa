module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.MeasureTheory.Measure.Regular
public import MovingSofaExtremal.Main
public import MovingSofaStability.Recovery

/-!
# Compactness and the stability theorems

Normalized sofas lie in a fixed box, and a Hausdorff limit of normalized sofas whose areas tend to
that of Gerver's sofa is a moving sofa of maximal area, hence Gerver's sofa by the uniqueness
theorem of the coercive route. So every sofa of small deficit enters the neighborhood of the local
estimates (`near_maximizers_enter_neighborhood`), which gives the two stability theorems
(`unrestricted_stability`, `terminal_angle_stability`). The constants are existential.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-! ## The sign of the deficit -/

/-- The deficit of a moving sofa is nonnegative: Gerver's sofa has the largest area, by the
optimality theorem of the coercive route (`MovingSofaExtremal.area_le_gerver`). -/
theorem sofaDeficit_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofa S) : 0 ≤ sofaDeficit P S :=
  sub_nonneg.mpr (MovingSofaExtremal.area_le_gerver hP hbox hS)

/-!
## Hausdorff limits of compact sets

The space of nonempty compact sets, convex or not, with the Hausdorff distance of the sup metric
of `ℝ × ℝ`; Euclidean witnesses cost a factor `2`. Area is only upper semicontinuous.
-/

/-- The nonempty compact subsets of the plane, with the Hausdorff distance. -/
abbrev CompactShape := NonemptyCompacts Point

/-- A point of `K` has a point of `L` within their Hausdorff distance, in the sup metric. -/
theorem compactShape_near_point (K L : CompactShape) {p : Point} (hp : p ∈ K) :
    ∃ q ∈ L, dist p q ≤ dist K L := by
  obtain ⟨q, hq, he⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty p
  exact ⟨q, hq, he ▸ Metric.infDist_le_hausdorffDist_of_mem hp (edist_ne_top K L)⟩

/-- Compact sets at Hausdorff distance `d` are Euclidean `2 d`-close. -/
theorem compactShape_euclideanClose (K L : CompactShape) :
    EuclideanClose (2 * dist K L) (K : Set Point) (L : Set Point) := by
  have forward (A B : CompactShape) :
      DirectedClose (2 * dist A B) (A : Set Point) (B : Set Point) := by
    intro p hp
    obtain ⟨q, hq, hd⟩ := compactShape_near_point A B hp
    exact ⟨q, hq, (norm2_le_two_product_norm (p - q)).trans (by rw [← dist_eq_norm]; linarith)⟩
  exact ⟨forward K L, by simpa only [dist_comm L K] using forward L K⟩

/-- Support functions converge along a convergent sequence of compact sets, also when the
direction varies with the sequence. -/
theorem compactShape_support_tendsto {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto (fun n => supp (K n : Set Point) (t n)) atTop (𝓝 (supp (L : Set Point) a)) := by
  -- `|h_{K n}(t n) - h_L(t n)| ≤ 2 d(K n, L)`, and `h_L` is continuous
  have hd : Tendsto (fun n => 2 * dist (K n) L) atTop (𝓝 0) := by
    simpa using (tendsto_iff_dist_tendsto_zero.1 hK).const_mul 2
  have herr : Tendsto (fun n => supp (K n : Set Point) (t n) - supp (L : Set Point) (t n))
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (compactShape_euclideanClose (K n) L).abs_supp_sub_le
      (K n).isCompact L.isCompact (K n).nonempty L.nonempty (t n)) hd
  simpa using herr.add (((continuous_supp L.isCompact).tendsto a).comp ht)

/-- Every point of the limit is a limit of points of the approximating sets. -/
theorem compactShape_approximate_point {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {p : Point} (hp : p ∈ L) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) := by
  choose q hq hd using fun n => compactShape_near_point L (K n) hp
  refine ⟨q, hq, tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
    (fun n => ?_) (tendsto_iff_dist_tendsto_zero.1 hK))⟩
  rw [dist_comm, dist_comm (K n)]
  exact hd n

/-- Hausdorff limits of compact connected sets are connected. -/
theorem compactShape_connected_limit {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) (hc : ∀ n, IsConnected (K n : Set Point)) :
    IsConnected (L : Set Point) := by
  refine ⟨L.nonempty,
    (isPreconnected_iff_subset_of_fully_disjoint_closed L.isCompact.isClosed).2 ?_⟩
  intro A B hA hB hcover hdisj
  by_contra! hnot
  obtain ⟨p, hp, hpA⟩ := not_subset.mp hnot.1
  obtain ⟨q, hq, hqB⟩ := not_subset.mp hnot.2
  -- disjoint open neighborhoods of `A` and `B` both meet `K n` and cover it, for large `n`
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hdisj
  have evcover : ∀ᶠ n in atTop, (K n : Set Point) ⊆ U ∪ V := hK.eventually
    ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).mem_nhds
      (hcover.trans (union_subset_union hAU hBV)))
  have evU : ∀ᶠ n in atTop, ((K n : Set Point) ∩ U).Nonempty := hK.eventually
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).mem_nhds
      ⟨q, hq, hAU ((hcover hq).resolve_right hqB)⟩)
  have evV : ∀ᶠ n in atTop, ((K n : Set Point) ∩ V).Nonempty := hK.eventually
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV).mem_nhds
      ⟨p, hp, hBV ((hcover hp).resolve_left hpA)⟩)
  obtain ⟨n, hn, hnU, hnV⟩ := (evcover.and (evU.and evV)).exists
  obtain ⟨x, -, hxU, hxV⟩ := (hc n).isPreconnected U V hU hV hn hnU hnV
  exact disjoint_left.mp hUV hxU hxV

/-- Inclusion in a fixed closed set passes to Hausdorff limits. -/
theorem compactShape_subset_limit {K : ℕ → CompactShape} {L : CompactShape} {B : Set Point}
    (hK : Tendsto K atTop (𝓝 L)) (hB : IsClosed B) (hsub : ∀ n, (K n : Set Point) ⊆ B) :
    (L : Set Point) ⊆ B :=
  (NonemptyCompacts.isClosed_subsets_of_isClosed hB).mem_of_tendsto hK
    (Eventually.of_forall hsub)

/-- Area is upper semicontinuous along a convergent sequence of compact sets. -/
theorem compactShape_area_limsup {K : ℕ → CompactShape} {L : CompactShape} {M : ℝ}
    (hK : Tendsto K atTop (𝓝 L))
    (harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 M)) :
    M ≤ area (L : Set Point) := by
  refine le_of_forall_gt fun r hr => ?_
  -- an open set `U ⊇ L` of area less than `r` contains `K n` for large `n`
  obtain ⟨U, hLU, hU, hvolU⟩ := (L : Set Point).exists_isOpen_lt_of_lt (μ := volume)
    (ENNReal.ofReal r) ((ENNReal.lt_ofReal_iff_toReal_lt L.isCompact.measure_lt_top.ne).2 hr)
  have ev : ∀ᶠ n in atTop, area (K n : Set Point) ≤ area U :=
    (hK.eventually ((NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hLU)).mono
      fun n hn => area_mono_of_finite hn (ne_top_of_lt hvolU)
  exact (le_of_tendsto harea ev).trans_lt (ENNReal.toReal_lt_of_lt_ofReal hvolU)

/-!
## A box containing the normalized sofas

By connectedness the inner corner at angle `π/4` lies at height at most `1`, which bounds the
horizontal width of a sofa by `6`. No balancedness is assumed.
-/

/-- The inner corner at an angle `t ∈ [0, π/2]` of a compact connected set in the strip
`0 ≤ y ≤ 1` lies at height at most `1`, if every point has a nonnegative inner slack. -/
theorem connected_corner_height {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (hconn : IsConnected S) (hstrip : S ⊆ hStrip) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2))
    (hslack : ∀ p ∈ S, 0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    (innerCorner S t).2 ≤ 1 := by
  -- the difference of the slacks changes sign between the contact points with the two walls
  obtain ⟨p, hp, hpu⟩ := exists_dot_eq_supp hS hne t
  obtain ⟨q, hq, hqv⟩ := exists_dot_eq_supp hS hne (t + π / 2)
  have hpv := dot_le_supp hS hp (t + π / 2)
  rw [uvec_add_pi_div_two] at hqv hpv
  have hfq : innerSlackU S t q - innerSlackV S t q ≤ 0 := by
    simp only [innerSlackU, innerSlackV]
    linarith [dot_le_supp hS hq t]
  have hfp : 0 ≤ innerSlackU S t p - innerSlackV S t p := by
    simp only [innerSlackU, innerSlackV]
    linarith
  have hf : ContinuousOn (fun z => innerSlackU S t z - innerSlackV S t z) S := by
    simp only [innerSlackU, innerSlackV, dot]
    fun_prop
  obtain ⟨z, hz, hfz⟩ := hconn.isPreconnected.intermediate_value hq hp hf ⟨hfq, hfp⟩
  -- at a point with equal slacks both are nonnegative, so the corner lies below the point
  have heq : innerSlackU S t z = innerSlackV S t z := sub_eq_zero.mp hfz
  have hu : 0 ≤ innerSlackU S t z := by simpa only [← heq, max_self] using hslack z hz
  have hid : innerSlackU S t z * sin t + innerSlackV S t z * cos t =
      z.2 - (innerCorner S t).2 := by
    rw [proposition2_2_2_innerCorner]
    simp only [innerSlackU, innerSlackV, dot, uvec, vvec, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul]
    linear_combination z.2 * sin_sq_add_cos_sq t
  rw [← heq] at hid
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hc := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
  linarith [mul_nonneg hu hs, mul_nonneg hu hc, (hstrip hz).2]

/-- A moving sofa with rotation angle at least `π/4` and top support `1` has horizontal width
at most `6`. -/
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
  -- `√2 (hu + hv)` with `√2 ^ 2 = 2`: `p.1 + p.2 - q.1 + q.2 ≤ √2 (h(π/4) + h(3π/4)) ≤ 2 + 2 √2`
  have hr0 := sqrt_nonneg (2 : ℝ)
  have h2 (x : ℝ) : x * √2 ^ 2 = 2 * x := by rw [sq_sqrt zero_le_two]; ring
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add hu hv) hr0, (hstrip hp).1, (hstrip hq).1,
    h2 p.1, h2 q.1, h2 p.2, h2 q.2]

/-- The box `[-h_G(π), -h_G(π) + 6] × [0, 1]`. -/
def normalizedBox (P : GerverParams) : Set Point :=
  Icc (-supp (gerverSofa P) π) (-supp (gerverSofa P) π + 6) ×ˢ Icc (0 : ℝ) 1

/-- A moving sofa with rotation angle at least `π/4`, top support `1` and the left support of
Gerver's sofa lies in `normalizedBox P`. -/
theorem pinned_sofa_subset_box {P : GerverParams} {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (hω : π / 4 ≤ ω)
    (htop : supp S (π / 2) = 1) (hleft : supp S π = supp (gerverSofa P) π) :
    S ⊆ normalizedBox P := by
  have hcpt := ms_isCompact_of_isMovingSofaWithAngle hS
  obtain ⟨q, hq, he⟩ := exists_dot_eq_supp hcpt hS.2.1.nonempty π
  intro p hp
  have hl := dot_le_supp hcpt hp π
  rw [dot_uvec_pi, hleft] at hl he
  have hw := moving_horizontal_span_le_six hS hω htop hp hq
  exact ⟨⟨by linarith, by linarith⟩, moving_strip_of_top ⟨ω, hS⟩ htop hp⟩

/-- `π/4 ≤ arccos (5/11)`. -/
theorem quarter_le_reduced_angle : π / 4 ≤ arccos (5 / 11 : ℝ) := by
  have hcos : (5 / 11 : ℝ) ≤ cos (π / 4) := by
    rw [cos_pi_div_four]
    nlinarith [sqrt_nonneg (2 : ℝ), sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  simpa only [arccos_cos (by positivity : (0 : ℝ) ≤ π / 4) (by linarith [pi_pos])] using
    arccos_le_arccos hcos

/-!
## The limit of normalized sofas is a moving sofa

The movements of the sofas need not converge. The movement of the limit is built from its support
function: the canonical placement at angle `t` puts the inner corner of the supporting hallway at
the origin, and closed inequalities on the inner slacks pass to the limit.
-/

/-- In the canonical placement at angle `t`, the coordinates of a point are its two inner
slacks. -/
theorem canonical_placement_coordinates (S : Set Point) (t : ℝ) (p : Point) :
    rot (-t) (p - innerCorner S t) = (innerSlackU S t p, innerSlackV S t p) := by
  ext
  · rw [ms_rot_neg_fst, dot_sub_left, (cn_innerCorner_dot S t).1, innerSlackU]
    ring
  · rw [ms_rot_neg_snd, dot_sub_left, opt_innerCorner_dot_v, innerSlackV]
    ring

/-- The inner slacks of a point of a compact set are at most `1`. -/
theorem innerSlack_le_one {S : Set Point} (hS : IsCompact S) {p : Point} (hp : p ∈ S) (t : ℝ) :
    innerSlackU S t p ≤ 1 ∧ innerSlackV S t p ≤ 1 := by
  have hv := dot_le_supp hS hp (t + π / 2)
  rw [uvec_add_pi_div_two] at hv
  constructor <;> simp only [innerSlackU, innerSlackV] <;> linarith [dot_le_supp hS hp t]

/-- A compact connected set in the strip `0 ≤ y ≤ 1` with top support `1`, terminal width at
most `1` and a nonnegative inner slack at every angle of `[0, ω]` is a moving sofa with rotation
angle `ω`, moved by the canonical placements. -/
theorem moving_of_supporting_constraints {S : Set Point} {ω : ℝ}
    (hS : IsCompact S) (hc : IsConnected S) (hω : 0 ≤ ω)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    (hwidth : supp S ω + supp S (ω + π) ≤ 1)
    (hslack : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    IsMovingSofaWithAngle S ω := by
  let θ : ℝ → ℝ := fun s => -(s * ω)
  let c : ℝ → Point := fun s => -rot (-(s * ω)) (innerCorner S (s * ω))
  have hplace (s : ℝ) (p : Point) :
      rot (θ s) p + c s = (innerSlackU S (s * ω) p, innerSlackV S (s * ω) p) := by
    rw [← canonical_placement_coordinates]
    ext <;> simp only [θ, c, rot, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_sub, Prod.snd_sub] <;> ring
  have hsupp := continuous_supp hS
  refine ⟨hS.isClosed, hc, θ, c, by fun_prop, by simp only [c, rot]; fun_prop, by simp [θ],
    by simp [θ], ?_, ?_, ?_⟩
  · intro p hp
    rw [hplace, zero_mul]
    have hV : innerSlackV S 0 p = p.2 := by
      simp only [innerSlackV, vvec_zero, dot, zero_add, htop]
      ring
    exact ⟨(innerSlack_le_one hS hp 0).1, hV ▸ (hstrip hp).1, hV ▸ (hstrip hp).2⟩
  · intro s hs p hp
    rw [hplace, ms_mem_hallway_iff]
    exact ⟨(innerSlack_le_one hS hp _).1, (innerSlack_le_one hS hp _).2,
      le_max_iff.mp (hslack p hp _ ⟨mul_nonneg hs.1 hω, by nlinarith [hs.2]⟩)⟩
  · intro p hp
    rw [hplace, one_mul]
    have hl := dot_le_supp hS hp (ω + π)
    rw [dot_uvec_add_pi] at hl
    exact ⟨by simp only [innerSlackU]; linarith, (innerSlack_le_one hS hp ω).1,
      (innerSlack_le_one hS hp ω).2⟩

/-- Both inner slacks pass to limits of compact sets, points and angles. -/
theorem compactShape_slack_limits {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {p : ℕ → Point} {q : Point}
    (hp : Tendsto p atTop (𝓝 q)) {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto (fun n => innerSlackU (K n : Set Point) (t n) (p n)) atTop
      (𝓝 (innerSlackU (L : Set Point) a q)) ∧
    Tendsto (fun n => innerSlackV (K n : Set Point) (t n) (p n)) atTop
      (𝓝 (innerSlackV (L : Set Point) a q)) := by
  have hdu := (continuous_dot_pair.tendsto _).comp
    (hp.prodMk_nhds ((continuous_uvec.tendsto _).comp ht))
  have hdv := (continuous_dot_pair.tendsto _).comp
    (hp.prodMk_nhds ((continuous_vvec.tendsto _).comp ht))
  exact ⟨(hdu.sub (compactShape_support_tendsto hK ht)).add_const 1,
    (hdv.sub (compactShape_support_tendsto hK (ht.add_const (π / 2)))).add_const 1⟩

/-- A Hausdorff limit of normalized moving sofas with rotation angles in
`[arccos (5/11), π/2]` is a normalized moving sofa, whose rotation angle is the limit angle. -/
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
  have hωpos : 0 < ω :=
    (by positivity : (0 : ℝ) < π / 4).trans_le (quarter_le_reduced_angle.trans hω.1)
  -- supports in fixed directions pass to the limit
  have hfix {u b : ℝ} (h : ∀ n, supp (K n : Set Point) u = b) : supp (L : Set Point) u = b :=
    tendsto_nhds_unique (compactShape_support_tendsto hK tendsto_const_nhds)
      (by simpa only [h] using tendsto_const_nhds)
  have htop := hfix htops
  have hstrip : (L : Set Point) ⊆ hStrip := compactShape_subset_limit hK
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))
    (fun n => moving_strip_of_top ⟨ωn n, hmove n⟩ (htops n))
  have hwidth : supp (L : Set Point) ω + supp (L : Set Point) (ω + π) ≤ 1 :=
    le_of_tendsto ((compactShape_support_tendsto hK hωn).add
      (compactShape_support_tendsto hK (hωn.add_const π)))
      (Eventually.of_forall fun n => moving_terminal_width (hmove n))
  have hslack : ∀ p ∈ (L : Set Point), ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU (L : Set Point) t p) (innerSlackV (L : Set Point) t p) := by
    intro p hp t ht
    obtain ⟨pn, hpn, hpt⟩ := compactShape_approximate_point hK hp
    -- `t = s ω` is the limit of the angles `s ωn n ∈ [0, ωn n]`, where `s = t / ω ∈ [0, 1]`
    have hs : t / ω ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hωpos.le, (div_le_one hωpos).2 ht.2⟩
    have htn : Tendsto (fun n => t / ω * ωn n) atTop (𝓝 t) := by
      simpa only [div_mul_cancel₀ t hωpos.ne'] using (tendsto_const_nhds (x := t / ω)).mul hωn
    obtain ⟨hU, hV⟩ := compactShape_slack_limits hK hpt htn
    exact ge_of_tendsto (hU.max hV) (Eventually.of_forall fun n =>
      moving_hallway_slacks (hmove n) (hpn n)
        ⟨mul_nonneg hs.1 ((arccos_nonneg _).trans (hangles n).1),
          by nlinarith [hs.2, (hangles n).1, arccos_nonneg (5 / 11 : ℝ)]⟩)
  exact ⟨moving_of_supporting_constraints L.isCompact
    (compactShape_connected_limit hK fun n => (hmove n).2.1) hωpos.le hstrip htop hwidth hslack,
    hω, htop, hfix hlefts⟩

/-!
## Near-maximizers enter every neighborhood of Gerver's sofa

A limit of normalized sofas whose areas tend to `|G|` has area `|G|`, so it is Gerver's sofa, by
the optimality and uniqueness theorems of the coercive route (`MovingSofaExtremal.area_le_gerver`,
`pinned_maximizer_eq_gerver`). This gives no rate.
-/

/-- A moving sofa as a nonempty compact set. -/
def compactShapeOfMoving {S : Set Point} (hS : IsMovingSofa S) : CompactShape where
  carrier := S
  isCompact' := isCompact_of_isMovingSofa hS
  nonempty' := hS.choose_spec.2.1.nonempty

/-- Gerver's sofa as a nonempty compact set. -/
def gerverCompactShape {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : CompactShape :=
  compactShapeOfMoving ⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩

/-- A movement of Gerver's sofa with rotation angle in `[arccos (5/11), π/2]` completes the
right-angle turn, since the width of Gerver's sofa in every other direction exceeds `1`. -/
theorem gerver_reduced_angle_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {ω : ℝ} (hω : ω ∈ Icc (arccos (5 / 11)) (π / 2))
    (hmove : IsMovingSofaWithAngle (gerverSofa P) ω) : ω = π / 2 := by
  by_contra hne
  obtain ⟨p, hp, q, hq, hgt⟩ := gerver_width_gt_one hP hbox
    ⟨(arccos_nonneg _).trans hω.1, by linarith [hω.2, pi_pos]⟩ hne
  linarith [moving_terminal_projection hmove hq hp]

/-- Normalized moving sofas with rotation angles in `[arccos (5/11), π/2]` and areas tending to
`|G|` have a subsequence that converges to Gerver's sofa, with angles tending to `π/2`. -/
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
  -- the sofas and their angles lie in a compact set, so a subsequence converges
  have hcpt : IsCompact ({L : CompactShape | (L : Set Point) ⊆ normalizedBox P} ×ˢ
      Icc (arccos (5 / 11 : ℝ)) (π / 2)) :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact (isCompact_Icc.prod isCompact_Icc)).prod
      isCompact_Icc
  obtain ⟨⟨L, ω⟩, -, σ, hσ, hlim⟩ := hcpt.tendsto_subseq (x := fun n => (K n, ωn n)) fun n =>
    ⟨pinned_sofa_subset_box (hmove n) (quarter_le_reduced_angle.trans (hangles n).1)
      (htops n) (hlefts n), hangles n⟩
  have hKlim : Tendsto (K ∘ σ) atTop (𝓝 L) := (continuous_fst.tendsto _).comp hlim
  have hωlim : Tendsto (ωn ∘ σ) atTop (𝓝 ω) := (continuous_snd.tendsto _).comp hlim
  -- the limit is a normalized moving sofa of area `|G|`, hence Gerver's sofa
  obtain ⟨hLmove, hω, htop, hleft⟩ := normalized_moving_limit hKlim hωlim
    (fun n => hmove (σ n)) (fun n => hangles (σ n)) (fun n => htops (σ n))
    (fun n => hlefts (σ n))
  have hset : (L : Set Point) = gerverSofa P := pinned_maximizer_eq_gerver hP hbox
    ⟨ω, hLmove⟩ htop hleft (le_antisymm (MovingSofaExtremal.area_le_gerver hP hbox ⟨ω, hLmove⟩)
      (compactShape_area_limsup hKlim (harea.comp hσ.tendsto_atTop)))
  have hLeq : L = gerverCompactShape hP hbox := NonemptyCompacts.ext hset
  rw [hset] at hLmove
  exact ⟨σ, hσ, hLeq ▸ hKlim, gerver_reduced_angle_eq hP hbox hω hLmove ▸ hωlim⟩

/-- For all `ρ, α₀ > 0`, every moving sofa of small enough deficit with rotation angle
`ω ∈ [arccos (5/11), π/2]` has its normalization `ρ`-close to Gerver's sofa and `π/2 - ω < α₀`. -/
theorem near_maximizers_enter_neighborhood {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {ρ α₀ : ℝ} (hρ : 0 < ρ) (hα₀ : 0 < α₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ S : Set Point, ∀ ω : ℝ,
      IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
      sofaDeficit P S < ε₀ →
      EuclideanClose ρ (normalizedSofa P S) (gerverSofa P) ∧ π / 2 - ω < α₀ := by
  -- otherwise there are counterexamples `S n` of deficit less than `1 / (n + 1)`
  by_contra! hn
  choose S ω hS hω hdef hbad using fun n : ℕ => hn (1 / ((n : ℝ) + 1)) (by positivity)
  have hcpt (n : ℕ) := ms_isCompact_of_isMovingSofaWithAngle (hS n)
  let K : ℕ → CompactShape := fun n => compactShapeOfMoving (normalizedSofa_moving P ⟨ω n, hS n⟩)
  have hdef0 : Tendsto (fun n => sofaDeficit P (S n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => sofaDeficit_nonneg hP hbox ⟨ω n, hS n⟩) (fun n => (hdef n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 (area (gerverSofa P))) := by
    simpa [K, compactShapeOfMoving, sofaDeficit] using
      (tendsto_const_nhds (x := area (gerverSofa P))).sub hdef0
  -- a subsequence converges to Gerver's sofa, which contradicts the choice of the `S n`
  obtain ⟨σ, -, hKlim, hωlim⟩ := maximizing_subsequence hP hbox K ω
    (fun n => normalizedSofa_movingWithAngle P (hS n)) hω
    (fun n => normalizedSofa_top P (hcpt n) (hS n).2.1.nonempty)
    (fun n => normalizedSofa_left P (hcpt n) (hS n).2.1.nonempty) harea
  obtain ⟨n, hnK, hnω⟩ := ((Metric.tendsto_nhds.1 hKlim (ρ / 2) (by positivity)).and
    (Metric.tendsto_nhds.1 hωlim α₀ hα₀)).exists
  rw [Function.comp_apply] at hnK hnω
  have hclose : EuclideanClose ρ (normalizedSofa P (S (σ n))) (gerverSofa P) :=
    (compactShape_euclideanClose (K (σ n)) (gerverCompactShape hP hbox)).mono (by linarith)
  rw [Real.dist_eq] at hnω
  linarith [hbad (σ n) hclose, (abs_lt.mp hnω).1]

/-!
## The stability theorems

The local estimates hold in a fixed neighborhood of Gerver's sofa, and every sofa of small enough
deficit enters it.
-/

/-- A moving sofa of zero deficit is Gerver's sofa after normalization. -/
theorem normalizedSofa_eq_gerver_of_zero_deficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Point}
    (hS : IsMovingSofa S) (hzero : sofaDeficit P S = 0) :
    normalizedSofa P S = gerverSofa P := by
  have hc := isCompact_of_isMovingSofa hS
  have hn := hS.choose_spec.2.1.nonempty
  exact pinned_maximizer_eq_gerver hP hbox (normalizedSofa_moving P hS)
    (normalizedSofa_top P hc hn) (normalizedSofa_left P hc hn)
    ((area_normalizedSofa P S).trans (sub_eq_zero.1 hzero).symm)

/-- Stability for moving sofas with rotation angle in `[arccos (5/11), π/2]`: one choice of
constants gives the three conclusions. -/
theorem reduced_sofa_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ C Carea Cangle ε₀ : ℝ,
      0 < C ∧ 0 < Carea ∧ 0 < Cangle ∧ 0 < ε₀ ∧
      ∀ S : Set Point, ∀ ω : ℝ, IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
        EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
        symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤
          Carea * sqrt (sofaDeficit P S) ∧
        0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S := by
  obtain ⟨C, c, δ, α₀, εL, hC, hc, hδ, -, hα₀, hεL, -, hlocal⟩ :=
    local_positive_sofa_hausdorff hP hbox
  obtain ⟨Carea, εA, hCarea, hεA, -, harea⟩ :=
    gerver_symmetricDifference_from_distance hP hbox hC
  obtain ⟨εQ, hεQ, hentry⟩ := near_maximizers_enter_neighborhood hP hbox hδ hα₀
  refine ⟨C, Carea, 1 / c, min εL (min εA εQ), hC, hCarea, one_div_pos.mpr hc,
    lt_min hεL (lt_min hεA hεQ), fun S ω hS hω hε => ?_⟩
  have eL : sofaDeficit P S < εL := hε.trans_le (min_le_left _ _)
  have eA : sofaDeficit P S < εA := hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have eQ : sofaDeficit P S < εQ := hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hSmove : IsMovingSofa S := ⟨ω, hS⟩
  rcases (sofaDeficit_nonneg hP hbox hSmove).eq_or_lt with hzero | hpositive
  · -- zero deficit: the normalized sofa is Gerver's sofa, which completes the turn
    have hset := normalizedSofa_eq_gerver_of_zero_deficit hP hbox hSmove hzero.symm
    have hGmove := normalizedSofa_movingWithAngle P hS
    rw [hset] at hGmove
    rw [← hzero, hset, gerver_reduced_angle_eq hP hbox hω hGmove]
    simp [EuclideanClose.refl, symmetricDifferenceArea, area]
  · -- positive deficit: the local estimates apply to the cap of the normalized sofa `N`
    let N := normalizedSofa P S
    have hNmove : IsMovingSofaWithAngle N ω := normalizedSofa_movingWithAngle P hS
    have hNc := ms_isCompact_of_isMovingSofaWithAngle hNmove
    have hNne := hNmove.2.1.nonempty
    have hcompact := ms_isCompact_of_isMovingSofaWithAngle hS
    have htop : supp N (π / 2) = 1 := normalizedSofa_top P hcompact hS.2.1.nonempty
    have hstrip := normalizedSofa_strip P hSmove
    obtain ⟨hclose, hangle⟩ := hentry S ω hS hω eQ
    have hKleft : supp (sofaCap N) π = supp P.cap π := by
      rw [sofaCap_upper_support hNc hNne hstrip htop ⟨pi_pos.le, le_rfl⟩,
        normalizedSofa_left P hcompact hS.2.1.nonempty,
        gerver_upper_support hP hbox ⟨pi_pos.le, le_rfl⟩]
    have hω' : ω ∈ Icc (0 : ℝ) (π / 2) := ⟨(arccos_nonneg _).trans hω.1, hω.2⟩
    have heq : sofaDeficit P S = area (gerverSofa P) - area N := by
      rw [area_normalizedSofa]
      rfl
    obtain ⟨hd, ha⟩ := hlocal (sofaCap N) (sofaCap_isCap hNc hNne hstrip htop) hKleft
      (sofaCap_close_to_gerver hP hbox hNc hNne hstrip htop hclose) N hNc.measurableSet ω hω'
      hangle.le (sofaCap_partial_constraints hNmove hω' htop) (sofaDeficit P S) heq hpositive eL
    exact ⟨hd, harea N hNc (sofaDeficit P S) ⟨hpositive, eA.le⟩ heq hd, sub_nonneg.mpr hω.2,
      ha.trans_eq (one_div_mul_eq_div c _).symm⟩

/-- The stability of Gerver's sofa (`UnrestrictedStability`). Every moving sofa of area at
least `2.2` has rotation angle at least `arccos (5/11)`, so `reduced_sofa_stability` applies. -/
theorem unrestricted_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P := by
  obtain ⟨C, Carea, _, εR, hC, hCarea, -, hεR, hresult⟩ := reduced_sofa_stability hP hbox
  have hgap : 0 < area (gerverSofa P) - 2.2 := by linarith [(gerverSofa_area_mem hP hbox).1]
  refine ⟨C, Carea, min εR (area (gerverSofa P) - 2.2), hC, hCarea, lt_min hεR hgap,
    fun S hS hε => ?_⟩
  have h22 : (2.2 : ℝ) ≤ area S := by
    have he := hε.trans_le (min_le_right _ _)
    unfold sofaDeficit at he
    linarith
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hω' : ω ∈ Icc (arccos (5 / 11 : ℝ)) (π / 2) := by
    simpa only [arcsec22, show (1 / 2.2 : ℝ) = 5 / 11 by norm_num] using hω
  have he := hresult S ω hSω hω' (hε.trans_le (min_le_left _ _))
  exact ⟨he.1, he.2.1⟩

/-- The stability of the rotation angle (`TerminalAngleStability`), from
`reduced_sofa_stability`. -/
theorem terminal_angle_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P := by
  obtain ⟨_, _, Cangle, ε₀, -, -, hCangle, hε₀, hresult⟩ := reduced_sofa_stability hP hbox
  exact ⟨Cangle, ε₀, hCangle, hε₀, fun S ω hS hω hε => (hresult S ω hS hω hε).2.2⟩

end MovingSofaStability
