module

public import MovingSofaStability.SymmetricDifference
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Limits of actual compact sets

The hyperspace here contains all nonempty compact sets, not only convex bodies.
Its ordinary product-metric Hausdorff distance is used only for topology;
Euclidean witnesses are recovered with factor two. Area is upper semicontinuous,
not asserted continuous.
-/

@[expose] public section
noncomputable section

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
