module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen

/-!
# Removing an interior disk from a connected set

No path connectedness of the original set is assumed. The boundary of the
removed open set connects every possible separation of the remainder. In
dimension two this applies to an interior disk because its circle is connected.
This avoids assuming that a general closed moving sofa has paths between all of
its points.
-/

@[expose] public section

open Set Metric

namespace MovingSofaStability

/-- An open region with connected boundary can be removed from a closed
connected set containing its closure without disconnecting the remainder. -/
theorem preconnected_sdiff_of_connected_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsClosed S) (hconn : IsPreconnected S)
    (hU : IsOpen U) (hcl : closure U ⊆ S) (hF : IsPreconnected (frontier U)) :
    IsPreconnected (S \ U) := by
  let Y := S \ U
  have hY : IsClosed Y := hS.sdiff hU
  have hFY : frontier U ⊆ Y := by
    intro x hx
    refine ⟨hcl (frontier_subset_closure hx), ?_⟩
    have hx' : x ∉ interior U := hx.2
    simpa only [hU.interior_eq] using hx'
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro A B hA hB hcover hdisj
  have hFC : frontier U ⊆ A ∪ B := hFY.trans hcover
  have hFD : frontier U ∩ (A ∩ B) = ∅ := by
    apply subset_empty_iff.mp
    intro x hx
    have hy : x ∈ Y ∩ (A ∩ B) := ⟨hFY hx.1, hx.2⟩
    exact hdisj.subset hy
  have step (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
      (hcover : Y ⊆ A ∪ B) (hdisj : Y ∩ (A ∩ B) = ∅)
      (hFA : frontier U ⊆ A) : Y ⊆ A ∨ Y ⊆ B := by
    let A' := (Y ∩ A) ∪ closure U
    let B' := Y ∩ B
    have hA' : IsClosed A' := (hY.inter hA).union isClosed_closure
    have hB' : IsClosed B' := hY.inter hB
    have hcov' : S ⊆ A' ∪ B' := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl (Or.inr (subset_closure hxU))
      · rcases hcover ⟨hx, hxU⟩ with ha | hb
        · exact Or.inl (Or.inl ⟨⟨hx, hxU⟩, ha⟩)
        · exact Or.inr ⟨⟨hx, hxU⟩, hb⟩
    have hdisj' : S ∩ (A' ∩ B') = ∅ := by
      apply subset_empty_iff.mp
      rintro x ⟨hxS, hxA | hxcl, hxY, hxB⟩
      · have hx : x ∈ Y ∩ (A ∩ B) := ⟨hxA.1, hxA.2, hxB⟩
        exact hdisj.subset hx
      · have hxf : x ∈ frontier U := by
          refine ⟨hxcl, ?_⟩
          simpa only [hU.interior_eq] using hxY.2
        have hx : x ∈ Y ∩ (A ∩ B) := ⟨hxY, hFA hxf, hxB⟩
        exact hdisj.subset hx
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn A' B' hA' hB' hcov' hdisj' with
      h | h
    · left
      intro x hx
      rcases h hx.1 with ha | hclx
      · exact ha.2
      · apply hFA
        refine ⟨hclx, ?_⟩
        simpa only [hU.interior_eq] using hx.2
    · exact Or.inr (fun x hx => (h hx.1).2)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hF A B hA hB hFC hFD with hFA | hFB
  · exact step A B hA hB hcover hdisj hFA
  · have hcover' : Y ⊆ B ∪ A := by simpa only [union_comm] using hcover
    have hdisj' : Y ∩ (B ∩ A) = ∅ := by simpa only [inter_comm A B] using hdisj
    exact (step B A hB hA hcover' hdisj' hFB).symm

/-- Removing a disk contained in a closed connected set preserves connectedness
in any nontrivial real normed space of dimension at least two. -/
theorem connected_sdiff_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (hdim : 1 < Module.rank ℝ E) {S : Set E} (hS : IsClosed S)
    (hconn : IsConnected S) {p : E} {r : ℝ} (hr : 0 < r)
    (hball : closedBall p r ⊆ S) : IsConnected (S \ ball p r) := by
  have hcircle := isConnected_sphere hdim p hr.le
  have hcircleSub : sphere p r ⊆ S \ ball p r := by
    intro q hq
    have he := mem_sphere.mp hq
    exact ⟨hball (mem_closedBall.mpr he.le), fun h => (mem_ball.mp h).ne he⟩
  refine ⟨hcircle.nonempty.mono hcircleSub, ?_⟩
  apply preconnected_sdiff_of_connected_frontier hS hconn.isPreconnected isOpen_ball
  · simpa only [closure_ball p hr.ne'] using hball
  · simpa only [frontier_ball p hr.ne'] using hcircle.isPreconnected

end MovingSofaStability
