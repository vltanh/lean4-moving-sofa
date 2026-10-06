module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen

/-!
# Removing an interior disk from a connected set

Uncompiled proof source. No path connectedness of the original set is assumed.
The boundary of the removed open set connects every possible separation of the
remainder. In dimension two this applies to an interior disk because its circle
is connected. This avoids assuming that a general closed moving sofa has paths
between all of its points.
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
  sorry

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
