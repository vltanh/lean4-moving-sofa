module

public import MovingSofaQuantitative.OrthogonalErosion

/-!
# Actual-set recovery by missing area

Uncompiled proof source. The comparison set need not be convex, and the sofa
need not be contained in the full-angle envelope. A whole measurable recovery
region, rather than a single small disk, can pay for a missing point.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- If every reference point has more available nearby area than the total
missing area, every reference point is close to the actual sofa. -/
theorem directedClose_of_available_area {S U G : Set Point} {ρ m : ℝ}
    (hUf : volume U ≠ ⊤) (hmissing : area (U \ S) ≤ m)
    (hregions : ∀ p ∈ G, ∃ R : Set Point,
      R ⊆ U ∧ (∀ q ∈ R, euclideanDist p q ≤ ρ) ∧ m < area R) :
    DirectedClose ρ G S := by
  intro p hp
  obtain ⟨R, hRU, hRρ, harea⟩ := hregions p hp
  by_contra hn
  have hsub : R ⊆ U \ S := by
    intro q hq
    refine ⟨hRU hq, ?_⟩
    intro hqS
    exact hn ⟨q, hqS, hRρ q hq⟩
  have hfinite : volume (U \ S) ≠ ⊤ := volume_ne_top_of_subset sdiff_subset hUf
  have hmono : area R ≤ area (U \ S) :=
    ENNReal.toReal_mono hfinite (measure_mono hsub)
  exact (not_lt_of_ge (hmono.trans hmissing)) harea

/-- An interior wedge, truncated at a fixed Euclidean radius. The two normals
point into the wedge; an aperture of `2*h` has normals at `theta +/- (pi/2-h)`. -/
def interiorSector (p : Point) (θ h R : ℝ) : Set Point :=
  {q | 0 ≤ dot (q - p) (uvec (θ + (π / 2 - h))) ∧
       0 ≤ dot (q - p) (uvec (θ - (π / 2 - h))) ∧
       euclideanDist p q ≤ R}

/-- The whole truncated wedge whose two side distances are at least r. -/
def erodedSector (p : Point) (θ h r ρ : ℝ) : Set Point :=
  {q | r ≤ dot (q - p) (uvec (θ + (π / 2 - h))) ∧
       r ≤ dot (q - p) (uvec (θ - (π / 2 - h))) ∧
       euclideanDist p q ≤ ρ}

theorem erodedSector_isClosed (p : Point) (θ h r ρ : ℝ) :
    IsClosed (erodedSector p θ h r ρ) := by
  apply (isClosed_le continuous_const (by unfold dot uvec; fun_prop)).inter
  exact (isClosed_le continuous_const (by unfold dot uvec; fun_prop)).inter
    (isClosed_le (by unfold euclideanDist norm2 dot; fun_prop) continuous_const)

/-- Every point of the eroded wedge has its entire radius-r disk in the
original sector, provided the outer circular boundary also has r clearance. -/
theorem erodedSector_subset_erosion {G : Set Point} {p : Point} {θ h r ρ R : ℝ}
    (hr : 0 ≤ r) (hscale : ρ + r ≤ R)
    (hsector : interiorSector p θ h R ⊆ G) :
    erodedSector p θ h r ρ ⊆ euclideanErosion r G := by
  intro q hq z hz
  apply hsector
  refine ⟨?_, ?_, ?_⟩
  · have hv := dot_uvec_le_norm2 (q - z) (θ + (π / 2 - h))
    have he : dot (z - p) (uvec (θ + (π / 2 - h))) =
        dot (q - p) (uvec (θ + (π / 2 - h))) - dot (q - z) (uvec (θ + (π / 2 - h))) := by
      rw [← dot_sub_left]
      congr 1
      abel
    have hd : norm2 (q - z) ≤ r := hz
    rw [he]
    linarith [hq.1]
  · have hv := dot_uvec_le_norm2 (q - z) (θ - (π / 2 - h))
    have he : dot (z - p) (uvec (θ - (π / 2 - h))) =
        dot (q - p) (uvec (θ - (π / 2 - h))) - dot (q - z) (uvec (θ - (π / 2 - h))) := by
      rw [← dot_sub_left]
      congr 1
      abel
    have hd : norm2 (q - z) ≤ r := hz
    rw [he]
    linarith [hq.2.1]
  · exact (euclideanDist_triangle p q z).trans ((add_le_add hq.2.2 hz).trans hscale)

/-- A generic sector-content criterion, directly for the original missing set.
The later reference-chart and polar-area theorems provide its two geometric
inputs; no Hausdorff conclusion is one of its hypotheses. -/
theorem directedClose_of_sector_content {S U G : Set Point} {h r ρ R m : ℝ}
    (hUf : volume U ≠ ⊤) (hr : 0 ≤ r) (hscale : ρ + r ≤ R)
    (herosion : euclideanErosion r G ⊆ U) (hmissing : area (U \ S) ≤ m)
    (hcones : ∀ p ∈ G, ∃ θ : ℝ, interiorSector p θ h R ⊆ G)
    (hcontent : ∀ p ∈ G, ∀ θ : ℝ, m < area (erodedSector p θ h r ρ)) :
    DirectedClose ρ G S := by
  apply directedClose_of_available_area hUf hmissing
  intro p hp
  obtain ⟨θ, hθ⟩ := hcones p hp
  exact ⟨erodedSector p θ h r ρ,
    (erodedSector_subset_erosion hr hscale hθ).trans herosion,
    fun q hq => hq.2.2, hcontent p hp θ⟩

/-- A strict slack violation excludes a point from an approximately feasible
competitor. This is the logical end of the normal-witness argument. -/
theorem normal_violation_excludes {K K₀ : Set Point} {p : Point} {t δ ζ c d : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) (hclose : UpperSupportClose δ K K₀)
    (hU : innerSlackU K₀ t p ≤ -c * d) (hV : innerSlackV K₀ t p ≤ -c * d)
    (hgap : δ + ζ < c * d)
    (hfeasible : -ζ ≤ innerSlackU K t p ∨ -ζ ≤ innerSlackV K t p) : False := by
  have hsu := (abs_le.mp (hclose t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩)).1
  have hsv := (abs_le.mp (hclose (t + π / 2)
    ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩)).1
  rcases hfeasible with hf | hf
  · unfold innerSlackU at hU hf
    linarith
  · unfold innerSlackV at hV hf
    linarith

end MovingSofaQuantitative
