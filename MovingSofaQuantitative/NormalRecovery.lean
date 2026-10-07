module

public import MovingSofaQuantitative.ReferenceSector
public import MovingSofaQuantitative.ActualSetRecovery
public import MovingSofaStability.Recovery

/-!
# Euclidean-normal hallway recovery with coefficient 100/49

UNCOMPILED SOURCE.  The witness angle depends on the nearest-point direction,
not on a fixed vertical coordinate.  Only Gerver's reference boundary is
differentiated.
-/

@[expose] public section
noncomputable section

open Real Set Topology
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def normalViolationCoefficient : ℝ := 49/100

theorem normalViolationCoefficient_pos : 0<normalViolationCoefficient := by
  norm_num [normalViolationCoefficient]

/-- Algebraic first variation of the two inner walls after balancing the test
angle. -/
theorem balanced_wall_first_variation
    {t a b : ℝ} {w n : Point}
    (ha : 0<a) (hb : 0<b)
    (hn : n=(b•uvec t+a•vvec t)/sqrt(a^2+b^2)) :
    let λ := (dot w (vvec t)-dot w (uvec t))/(a+b)
    wallVariationU t a b w λ =
      sqrt(a^2+b^2)/(a+b)*dot w n ∧
    wallVariationV t a b w λ =
      sqrt(a^2+b^2)/(a+b)*dot w n := by
  dsimp
  rw [hn]
  have hs : 0<sqrt(a^2+b^2) := Real.sqrt_pos.2 (by positivity)
  field_simp [ne_of_gt (add_pos ha hb),ne_of_gt hs]
  constructor <;>
    simp [wallVariationU,wallVariationV,dot_add_right,dot_smul_right,
      dot_uvec_self,dot_vvec_self,dot_uvec_vvec,dot_vvec_uvec] <;>
    ring

theorem balanced_ratio_half {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    1/sqrt 2 ≤ sqrt(a^2+b^2)/(a+b) := by
  rcases ha.eq_or_lt with rfl|ha' <;>
    rcases hb.eq_or_lt with rfl|hb'
  · norm_num
  · simp only [zero_pow,zero_add,zero_add,sqrt_sq hb'.le,div_self hb'.ne']
    exact one_div_sqrt_two_le_one
  · simp only [zero_pow,add_zero,add_zero,sqrt_sq ha'.le,div_self ha'.ne']
    exact one_div_sqrt_two_le_one
  · have hs := sq_nonneg (a-b)
    have hab : 0<a+b := add_pos ha' hb'
    have hroot : 0<sqrt(a^2+b^2) := Real.sqrt_pos.2 (by positivity)
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)) hab]
    nlinarith [sq_sqrt (by positivity : 0≤a^2+b^2),
      sq_sqrt (by norm_num : (0:ℝ)≤2)]

/-- A nearest exterior direction at a regular reference point is the negative
unit inward normal. At a corner, one incident inward normal has cosine at
least 1/sqrt(2). -/
theorem nearest_direction_reference_normal {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p q : Point} (hp : p∉gerverSofa P) (hq : q∈gerverSofa P)
    (hnear : euclideanDist p q = infDist p (gerverSofa P)) :
    ∃ t∈Icc (0:ℝ) (π/2), ∃ n : Point,
      referenceInwardNormal P t=n ∧
      dot ((p-q)/euclideanDist p q) n ≤ -1/sqrt 2 := by
  obtain hreg|hcorner := reference_nearest_regular_or_corner hP hbox hp hq hnear
  · refine ⟨hreg.t,hreg.ht,referenceInwardNormal P hreg.t,rfl,?_⟩
    rw [hreg.direction]
    simp [dot_smul_left,referenceInwardNormal_unit]
    exact neg_le_neg one_div_sqrt_two_le_one
  · obtain ⟨n,hnmem,hcos⟩ := corner_normal_choice hcorner
    exact ⟨hnmem.angle,hnmem.interval,n,hnmem.eq,hcos⟩

/-- Uniform nonlinear reserve.  Reference derivatives are Lipschitz on each
phase and one-sided derivatives agree at the C1 junctions, so the first-order
coefficient 1/2 can be reduced to 49/100 on one common depth. -/
theorem gerver_normal_slack_reserve {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ d₀ : ℝ, 0<d₀ ∧
      ∀ p∉gerverSofa P, ∀q∈gerverSofa P,
      euclideanDist p q=infDist p (gerverSofa P) →
      0<euclideanDist p q → euclideanDist p q≤d₀ →
      ∃t∈Ioo (0:ℝ) (π/2),
        innerSlackU P.cap t p ≤ -normalViolationCoefficient*euclideanDist p q ∧
        innerSlackV P.cap t p ≤ -normalViolationCoefficient*euclideanDist p q := by
  obtain ⟨R,hR,hvel,hLip⟩ := gerver_reference_velocity_bounds hP hbox
  let d₀ := min (1/1000000:ℝ) (1/(1000*(R+1)))
  refine ⟨d₀,lt_min (by norm_num) (by positivity),?_⟩
  intro p hp q hq hnear hd hsmall
  obtain ⟨t,ht,n,hn,hdir⟩ :=
    nearest_direction_reference_normal hP hbox hp hq hnear
  obtain ⟨a,b,ha,hb,hvelEq⟩ := reference_core_velocity_decomposition hP hbox t ht
  let w := (p-q)/euclideanDist p q
  let λ := (dot w (vvec t)-dot w (uvec t))/(a+b)
  have hfirst := balanced_wall_first_variation ha hb
    (reference_normal_formula hP hbox t ht hvelEq)
  have hratio := balanced_ratio_half ha.le hb.le
  have hlead : sqrt(a^2+b^2)/(a+b)*dot w n ≤ -1/2 := by
    have hm := mul_le_mul_of_nonneg_left hdir (by positivity)
    nlinarith [hratio]
  let s := t+λ*euclideanDist p q
  have hs : s∈Ioo (0:ℝ) (π/2) := by
    have hλ : |λ|≤1 := balanced_angle_adjustment_le_one ha hb
    dsimp [s,d₀] at *
    exact reference_phase_interior_after_adjustment ht hλ hsmall
  refine ⟨s,hs,?_,?_⟩
  · have hr := wallVariationU_remainder hP hbox t s p q hnear hLip hsmall
    unfold normalViolationCoefficient
    nlinarith [hlead]
  · have hr := wallVariationV_remainder hP hbox t s p q hnear hLip hsmall
    unfold normalViolationCoefficient
    nlinarith [hlead]

/-- Forward recovery for the actual possibly nonconvex competitor.  The outer
cap layer is handled by support distance; points in the reference cap but
outside Gerver use the normal hallway witness. -/
theorem directed_to_gerver_normal {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ₀ ζ₀ : ℝ, 0<δ₀ ∧ 0<ζ₀ ∧
      ∀ K : Set Point, IsCap K (π/2) →
      ∀ δ, 0≤δ → δ≤δ₀ → UpperSupportClose δ K P.cap →
      ∀ S : Set Point, S⊆K →
      ∀ ζ, 0≤ζ → ζ≤ζ₀ → ApproxHallways K S ζ →
      DirectedClose ((100/49)*(δ+ζ)) S (gerverSofa P) := by
  obtain ⟨d₀,hd₀,hreserve⟩ := gerver_normal_slack_reserve hP hbox
  obtain ⟨H,L,γ,hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨douter,hdouter,houter⟩ := hroof.outer_margin
  let δ₀:=min (douter/4) (normalViolationCoefficient*d₀/4)
  let ζ₀:=normalViolationCoefficient*d₀/4
  refine ⟨δ₀,ζ₀,lt_min (by positivity) (by positivity),by positivity,?_⟩
  intro K hK δ hδ hδsmall hclose S hSK ζ hζ hζsmall hhall p hp
  by_cases hpG : p∈gerverSofa P
  · exact ⟨p,hpG,by
      have hrad : 0≤(100/49)*(δ+ζ) := by positivity
      simpa using hrad⟩
  let q := nearestPoint (gerverSofa P) p
  have hq := nearestPoint_mem (gerver_compact hP hbox) hpG
  have hnear := nearestPoint_dist (gerver_compact hP hbox) hpG
  let d:=euclideanDist p q
  by_cases hdlarge : d₀<d
  · have houterCap := point_far_from_shape_gives_cap_support_gap
      hP hbox hroof hpG hq hnear hdlarge
    have hKp := hSK hp
    have hsupport := cap_close_from_support hK hroof.cap hδ hclose
    have : d≤(100/49)*(δ+ζ) := by
      exfalso
      exact houterCap (hδsmall.trans (min_le_left _ _)) hsupport hKp
    exact ⟨q,hq,this⟩
  · have hdpos : 0<d := by
      dsimp [d]
      exact euclideanDist_pos_of_ne (by intro he; subst q; exact hpG hq)
    obtain ⟨t,ht,hU,hV⟩ := hreserve p hpG q hq hnear hdpos (not_lt.mp hdlarge)
    have hfeas := hhall p hp t ⟨ht.1.le,ht.2.le⟩
    have hgap : δ+ζ<normalViolationCoefficient*d := by
      by_contra hn
      have : d≤(δ+ζ)/normalViolationCoefficient := by
        rw [le_div_iff₀ normalViolationCoefficient_pos]
        exact not_lt.mp hn
      exact False.elim (by nlinarith [hδsmall,hζsmall])
    exact (normal_violation_excludes ht hclose hU hV hgap hfeas).elim

end MovingSofaQuantitative
