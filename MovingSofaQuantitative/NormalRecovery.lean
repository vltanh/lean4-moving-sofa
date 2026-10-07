module

public import MovingSofaQuantitative.ReferenceSector
public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.ActualSetRecovery
public import MovingSofaStability.Recovery
public import MovingSofaUniqueness.RegularClosed

/-!
# Euclidean-normal hallway recovery with coefficient 100/49

UNCOMPILED SOURCE.  This version is deliberately expressed only in terms of
the existing Gerver path/envelope API.  No parallel reference-boundary API is
introduced.

For a point of the reference niche, take a nearest point on the niche envelope.
On the core the nearest direction is orthogonal to
  x'(t) = -a u_t + b v_t,   a,b>0,
so the inward normal is proportional to b u_t + a v_t.  Balancing the test
angle makes both hallway first variations equal to
  sqrt(a^2+b^2)/(a+b) <w,n>,
whose magnitude is at least 1/sqrt(2).  The explicit phase formulas give a
very coarse quadratic remainder below 100 d^2; at d<=10^-8 this leaves the
common coefficient 49/100.  The two envelope tails are easier: one wall is
active and the other has a fixed negative margin.
-/

@[expose] public section
noncomputable section

open Real Set Topology
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def normalViolationCoefficient : ℝ := 49/100
def normalRecoveryDepth : ℝ := 1/(10:ℝ)^8

theorem normalViolationCoefficient_pos : 0<normalViolationCoefficient := by
  norm_num [normalViolationCoefficient]

theorem normalRecoveryDepth_pos : 0<normalRecoveryDepth := by
  unfold normalRecoveryDepth
  positivity

def wallVariationU (t a b : ℝ) (w : Point) (λ : ℝ) : ℝ :=
  dot w (uvec t)+a*λ

def wallVariationV (t a b : ℝ) (w : Point) (λ : ℝ) : ℝ :=
  dot w (vvec t)-b*λ

/-- Algebraic balancing identity used by the normal argument. -/
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
  unfold wallVariationU wallVariationV
  rw [hn]
  have hs : 0<sqrt(a^2+b^2) := Real.sqrt_pos.2 (by positivity)
  have hab : a+b≠0 := ne_of_gt (add_pos ha hb)
  have hsne : sqrt(a^2+b^2)≠0 := ne_of_gt hs
  simp only [dot_smul_right,dot_add_right]
  rw [div_eq_mul_inv]
  field_simp [hab,hsne]
  constructor <;>
    simp [dot_uvec_self,dot_vvec_self,dot_uvec_vvec,dot_vvec_uvec] <;>
    ring

theorem one_div_sqrt_two_le_one : (1/sqrt 2:ℝ)≤1 := by
  have hs : 1≤sqrt 2 := by
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  exact (div_le_one (sqrt_pos.2 (by norm_num : (0:ℝ)<2))).2 hs

theorem balanced_ratio_half {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hab : 0<a+b) :
    1/sqrt 2 ≤ sqrt(a^2+b^2)/(a+b) := by
  have hs := sq_nonneg (a-b)
  have hroot : 0<sqrt(a^2+b^2) := Real.sqrt_pos.2 (by
    nlinarith [hab,ha,hb])
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)) hab]
  nlinarith [sq_sqrt (by positivity : 0≤a^2+b^2),
    sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem balanced_angle_adjustment_le_one {t a b : ℝ} {w : Point}
    (ha : 0≤a) (hb : 0≤b) (hab : 0<a+b)
    (hw : norm2 w≤1) :
    |(dot w (vvec t)-dot w (uvec t))/(a+b)|≤2/(a+b) := by
  have hu:=abs_dot_uvec_le_norm2 w t
  have hv:=abs_dot_vvec_le_norm2 w t
  rw [abs_div]
  have hden : |a+b|=a+b:=abs_of_pos hab
  rw [hden]
  apply (div_le_div_iff₀ hab).2
  nlinarith [hu.trans hw,hv.trans hw]


theorem abs_dot_uvec_le_norm2 (w : Point) (t : ℝ) :
    |dot w (uvec t)|≤norm2 w := by
  rw [abs_le]
  constructor
  · have h:=dot_uvec_le_norm2 (-w) t
    simpa [dot_neg_left] using h
  · exact dot_uvec_le_norm2 w t

theorem abs_dot_vvec_le_norm2 (w : Point) (t : ℝ) :
    |dot w (vvec t)|≤norm2 w := by
  simpa [vvec] using abs_dot_uvec_le_norm2 w (t+π/2)

theorem dot_uvec_sub_le_dist (p q : Point) (t : ℝ) :
    dot (p-q) (uvec t)≤euclideanDist p q := by
  exact (dot_uvec_le_norm2 (p-q) t)

theorem norm2_div (w : Point) {d : ℝ} (hd : 0<d) :
    norm2 (w/d)=norm2 w/d := by
  unfold norm2 dot
  have hd0 : 0≤d:=hd.le
  rw [show ((w/d).1)^2+((w/d).2)^2=(w.1^2+w.2^2)/d^2 by
    simp [div_pow]; ring]
  rw [Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq hd0]
  rfl

theorem exists_mem_eq_infDist {K : Set Point} (hK : IsCompact K)
    {p : Point} (hne : K.Nonempty) :
    ∃q∈K,euclideanDist p q=infDist p K := by
  obtain ⟨q,hq,hmin⟩:=hK.exists_isMinOn hne
    (continuous_const.sub continuous_id |>.norm)
  refine ⟨q,hq,?_⟩
  apply le_antisymm
  · exact le_csInf (Metric.bddBelow_dist p) ⟨q,hq,rfl⟩
  · exact csInf_le (Metric.bddBelow_dist p) ⟨q,hq,rfl⟩

theorem infDist_zero_of_mem {K : Set Point} {p : Point} (hp : p∈K) :
    infDist p K=0 := by
  apply le_antisymm
  · exact (infDist_le_of_mem hp).trans (by rw [euclideanDist_self])
  · exact infDist_nonneg

theorem infDist_pos_of_compact {K : Set Point} (hK : IsCompact K)
    {p : Point} (hp : p∉K) :
    0<infDist p K := by
  by_contra hn
  have hz : infDist p K=0:=le_antisymm (not_lt.mp hn) infDist_nonneg
  obtain ⟨q,hq,hq0⟩:=exists_mem_eq_infDist hK
    (by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty.mp he,infDist_empty] at hz
      exact top_ne_zero hz)
  rw [hz] at hq0
  have hpq:=euclideanDist_eq_zero.mp hq0
  subst q
  exact hp hq

theorem exists_mem_le_infDist {K : Set Point} (hK : IsCompact K)
    (p : Point) :
    ∃q∈K,euclideanDist p q≤infDist p K := by
  by_cases hne : K.Nonempty
  · obtain ⟨q,hq,hEq⟩:=exists_mem_eq_infDist hK hne
    exact ⟨q,hq,hEq.le⟩
  · exfalso
    have he:=Set.not_nonempty_iff_eq_empty.mp hne
    rw [he] at hK
    simpa using hK.nonempty

theorem gerver_path_mem_shape {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
    P.path t∈gerverSofa P := by
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  rw [gerver_shape_eq hP hbox,gerver_niche_envelope hP hbox]
  refine ⟨?_,?_⟩
  · have hx:=gm_innerCorner hP hbox
      ⟨(hB.φ_mem.1.trans_le ht.1).le,by linarith [ht.2,hB.φ_mem.1]⟩
    rw [←hx]
    exact innerCorner_mem_cap (gm_isCap hP hbox)
      ⟨(hB.φ_mem.1.trans_le ht.1).le,by linarith [ht.2,hB.φ_mem.1]⟩
  · intro hn
    obtain ⟨hy,q,hq,hqx,hlt⟩:=hn
    have hself : P.path t∈gerverEnvelope P := by
      unfold gerverEnvelope
      exact Or.inl (Or.inr ⟨t,ht,rfl⟩)
    have hgraph:=env_x₁_strictAnti henv
    have hsame:=env_same_fst_eq henv hself hq hqx
    subst q
    linarith

/-- A nearest point from an exterior point lies on the frontier. -/
theorem nearest_point_frontier {K : Set Point} (hK : IsCompact K)
    {p q : Point} (hp : p∉K) (hq : q∈K)
    (hnear : euclideanDist p q=infDist p K) :
    q∈frontier K := by
  refine ⟨hK.isClosed.mem_closure hq,?_⟩
  intro hqi
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.1 isOpen_interior q hqi
  let z:=q+(min (r/2) (euclideanDist p q/2)/euclideanDist p q)•(p-q)
  have hd:=infDist_pos_of_compact hK hp
  have hzK : z∈K := by
    apply interior_subset
    apply hball
    dsimp [z]
    have hcoef : 0<euclideanDist p q:=by rw [hnear]; exact hd
    have hstep : euclideanDist q z<r := by
      unfold euclideanDist
      simp [norm2_smul,hcoef.ne']
      nlinarith [min_le_left (r/2) (euclideanDist p q/2)]
    exact hstep
  have hcloser : euclideanDist p z<euclideanDist p q := by
    dsimp [z]
    have hcoef : 0<euclideanDist p q:=by rw [hnear]; exact hd
    exact point_toward_distance_lt hcoef hr
  have hmin:=infDist_le_of_mem hzK
  rw [←hnear] at hmin
  exact (not_lt_of_ge hmin) hcloser

/-- For a point in the open niche, a nearest point of the sofa lies on the
niche envelope. -/
theorem nearest_from_niche_lands_on_envelope {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p q : Point}
    (hp : p∈niche P.cap (π/2))
    (hqG : q∈gerverSofa P)
    (hqfront : q∈frontier (gerverSofa P))
    (hnear : euclideanDist p q=infDist p (gerverSofa P)) :
    q∈gerverEnvelope P := by
  have hB:=romik_bounds hP hbox
  have hreg:=gerver_regularClosed hP hbox
  have hN:=gerver_niche_envelope hP hbox
  have hshape:=gerver_shape_eq hP hbox
  have houter : frontier (gerverSofa P)\gerverEnvelope P⊆frontier P.cap := by
    exact frontier_shape_off_envelope hreg hN hshape
  by_contra hn
  have hqOuter:=houter ⟨hqfront,hn⟩
  have hseg:=segment_from_niche_to_outer_crosses_envelope hP hbox hp hqOuter
  obtain ⟨z,hzEnv,hzBetween,hzStrict⟩:=hseg
  have hzG : z∈gerverSofa P:=envelope_subset_shape hP hbox hzEnv
  have hdist:=segment_point_closer hp hqG hzBetween hzStrict
  have hmin:=infDist_le_of_mem hzG
  rw [←hnear] at hmin
  exact (not_lt_of_ge hmin) hdist

/-- A core endpoint cannot be the nearest sofa point to a point of the strict
niche; the adjacent envelope tail gives a closer point. -/
theorem endpoint_not_nearest_from_open_niche {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ}
    (hnear : euclideanDist p (P.path t)=infDist p (gerverSofa P))
    (hend : t=P.φ ∨ t=π/2-P.φ) : False := by
  have hB:=romik_bounds hP hbox
  rcases hend with rfl|rfl
  · obtain ⟨s,hs,hclose⟩:=env_D_closer_than_core_endpoint hP hB hp hnear
    exact (not_lt_of_ge (infDist_le_of_mem
      (envelope_subset_shape hP hbox hs.1))) hclose
  · obtain ⟨s,hs,hclose⟩:=env_B_closer_than_core_endpoint hP hB hp hnear
    exact (not_lt_of_ge (infDist_le_of_mem
      (envelope_subset_shape hP hbox hs.1))) hclose

/-- Orthogonality to the core tangent determines the magnitude of the dot
product with the perpendicular normal. -/
theorem unit_perp_dot_eq_norm {t a b : ℝ} {w : Point}
    (hw : norm2 w=1)
    (hortho : dot w (-a•uvec t+b•vvec t)=0) :
    |dot w (b•uvec t+a•vvec t)|=sqrt(a^2+b^2) := by
  have hcoords:=norm2_sq_in_frame w t
  have hu:=dot w (uvec t)
  have hv:=dot w (vvec t)
  simp only [dot_add_right,dot_smul_right] at hortho ⊢
  rw [←sq_eq_sq₀ (abs_nonneg _) (sqrt_nonneg _)]
  rw [sq_abs,sq_sqrt (by positivity)]
  nlinarith [hcoords]

/-- The inward core normal points into the reference sofa. -/
theorem core_inward_normal_enters_shape {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Ioo P.φ (π/2-P.φ)) :
    ∃r>0,∀s∈Ioc (0:ℝ) r,
      P.path t+s•
        ((P.gs_β t)•uvec t+(-P.gs_α t)•vvec t)∈gerverSofa P := by
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  exact envelope_core_inward_segment hP hbox henv ht

theorem nearest_vector_opposes_inward {K : Set Point}
    {p q n : Point} {d : ℝ}
    (hnear : euclideanDist p q=infDist p K)
    (hin : ∃r>0,∀s∈Ioc (0:ℝ) r,q+s•n∈K)
    (hd : 0<d) (hdEq : d=euclideanDist p q)
    (hnorm : norm2 n>0) :
    dot ((p-q)/d) n≤0 := by
  obtain ⟨r,hr,hin⟩:=hin
  by_contra hp
  have hdot : 0<dot (p-q) n:=by
    rw [←hdEq] at hp
    have:=mul_pos hd (not_le.mp hp)
    simpa [dot_div_left] using this
  let s:=min (r/2) (dot (p-q) n/(2*norm2 n^2))
  have hs : s∈Ioc (0:ℝ) r := by
    constructor
    · dsimp [s]
      positivity
    · exact (min_le_left _ _).trans_lt (by linarith [hr])
  have hK:=hin s hs
  have hcloser : euclideanDist p (q+s•n)<euclideanDist p q := by
    rw [←sq_lt_sq₀ (euclideanDist_nonneg _ _) (euclideanDist_nonneg _ _)]
    unfold euclideanDist
    rw [norm2_sq,norm2_sq]
    simp only [Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
      Prod.fst_smul,Prod.snd_smul]
    have hs2:=sq_nonneg s
    nlinarith [norm2_sq n]
  have hmin:=infDist_le_of_mem hK
  rw [←hnear] at hmin
  exact (not_lt_of_ge hmin) hcloser

/-- Uniform second-order expansion of the two hallway slacks on the core. -/
theorem innerSlackU_balanced_expansion {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t a b d λ : ℝ} {w : Point}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hp : p=P.path t+d•w)
    (hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t) :
    innerSlackU P.cap (t+λ*d) p =
      d*wallVariationU t a b w λ+
        secondOrderWallErrorU P.cap (P.path t) t (t+λ*d) d := by
  subst p
  have hcorner:=gm_innerCorner hP hbox
  exact inner_slack_taylor_U hP hbox ht hcorner hvel

theorem innerSlackV_balanced_expansion {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t a b d λ : ℝ} {w : Point}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hp : p=P.path t+d•w)
    (hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t) :
    innerSlackV P.cap (t+λ*d) p =
      d*wallVariationV t a b w λ+
        secondOrderWallErrorV P.cap (P.path t) t (t+λ*d) d := by
  subst p
  have hcorner:=gm_innerCorner hP hbox
  exact inner_slack_taylor_V hP hbox ht hcorner hvel

def secondOrderWallErrorU (K : Set Point) (q : Point)
    (t s d : ℝ) : ℝ :=
  innerSlackU K s q-
    innerSlackU K t q+
    (s-t)*sin t

def secondOrderWallErrorV (K : Set Point) (q : Point)
    (t s d : ℝ) : ℝ :=
  innerSlackV K s q-
    innerSlackV K t q+
    (s-t)*cos t

/-- Absolute sine/cosine increments are bounded by the angular increment. -/
theorem abs_sin_sub_le (s t : ℝ) : |sin s-sin t|≤|s-t| := by
  exact abs_sub_le_of_lipschitz (Real.lipschitzWith_sin) s t

theorem abs_cos_sub_le (s t : ℝ) : |cos s-cos t|≤|s-t| := by
  exact abs_sub_le_of_lipschitz (Real.lipschitzWith_cos) s t

/-- Tail active-wall bounds.  These are direct one-dimensional nearest-point
conditions on the B and D envelope arcs. -/
theorem active_tail_normal_bound_B {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ} (ht : t∈Icc (π/2-P.θ) (π/2))
    (hnear : euclideanDist p (envB P.path P.gs_α t)=infDist p (gerverSofa P))
    (hd8 : euclideanDist p (envB P.path P.gs_α t)≤normalRecoveryDepth) :
    innerSlackU P.cap t p≤-(49/100)*euclideanDist p (envB P.path P.gs_α t) := by
  have henv:=gn_envHyp hP (romik_bounds hP hbox)
  exact envelope_B_nearest_active_slack hP hbox henv hp ht hnear hd8
    (by norm_num [normalRecoveryDepth])

theorem inactive_tail_margin_B {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ} (ht : t∈Icc (π/2-P.θ) (π/2))
    (hnear : euclideanDist p (envB P.path P.gs_α t)=infDist p (gerverSofa P))
    (hd8 : euclideanDist p (envB P.path P.gs_α t)≤normalRecoveryDepth) :
    innerSlackV P.cap t p≤-(49/100)*euclideanDist p (envB P.path P.gs_α t) := by
  have henv:=gn_envHyp hP (romik_bounds hP hbox)
  exact envelope_B_inactive_margin hP hbox henv hp ht hnear hd8
    (by norm_num [normalRecoveryDepth])

theorem active_tail_normal_bound_D {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ} (ht : t∈Icc (0:ℝ) P.θ)
    (hnear : euclideanDist p (envD P.path P.gs_β t)=infDist p (gerverSofa P))
    (hd8 : euclideanDist p (envD P.path P.gs_β t)≤normalRecoveryDepth) :
    innerSlackV P.cap t p≤-(49/100)*euclideanDist p (envD P.path P.gs_β t) := by
  have henv:=gn_envHyp hP (romik_bounds hP hbox)
  exact envelope_D_nearest_active_slack hP hbox henv hp ht hnear hd8
    (by norm_num [normalRecoveryDepth])

theorem inactive_tail_margin_D {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ} (ht : t∈Icc (0:ℝ) P.θ)
    (hnear : euclideanDist p (envD P.path P.gs_β t)=infDist p (gerverSofa P))
    (hd8 : euclideanDist p (envD P.path P.gs_β t)≤normalRecoveryDepth) :
    innerSlackU P.cap t p≤-(49/100)*euclideanDist p (envD P.path P.gs_β t) := by
  have henv:=gn_envHyp hP (romik_bounds hP hbox)
  exact envelope_D_inactive_margin hP hbox henv hp ht hnear hd8
    (by norm_num [normalRecoveryDepth])

/-- First-order orthogonality at a nearest point on the smooth core. -/
theorem nearest_core_direction {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t : ℝ}
    (ht : t∈Ioo P.φ (π/2-P.φ))
    (hp : p∉gerverSofa P)
    (hnear : euclideanDist p (P.path t)=infDist p (gerverSofa P)) :
    let d:=euclideanDist p (P.path t)
    let w:=(p-P.path t)/d
    d>0 ∧ norm2 w=1 ∧
      dot w (referenceBoundaryVelocity P t)=0 := by
  let q:=P.path t
  let d:=euclideanDist p q
  let w:=(p-q)/d
  have hqG : q∈gerverSofa P := by
    rw [gerver_shape_eq hP hbox]
    exact gerver_path_mem_shape hP hbox ht.le
  have hd : 0<d := by
    dsimp [d]
    exact euclideanDist_pos_of_ne (by
      intro he
      subst p
      exact hp hqG)
  have hw : norm2 w=1 := by
    dsimp [w,d,euclideanDist]
    rw [norm2_div,div_self (ne_of_gt hd)]
  have hder:=gs_hasDerivAt_path' hP t
  have hmin : HasDerivAt
      (fun s=>euclideanDist p (P.path s)^2)
      (-2*dot (p-q) (referenceBoundaryVelocity P t)) t := by
    dsimp [q,referenceBoundaryVelocity]
    convert (norm2_sq_deriv hder p) using 1 <;> ring
  have hzero : deriv (fun s=>euclideanDist p (P.path s)^2) t=0 := by
    apply deriv_eq_zero_of_local_min
    have hlocal : ∀ᶠ s in 𝓝 t,P.path s∈gerverSofa P := by
      have hopen : Ioo P.φ (π/2-P.φ)∈𝓝 t:=Ioo_mem_nhds ht.1 ht.2
      filter_upwards [hopen] with s hs
      rw [gerver_shape_eq hP hbox]
      exact gerver_path_mem_shape hP hbox hs.le
    filter_upwards [hlocal] with s hs
    have hm:=infDist_le_of_mem hs
    rw [←hnear]
    exact sq_le_sq₀ (euclideanDist_nonneg _ _) hm
  rw [hmin.deriv] at hzero
  refine ⟨hd,hw,?_⟩
  dsimp [w]
  rw [dot_div_left]
  field_simp [ne_of_gt hd]
  nlinarith

/-- The nearest direction to the core is the outward unit normal. -/
theorem nearest_core_outward_normal {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t : ℝ}
    (ht : t∈Ioo P.φ (π/2-P.φ))
    (hp : p∉gerverSofa P)
    (hpN : p∈niche P.cap (π/2))
    (hnear : euclideanDist p (P.path t)=infDist p (gerverSofa P)) :
    let a:=-P.gs_α t
    let b:=P.gs_β t
    let d:=euclideanDist p (P.path t)
    let w:=(p-P.path t)/d
    let n:=(b•uvec t+a•vvec t)/sqrt(a^2+b^2)
    dot w n≤-1 := by
  dsimp
  have hB:=romik_bounds hP hbox
  have ha : 0<-P.gs_α t := neg_pos.mpr
    (gs_α_neg hP hB (by linarith [ht.1,hB.φ_mem.1]) ht.2.le)
  have hb : 0<P.gs_β t := gs_β_pos hP hB ht.1.le
    (by linarith [ht.2,hB.φ_mem.1])
  obtain ⟨hd,hw,hortho⟩:=nearest_core_direction hP hbox ht hp hnear
  have hvel:=referenceBoundaryVelocity_eq hP t
  rw [hvel] at hortho
  have hnormal : |dot ((p-P.path t)/euclideanDist p (P.path t))
      ((P.gs_β t)•uvec t+(-P.gs_α t)•vvec t)|
      =sqrt((-P.gs_α t)^2+(P.gs_β t)^2) := by
    exact unit_perp_dot_eq_norm hw hortho
      (by
        rw [hvel]
        abel)
  have hsign : dot ((p-P.path t)/euclideanDist p (P.path t))
      ((P.gs_β t)•uvec t+(-P.gs_α t)•vvec t)<0 := by
    -- The niche is the side below the envelope; a short inward displacement
    -- along this normal stays in Gerver's sofa, so the nearest exterior vector
    -- must point in the opposite direction.
    have hinside:=core_inward_normal_enters_shape hP hbox ht hpN
    exact nearest_vector_opposes_inward hnear hinside hd
  rw [dot_div_right]
  have hs : 0<sqrt((-P.gs_α t)^2+(P.gs_β t)^2):=by positivity
  have habs:=abs_of_neg hsign
  rw [habs] at hnormal
  field_simp [ne_of_gt hs]
  nlinarith

/-- Explicit quadratic Taylor remainder for both balanced hallway slacks on the
core.  The constant 100 is intentionally crude; the five Gerver phase formulas
and the Romik parameter box give much smaller values. -/
theorem core_balanced_slack_remainder {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t d λ : ℝ} (ht : t∈Icc P.φ (π/2-P.φ))
    (hd : 0≤d) (hd8 : d≤normalRecoveryDepth)
    (hλ : |λ|≤4) :
    let q:=P.path t
    let s:=t+λ*d
    let p:=(q.1,q.2) -- base point only; the direction term is supplied separately below
    |secondOrderWallErrorU P.cap q t s d|≤100*d^2 ∧
    |secondOrderWallErrorV P.cap q t s d|≤100*d^2 := by
  have hB:=romik_bounds hP hbox
  rcases gs_cases (P:=P) t with h1|h2|h3|h4|h5
  all_goals
    have hstep : |s-t|≤4*d := by
      dsimp
      rw [abs_mul]
      nlinarith [abs_nonneg λ]
    have hsmall : |s-t|≤1/(10:ℝ)^7 := by
      unfold normalRecoveryDepth at hd8
      nlinarith
    simp only
    all_goals
      first
      | rw [gs_pathD_eq_phase hP h1]
      | rw [gs_pathD_eq_phase hP h2]
      | rw [gs_pathD_eq_phase hP h3]
      | rw [gs_pathD_eq_phase hP h4]
      | rw [gs_pathD_eq_phase hP h5]
    all_goals
      have hsine:=abs_sin_sub_le s t
      have hcosine:=abs_cos_sub_le s t
      norm_num at *
      nlinarith

/-- Core normal estimate with the common 49/100 coefficient. -/
theorem core_normal_slack_49 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t : ℝ}
    (ht : t∈Ioo P.φ (π/2-P.φ))
    (hp : p∉gerverSofa P) (hpN : p∈niche P.cap (π/2))
    (hnear : euclideanDist p (P.path t)=infDist p (gerverSofa P))
    (hd8 : euclideanDist p (P.path t)≤normalRecoveryDepth) :
    ∃s∈Ioo (0:ℝ) (π/2),
      innerSlackU P.cap s p≤-(49/100)*euclideanDist p (P.path t) ∧
      innerSlackV P.cap s p≤-(49/100)*euclideanDist p (P.path t) := by
  let a:=-P.gs_α t
  let b:=P.gs_β t
  let d:=euclideanDist p (P.path t)
  let w:=(p-P.path t)/d
  have hB:=romik_bounds hP hbox
  have ha : 0<a:=by dsimp [a]; exact neg_pos.mpr
    (gs_α_neg hP hB (by linarith [ht.1]) ht.2.le)
  have hb : 0<b:=by dsimp [b]; exact
    gs_β_pos hP hB ht.1.le (by linarith [ht.2])
  obtain ⟨hd,hw,hortho⟩:=nearest_core_direction hP hbox ht hp hnear
  let n:=(b•uvec t+a•vvec t)/sqrt(a^2+b^2)
  have hout : dot w n≤-1 :=
    nearest_core_outward_normal hP hbox ht hp hpN hnear
  let λ:=(dot w (vvec t)-dot w (uvec t))/(a+b)
  have hλ : |λ|≤4 := by
    have hab : 0<a+b:=add_pos ha hb
    have hraw:=balanced_angle_adjustment_le_one (t:=t) ha.le hb.le hab hw.le
    have hablo : 1/2≤a+b := by
      have htr:=gerver_core_transversality hP hbox ht.le
      obtain ⟨a',b',ha',hb',hvel,htrans⟩:=htr
      have heq : a=a'∧b=b':=by
        have hv:=referenceBoundaryVelocity_eq hP t
        rw [hv] at hvel
        dsimp [a,b]
        have hu:=congrArg (fun z=>dot z (uvec t)) hvel
        have hvv:=congrArg (fun z=>dot z (vvec t)) hvel
        simp [dot_add_left,dot_smul_left] at hu hvv
        constructor <;> linarith
      nlinarith [ha,hb,heq.1,heq.2,htrans,
        sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2,pi_pos]),
        cos_nonneg_of_mem_Icc ⟨by linarith [ht.1,pi_pos],ht.2.le⟩]
    dsimp [λ] at *
    nlinarith
  let s:=t+λ*d
  have hs : s∈Ioo (0:ℝ) (π/2) := by
    have hφ:=hB.φ_mem.1
    have hshift : |λ*d|≤4*normalRecoveryDepth := by
      rw [abs_mul]
      have hd0 : 0≤d:=hd.le
      have habsd : |d|=d:=abs_of_nonneg hd0
      rw [habsd]
      exact mul_le_mul hλ hd8 (abs_nonneg _) (by norm_num)
    unfold normalRecoveryDepth at hshift
    constructor <;> nlinarith [ht.1,ht.2,hφ,neg_abs_le (λ*d),le_abs_self (λ*d)]
  have hfirst:=balanced_wall_first_variation ha hb
    (show n=(b•uvec t+a•vvec t)/sqrt(a^2+b^2) by rfl)
  have hratio:=balanced_ratio_half ha.le hb.le (add_pos ha hb)
  have hlead : wallVariationU t a b w λ≤-1/sqrt 2 ∧
      wallVariationV t a b w λ≤-1/sqrt 2 := by
    dsimp [λ] at hfirst
    rw [hfirst.1,hfirst.2]
    constructor <;>
      exact mul_le_mul_of_nonneg_left hout
        (div_nonneg (sqrt_nonneg _) (add_pos ha hb).le) |>.trans
          (by nlinarith [hratio])
  have hrem:=core_balanced_slack_remainder hP hbox ht.le hd.le hd8 hλ
  have hgap : (49/100:ℝ)+100*normalRecoveryDepth<1/sqrt 2 := by
    have hs2:=sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hspos:=sqrt_pos.2 (by norm_num : (0:ℝ)<2)
    unfold normalRecoveryDepth
    nlinarith
  refine ⟨s,hs,?_,?_⟩
  · have hexp:=innerSlackU_balanced_expansion hP hbox ht.le hpN hnear
      (a:=a) (b:=b) (w:=w) (λ:=λ)
    nlinarith [hlead.1,hrem.1,hd8,mul_nonneg hd.le hd8]
  · have hexp:=innerSlackV_balanced_expansion hP hbox ht.le hpN hnear
      (a:=a) (b:=b) (w:=w) (λ:=λ)
    nlinarith [hlead.2,hrem.2,hd8,mul_nonneg hd.le hd8]

/-- Tail points of the envelope have one active wall with normal coefficient at
least one half and the other wall has a fixed negative margin.  At the tiny
normal-recovery depth this gives the same 49/100 coefficient. -/
theorem tail_normal_slack_49 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p q : Point}
    (hp : p∈niche P.cap (π/2))
    (hq : q∈gerverEnvelope P)
    (htail : q∉P.path '' Icc P.φ (π/2-P.φ))
    (hnear : euclideanDist p q=infDist p (gerverSofa P))
    (hd8 : euclideanDist p q≤normalRecoveryDepth) :
    ∃t∈Ioo (0:ℝ) (π/2),
      innerSlackU P.cap t p≤-(49/100)*euclideanDist p q ∧
      innerSlackV P.cap t p≤-(49/100)*euclideanDist p q := by
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  rcases hq with (⟨t,ht,rfl⟩|⟨t,ht,rfl⟩)|⟨t,ht,rfl⟩
  · -- B tail
    refine ⟨t,⟨by linarith [ht.1,hB.θ_mem.2],by
      by_contra he
      have :=env_B_snd_end henv ht he
      nlinarith⟩,?_,?_⟩
    · exact active_tail_normal_bound_B hP hbox hp hnear hd8 ht
    · exact inactive_tail_margin_B hP hbox hp hnear hd8 ht
  · exact False.elim (htail ⟨t,ht,rfl⟩)
  · refine ⟨t,⟨by
      by_contra he
      have :=env_D_snd_end henv ht he
      nlinarith,by linarith [ht.2,hB.θ_mem.2,pi_pos]⟩,?_,?_⟩
    · exact inactive_tail_margin_D hP hbox hp hnear hd8 ht
    · exact active_tail_normal_bound_D hP hbox hp hnear hd8 ht

/-- Every point of the Gerver niche within 10^-8 of the sofa violates both
reference hallway inequalities by at least 49/100 times its Euclidean distance
to the sofa. -/
theorem gerver_niche_normal_slack_explicit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀p∈niche P.cap (π/2),
      0<infDist p (gerverSofa P) →
      infDist p (gerverSofa P)≤normalRecoveryDepth →
      ∃t∈Ioo (0:ℝ) (π/2),
        innerSlackU P.cap t p≤-(49/100)*infDist p (gerverSofa P) ∧
        innerSlackV P.cap t p≤-(49/100)*infDist p (gerverSofa P) := by
  intro p hp hd hd8
  have hGc:=ms_isCompact_of_isMovingSofaWithAngle
    (gm_movingSofa_std hP hbox).1
  obtain ⟨q,hqG,hnear⟩:=exists_mem_eq_infDist hGc hp.1
  have hqfront : q∈frontier (gerverSofa P) := by
    exact nearest_point_frontier hGc hp.1 hqG hnear
  have henv : q∈gerverEnvelope P := by
    -- Since p lies in the open niche, a nearest sofa point cannot lie on the
    -- outer cap boundary.  The regular-closed description therefore puts it on
    -- the niche envelope.
    rw [gerver_shape_eq hP hbox] at hqG
    have hn:=gerver_niche_envelope hP hbox
    exact nearest_from_niche_lands_on_envelope hP hbox hp hqG hqfront hnear
  by_cases hcore : q∈P.path '' Icc P.φ (π/2-P.φ)
  · obtain ⟨t,ht,rfl⟩:=hcore
    have htI : t∈Ioo P.φ (π/2-P.φ) := by
      refine ⟨ht.1.lt_of_ne ?_,ht.2.lt_of_ne ?_⟩
      · intro he
        subst t
        exact endpoint_not_nearest_from_open_niche hP hbox hp hnear Or.inl
      · intro he
        subst t
        exact endpoint_not_nearest_from_open_niche hP hbox hp hnear Or.inr
    simpa [hnear] using core_normal_slack_49 hP hbox htI
      (by
        intro hmem
        rw [hnear] at hd
        exact lt_irrefl 0 (hd.trans_le (infDist_zero_of_mem hmem)))
      hp hnear (by simpa [hnear] using hd8)
  · obtain ⟨t,ht,hU,hV⟩:=tail_normal_slack_49 hP hbox hp henv hcore
      hnear (by simpa [hnear] using hd8)
    exact ⟨t,ht,by simpa [hnear] using hU,by simpa [hnear] using hV⟩

theorem gerver_normal_slack_reserve {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃d₀ : ℝ,0<d₀ ∧
      ∀p∈niche P.cap (π/2),
      0<infDist p (gerverSofa P) →
      infDist p (gerverSofa P)≤d₀ →
      ∃t∈Ioo (0:ℝ) (π/2),
        innerSlackU P.cap t p≤-normalViolationCoefficient*infDist p (gerverSofa P) ∧
        innerSlackV P.cap t p≤-normalViolationCoefficient*infDist p (gerverSofa P) := by
  refine ⟨normalRecoveryDepth,normalRecoveryDepth_pos,?_⟩
  intro p hp hd hd8
  simpa [normalViolationCoefficient] using
    gerver_niche_normal_slack_explicit hP hbox p hp hd hd8

/-- If K is delta-close to the reference cap and p∈K lies outside the
reference cap, then p is already delta-close to Gerver's sofa.  Otherwise a
delta-nearest point of the reference cap would lie in the niche, whose uniform
outer support margin would force p back into the reference cap. -/
theorem outside_reference_cap_close_to_sofa {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2))
    {δ : ℝ} (hδ : 0≤δ)
    (hclose : UpperSupportClose δ K P.cap)
    {douter : ℝ} (hdouter : 0<douter)
    (houter : ∀q∈niche P.cap (π/2),∀t∈Icc (0:ℝ) π,
      douter≤supp P.cap t-dot q (uvec t))
    (hsmall : δ<douter)
    {p : Point} (hpK : p∈K) (hp0 : p∉P.cap) :
    ∃q∈gerverSofa P,euclideanDist p q≤δ := by
  have hE:=upperSupportClose_euclidean hδ hK (gm_isCap hP hbox) hclose
  obtain ⟨q,hq,hpq⟩:=hE.1 p hpK
  by_cases hqN : q∈niche P.cap (π/2)
  · have hpHalf : ∀t∈Icc (0:ℝ) π,dot p (uvec t)≤supp P.cap t := by
      intro t ht
      have hg:=houter q hqN t ht
      have hd:=dot_uvec_sub_le_dist p q t
      nlinarith [hpq,hsmall]
    have hfloor : 0≤p.2:=hK.snd_nonneg hpK
    exact False.elim (hp0 ((cap_mem_iff_upper (gm_isCap hP hbox) p).2
      ⟨hfloor,hpHalf⟩))
  · exact ⟨q,by rw [←gerver_shape_eq hP hbox]; exact ⟨hq,hqN⟩,hpq⟩

/-- Forward recovery for the actual possibly nonconvex competitor. -/
theorem directed_to_gerver_normal {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃δ₀ ζ₀ : ℝ,0<δ₀ ∧ 0<ζ₀ ∧
      ∀K : Set Point,IsCap K (π/2) →
      ∀δ,0≤δ → δ≤δ₀ → UpperSupportClose δ K P.cap →
      ∀S : Set Point,S⊆K →
      ∀ζ,0≤ζ → ζ≤ζ₀ → ApproxHallways K S ζ →
      DirectedClose ((100/49)*(δ+ζ)) S (gerverSofa P) := by
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  obtain ⟨douter,hdouter,houter⟩:=hroof.outer_margin
  let δ₀:=min (douter/2) ((49/200)*normalRecoveryDepth)
  let ζ₀:=(49/200)*normalRecoveryDepth
  refine ⟨δ₀,ζ₀,lt_min (by positivity) (by positivity),by positivity,?_⟩
  intro K hK δ hδ hδsmall hclose S hSK ζ hζ hζsmall hhall p hp
  by_cases hp0 : p∈P.cap
  · by_cases hpG : p∈gerverSofa P
    · exact ⟨p,hpG,by
        rw [euclideanDist_self]
        positivity⟩
    · have hpN : p∈niche P.cap (π/2):=by
        rw [←gerver_shape_eq hP hbox] at hpG
        exact Classical.byContradiction fun hn=>hpG ⟨hp0,not_not.mp hn⟩
      let d:=infDist p (gerverSofa P)
      have hd : 0<d:=infDist_pos_of_compact
        (ms_isCompact_of_isMovingSofaWithAngle (gm_movingSofa_std hP hbox).1)
        hpG
      by_cases hdbig : normalRecoveryDepth<d
      · have hsum : δ+ζ<(49/100)*d := by
          have hδb:=δsmall.trans (min_le_right _ _)
          dsimp [ζ₀] at ζsmall
          nlinarith
        obtain ⟨t,ht,hU,hV⟩:=gerver_niche_normal_slack_explicit hP hbox p hpN hd
          (by linarith [hdbig])
        exact False.elim (normal_violation_excludes ht hclose hU hV hsum
          (by
            have hf:=hhall p hp t ht
            simpa [max_le_iff] using hf))
      · have hd8 : d≤normalRecoveryDepth:=not_lt.mp hdbig
        obtain ⟨t,ht,hU,hV⟩:=gerver_niche_normal_slack_explicit hP hbox p hpN hd hd8
        have hfeas:=hhall p hp t ht
        have hbound : d≤(100/49)*(δ+ζ) := by
          by_contra hn
          have hgap : δ+ζ<(49/100)*d := by nlinarith
          exact normal_violation_excludes ht hclose hU hV hgap
            (by simpa [max_le_iff] using hfeas)
        obtain ⟨q,hq,hqdist⟩:=exists_mem_le_infDist
          (ms_isCompact_of_isMovingSofaWithAngle
            (gm_movingSofa_std hP hbox).1) p
        exact ⟨q,hq,hqdist.trans hbound⟩
  · obtain ⟨q,hq,hpq⟩:=outside_reference_cap_close_to_sofa hP hbox hK
      hδ hclose hdouter houter
      (hδsmall.trans_lt (min_le_left _ _ |>.trans_lt (half_lt_self hdouter)))
      hp hp0
    exact ⟨q,hq,hpq.trans (by
      have hfactor : 1≤(100/49:ℝ):=by norm_num
      have hsum : δ≤δ+ζ:=by linarith
      nlinarith)⟩

end MovingSofaQuantitative
