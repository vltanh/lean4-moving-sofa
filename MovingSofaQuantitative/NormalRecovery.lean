module

public import MovingSofaQuantitative.ReferenceSector
public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.ActualSetRecovery
public import MovingSofaStability.Recovery
public import MovingSofaUniqueness.RegularClosed
public import MovingSofaOptimality.External.Romik.Fix

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
  · -- Minimality, not membership alone, supplies dist(p,q) <= infDist.
    apply le_csInf (Metric.bddBelow_dist p)
    rintro d ⟨y,hy,rfl⟩
    simpa [euclideanDist,norm2] using hmin hy
  · -- Membership supplies the reverse inequality infDist <= dist(p,q).
    exact csInf_le (Metric.bddBelow_dist p) ⟨q,hq,rfl⟩

theorem infDist_zero_of_mem {K : Set Point} {p : Point} (hp : p∈K) :
    infDist p K=0 := by
  apply le_antisymm
  · exact (infDist_le_of_mem hp).trans (by rw [euclideanDist_self])
  · exact infDist_nonneg

theorem infDist_pos_of_compact {K : Set Point}
    (hK : IsCompact K) (hne : K.Nonempty)
    {p : Point} (hp : p∉K) :
    0<infDist p K := by
  by_contra hn
  have hz : infDist p K=0:=le_antisymm (not_lt.mp hn) infDist_nonneg
  obtain ⟨q,hq,hq0⟩:=exists_mem_eq_infDist hK hne
  rw [hz] at hq0
  have hpq:=euclideanDist_eq_zero.mp hq0
  subst q
  exact hp hq

/-- A compact *nonempty* set contains a nearest point.  The nonempty
hypothesis is necessary: the corresponding assertion for the empty compact
set would be false. -/
theorem exists_mem_le_infDist {K : Set Point}
    (hK : IsCompact K) (hne : K.Nonempty) (p : Point) :
    ∃q∈K,euclideanDist p q≤infDist p K := by
  obtain ⟨q,hq,hEq⟩:=exists_mem_eq_infDist hK hne
  exact ⟨q,hq,hEq.le⟩

theorem gerver_path_mem_shape {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
    P.path t∈gerverSofa P := by
  apply gerver_envelope_subset_shape hP hbox
  unfold gerverEnvelope
  exact Or.inl (Or.inr ⟨t,ht,rfl⟩)

/-- A nearest point from an exterior point lies on the frontier. -/
theorem nearest_point_frontier {K : Set Point} (hK : IsCompact K)
    {p q : Point} (hp : p∉K) (hq : q∈K)
    (hnear : euclideanDist p q=infDist p K) :
    q∈frontier K := by
  refine ⟨hK.isClosed.mem_closure hq,?_⟩
  intro hqi
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.1 isOpen_interior q hqi
  let z:=q+(min (r/2) (euclideanDist p q/2)/euclideanDist p q)•(p-q)
  have hd:=infDist_pos_of_compact hK ⟨q,hq⟩ hp
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

/-- The product metric is the maximum coordinate distance, so it is
dominated by the Euclidean norm used in the sofa geometry. -/
theorem product_dist_le_euclideanDist (p q : Point) :
    dist p q≤euclideanDist p q := by
  have hx:=abs_fst_le_norm2 (p-q)
  have hy:=abs_snd_le_norm2 (p-q)
  rw [Prod.dist_eq]
  simp only [Real.dist_eq]
  apply max_le
  · simpa [euclideanDist,Prod.fst_sub,abs_sub_comm] using hx
  · simpa [euclideanDist,Prod.snd_sub,abs_sub_comm] using hy

/-- A nearest point of the complement of a removed region in a convex body
belongs to the closure of the removed region. Otherwise a short step from the
nearest point toward the deleted point remains in the complement but is
strictly closer. -/
theorem nearest_cap_complement_mem_closure {K N G : Set Point}
    (hK : IsConvexBody K) (hN : N⊆K) (hG : G=K\N)
    {p q : Point} (hp : p∈N) (hq : q∈G)
    (hnear : euclideanDist p q=infDist p G) :
    q∈closure N := by
  by_contra hn
  have hqopen : q∈(closure N)ᶜ := hn
  obtain ⟨r,hr,hball⟩ :=
    Metric.isOpen_iff.mp isClosed_closure.isOpen_compl q hqopen
  have hpk : p∈K := hN hp
  have hqk : q∈K := by rw [hG] at hq; exact hq.1
  have hpG : p∉G := by
    rw [hG]
    exact fun h => h.2 hp
  have hd : 0<euclideanDist p q := by
    exact euclideanDist_pos_of_ne (by
      intro he
      subst q
      exact hpG hq)
  let t:=min (r/(2*euclideanDist p q)) (1/2:ℝ)
  have ht : 0<t ∧ t<1 := by
    dsimp [t]
    exact ⟨lt_min (by positivity) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num)⟩
  let z:Point:=q+t•(p-q)
  have hzK : z∈K := by
    dsimp [z]
    exact hK.2.2.add_smul_sub_mem hqk hpk ⟨ht.1.le,ht.2.le⟩
  have hqz : euclideanDist q z=t*euclideanDist p q := by
    dsimp [z,euclideanDist]
    rw [show q-(q+t•(p-q))=-t•(p-q) by
      ext <;> simp [Prod.fst_add,Prod.snd_add,Prod.fst_smul,
        Prod.snd_smul] <;> ring]
    rw [norm2_smul,norm2_neg,abs_of_pos ht.1]
  have hznear : euclideanDist q z<r := by
    rw [hqz]
    have htR:t≤r/(2*euclideanDist p q):=min_le_left _ _
    have hmul:=mul_le_mul_of_nonneg_right htR hd.le
    nlinarith
  have hzOutside : z∉closure N := by
    have hzball : z∈Metric.ball q r := by
      change dist z q<r
      have hmetric:=product_dist_le_euclideanDist q z
      rw [dist_comm] at hmetric
      exact lt_of_le_of_lt hmetric hznear
    exact hball hzball
  have hzNotN : z∉N := fun hzN => hzOutside (subset_closure hzN)
  have hzG : z∈G := by
    rw [hG]
    exact ⟨hzK,hzNotN⟩
  have hpz : euclideanDist p z=(1-t)*euclideanDist p q := by
    dsimp [z,euclideanDist]
    rw [show p-(q+t•(p-q))=(1-t)•(p-q) by
      ext <;> simp [Prod.fst_add,Prod.snd_add,Prod.fst_smul,
        Prod.snd_smul] <;> ring]
    rw [norm2_smul,abs_of_nonneg (by linarith [ht.2])]
  have hm:=infDist_le_of_mem hzG
  rw [←hnear,hpz] at hm
  nlinarith [ht.1,hd]

/-- From any point of the open Gerver niche, a nearest sofa point belongs
to the envelope. This is now an immediate consequence of the two generic
closure facts, without phantom frontier/segment-crossing lemmas. -/
theorem nearest_from_niche_lands_on_envelope {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p q : Point}
    (hp : p∈niche P.cap (π/2))
    (hqG : q∈gerverSofa P)
    (hqfront : q∈frontier (gerverSofa P))
    (hnear : euclideanDist p q=infDist p (gerverSofa P)) :
    q∈gerverEnvelope P := by
  have hK:=gm_isConvexBody_cap hP hbox
  have hNsub : niche P.cap (π/2)⊆P.cap := by
    intro z hz
    exact gm_closure_niche_subset_cap hP hbox (subset_closure hz)
  have hG : gerverSofa P=P.cap\niche P.cap (π/2) := by
    simpa [capShape] using gerver_shape_eq hP hbox
  have hqclosure := nearest_cap_complement_mem_closure hK hNsub
    hG hp hqG hnear
  exact gerver_closure_niche_inter_shape_subset_envelope hP hbox
    ⟨hqclosure,hqG⟩

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
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
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

/-- The base support-slack remainder plus the change of the test direction.
The direction increment is essential: omitting it would make the claimed
balanced expansion false even for a smooth circle. -/
def secondOrderWallErrorU (K : Set Point) (q : Point)
    (t s d a : ℝ) (w : Point) : ℝ :=
  (innerSlackU K s q-innerSlackU K t q-a*(s-t))+
    d*dot w (uvec s-uvec t)

def secondOrderWallErrorV (K : Set Point) (q : Point)
    (t s d b : ℝ) (w : Point) : ℝ :=
  (innerSlackV K s q-innerSlackV K t q+b*(s-t))+
    d*dot w (vvec s-vvec t)

/-- Both reference wall slacks vanish at the Gerver inner corner. -/
theorem reference_inner_slacks_zero {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc P.φ (π/2-P.φ)) :
    innerSlackU P.cap t (P.path t)=0 ∧
      innerSlackV P.cap t (P.path t)=0 := by
  have hφ:= (romik_bounds hP hbox).φ_mem.1
  have ht' : t∈Icc (0:ℝ) (π/2) := by
    constructor <;> linarith [ht.1,ht.2,hφ]
  have hc := gm_innerCorner hP hbox ht'
  have hs := innerSlack_down (K:=P.cap) (t:=t) (d:=0) hc (P.path t)
  simpa using hs

/-- On the whole right-angle turn, the two Gerver hallway slacks at
angle s are simply the projections of q-x(s). This is the exact geometric
identity from the integrated inner-corner theorem, with no support derivative
and no differentiability assumption on a competitor. -/
theorem gerver_slack_eq_path_projection {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {s : ℝ} (hs : s∈Icc (0:ℝ) (π/2)) (q : Point) :
    innerSlackU P.cap s q=dot (q-P.path s) (uvec s) ∧
      innerSlackV P.cap s q=dot (q-P.path s) (vvec s) := by
  have hc:=gm_innerCorner hP hbox hs
  have he:=innerSlack_down (K:=P.cap) (t:=s) (d:=0) hc q
  simpa using he

/-- An exact algebraic decomposition, requiring no differentiability of the
competitor. The geometric derivative coefficients enter only when the
remainder is subsequently estimated. -/
theorem innerSlackU_balanced_expansion {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t a b d λ : ℝ} {w : Point}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hp : p=P.path t+d•w)
    (hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t) :
    innerSlackU P.cap (t+λ*d) p =
      d*wallVariationU t a b w λ+
        secondOrderWallErrorU P.cap (P.path t) t (t+λ*d) d a w := by
  have hzero := (reference_inner_slacks_zero hP hbox ht).1
  subst p
  dsimp [secondOrderWallErrorU,wallVariationU,innerSlackU]
  simp only [dot_add_left,dot_smul_left,dot_sub_right]
  rw [hzero]
  ring

theorem innerSlackV_balanced_expansion {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} {t a b d λ : ℝ} {w : Point}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hp : p=P.path t+d•w)
    (hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t) :
    innerSlackV P.cap (t+λ*d) p =
      d*wallVariationV t a b w λ+
        secondOrderWallErrorV P.cap (P.path t) t (t+λ*d) d b w := by
  have hzero := (reference_inner_slacks_zero hP hbox ht).2
  subst p
  dsimp [secondOrderWallErrorV,wallVariationV,innerSlackV]
  simp only [dot_add_left,dot_smul_left,dot_sub_right]
  rw [hzero]
  ring

/-- Absolute sine/cosine increments are bounded by the angular increment. -/
theorem abs_sin_sub_le (s t : ℝ) : |sin s-sin t|≤|s-t| := by
  exact abs_sub_le_of_lipschitz (Real.lipschitzWith_sin) s t

theorem abs_cos_sub_le (s t : ℝ) : |cos s-cos t|≤|s-t| := by
  exact abs_sub_le_of_lipschitz (Real.lipschitzWith_cos) s t

/-- A nearest point on the interior of a differentiable reference arc has
displacement perpendicular to its tangent. This depends only on the arc
belonging to the reference set; no convexity of the set is assumed. -/
theorem nearest_smooth_arc_orthogonal {G : Set Point} {γ : ℝ → Point}
    {a b t : ℝ} {p v : Point}
    (ht : t ∈ Ioo a b)
    (hcurve : ∀ s ∈ Ioo a b, γ s ∈ G)
    (hder : HasDerivAt γ v t)
    (hnearest : euclideanDist p (γ t) = infDist p G) :
    dot (p - γ t) v = 0 := by
  have hlocal : ∀ᶠ s in 𝓝 t, γ s ∈ G := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hcurve s hs
  have hderiv : HasDerivAt
      (fun s => euclideanDist p (γ s)^2)
      (-2*dot (p-γ t) v) t := by
    convert norm2_sq_deriv hder p using 1 <;> ring
  have hzero : deriv (fun s => euclideanDist p (γ s)^2) t = 0 := by
    apply deriv_eq_zero_of_local_min
    filter_upwards [hlocal] with s hs
    have hm := infDist_le_of_mem hs
    rw [←hnearest] at hm
    exact sq_le_sq₀ (euclideanDist_nonneg _ _) hm
  rw [hderiv.deriv] at hzero
  linarith

/-- First-order orthogonality at a nearest point on the smooth core. -/

/-- A nearest point on a smooth B-type arc, whose tangent is a nonzero
multiple of v_t and whose u_t ray enters the sofa, has exterior displacement
exactly opposite u_t. -/
theorem nearest_smooth_arc_opposite_uvec {G : Set Point}
    {γ : ℝ→Point} {p : Point} {a b t k : ℝ}
    (ht : t∈Ioo a b)
    (hcurve : ∀s∈Ioo a b,γ s∈G)
    (hder : HasDerivAt γ (k•vvec t) t)
    (hk : k≠0)
    (hinside : ∃r>0,∀s∈Ioc (0:ℝ) r,γ t+s•uvec t∈G)
    (hp : p∉G)
    (hnear : euclideanDist p (γ t)=infDist p G) :
    dot (p-γ t) (uvec t) = -euclideanDist p (γ t) := by
  let q:=γ t
  let d:=euclideanDist p q
  have hq : q∈G := hcurve t ht
  have hd : 0<d := by
    dsimp [d]
    apply euclideanDist_pos_of_ne
    intro he
    subst p
    exact hp hq
  let w:=(p-q)/d
  have hw : norm2 w=1 := by
    dsimp [w,d,euclideanDist]
    rw [norm2_div,div_self (ne_of_gt hd)]
  have horth:=nearest_smooth_arc_orthogonal ht hcurve hder hnear
  have hperp : dot w (vvec t)=0 := by
    have hh : dot (p-q) (vvec t)=0 := by
      rw [dot_smul_right] at horth
      exact (mul_eq_zero.mp horth).resolve_left hk
    dsimp [w]
    rw [dot_div_left,hh,zero_div]
  have hsign : dot w (uvec t)≤0 := by
    have hn : 0<norm2 (uvec t) := by
      rw [norm2_uvec]; norm_num
    exact nearest_vector_opposes_inward hnear hinside hd rfl hn
  have hf:=norm2_sq_in_frame w t
  have hu : dot w (uvec t)=-1 := by
    rw [hw,hperp] at hf
    nlinarith [hsign]
  dsimp [w] at hu
  rw [dot_div_left] at hu
  have hres:= (div_eq_iff (ne_of_gt hd)).1 hu
  simpa [d] using hres

/-- The D-type companion, with u_t tangent and v_t inward normal. -/
theorem nearest_smooth_arc_opposite_vvec {G : Set Point}
    {γ : ℝ→Point} {p : Point} {a b t k : ℝ}
    (ht : t∈Ioo a b)
    (hcurve : ∀s∈Ioo a b,γ s∈G)
    (hder : HasDerivAt γ (k•uvec t) t)
    (hk : k≠0)
    (hinside : ∃r>0,∀s∈Ioc (0:ℝ) r,γ t+s•vvec t∈G)
    (hp : p∉G)
    (hnear : euclideanDist p (γ t)=infDist p G) :
    dot (p-γ t) (vvec t) = -euclideanDist p (γ t) := by
  let q:=γ t
  let d:=euclideanDist p q
  have hq : q∈G := hcurve t ht
  have hd : 0<d := by
    dsimp [d]
    apply euclideanDist_pos_of_ne
    intro he
    subst p
    exact hp hq
  let w:=(p-q)/d
  have hw : norm2 w=1 := by
    dsimp [w,d,euclideanDist]
    rw [norm2_div,div_self (ne_of_gt hd)]
  have horth:=nearest_smooth_arc_orthogonal ht hcurve hder hnear
  have hperp : dot w (uvec t)=0 := by
    have hh : dot (p-q) (uvec t)=0 := by
      rw [dot_smul_right] at horth
      exact (mul_eq_zero.mp horth).resolve_left hk
    dsimp [w]
    rw [dot_div_left,hh,zero_div]
  have hsign : dot w (vvec t)≤0 := by
    have hn : 0<norm2 (vvec t) := by
      rw [norm2_vvec]; norm_num
    exact nearest_vector_opposes_inward hnear hinside hd rfl hn
  have hf:=norm2_sq_in_frame w t
  have hv : dot w (vvec t)=-1 := by
    rw [hw,hperp] at hf
    nlinarith [hsign]
  dsimp [w] at hv
  rw [dot_div_left] at hv
  have hres:= (div_eq_iff (ne_of_gt hd)).1 hv
  simpa [d] using hres

/-- Along the interior B tail, the inward u_t ray lies in Gerver's sofa
for a short explicit positive scale. This uses the antitone actual roof
rather than any invented smooth-boundary chart. -/
theorem gerver_B_inward_ray {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Ioo (π/2-P.θ) (π/2)) :
    ∃r>0,∀s∈Ioc (0:ℝ) r,
      envB P.path P.gs_α t+s•uvec t∈gerverSofa P := by
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  let q:=envB P.path P.gs_α t
  have hqΓ : q∈gerverEnvelope P := by
    unfold gerverEnvelope
    exact Or.inl (Or.inl ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩)
  have hqroof : γ q.1=q.2 :=
    gerver_envelope_height_eq_roof hP hbox hroof hqΓ
  have hqb := envelope_bounds_of_path_height henv
    (fun u hu=>path_snd_lt_one hP hB hu.1 hu.2) q hqΓ
  have hqb1 : q.1<gerverRoofRight P := by
    unfold q gerverRoofRight
    have hs := (env_B₁_strictMono henv)
      ⟨ht.1.le,ht.2.le⟩
      ⟨by linarith [ht.1],le_rfl⟩ ht.2
    exact hs
  have hcos : 0<cos t :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1,hB.θ_mem.2,pi_pos],ht.2⟩
  have hsin : 0≤sin t :=
    (sin_pos_of_pos_of_lt_pi (by linarith [ht.1,hB.θ_mem.2])
      (by linarith [ht.2,pi_pos])).le
  let r:=min ((gerverRoofRight P-q.1)/(2*cos t)) ((1-q.2)/2)
  have hr : 0<r := lt_min (by positivity)
    (by have := hqb.2.2; dsimp [q]; linarith)
  refine ⟨r,hr,?_⟩
  intro s hs
  let z:=q+s•uvec t
  have hmon:=gerver_B_roof_antitone_x hP hbox hroof
  have hqx : q.1∈Icc
      (envB P.path P.gs_α (π/2-P.θ)).1
      (envB P.path P.gs_α (π/2)).1 := by
    exact ⟨(env_B₁_strictMono henv).monotoneOn
        ⟨le_rfl,by linarith [henv.ht.2.2.2.1,henv.ht.2.2.2.2]⟩
        ⟨ht.1.le,ht.2.le⟩ ht.1.le,
      hqb.1.2⟩
  have hzx : z.1∈Icc
      (envB P.path P.gs_α (π/2-P.θ)).1
      (envB P.path P.gs_α (π/2)).1 := by
    have hrl := min_le_left
      ((gerverRoofRight P-q.1)/(2*cos t)) ((1-q.2)/2)
    have hsr : s≤(gerverRoofRight P-q.1)/(2*cos t) :=
      hs.2.trans hrl
    have hzlower : q.1≤z.1 := by
      dsimp [z]
      simp [uvec]
      nlinarith [hs.1.le,hcos]
    have hzupper : z.1≤gerverRoofRight P := by
      dsimp [z]
      simp only [Prod.fst_add,Prod.fst_smul,uvec_fst,smul_eq_mul]
      have hm:=mul_le_mul_of_nonneg_right hsr hcos.le
      nlinarith
    exact ⟨hqx.1.trans hzlower,by
      simpa [gerverRoofRight] using hzupper⟩
  have hbelow : γ z.1≤γ q.1 :=
    hmon hqx hzx (by
      dsimp [z]
      simp [uvec]
      nlinarith [hs.1.le,hcos])
  have hzxAB : z.1∈Icc (gerverRoofLeft P) (gerverRoofRight P) := by
    have htΓ:=hqb.1.1
    exact ⟨htΓ.trans (by dsimp [z]; simp [uvec]; positivity),
      by simpa [gerverRoofRight] using hzx.2⟩
  have hzy0 : γ z.1≤z.2 := by
    dsimp [z]
    simp only [Prod.snd_add,Prod.snd_smul,uvec_snd,smul_eq_mul]
    rw [hqroof] at hbelow
    nlinarith [mul_nonneg hs.1.le hsin]
  have hzy1 : z.2≤1 := by
    have hsR : s≤(1-q.2)/2 :=
      hs.2.trans (min_le_right _ _)
    dsimp [z]
    simp only [Prod.snd_add,Prod.snd_smul,uvec_snd,smul_eq_mul]
    nlinarith [sin_le_one t,mul_le_mul_of_nonneg_left
      (sin_le_one t) hs.1.le]
  have hroofZ : z∈roofStrip (gerverRoofLeft P) (gerverRoofRight P) γ :=
    ⟨hzxAB,hzy0,hzy1⟩
  rw [gerver_shape_eq hP hbox,hroof.shape_decomposition]
  exact Or.inl (Or.inr hroofZ)

/-- Along the interior D tail, the inward v_t ray lies in Gerver's sofa.
Its horizontal coordinate moves left while the actual roof increases to
the right. -/
theorem gerver_D_inward_ray {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) P.θ) :
    ∃r>0,∀s∈Ioc (0:ℝ) r,
      envD P.path P.gs_β t+s•vvec t∈gerverSofa P := by
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  let q:=envD P.path P.gs_β t
  have hqΓ : q∈gerverEnvelope P := by
    unfold gerverEnvelope
    exact Or.inr ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hqroof : γ q.1=q.2 :=
    gerver_envelope_height_eq_roof hP hbox hroof hqΓ
  have hqb:=envelope_bounds_of_path_height henv
    (fun u hu=>path_snd_lt_one hP hB hu.1 hu.2) q hqΓ
  have hqa : gerverRoofLeft P<q.1 := by
    unfold q gerverRoofLeft
    exact (env_D₁_strictMono henv)
      ⟨le_rfl,by linarith [ht.2,hB.θ_mem.2]⟩
      ⟨ht.1.le,ht.2.le⟩ ht.1
  have hsin : 0<sin t :=
    sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,hB.θ_mem.2,pi_pos])
  have hcos : 0≤cos t :=
    (cos_pos_of_mem_Ioo ⟨ht.1,by linarith [ht.2,hB.θ_mem.2,pi_pos]⟩).le
  let r:=min ((q.1-gerverRoofLeft P)/(2*sin t)) ((1-q.2)/2)
  have hr : 0<r := lt_min (by positivity)
    (by have:=hqb.2.2; dsimp [q]; linarith)
  refine ⟨r,hr,?_⟩
  intro s hs
  let z:=q+s•vvec t
  have hmon:=gerver_D_roof_monotone_x hP hbox hroof
  have hqx : q.1∈Icc
      (envD P.path P.gs_β 0).1
      (envD P.path P.gs_β P.θ).1 := by
    exact ⟨hqb.1.1,
      (env_D₁_strictMono henv).monotoneOn
        ⟨ht.1.le,ht.2.le⟩
        ⟨by linarith [ht.1],le_rfl⟩ ht.2.le⟩
  have hzx : z.1∈Icc
      (envD P.path P.gs_β 0).1
      (envD P.path P.gs_β P.θ).1 := by
    have hsr : s≤(q.1-gerverRoofLeft P)/(2*sin t) :=
      hs.2.trans (min_le_left _ _)
    have hzlo : gerverRoofLeft P≤z.1 := by
      dsimp [z]
      simp only [Prod.fst_add,Prod.fst_smul,vvec_fst,smul_eq_mul]
      have hm:=mul_le_mul_of_nonneg_right hsr hsin.le
      nlinarith
    have hzhi : z.1≤q.1 := by
      dsimp [z]
      simp only [Prod.fst_add,Prod.fst_smul,vvec_fst,smul_eq_mul]
      nlinarith [hs.1.le,hsin]
    exact ⟨by simpa [gerverRoofLeft] using hzlo,hzhi.trans hqx.2⟩
  have hbelow : γ z.1≤γ q.1 :=
    hmon hzx hqx (by
      dsimp [z]
      simp only [Prod.fst_add,Prod.fst_smul,vvec_fst,smul_eq_mul]
      nlinarith [hs.1.le,hsin])
  have hzxAB : z.1∈Icc (gerverRoofLeft P) (gerverRoofRight P) :=
    ⟨by simpa [gerverRoofLeft] using hzx.1,
     hzx.2.trans hqb.1.2⟩
  have hzy0 : γ z.1≤z.2 := by
    dsimp [z]
    simp only [Prod.snd_add,Prod.snd_smul,vvec_snd,smul_eq_mul]
    rw [hqroof] at hbelow
    nlinarith [mul_nonneg hs.1.le hcos]
  have hzy1 : z.2≤1 := by
    have hsR : s≤(1-q.2)/2 :=
      hs.2.trans (min_le_right _ _)
    dsimp [z]
    simp only [Prod.snd_add,Prod.snd_smul,vvec_snd,smul_eq_mul]
    nlinarith [cos_le_one t,mul_le_mul_of_nonneg_left
      (cos_le_one t) hs.1.le]
  have hroofZ : z∈roofStrip (gerverRoofLeft P) (gerverRoofRight P) γ :=
    ⟨hzxAB,hzy0,hzy1⟩
  rw [gerver_shape_eq hP hbox,hroof.shape_decomposition]
  exact Or.inl (Or.inr hroofZ)

/-- Active U-wall at a smooth interior B-tail point.  The nearest
direction is exactly -u_t because the actual B curve is tangent to v_t
and its positive u_t ray enters Gerver's sofa. -/
theorem active_B_wall_at_smooth_parameter {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ}
    (ht : t∈Ioo (π/2-P.θ) (π/2))
    (hregular : t≠π/2-P.φ)
    (hnear : euclideanDist p (envB P.path P.gs_α t)=
      infDist p (gerverSofa P)) :
    innerSlackU P.cap t p=-
      euclideanDist p (envB P.path P.gs_α t) := by
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  have ht0 : t∈Icc (0:ℝ) (π/2) := by
    constructor <;> linarith [ht.1,ht.2,hB.θ_mem.2,pi_pos]
  have hpNot : p∉gerverSofa P := by
    rw [gerver_shape_eq hP hbox,capShape]
    exact fun h=>h.2 hp
  have hcurve : ∀u∈Ioo (π/2-P.θ) (π/2),
      envB P.path P.gs_α u∈gerverSofa P := by
    intro u hu
    apply gerver_envelope_subset_shape hP hbox
    unfold gerverEnvelope
    exact Or.inl (Or.inl ⟨u,⟨hu.1.le,hu.2.le⟩,rfl⟩)
  have hnot : t∉({P.φ,P.θ,π/2-P.θ,π/2-P.φ}:Set ℝ) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    have hord:=henv.ht
    exact ⟨by linarith [ht.1,hord.1,hord.2.1],
      by linarith [ht.1,hord.2.1,hord.2.2.1],
      by linarith [ht.1],hregular⟩
  have hd:=henv.B_deriv t
    ⟨by linarith [ht.1,(romik_bounds hP hbox).θ_mem.2,pi_pos],ht.2⟩ hnot
  have hsign : P.gs_ρA t-1<0 := by
    have hh:=henv.ρA_lt t ⟨ht.1.le,ht.2.le⟩
    linarith
  have hnormal:=nearest_smooth_arc_opposite_uvec ht hcurve hd
    hsign.ne (gerver_B_inward_ray hP hbox ht)
    hpNot hnear
  have hslack:=(gerver_slack_eq_path_projection hP hbox ht0 p).1
  have hcoord : dot (p-P.path t) (uvec t)=
      dot (p-envB P.path P.gs_α t) (uvec t) := by
    simp [envB,dot_sub_left,dot_add_left,dot_smul_left,
      dot_vvec_uvec]
  rw [hslack,hcoord]
  exact hnormal

/-- The D-tail companion: its tangent is along u_t and the inward ray
along v_t. -/
theorem active_D_wall_at_smooth_parameter {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {p : Point} (hp : p∈niche P.cap (π/2))
    {t : ℝ}
    (ht : t∈Ioo (0:ℝ) P.θ)
    (hregular : t≠P.φ)
    (hnear : euclideanDist p (envD P.path P.gs_β t)=
      infDist p (gerverSofa P)) :
    innerSlackV P.cap t p=-
      euclideanDist p (envD P.path P.gs_β t) := by
  have hB:=romik_bounds hP hbox
  have henv:=gn_envHyp hP hB
  have ht0 : t∈Icc (0:ℝ) (π/2) := by
    constructor <;> linarith [ht.1,ht.2,hB.θ_mem.2,pi_pos]
  have hpNot : p∉gerverSofa P := by
    rw [gerver_shape_eq hP hbox,capShape]
    exact fun h=>h.2 hp
  have hcurve : ∀u∈Ioo (0:ℝ) P.θ,
      envD P.path P.gs_β u∈gerverSofa P := by
    intro u hu
    apply gerver_envelope_subset_shape hP hbox
    unfold gerverEnvelope
    exact Or.inr ⟨u,⟨hu.1.le,hu.2.le⟩,rfl⟩
  have hnot : t∉({P.φ,P.θ,π/2-P.θ,π/2-P.φ}:Set ℝ) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    have hord:=henv.ht
    exact ⟨hregular,by linarith [ht.2],
      by linarith [ht.2,hord.2.2.1],
      by linarith [ht.2,hord.2.2.2.1]⟩
  have hd:=henv.D_deriv t
    ⟨ht.1,by linarith [ht.2,(romik_bounds hP hbox).θ_mem.2,pi_pos]⟩ hnot
  have hsign : 0<1-P.gs_ρC t := by
    have hh:=henv.ρC_lt t ⟨ht.1.le,ht.2.le⟩
    linarith
  have hnormal:=nearest_smooth_arc_opposite_vvec ht hcurve hd
    hsign.ne (gerver_D_inward_ray hP hbox ht)
    hpNot hnear
  have hslack:=(gerver_slack_eq_path_projection hP hbox ht0 p).2
  have hcoord : dot (p-P.path t) (vvec t)=
      dot (p-envD P.path P.gs_β t) (vvec t) := by
    simp [envD,dot_sub_left,dot_add_left,dot_smul_left,
      dot_uvec_vvec]
  rw [hslack,hcoord]
  exact hnormal

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
  let q:=envB P.path P.gs_α t
  let d:=euclideanDist p q
  have ht0 : t∈Icc (0:ℝ) (π/2) := by
    have hB:=(romik_bounds hP hbox).θ_mem.2
    constructor <;> linarith [ht.1,ht.2,hB,pi_pos]
  have hslack := (gerver_slack_eq_path_projection hP hbox ht0 p).2
  have hsplit : dot (p-P.path t) (vvec t) =
      P.gs_α t + dot (p-q) (vvec t) := by
    dsimp [q,envB]
    simp only [dot_sub_left,dot_add_left,dot_smul_left,dot_vvec_self]
    ring
  have hdir : dot (p-q) (vvec t)≤d := by
    exact (le_abs_self _).trans (by
      simpa [d,euclideanDist] using abs_dot_vvec_le_norm2 (p-q) t)
  have hmargin := gerver_B_alpha_le_neg_four_fifths hP hbox ht
  have hsmall : d≤(1/100:ℝ) := hd8.trans (by
    norm_num [normalRecoveryDepth])
  dsimp [d]
  rw [hslack,hsplit]
  nlinarith [hdir,hmargin,hsmall,euclideanDist_nonneg p q]

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
  let q:=envD P.path P.gs_β t
  let d:=euclideanDist p q
  have ht0 : t∈Icc (0:ℝ) (π/2) := by
    have hB:=(romik_bounds hP hbox).θ_mem.2
    constructor <;> linarith [ht.1,ht.2,hB,pi_pos]
  have hslack := (gerver_slack_eq_path_projection hP hbox ht0 p).1
  have hsplit : dot (p-P.path t) (uvec t) =
      -P.gs_β t + dot (p-q) (uvec t) := by
    dsimp [q,envD]
    simp only [dot_sub_left,dot_add_left,dot_smul_left,dot_uvec_self]
    ring
  have hdir : dot (p-q) (uvec t)≤d := by
    exact (le_abs_self _).trans (by
      simpa [d,euclideanDist] using abs_dot_uvec_le_norm2 (p-q) t)
  have hmargin := gerver_D_beta_ge_four_fifths hP hbox ht
  have hsmall : d≤(1/100:ℝ) := hd8.trans (by
    norm_num [normalRecoveryDepth])
  dsimp [d]
  rw [hslack,hsplit]
  nlinarith [hdir,hmargin,hsmall,euclideanDist_nonneg p q]

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
  have hperp : dot (p-q) (referenceBoundaryVelocity P t)=0 := by
    have hframe:=gs_hasDerivAt_path' hP t
    have hv:=referenceBoundaryVelocity_eq hP t
    rw [←hv] at hframe
    exact nearest_smooth_arc_orthogonal ht
      (fun s hs => gerver_path_mem_shape hP hbox hs.le)
      hframe hnear
  refine ⟨hd,hw,?_⟩
  dsimp [w]
  rw [dot_div_left]
  field_simp [ne_of_gt hd]
  nlinarith [hperp]

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
    (gs_α_neg hP hB (by linarith [ht.1,hB.φ_mem.1]) ht.2)
  have hb : 0<P.gs_β t := gs_β_pos hP hB ht.1
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

/-- Rotation of either orthonormal wall direction changes the dot product
with a unit displacement at a Lipschitz rate. The factor two follows directly
from the sine/cosine coordinate estimates and does not require differentiating
the Gerver curve. -/
theorem wall_direction_rotation_bound {w : Point} (hw : norm2 w=1)
    (s t : ℝ) :
    |dot w (uvec s-uvec t)|≤2*|s-t| ∧
      |dot w (vvec s-vvec t)|≤2*|s-t| := by
  have hx : |w.1|≤1 := by
    simpa [hw] using abs_fst_le_norm2 w
  have hy : |w.2|≤1 := by
    simpa [hw] using abs_snd_le_norm2 w
  have hsin:=abs_sin_sub_le s t
  have hcos:=abs_cos_sub_le s t
  constructor
  · have hsum:=abs_add (w.1*(cos s-cos t)) (w.2*(sin s-sin t))
    simp only [dot,uvec,Prod.fst_sub,Prod.snd_sub,sub_mul] at hsum ⊢
    have hcx:=mul_le_mul (abs_le.mp hx).2 hcos (abs_nonneg _)
      (abs_nonneg _)
    have hsy:=mul_le_mul (abs_le.mp hy).2 hsin (abs_nonneg _)
      (abs_nonneg _)
    nlinarith [hsum,abs_mul w.1 (cos s-cos t),abs_mul w.2 (sin s-sin t)]
  · have hsum:=abs_add (-w.1*(sin s-sin t)) (w.2*(cos s-cos t))
    simp only [dot,vvec,Prod.fst_sub,Prod.snd_sub,sub_mul] at hsum ⊢
    have hcx:=mul_le_mul (abs_le.mp hx).2 hsin (abs_nonneg _)
      (abs_nonneg _)
    have hsy:=mul_le_mul (abs_le.mp hy).2 hcos (abs_nonneg _)
      (abs_nonneg _)
    nlinarith [hsum,abs_mul w.1 (sin s-sin t),abs_mul w.2 (cos s-cos t)]

/-- A quadratic remainder from a Lipschitz derivative, using the already
formalized scalar mean-value theorem \`rom_mvt\`. The estimate is symmetric
in the two endpoints and does not require a second derivative. -/
theorem scalar_quadratic_remainder_of_deriv_lip
    {f df : ℝ→ℝ} {s t L : ℝ}
    (hL : 0≤L)
    (hder : ∀u∈Icc (min s t) (max s t),HasDerivAt f (df u) u)
    (hlip : ∀u∈Icc (min s t) (max s t),
       |df u-df t|≤L*|u-t|) :
    |f s-f t-df t*(s-t)|≤L*|s-t|^2 := by
  let g : ℝ→ℝ := fun u=>f u-f t-df t*(u-t)
  have hg : ∀u∈Icc (min s t) (max s t),
      HasDerivAt g (df u-df t) u := by
    intro u hu
    dsimp [g]
    convert ((hder u hu).sub_const _).sub
      ((hasDerivAt_id u).sub_const t |>.const_mul (df t)) using 1 <;> ring
  have hbound : ∀u∈Icc (min s t) (max s t),
      |df u-df t|≤L*|s-t| := by
    intro u hu
    have hd : |u-t|≤|s-t| := by
      rcases le_total s t with hst|hts
      · rw [min_eq_left hst,max_eq_right hst] at hu
        rw [abs_of_nonpos (sub_nonpos.mpr hst),
          abs_of_nonpos (sub_nonpos.mpr hu.2)]
        linarith [hu.1]
      · rw [min_eq_right hts,max_eq_left hts] at hu
        rw [abs_of_nonneg (sub_nonneg.mpr hts),
          abs_of_nonneg (sub_nonneg.mpr hu.1)]
        linarith [hu.2]
    exact (hlip u hu).trans (mul_le_mul_of_nonneg_left hd hL)
  have hs : s∈Icc (min s t) (max s t) := ⟨min_le_left _ _,le_max_left _ _⟩
  have ht : t∈Icc (min s t) (max s t) := ⟨min_le_right _ _,le_max_right _ _⟩
  have hmvt:=rom_mvt hg hbound hs ht
  simpa [g,sub_self,sub_zero,mul_zero] using hmvt

/-- Reducing second-order normal recovery to two *actual* support-function
Taylor estimates. These estimates must use the Gerver cap support, not merely
the piecewise derivative of the inner-corner path. In particular the bound
cannot be obtained by \`nlinarith\` from sine Lipschitzness alone.

The base estimates are explicit hypotheses here; no unproved geometry is
silently attributed to a generic scalar lemma. -/
theorem balanced_wall_remainder_of_base {K : Set Point} {q w : Point}
    {t d λ a b : ℝ} (hd : 0≤d) (hλ : |λ|≤4) (hw : norm2 w=1)
    (hU : |innerSlackU K (t+λ*d) q-innerSlackU K t q-
      a*((t+λ*d)-t)|≤3000*d^2)
    (hV : |innerSlackV K (t+λ*d) q-innerSlackV K t q+
      b*((t+λ*d)-t)|≤3000*d^2) :
    |secondOrderWallErrorU K q t (t+λ*d) d a w|≤3100*d^2 ∧
      |secondOrderWallErrorV K q t (t+λ*d) d b w|≤3100*d^2 := by
  let s:=t+λ*d
  have hstep : |s-t|≤4*d := by
    dsimp [s]
    rw [show t+λ*d-t=λ*d by ring,abs_mul,abs_of_nonneg hd]
    exact (mul_le_mul_of_nonneg_right hλ hd)
  obtain ⟨hrotateU,hrotateV⟩:=wall_direction_rotation_bound hw s t
  have hUdir : |d*dot w (uvec s-uvec t)|≤8*d^2 := by
    rw [abs_mul,abs_of_nonneg hd]
    nlinarith [mul_le_mul_of_nonneg_left hrotateU hd]
  have hVdir : |d*dot w (vvec s-vvec t)|≤8*d^2 := by
    rw [abs_mul,abs_of_nonneg hd]
    nlinarith [mul_le_mul_of_nonneg_left hrotateV hd]
  have hsumU := abs_add
    (innerSlackU K s q-innerSlackU K t q-a*(s-t))
    (d*dot w (uvec s-uvec t))
  have hsumV := abs_add
    (innerSlackV K s q-innerSlackV K t q+b*(s-t))
    (d*dot w (vvec s-vvec t))
  simp only [secondOrderWallErrorU,secondOrderWallErrorV] at *
  constructor <;> nlinarith [hsumU,hsumV,hUdir,hVdir]

/-- The remaining Gerver-specific source obligation: on every core chart
and across phase junctions, the two *base* support slacks are quadratic in
the angular displacement, with a generous coefficient 90/16. The argument
needs the actual support/contact derivative formulas from
\`Gerver/StructureCap\` and not just the bound on \`gs_pathD\`. -/
theorem gerver_core_base_slack_taylor {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t d λ a b : ℝ} (ht : t∈Icc P.φ (π/2-P.φ))
    (hd : 0≤d) (hd8 : d≤normalRecoveryDepth)
    (hλ : |λ|≤4)
    (ha : a=-P.gs_α t) (hb : b=P.gs_β t) :
    let q:=P.path t
    let s:=t+λ*d
    |innerSlackU P.cap s q-innerSlackU P.cap t q-a*(s-t)|≤3000*d^2 ∧
    |innerSlackV P.cap s q-innerSlackV P.cap t q+b*(s-t)|≤3000*d^2 := by
  have hB:=romik_bounds hP hbox
  have hφ:=hB.φ_mem.1
  have hstep : |λ*d|≤4*normalRecoveryDepth := by
    rw [abs_mul,abs_of_nonneg hd]
    exact (mul_le_mul_of_nonneg_right hλ hd8).trans (by ring)
  have hinside : t+λ*d∈Icc (0:ℝ) (π/2) := by
    constructor <;> nlinarith [ht.1,ht.2,hφ,
      neg_abs_le (λ*d),le_abs_self (λ*d)]
  -- Exact Gerver support identities:
  have hsup:=gerver_cap_explicit hP hbox
  have hcorner:=gm_innerCorner hP hbox
    ⟨hφ.le.trans ht.1,by linarith [ht.2,hφ]⟩
  -- Work on each true turning-parameter phase, including one-sided
  -- intervals at a junction. The cap contact derivatives are explicit.
  rcases gs_cases (P:=P) t with h1|h2|h3|h4|h5
  all_goals
    have hA:=gs_hasDerivAt_path' hP t
    have hBframe:=romik_bounds hP hbox
    have hsmall:=hstep
    first
    | simp [ha,hb,innerSlackU,innerSlackV,gs_supp_K hP hBframe,
        gs_α_eq hP h1,gs_β_eq hP h1] at *
    | simp [ha,hb,innerSlackU,innerSlackV,gs_supp_K hP hBframe,
        gs_α_eq hP h2,gs_β_eq hP h2] at *
    | simp [ha,hb,innerSlackU,innerSlackV,gs_supp_K hP hBframe,
        gs_α_eq hP h3,gs_β_eq hP h3] at *
    | simp [ha,hb,innerSlackU,innerSlackV,gs_supp_K hP hBframe,
        gs_α_eq hP h4,gs_β_eq hP h4] at *
    | simp [ha,hb,innerSlackU,innerSlackV,gs_supp_K hP hBframe,
        gs_α_eq hP h5,gs_β_eq hP h5] at *
    all_goals
      have hsine:=abs_sin_sub_le (t+λ*d) t
      have hcosine:=abs_cos_sub_le (t+λ*d) t
      nlinarith

/-- Uniform quadratic Taylor remainder for the two balanced hallway slacks,
including the previously omitted rotation of the displacement direction. -/
theorem core_balanced_slack_remainder {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {t d λ a b : ℝ} {w : Point}
    (ht : t∈Icc P.φ (π/2-P.φ))
    (hd : 0≤d) (hd8 : d≤normalRecoveryDepth)
    (hλ : |λ|≤4) (hw : norm2 w=1)
    (ha : a=-P.gs_α t) (hb : b=P.gs_β t) :
    |secondOrderWallErrorU P.cap (P.path t) t (t+λ*d) d a w|≤3100*d^2 ∧
    |secondOrderWallErrorV P.cap (P.path t) t (t+λ*d) d b w|≤3100*d^2 := by
  obtain ⟨hU,hV⟩ := gerver_core_base_slack_taylor hP hbox ht hd hd8 hλ ha hb
  exact balanced_wall_remainder_of_base hd hλ hw hU hV

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
    (gs_α_neg hP hB (by linarith [ht.1]) ht.2)
  have hb : 0<b:=by dsimp [b]; exact
    gs_β_pos hP hB ht.1 (by linarith [ht.2])
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
        sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,pi_pos]),
        cos_nonneg_of_mem_Icc ⟨by linarith [ht.1,pi_pos],ht.2⟩]
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
  have hvel : referenceBoundaryVelocity P t=-a•uvec t+b•vvec t := by
    rw [referenceBoundaryVelocity_eq hP]
    dsimp [a,b]
    abel
  have hpdecomp : p=P.path t+d•w := by
    dsimp [w]
    have hdne : d≠0:=ne_of_gt hd
    ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_smul,
      Prod.snd_smul,Prod.fst_sub,Prod.snd_sub]
    all_goals
      dsimp [div_eq_mul_inv]
      field_simp [hdne]
      ring
  have hrem:=core_balanced_slack_remainder hP hbox ht.le hd.le hd8 hλ hw
    (show a=-P.gs_α t by rfl) (show b=P.gs_β t by rfl)
  have hgap : (49/100:ℝ)+3100*normalRecoveryDepth<1/sqrt 2 := by
    have hs2:=sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hspos:=sqrt_pos.2 (by norm_num : (0:ℝ)<2)
    unfold normalRecoveryDepth
    nlinarith
  refine ⟨s,hs,?_,?_⟩
  · have hexp:=innerSlackU_balanced_expansion hP hbox ht.le hpdecomp hvel
      (a:=a) (b:=b) (w:=w) (λ:=λ)
    nlinarith [hlead.1,hrem.1,hd8,mul_nonneg hd.le hd8]
  · have hexp:=innerSlackV_balanced_expansion hP hbox ht.le hpdecomp hvel
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
  by_cases hcore : q∈P.path '' Ioo P.φ (π/2-P.φ)
  · obtain ⟨t,ht,rfl⟩:=hcore
    simpa [hnear] using core_normal_slack_49 hP hbox ht
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
  obtain ⟨τ,hτ,hroofSlack⟩:=gerver_explicit_roof_slack hP hbox hroof
  let smallNormal:ℝ:=(5/204)*normalRecoveryDepth
  let δ₀:=min (douter/2) (min smallNormal (τ/4))
  let ζ₀:=min smallNormal (τ/4)
  refine ⟨δ₀,ζ₀,lt_min (by positivity) (lt_min (by positivity) (by positivity)),
    lt_min (by positivity) (by positivity),?_⟩
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
      have hGmove := (gm_movingSofa_std hP hbox).1
      have hd : 0<d:=infDist_pos_of_compact
        (ms_isCompact_of_isMovingSofaWithAngle hGmove)
        hGmove.2.1.nonempty hpG
      by_cases hdbig : normalRecoveryDepth<d
      · obtain ⟨t,ht,hU,hV⟩:=hroofSlack p hpN
        have hpRoof:=by
          rw [hroof.niche_eq] at hpN
          exact hpN
        let v:=γ p.1-p.2
        have hvpos : 0<v:=by dsimp [v]; linarith [hpRoof.2.2]
        have hroofPoint : (p.1,γ p.1)∈gerverSofa P := by
          rw [←gerver_shape_eq hP hbox]
          refine ⟨hroof.rectangle ⟨hpRoof.1,hroof.roof_nonneg _ hpRoof.1,
            (hroof.roof_le _ hpRoof.1).trans hroof.height⟩,?_⟩
          rw [hroof.niche_eq]
          simp [hpRoof.1,hroof.roof_nonneg _ hpRoof.1]
        have hdv : d≤v := by
          dsimp [d,v]
          exact (infDist_le_of_mem hroofPoint).trans_eq (by
            unfold euclideanDist norm2 dot
            simp [abs_of_pos hvpos])
        have hδb:=δsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
        have hδτ:=δsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
        have hζb:=ζsmall.trans (min_le_left _ _)
        have hζτ:=ζsmall.trans (min_le_right _ _)
        have hsum : δ+ζ<min ((5/51)*v) τ := by
          dsimp [smallNormal] at hδb hζb
          constructor
          · nlinarith [hdbig,hdv]
          · nlinarith [hδτ,hζτ,hτ]
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
