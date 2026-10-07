module

public import MovingSofaQuantitative.MidpointEntry
public import MovingSofaQuantitative.ExplicitTerminal
public import MovingSofaQuantitative.ReferenceSector
public import MovingSofaQuantitative.NormalRecovery
public import MovingSofaQuantitative.DirectArea
public import MovingSofaQuantitative.CenteredCap
public import MovingSofaQuantitative.OrthogonalErosion
public import MovingSofaQuantitative.SectorBudget
public import MovingSofaQuantitative.SectorContent
public import MovingSofaStability.LocalBound

/-!
# Explicit local stability: 2.3 / 50 / 3.1

UNCOMPILED SOURCE.  This file assembles the quantitative appendix's local
theorem from actual original-sofa data.  Qualitative compactness supplies only
entry into one fixed neighborhood.  All displayed numerical coefficients are
proved after entry.

No containment S subset U is assumed: the surplus and missing portions are
tracked separately.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def kCenter : ℝ := 1001/1000
def CHaus : ℝ := 23/10
def lambdaMissing : ℝ := 10031/10000

structure LocalData (P : GerverParams) (S : Set Point) (ω ε : ℝ) where
  N : Set Point
  K : Set Point
  U : Set Point
  e : ℝ
  R : ℝ
  N_eq : N=midpointNormalizedSofa P S
  K_eq : K=sofaCap N
  U_eq : U=capShape K
  Nmove : IsMovingSofaWithAngle N ω
  Ncompact : IsCompact N
  Kcap : IsCap K (π/2)
  top : supp N (π/2)=1
  strip : N⊆hStrip
  midpoint : horizontalMidpoint K=horizontalMidpoint P.cap
  e_def : e=area (gerverSofa P)-area U
  eps_def : ε=area (gerverSofa P)-area N
  e_nonneg : 0≤e
  e_le : e≤ε
  angle : 0≤π/2-ω ∧ π/2-ω≤(31/10)*(ε-e)
  surplus : area (N\U)≤(31/10000)*(ε-e)
  missing : area (U\N)≤lambdaMissing*(ε-e)
  hallways : ApproxHallways K N (4*R*(π/2-ω))
  cap_close : EuclideanClose (kCenter*sqrt e) K P.cap
  support_close : UpperSupportClose (kCenter*sqrt e) K P.cap
  niche_subset : niche K (π/2)⊆K

theorem gerver_midpoint_cap {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    horizontalMidpoint (gerverSofa P)=horizontalMidpoint P.cap := by
  unfold horizontalMidpoint
  rw [gerver_upper_support hP hbox ⟨le_rfl,pi_pos.le⟩,
      gerver_upper_support hP hbox ⟨pi_pos.le,le_rfl⟩]

/-- Build all local quantitative data once support/angle entry hypotheses hold. -/
theorem build_local_data {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω ε : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω : ω∈Icc (arccos (5/11:ℝ)) (π/2))
    (hε : ε=sofaDeficit P S) (hεpos : 0<ε)
    {δT αT R : ℝ}
    (hterminal :
      ∀ K : Set Point, IsCap K (π/2) → UpperSupportClose δT K P.cap →
      ∀ S' : Set Point, MeasurableSet S' → ∀ ω'∈Icc (0:ℝ) (π/2),
      π/2-ω'≤αT → PartialSofaConstraints K S' ω' →
      let U:=capShape K
      let ε':=area (gerverSofa P)-area S'
      let e':=area (gerverSofa P)-area U
      0≤e' ∧ e'≤ε' ∧
      π/2-ω'≤(31/10)*(ε'-e') ∧
      area (S'\U)≤(31/10000)*(ε'-e') ∧
      area (U\S')≤lambdaMissing*(ε'-e') ∧
      ApproxHallways K S' (4*R*(π/2-ω')))
    {δQ : ℝ}
    (hcert :
      ∀ K : Set Point,IsCap K (π/2) → UpperSupportClose δQ K P.cap →
      InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
      niche K (π/2)⊆K ∧
      sofaArea (π/2) K≤upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
      upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K)≤area (gerverSofa P))
    (hentry : EuclideanClose (min δT δQ)
      (midpointNormalizedSofa P S) (gerverSofa P))
    (hangleEntry : π/2-ω≤αT) :
    ∃ D : LocalData P S ω ε, D.R=R := by
  let N:=midpointNormalizedSofa P S
  have hNm:=midpointNormalizedSofa_movingWithAngle P hS
  have hNc:=ms_isCompact_of_isMovingSofaWithAngle hNm
  have hNn:=hNm.2.1.nonempty
  have htop:=midpointNormalizedSofa_top P
    (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty
  have hstrip:=moving_strip_of_top ⟨ω,hNm⟩ htop
  let K:=sofaCap N
  have hK:=sofaCap_isCap hNc hNn hstrip htop
  have hKclose0:=sofaCap_close_to_gerver hP hbox hNc hNn hstrip htop hentry
  have hmidK : horizontalMidpoint K=horizontalMidpoint P.cap := by
    unfold horizontalMidpoint K
    rw [sofaCap_upper_support hNc hNn hstrip htop ⟨le_rfl,pi_pos.le⟩,
      sofaCap_upper_support hNc hNn hstrip htop ⟨pi_pos.le,le_rfl⟩]
    rw [←horizontalMidpoint]
    calc
      horizontalMidpoint N=horizontalMidpoint (gerverSofa P) :=
        midpointNormalizedSofa_midpoint P
          (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty
      _=horizontalMidpoint P.cap := gerver_midpoint_cap hP hbox
  have hpc:=sofaCap_partial_constraints hNm
    ⟨(arccos_nonneg _).trans hω.1,hω.2⟩ htop
  obtain ⟨he0,heeps,hang,hsur,hmiss,hhall⟩ :=
    hterminal K hK (hKclose0.mono (min_le_left _ _))
      N hNc.measurableSet ω
      ⟨(arccos_nonneg _).trans hω.1,hω.2⟩ hangleEntry hpc
  obtain ⟨hwide,hNK,hAQ,hQM⟩ :=
    hcert K hK (hKclose0.mono (min_le_right _ _))
  let U:=capShape K
  let e:=area (gerverSofa P)-area U
  have hUarea : area U=sofaArea (π/2) K :=
    area_capShape_of_niche_subset hK hNK
  have hεN : ε=area (gerverSofa P)-area N := by
    rw [hε,sofaDeficit,area_midpointNormalizedSofa]
  have he0' : 0≤e := by simpa [e,U,hUarea] using he0
  have heeps' : e≤ε := by simpa [e,U,hεN] using heeps
  let x:=canonicalWideTriple hwide
  have hΔe : qDeficit P x≤e := by
    unfold qDeficit e U
    rw [hUarea]
    exact sub_le_sub_left hAQ _
  have hQclose0:=centered_cap_1001 hP hbox x
  have href : centeredReference P.cap K=P.cap := by
    unfold centeredReference horizontalReference
    rw [hmidK]
    simp [Rigid.coe_translate]
  have hQclose : EuclideanClose (kCenter*sqrt e) K P.cap := by
    rw [show x.1.1.1=K by rfl,href] at hQclose0
    exact hQclose0.mono (mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt hΔe) (by norm_num [kCenter]))
  have hsupport:=hQclose.abs_supp_sub_le hK.2.1.2.1
    (gm_isConvexBody_cap hP hbox).2.1 hK.2.1.1
    (gm_isConvexBody_cap hP hbox).1
  refine ⟨{
    N:=N,K:=K,U:=U,e:=e,R:=R,N_eq:=rfl,K_eq:=rfl,U_eq:=rfl,
    Nmove:=hNm,Ncompact:=hNc,Kcap:=hK,top:=htop,strip:=hstrip,
    midpoint:=hmidK,e_def:=rfl,eps_def:=hεN,
    e_nonneg:=he0',e_le:=heeps',
    angle:=by simpa [hεN,e,U] using hang,
    surplus:=by simpa [hεN,e,U] using hsur,
    missing:=by simpa [hεN,e,U,lambdaMissing] using hmiss,
    hallways:=by simpa [N,K] using hhall,
    cap_close:=hQclose,
    support_close:=fun t ht => hsupport t,
    niche_subset:=hNK},rfl⟩

/-- Reverse distance from Gerver to the original set, using the whole eroded
sector and the complementary missing-area budget. -/
theorem reverse_distance_23 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω ε : ℝ} (D : LocalData P S ω ε)
    (hε : 0<ε)
    {R₀ : ℝ} (hR₀ : 0<R₀)
    (hcones : ∀p∈gerverSofa P,
      ∃θ,interiorSector p θ sectorHalfAngle R₀⊆gerverSofa P)
    (hscale : CHaus*sqrt ε+sqrt 2*(kCenter*sqrt D.e)≤R₀) :
    DirectedClose (CHaus*sqrt ε) (gerverSofa P) D.N := by
  let δ:=kCenter*sqrt D.e
  let r:=sqrt 2*δ
  let ρ:=CHaus*sqrt ε
  have hδ : 0≤δ := by positivity
  have hr : 0≤r := by positivity
  have hρ : 0<ρ := mul_pos (by norm_num [CHaus]) (sqrt_pos.mpr hε)
  have herode : euclideanErosion r (gerverSofa P)⊆D.U := by
    rw [←gerver_shape_eq hP hbox,D.U_eq]
    exact orthogonal_reference_erosion hδ (gm_isCap hP hbox) D.Kcap D.support_close
  have hUf : volume D.U≠⊤ :=
    volume_ne_top_of_subset (show D.U⊆D.K by
      rw [D.U_eq]; exact sdiff_subset) D.Kcap.2.1.2.1.measure_lt_top.ne
  apply directedClose_of_available_area hUf D.missing
  intro p hp
  obtain ⟨θ,hsector⟩:=hcones p hp
  have hsinpos : 0<sin sectorHalfAngle :=
    sin_pos_of_pos_of_lt_pi referenceSectorHalfAngle_pos.1
      (by linarith [referenceSectorHalfAngle_pos.2,pi_pos])
  have hfit : r<ρ*sin sectorHalfAngle := by
    have hrat:=sector_rational_margins.2.2.2.2.2.1
    have hsin:=sinPoly7_le_sin referenceSectorHalfAngle_pos.1.le
    have hse:=sq_sqrt D.e_nonneg
    have hsp:=sq_sqrt hε.le
    have he:=D.e_le
    have hn : 0≤r := hr
    have hm : 0≤ρ*sin sectorHalfAngle := by positivity
    dsimp [r,ρ,δ,CHaus,kCenter,centeredCapCoefficient] at *
    nlinarith
  obtain ⟨W,hWsub,hWarea⟩ :=
    erodedSector_area_witness p θ referenceSectorHalfAngle_pos hρ hr hfit
  refine ⟨W,?_,?_,?_⟩
  · exact hWsub.trans ((erodedSector_subset_erosion hr hscale hsector).trans herode)
  · intro q hq
    exact (hWsub hq).2.2
  · let u:=r/ρ
    let z:=D.e/ε
    have hu0 : 0≤u := div_nonneg hr hρ.le
    have hu1 : u≤1 := by
      have := (div_lt_iff₀ hρ).2
        (hfit.trans_le (mul_le_of_le_one_right hρ.le (sin_le_one sectorHalfAngle)))
      exact this.le
    have hz0 : 0≤z := div_nonneg D.e_nonneg hε.le
    have hz1 : z≤1 := (div_le_one hε).2 D.e_le
    have hrel : (23/10:ℝ)^2*u^2=2*centeredCapCoefficient^2*z := by
      dsimp [u,z,r,ρ,δ,CHaus,kCenter,centeredCapCoefficient]
      have he:=sq_sqrt D.e_nonneg
      have hp:=sq_sqrt hε.le
      field_simp [hε.ne']
      nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2)]
    have hbudget:=centered_sector_split_budget ⟨hu0,hu1⟩ hrel
    have hmissing : area (D.U\D.N)≤
        missingBudgetCoefficient*(ε-D.e) := by
      simpa [missingBudgetCoefficient,lambdaMissing] using D.missing
    have hscaleArea :
        missingBudgetCoefficient*(ε-D.e)<
          ρ^2*sectorAreaFactor sectorHalfAngle u := by
      have hp:=sq_sqrt hε.le
      have hz : ε*(1-z)=ε-D.e := by
        dsimp [z]; field_simp [hε.ne']; ring
      have hrho : ρ^2=(23/10:ℝ)^2*ε := by
        dsimp [ρ,CHaus]; rw [mul_pow,sq_sqrt hε.le]
      nlinarith [mul_lt_mul_of_pos_left hbudget hε]
    rw [hWarea]
    exact hmissing.trans_lt (by simpa [u] using hscaleArea)

/-- Local numerical recovery once LocalData has been built. -/
theorem recover_local_23_50 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω ε : ℝ} (D : LocalData P S ω ε)
    (hε : 0<ε)
    {R₀ δN ζN τ : ℝ}
    (hR₀ : 0<R₀)
    (hcones : ∀p∈gerverSofa P,
      ∃θ,interiorSector p θ sectorHalfAngle R₀⊆gerverSofa P)
    (hscale : CHaus*sqrt ε+sqrt 2*(kCenter*sqrt D.e)≤R₀)
    (hnormal : DirectedClose ((100/49)*(kCenter*sqrt D.e+
        4*D.R*(π/2-ω))) D.N (gerverSofa P))
    (hforward : (100/49)*(kCenter*sqrt D.e+
        4*D.R*(π/2-ω))≤CHaus*sqrt ε)
    {H L : ℝ} {γ : ℝ→ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ)
    (hτ : 0<τ) (hmargin : RoofSlackMargin P.cap γ (5/51) τ)
    (hδτ : kCenter*sqrt D.e<τ)
    (hsmallArea : sqrt ε≤1/200) :
    Targets.SofaConclusions P S := by
  have hback:=reverse_distance_23 hP hbox D hε hR₀ hcones hscale
  have hclose : EuclideanClose (CHaus*sqrt ε) D.N (gerverSofa P) :=
    ⟨hnormal.mono hforward,hback⟩
  have hexcess:=quantitative_envelope_excess_with_margin hP hbox
    hroof hτ hmargin D.Kcap (by positivity) hδτ D.support_close
  have harea:=symmetric_difference_50 hP hbox
    D.Ncompact.measurableSet (by
      rw [D.U_eq]; exact D.Kcap.2.1.2.1.measurableSet.diff (niche_measurable D.K))
    D.Ncompact.measure_lt_top.ne
    (volume_ne_top_of_subset (by rw [D.U_eq]; exact sdiff_subset)
      D.Kcap.2.1.2.1.measure_lt_top.ne)
    hε.le D.e_nonneg D.e_le
    (by rw [←D.eps_def]) D.surplus
    (by positivity) le_rfl hexcess hsmallArea
  simpa [D.N_eq,CHaus] using ⟨hclose,harea⟩

/-- Exact paper target Main 10 / G.2. -/
theorem explicit_local_stability : Targets.ExplicitLocalStability := by
  intro P hP hbox
  obtain ⟨δT,αT,R,hδT,hδT1,hαT,hR,hterminal⟩ :=
    explicit_terminal_comparison hP hbox
  obtain ⟨δQ,hδQ,hδQ1,hcert⟩:=nearby_cap_certificate hP hbox
  obtain ⟨δN,ζN,hδN,hζN,hnormalRaw⟩:=directed_to_gerver_normal hP hbox
  obtain ⟨R₀,hR₀,hcones⟩:=gerver_uniform_sector hP hbox
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  obtain ⟨τ,hτ,hmargin⟩:=gerver_explicit_roof_slack hP hbox hroof
  let ρentry:=min δT (min δQ δN)
  have hρentry : 0<ρentry := lt_min hδT (lt_min hδQ hδN)
  obtain ⟨εE,hεE,hentry⟩:=
    near_maximizers_enter_midpoint_neighborhood hP hbox hρentry hαT
  let B:=(100/49)*(4*R*(31/10))
  have hA : (100/49)*kCenter<CHaus := by norm_num [kCenter,CHaus]
  obtain ⟨εF,hεF,hF⟩:=absorb_linear_term hA
    (show 0≤B by positivity)
  obtain ⟨εR,hεR,_,hRsmall⟩:=exists_sqrt_threshold
    (A:=CHaus+sqrt 2*kCenter) (by positivity) hR₀
  obtain ⟨εN,hεN,_,hNsmall⟩:=exists_sqrt_threshold
    (A:=kCenter) (by norm_num [kCenter]) hδN
  obtain ⟨ετ,hετ,_,hτsmall⟩:=exists_sqrt_threshold
    (A:=kCenter) (by norm_num [kCenter]) hτ
  let εζ:=ζN/(4*R*(31/10)+1)
  have hεζ : 0<εζ := by positivity
  have hgap : 0<area (gerverSofa P)-2.2 := by
    linarith [(gerverSofa_area_mem hP hbox).1]
  let ε₀:=min εE (min εF (min εR (min εN
    (min ετ (min εζ (min (1/40000) hgap))))))
  have hε₀ : 0<ε₀ := by
    dsimp [ε₀]
    positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro S hS hdef
  have hεnonneg:=sofaDeficit_nonneg hP hbox hS
  rcases hεnonneg.eq_or_lt with hz|hp
  · have hpin:=normalizedSofa_eq_gerver_of_zero_deficit hP hbox hS hz.symm
    have hc:=isCompact_of_isMovingSofa hS
    have hn:=hS.choose_spec.2.1.nonempty
    have hm:=midpoint_eq_translate_normalized (P:=P) hc hn
    rw [hpin] at hm
    have hmid : horizontalMidpoint (gerverSofa P)-
        horizontalMidpoint (gerverSofa P)=0 := by ring
    simp [hmid] at hm
    refine ⟨?_,?_⟩
    · constructor
      · rw [hz,sqrt_zero,mul_zero,hm]
        exact EuclideanClose.refl _ le_rfl
      · rw [hz,sqrt_zero,mul_zero,hm,symmetricDifferenceArea]
        simp
    · intro ω hω hred
      have hNm:=midpointNormalizedSofa_movingWithAngle P hω
      rw [hm] at hNm
      have he:=gerver_reduced_angle_eq hP hbox hred hNm
      rw [he,hz]
      norm_num
  · have h22 : 2.2≤area S := by
      have hsmall : sofaDeficit P S<area (gerverSofa P)-2.2 :=
        hdef.trans_le (by
          dsimp [ε₀]
          exact (min_le_right _ _).trans (min_le_right _ _))
      unfold sofaDeficit at hsmall
      linarith
    obtain ⟨ω,hred,hSω⟩:=theorem1_5_1 hS h22
    have hE := hdef.trans_le (by dsimp [ε₀]; exact min_le_left _ _)
    obtain ⟨hentryClose,hentryAngle⟩:=hentry S ω hSω hred hE
    obtain ⟨D,hDR⟩:=build_local_data hP hbox hSω hred rfl hp
      hterminal hcert
      (hentryClose.mono (by dsimp [ρentry]; exact min_le_left _ _))
      hentryAngle.le
    subst D.R
    have hsmallF : sofaDeficit P S≤εF :=
      hdef.le.trans (by dsimp [ε₀]; exact (min_le_right _ _).trans (min_le_left _ _))
    have hforward :
        (100/49)*(kCenter*sqrt D.e+4*R*(π/2-ω))≤
          CHaus*sqrt (sofaDeficit P S) := by
      have hδ:=mul_le_mul_of_nonneg_left (sqrt_le_sqrt D.e_le)
        (by norm_num [kCenter])
      have hα:=D.angle.2
      have hlin : (100/49)*(kCenter*sqrt D.e+4*R*(π/2-ω))≤
          ((100/49)*kCenter)*sqrt (sofaDeficit P S)+B*(sofaDeficit P S) := by
        dsimp [B]
        nlinarith
      exact hlin.trans (hF _ hεnonneg hsmallF)
    have hδsmall : kCenter*sqrt D.e≤δN := by
      have he:=sqrt_le_sqrt D.e_le
      exact (mul_le_mul_of_nonneg_left he (by norm_num [kCenter])).trans
        (hNsmall _ (hdef.trans_le (by
          dsimp [ε₀]
          exact (min_le_right _ _).trans ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _))))))
    have hζsmall : 4*R*(π/2-ω)≤ζN := by
      have ha:=D.angle.2
      have heps : sofaDeficit P S≤εζ := hdef.le.trans (by
        dsimp [ε₀]
        exact (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))))))
      dsimp [εζ] at heps
      have hden : 0<4*R*(31/10)+1 := by positivity
      have hm: (4*R*(31/10))*sofaDeficit P S≤ζN := by
        apply (le_div_iff₀ hden).mp at heps
        nlinarith
      nlinarith
    have hnormal:=hnormalRaw D.K D.Kcap
      (kCenter*sqrt D.e) (by positivity) hδsmall D.support_close
      D.N (by
        rw [D.K_eq,D.N_eq]
        exact subset_sofaCap D.Ncompact D.strip)
      (4*R*(π/2-ω)) (by positivity) hζsmall D.hallways
    have hscale : CHaus*sqrt (sofaDeficit P S)+
        sqrt 2*(kCenter*sqrt D.e)≤R₀ := by
      have he:=sqrt_le_sqrt D.e_le
      have hm : (CHaus+sqrt 2*kCenter)*sqrt (sofaDeficit P S)≤R₀ :=
        hRsmall _ (hdef.trans_le (by
          dsimp [ε₀]
          exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
      nlinarith [mul_le_mul_of_nonneg_left he (by positivity)]
    have hδτ : kCenter*sqrt D.e<τ := by
      have he:=sqrt_le_sqrt D.e_le
      have hm:=hτsmall _ (hdef.trans_le (by
        dsimp [ε₀]
        exact (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
      exact (mul_le_mul_of_nonneg_left he (by norm_num [kCenter])).trans_lt hm
    have hareaSmall : sqrt (sofaDeficit P S)≤1/200 := by
      have hs : sofaDeficit P S≤1/40000 := hdef.le.trans (by
        dsimp [ε₀]
        exact (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans
            ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
      nlinarith [sq_sqrt hεnonneg,sqrt_nonneg (sofaDeficit P S)]
    have hsofa:=recover_local_23_50 hP hbox D hp hR₀ hcones hscale
      hnormal hforward hroof hτ hmargin hδτ hareaSmall
    refine ⟨hsofa,?_⟩
    intro ω' hSω' hred'
    obtain ⟨hc',ha'⟩:=hentry S ω' hSω' hred' hE
    obtain ⟨D',-⟩:=build_local_data hP hbox hSω' hred' rfl hp
      hterminal hcert
      (hc'.mono (by dsimp [ρentry]; exact min_le_left _ _)) ha'.le
    exact ⟨sub_nonneg.mpr hred'.2,D'.angle.2.trans
      (mul_le_mul_of_nonneg_left
        (show sofaDeficit P S-D'.e≤sofaDeficit P S by linarith [D'.e_nonneg])
        (by norm_num))⟩

end MovingSofaQuantitative
