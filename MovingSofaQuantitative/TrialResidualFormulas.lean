module

public import MovingSofaQuantitative.TrialEnergy
public import MovingSofaQuantitative.CriticalTrialData

/-!
# Explicit residual formulas for the fixed critical trial

Uncompiled proof source. The formulas are derived from the actual half-profile,
not substituted for its energy definition. Reflection carries the fourth cap
arc and the left auxiliary arc to the first half. The harmless top endpoint is
handled separately, so the certificate need not divide by zero there.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative.CriticalTrial

variable {P : GerverParams}

def g (P : GerverParams) := rightJoin P.φ (fun t => -cos t+q*sin t) (hermiteChain (nodes P))
def dg (P : GerverParams) := rightJoin P.φ (fun t => sin t+q*cos t) (hermiteChainFirst (nodes P))

@[simp] theorem profile_value (hP : P.IsSolution) : (profile hP).value=g P := rfl
@[simp] theorem profile_first (hP : P.IsSolution) : (profile hP).first=dg P := rfl

theorem gap_values (hP : P.IsSolution) {t : ℝ} (ht : t∈Icc (0 : ℝ) P.φ) :
    g P t= -cos t+q*sin t ∧ dg P t=sin t+q*cos t := by
  rcases ht.2.lt_or_eq with h | rfl
  · simp only [g,dg,rightJoin,if_pos h]
    exact ⟨rfl,rfl⟩
  · have hn := profile_at_node hP (0 : Fin 17)
    simpa only [profile_value,profile_first,node,startValue,startSlope] using hn

def r2 (P : GerverParams) (t : ℝ) : ℝ := g P (π/2-t)-dg P t

def r3 (P : GerverParams) (t : ℝ) : ℝ :=
  (startValue P-g P t*cos(π-P.φ-t))/sin(π-P.φ-t)-dg P t

def r4 (P : GerverParams) (t : ℝ) : ℝ :=
  dg P t-(cos t*g P t+1)/sin t

def rB (P : GerverParams) (t : ℝ) : ℝ :=
  if t=π/2 then 0 else tan t*g P t+dg P t

def rD (P : GerverParams) (t : ℝ) : ℝ :=
  dg P t+(startValue P-g P t*cos(t-P.φ))/sin(t-P.φ)

def bridgeSineCoefficient (P : GerverParams) : ℝ :=
  (contactValue*cos P.φ-startValue P*cos(c P))/sin(c P-P.φ)

def scalarEnergy (P : GerverParams) : ℝ :=
  (q^2*tan P.φ + bridgeSineCoefficient P^2*(tan(c P)-tan P.φ) +
    arcSquare P.φ (π/2-P.φ) (r2 P) + arcSquare (π/2-P.φ) (π/2) (r3 P) +
    arcSquare P.φ (π/2) (r4 P) + arcSquare (c P) (π/2) (rB P) +
    arcSquare (c P) (π/2) (rD P))/2

private theorem harmonic_coefficients (a b ya yb t : ℝ) :
    harmonicBridge a b ya yb t =
      ((ya*sin b-yb*sin a)/sin(b-a))*cos t +
      ((yb*cos a-ya*cos b)/sin(b-a))*sin t := by
  unfold harmonicBridge
  rw [sin_sub,sin_sub]
  ring

private theorem harmonicFirst_coefficients (a b ya yb t : ℝ) :
    harmonicBridgeFirst a b ya yb t =
      -((ya*sin b-yb*sin a)/sin(b-a))*sin t +
      ((yb*cos a-ya*cos b)/sin(b-a))*cos t := by
  unfold harmonicBridgeFirst
  rw [cos_sub,cos_sub]
  ring

private theorem harmonic_tangent_residual (A B T t : ℝ) (hs : sin(T-t)≠0) :
    tangentResidual T (fun u => A*cos u+B*sin u)
      (fun u => -A*sin u+B*cos u) t=0 := by
  have hcos : cos T=cos t*cos(T-t)-sin t*sin(T-t) := by rw [←cos_add,add_sub_cancel]
  have hsin : sin T=sin t*cos(T-t)+cos t*sin(T-t) := by rw [←sin_add,add_sub_cancel]
  unfold tangentResidual
  rw [hcos,hsin]
  field_simp [hs]
  ring

/-- The exact unpinned residuals on the cap's first three arcs. -/
theorem cap_residual_formulas (hP : P.IsSolution) :
    (∀ t∈Ioo (0 : ℝ) P.φ,
      tangentResidual (π/2) (profile hP).symmetricValue (profile hP).symmetricDerivative t = -q/cos t) ∧
    (∀ t∈Ioo P.φ (π/2-P.φ),
      cornerResidual (profile hP).symmetricValue (profile hP).symmetricDerivative t=r2 P t) ∧
    (∀ t∈Ioo (π/2-P.φ) (π/2),
      tangentResidual (π-P.φ) (profile hP).symmetricValue (profile hP).symmetricDerivative t=r3 P t) := by
  have hO := GerverParams.gs_ord hP
  have hφv : P.φ<π/2 := by linarith [hO.2.1,hO.2.2,pi_pos]
  refine ⟨?_,?_,?_⟩
  · intro t ht
    have hc : cos t≠0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1,pi_pos],ht.2.trans hφv⟩).ne'
    have hg := gap_values hP ⟨ht.1.le,ht.2.le⟩
    simp only [tangentResidual,HalfCapProfile.symmetricValue_top,
      HalfCapProfile.symmetricValue,HalfCapProfile.symmetricDerivative,
      if_pos (ht.2.trans hφv).le,if_pos (ht.2.trans hφv),profile_value,profile_first,
      sin_pi_div_two_sub,cos_pi_div_two_sub,hg.1,hg.2]
    field_simp [hc]
    linear_combination -q*sin_sq_add_cos_sq t
  · intro t ht
    have htv : t<π/2 := by linarith [ht.2,hO.1]
    have hplus : π/2<t+π/2 := by linarith [ht.1,hO.1]
    simp only [cornerResidual,HalfCapProfile.symmetricValue,HalfCapProfile.symmetricDerivative,
      if_neg (not_le.mpr hplus),if_pos htv,show π-(t+π/2)=π/2-t by ring,
      profile_value,profile_first,r2]
  · intro t ht
    have hTv : π/2<π-P.φ := by linarith
    have hcut := profile_cut_value hP
    simp only [tangentResidual,HalfCapProfile.symmetricValue,HalfCapProfile.symmetricDerivative,
      if_neg (not_le.mpr hTv),if_pos ht.2.le,if_pos ht.2,
      show π-(π-P.φ)=P.φ by ring,hcut,profile_value,profile_first,r3]

/-- Reflection of the last cap residual, including its vanishing tail. -/
theorem last_cap_residual (hP : P.IsSolution) {t : ℝ} (ht : t∈Ioo (π/2) π) :
    tangentResidual π (profile hP).symmetricValue (profile hP).symmetricDerivative t = r4 P (π-t) := by
  have htop : π/2<π := by linarith [pi_pos]
  have hsin : sin t≠0 := (sin_pos_of_pos_of_lt_pi (by linarith [ht.1,pi_pos]) ht.2).ne'
  simp only [tangentResidual,HalfCapProfile.symmetricValue,HalfCapProfile.symmetricDerivative,
    if_neg (not_le.mpr htop),if_neg (not_le.mpr ht.1),if_neg (not_lt.mpr ht.1.le),
    sub_self,profile_value,profile_first,←profile_value hP,profile_zero hP,
    r4,profile_value,cos_pi_sub,sin_pi_sub]
  ring

theorem r4_gap_zero (hP : P.IsSolution) {t : ℝ} (ht : t∈Ioo (0 : ℝ) P.φ) : r4 P t=0 := by
  have hO := GerverParams.gs_ord hP
  have hs : sin t≠0 := (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,hO.2.1,hO.2.2,pi_pos])).ne'
  rw [r4,(gap_values hP (Ioo_subset_Icc_self ht)).1,(gap_values hP (Ioo_subset_Icc_self ht)).2]
  field_simp [hs]
  linear_combination sin_sq_add_cos_sq t

/-- The B inactive residual is one constant times secant. The active residual
is the additional first-order penalty appearing in the full Q deficit. -/
theorem right_aux_residual (hP : P.IsSolution) :
    (∀ t∈Ioo P.φ (c P),tangentResidual (π/2)
      (trialAuxiliaryProfile (profile hP) (c P)) (trialAuxiliaryDerivative (profile hP) (c P)) t =
      bridgeSineCoefficient P/cos t) ∧
    (∀ t∈Ioo (c P) (π/2),tangentResidual (π/2)
      (trialAuxiliaryProfile (profile hP) (c P)) (trialAuxiliaryDerivative (profile hP) (c P)) t=rB P t) := by
  have hord := positions hP
  have htop : trialAuxiliaryProfile (profile hP) (c P) (π/2)=0 := by
    simp [trialAuxiliaryProfile,not_le.mpr hord.2,HalfCapProfile.top_zero]
  constructor
  · intro t ht
    have hc : cos t≠0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1,hP.1,pi_pos],ht.2.trans hord.2⟩).ne'
    rw [tangentResidual,htop,trialAuxiliaryProfile,trialAuxiliaryDerivative,
      if_pos ht.2.le,if_pos ht.2,profile_cut_value,profile_contact_value,
      harmonic_coefficients,harmonicFirst_coefficients]
    simp only [sin_pi_div_two_sub,cos_pi_div_two_sub,bridgeSineCoefficient]
    field_simp [hc]
    linear_combination ((contactValue*cos P.φ-startValue P*cos(c P))/sin(c P-P.φ))*sin_sq_add_cos_sq t
  · intro t ht
    simp only [tangentResidual,htop,trialAuxiliaryProfile,trialAuxiliaryDerivative,
      if_neg (not_le.mpr ht.1),if_neg (not_lt.mpr ht.1.le),profile_value,profile_first,
      sin_pi_div_two_sub,cos_pi_div_two_sub,rB,if_neg (ne_of_lt ht.2),tan_eq_sin_div_cos]
    ring

/-- After reflection, the D active residual is -rD and its inactive residual
vanishes identically; sign disappears in the squared energy. -/
theorem left_aux_residual (hP : P.IsSolution) :
    (∀ t∈Ioo (π/2) (π/2+P.θ),tangentResidual (π-P.φ)
      (fun u => trialAuxiliaryProfile (profile hP) (c P) (π-u))
      (fun u => -trialAuxiliaryDerivative (profile hP) (c P) (π-u)) t= -rD P (π-t)) ∧
    (∀ t∈Ioo (π/2+P.θ) (π-P.φ),tangentResidual (π-P.φ)
      (fun u => trialAuxiliaryProfile (profile hP) (c P) (π-u))
      (fun u => -trialAuxiliaryDerivative (profile hP) (c P) (π-u)) t=0) := by
  have hord := positions hP
  have hs : sin(c P-P.φ)≠0 :=
    (sin_pos_of_pos_of_lt_pi (sub_pos.mpr hord.1) (by linarith [hord.2,hP.1,pi_pos])).ne'
  have hcut : trialAuxiliaryProfile (profile hP) (c P) P.φ= -startValue P := by
    rw [trialAuxiliaryProfile,if_pos hord.1.le,(harmonicBridge_endpoints hs).1,profile_cut_value]
  constructor
  · intro t ht
    have hu : c P<π-t := by unfold c; linarith [ht.2]
    simp only [tangentResidual,show π-(π-P.φ)=P.φ by ring,hcut,
      trialAuxiliaryProfile,trialAuxiliaryDerivative,if_neg (not_le.mpr hu),
      if_neg (not_lt.mpr hu.le),neg_neg,profile_value,profile_first,rD,
      show π-P.φ-t=(π-t)-P.φ by ring]
    ring
  · intro t ht
    have hu : π-t<c P := by unfold c; linarith [ht.1]
    have hsin : sin(π-P.φ-t)≠0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1,hP.1,pi_pos])).ne'
    rw [tangentResidual]
    simp only [show π-(π-P.φ)=P.φ by ring,hcut,trialAuxiliaryProfile,trialAuxiliaryDerivative,
      if_pos hu.le,if_pos hu,neg_neg,profile_cut_value,profile_contact_value,
      harmonic_coefficients,harmonicFirst_coefficients]
    simp only [sin_pi_sub,cos_pi_sub]
    field_simp [hs,hsin]
    simp only [sin_sub,cos_sub,sin_pi_sub,cos_pi_sub]
    ring_nf
    nlinarith [sin_sq_add_cos_sq P.φ,sin_sq_add_cos_sq t]

/-- Scalar secant energy on a nonsingular compact interval. -/
private theorem secant_energy {a b k : ℝ} (hab : a≤b)
    (hc : ∀t∈Icc a b,cos t≠0) : arcSquare a b (fun t => k/cos t)=k^2*(tan b-tan a) := by
  unfold arcSquare
  have he : (fun t => (k/cos t)^2)=(fun t => k^2*(1/cos t)^2) := by funext t; ring
  rw [he,intervalIntegral.integral_const_mul,secant_sq_integral hab hc]

/-- Reversing an interval under t -> pi-t preserves square energy. -/
private theorem reflected_square (a b : ℝ) (r : ℝ→ℝ) :
    arcSquare a b (fun t => r (π-t))=arcSquare (π-b) (π-a) r :=
  intervalIntegral.integral_comp_sub_left (fun t => r t^2) π

/-- The full energy agrees with the explicit form certified in the numerical
file. The integrability inputs are supplied by the genuine trial bodies. -/
theorem trialEnergy_eq_scalar (hP : P.IsSolution) (hbox : P.InBox)
    (hiB : IntervalIntegrable (fun t => tangentResidual (π/2)
      (trialAuxiliaryProfile (profile hP) (c P)) (trialAuxiliaryDerivative (profile hP) (c P)) t^2)
      volume P.φ (π/2))
    (hiD : IntervalIntegrable (fun t => tangentResidual (π-P.φ)
      (fun u => trialAuxiliaryProfile (profile hP) (c P) (π-u))
      (fun u => -trialAuxiliaryDerivative (profile hP) (c P) (π-u)) t^2)
      volume (π/2) (π-P.φ)) : trialEnergy (profile hP) (c P)=scalarEnergy P := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hord := positions hP
  let F := profile hP
  have hdata := halfCapProfile_data hP hbox F
  have hepin := fourResidualEnergy_pinning hφ F.symmetricValue F.symmetricDerivative
  have unpin {a b T : ℝ} (hab : a≤b) (hs : ∀t∈Ioo a b,sin(T-t)≠0)
      (hi : IntervalIntegrable (fun t => tangentResidual T F.pinnedProfile F.pinnedProfileDerivative t^2) volume a b) :
      IntervalIntegrable (fun t => tangentResidual T F.symmetricValue F.symmetricDerivative t^2) volume a b := by
    apply intervalIntegrable_of_eqOn_Ioo hab hi
    intro t ht
    simp only [HalfCapProfile.pinnedProfile,HalfCapProfile.pinnedProfileDerivative,
      tangentResidual_pinned T F.symmetricValue F.symmetricDerivative t (hs t ht)]
  have hi4 := unpin (a := π/2) (b := π) (T := π) (by linarith [pi_pos])
    (fun t ht => (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1,pi_pos])).ne') hdata.last_sq
  have eqI {a b : ℝ} (hab : a≤b) {f g : ℝ→ℝ} (he : ∀t∈Ioo a b,f t=g t) :
      arcSquare a b f=arcSquare a b g := by
    unfold arcSquare
    exact intervalIntegral_eq_of_eqOn_Ioo hab (fun t ht => by rw [he t ht])
  have cap1 := eqI hφ.1.le (cap_residual_formulas hP).1
  rw [secant_energy hφ.1.le (fun t ht =>
    (cos_pos_of_mem_Ioo ⟨by linarith [ht.1,pi_pos],by linarith [ht.2,hφ.2,pi_pos]⟩).ne'),
    tan_zero,sub_zero,neg_sq] at cap1
  have cap2 := eqI (by linarith [hφ.2] : P.φ≤π/2-P.φ) (cap_residual_formulas hP).2.1
  have cap3 := eqI (by linarith [hφ.1] : π/2-P.φ≤π/2) (cap_residual_formulas hP).2.2
  have cap4 := eqI (by linarith [pi_pos] : π/2≤π) (last_cap_residual hP)
  rw [reflected_square,sub_self,show π-π/2=π/2 by ring] at cap4
  have hi4' : IntervalIntegrable (fun t => r4 P t^2) volume 0 (π/2) := by
    have htmp := intervalIntegrable_of_eqOn_Ioo (by linarith [pi_pos]) hi4
      (fun t ht => by rw [last_cap_residual hP ht])
    simpa only [sub_self,show π-π/2=π/2 by ring] using htmp.comp_sub_left π
  have cap4split := arcSquare_split hi4' hφ.1.le (by linarith [hφ.2,pi_pos])
  rw [arcSquare_eq_zero_of_zero_on hφ.1.le (r4_gap_zero hP),zero_add] at cap4split
  have auxBsplit := arcSquare_split hiB hord.1.le hord.2.le
  have auxB1 := eqI hord.1.le (right_aux_residual hP).1
  rw [secant_energy hord.1.le (fun t ht =>
    (cos_pos_of_mem_Ioo ⟨by linarith [ht.1,hφ.1,pi_pos],ht.2.trans_lt hord.2⟩).ne')] at auxB1
  have auxB2 := eqI hord.2.le (right_aux_residual hP).2
  have hDcut : π/2≤π/2+P.θ ∧ π/2+P.θ≤π-P.φ := by
    unfold c at hord
    constructor <;> linarith [hφ.1]
  have auxDsplit := arcSquare_split hiD hDcut.1 hDcut.2
  have auxD1 := eqI hDcut.1 (left_aux_residual hP).1
  have hneg : arcSquare (π/2) (π/2+P.θ) (fun t => -rD P (π-t))=
      arcSquare (π/2) (π/2+P.θ) (fun t => rD P (π-t)) := by
    unfold arcSquare
    simp only [neg_sq]
  rw [hneg,reflected_square,show π-(π/2+P.θ)=c P by unfold c; ring,
    show π-π/2=π/2 by ring] at auxD1
  have auxD2 := arcSquare_eq_zero_of_zero_on hDcut.2 (left_aux_residual hP).2
  unfold trialEnergy fourResidualEnergy scalarEnergy
  rw [cap1,cap2,cap3,cap4,←cap4split,←auxBsplit,auxB1,auxB2,←auxDsplit,auxD1,auxD2]
  ring

end MovingSofaQuantitative.CriticalTrial
