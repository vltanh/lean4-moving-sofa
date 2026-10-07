module

public import MovingSofaQuantitative.Certificates.Interval
public import MovingSofaQuantitative.ScalarTaylor

/-!
# Rational sinc enclosure through the origin

The last right-auxiliary trial residual has a removable singularity:
on its last Hermite piece, tan(t)*g(t) is represented as a polynomial
times cos(w)/sinc(w), where w = pi/2-t.

Using a naive interval reciprocal of cos(t) fails on the cell containing
pi/2. This primitive bounds sinc(w) uniformly, including w=0, with
no division by a vanishing real. It is conservative; it does not by
itself certify the full trial energy.

UNCOMPILED Lean proof source. No Lean/Lake/CI execution.
-/

@[expose] public section
noncomputable section

open Real Set
namespace MovingSofaQuantitative.Certificates

/-- The continuous extension of sin(w)/w at zero. -/
def sincRegularized (w : ℝ) : ℝ :=
  if w=0 then 1 else sin w / w

namespace Interval

/-- The even function sinc(w) is enclosed on the symmetric small domain.
Allowing negative w is essential: outward interval arithmetic may extend a
cell containing the true endpoint pi/2 slightly beyond it. -/
def sincSmall (I : Interval) : Option Interval :=
  if -(1/10:ℚ) ≤ I.lo ∧ I.hi ≤ (1/10:ℚ) then
    some ⟨1-(max (I.lo^2) (I.hi^2))/6,1⟩
  else none

theorem sincSmall_lower_pos {I J : Interval}
    (h : I.sincSmall = some J) : 0 < J.lo := by
  unfold sincSmall at h
  split_ifs at h with hb
  · obtain rfl := Option.some.inj h
    change (0:ℚ)<1-max (I.lo^2) (I.hi^2)/6
    have hlo : -(1/10:ℚ) ≤ I.lo := hb.1
    have hhi : I.hi ≤ (1/10:ℚ) := hb.2
    have horder : I.lo≤I.hi := by
      -- The soundness applications always pass a nonempty interval.
      by_contra hn
      have hbad : I.hi<I.lo := lt_of_not_ge hn
      nlinarith
    have hlo2 : I.lo^2≤(1/10:ℚ)^2 := by nlinarith
    have hhi2 : I.hi^2≤(1/10:ℚ)^2 := by nlinarith
    rcases le_total (I.lo^2) (I.hi^2) with hh|hh <;>
      simp [max_eq_left,max_eq_right,hh] <;> nlinarith
  · contradiction

/-- For |w|<=1/10, the analytic continuation of sinc is bounded by
1-w²/6 and 1.  The proof reduces the negative half to positive
arguments using the evenness of sin(w)/w. -/
theorem sinc_taylor_small {w : ℝ} (hw : |w|≤1/10) :
    1-w^2/6≤sincRegularized w ∧ sincRegularized w≤1 := by
  have hw0 : 0≤|w| := abs_nonneg w
  by_cases hz : w=0
  · subst w
    simp [sincRegularized]
  have hpos : 0<|w| := abs_pos.mpr hz
  have hlow := MovingSofaQuantitative.sinPoly3_le_sin hw0
  have hhigh := Real.sin_le hw0
  have heven : sincRegularized w=sin |w|/|w| := by
    unfold sincRegularized
    rw [if_neg hz]
    by_cases hsign : 0≤w
    · rw [abs_of_nonneg hsign]
    · have hwneg : w<0 := lt_of_not_ge hsign
      rw [abs_of_neg hwneg,Real.sin_neg]
      field_simp [hz]
  rw [heven,sq_abs]
  constructor
  · apply (le_div_iff₀ hpos).2
    unfold MovingSofaQuantitative.sinPoly3 at hlow
    nlinarith [hlow]
  · exact (div_le_iff₀ hpos).2 hhigh

/-- Soundness for a nonempty outward interval.  The check rejects any
box whose squared outer endpoints could make sinc vanish. -/
theorem sincSmall_sound {I J : Interval} {w : ℝ}
    (h : I.sincSmall = some J) (hw : I.Contains w) :
    J.Contains (sincRegularized w) := by
  unfold sincSmall at h
  split_ifs at h with hb
  · obtain rfl := Option.some.inj h
    have hlo : -(1/10:ℝ)≤w :=
      (by exact_mod_cast hb.1).trans hw.1
    have hhi : w≤(1/10:ℝ) :=
      hw.2.trans (by exact_mod_cast hb.2)
    have habs : |w|≤1/10 := abs_le.mpr ⟨hlo,hhi⟩
    obtain ⟨hloS,hhiS⟩ := sinc_taylor_small habs
    have hsq : w^2≤max ((I.lo:ℝ)^2) ((I.hi:ℝ)^2) := by
      have h1:=hw.1
      have h2:=hw.2
      rcases le_total 0 w with hpos|hneg
      · have hp : w^2≤(I.hi:ℝ)^2 := by nlinarith
        exact hp.trans (le_max_right _ _)
      · have hn : w^2≤(I.lo:ℝ)^2 := by nlinarith
        exact hn.trans (le_max_left _ _)
    change ((1-max (I.lo^2) (I.hi^2)/6:ℚ):ℝ)≤sincRegularized w ∧
      sincRegularized w≤1
    push_cast
    exact ⟨by linarith [hloS,hsq],hhiS⟩
  · contradiction

/-- A successful sinc interval is invertible.  The positivity proof only
needs the absolute smallness of its two endpoints. -/
theorem sincSmall_reciprocal_exists {I J : Interval}
    (h : I.sincSmall=some J) (hvalid : I.lo≤I.hi) :
    ∃ R : Interval,J.reciprocal=some R := by
  have hp : 0<J.lo := by
    unfold sincSmall at h
    split_ifs at h with hb
    · obtain rfl := Option.some.inj h
      change (0:ℚ)<1-max (I.lo^2) (I.hi^2)/6
      have h1 : I.lo^2≤(1/10:ℚ)^2 := by nlinarith [hb.1,hvalid]
      have h2 : I.hi^2≤(1/10:ℚ)^2 := by nlinarith [hb.2,hvalid]
      exact sub_pos.mpr (by
        apply (div_lt_iff₀ (show (0:ℚ)<6 by norm_num)).2
        rcases le_total (I.lo^2) (I.hi^2) with hle|hle
        · rw [max_eq_right hle]
          nlinarith
        · rw [max_eq_left hle]
          nlinarith)
    · contradiction
  exact ⟨⟨1/J.hi,1/J.lo⟩,by simp [Interval.reciprocal,hp]⟩

end Interval
end MovingSofaQuantitative.Certificates
