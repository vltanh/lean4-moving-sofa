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

/-- On a nonnegative interval of width below 1/10,
1-w²/6 <= sinc(w) <= 1. The lower endpoint is strictly positive.
The result may be safely inverted, unlike the raw sin(w)/w formula.
-/
def sincSmall (I : Interval) : Option Interval :=
  if 0 ≤ I.lo ∧ I.hi ≤ (1/10:ℚ) then
    some ⟨1-I.hi^2/6,1⟩
  else none

theorem sincSmall_lower_pos {I J : Interval}
    (h : I.sincSmall = some J) : 0 < J.lo := by
  unfold sincSmall at h
  split_ifs at h with hb
  · obtain rfl := Option.some.inj h
    have hh : I.hi ≤ (1/10:ℚ) := hb.2
    have hlo : 0 ≤ I.hi := (le_trans hb.1 (by
      exact le_of_lt (lt_of_le_of_lt hh (by norm_num))))
    change (0:ℚ) < 1-I.hi^2/6
    nlinarith [sq_nonneg (I.hi:ℚ)]
  · contradiction

/-- The interval evaluation encloses the real regularized sinc on every
point of the input enclosure. Neither endpoint requires a nonzero argument.
-/
theorem sincSmall_sound {I J : Interval} {w : ℝ}
    (h : I.sincSmall = some J) (hw : I.Contains w) :
    J.Contains (sincRegularized w) := by
  unfold sincSmall at h
  split_ifs at h with hb
  · obtain rfl := Option.some.inj h
    have hw0 : 0≤w := (by exact_mod_cast hb.1).trans hw.1
    have hwmax : w≤1/10 :=
      hw.2.trans (by exact_mod_cast hb.2)
    have hi : w≤(I.hi:ℝ) := hw.2
    by_cases hz : w=0
    · subst w
      simp [sincRegularized]
      have hi2 : (I.hi:ℝ)^2 ≤ (1/10:ℝ)^2 := by
        have hh0 : (0:ℝ)≤I.hi := by
          exact_mod_cast (le_trans hb.1 (le_of_lt (lt_of_le_of_lt hb.2
            (by norm_num : (1/10:ℚ)<1))))
        nlinarith
      constructor
      · push_cast
        nlinarith
      · norm_num
    · have hpos : 0<w := lt_of_le_of_ne hw0 (Ne.symm hz)
      have hsinLower := MovingSofaQuantitative.sinPoly3_le_sin hw0
      have hsinUpper := Real.sin_le hpos.le
      have hlower : 1-w^2/6 ≤ sin w/w := by
        apply (le_div_iff₀ hpos).2
        unfold MovingSofaQuantitative.sinPoly3 at hsinLower
        nlinarith
      have hupper : sin w/w ≤ 1 := by
        apply (div_le_iff₀ hpos).2
        linarith
      have hi2 : w^2 ≤ (I.hi:ℝ)^2 := by
        nlinarith [hw0,hi]
      change ((1-I.hi^2/6:ℚ):ℝ)≤sincRegularized w ∧
        sincRegularized w≤1
      rw [sincRegularized,if_neg hz]
      push_cast
      constructor
      · linarith
      · exact hupper
  · contradiction

/-- A successful sinc enclosure can always be inverted. -/
theorem sincSmall_reciprocal_exists {I J : Interval}
    (h : I.sincSmall=some J) :
    ∃ R : Interval, J.reciprocal=some R := by
  have hp:=sincSmall_lower_pos h
  refine ⟨⟨1/J.hi,1/J.lo⟩,?_⟩
  simp [reciprocal,hp]

end Interval
end MovingSofaQuantitative.Certificates
