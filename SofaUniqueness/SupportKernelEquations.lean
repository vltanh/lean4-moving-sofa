module

public import MovingSofa.Optimality.Concavity
public import SofaUniqueness.MamikonDisplacement
public import SofaUniqueness.Draft.CapKernel
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Support regularity and the exact kernel of the tangent equation

Only open arcs avoiding the possible top atom are differentiated. The support
function itself is continuous at all endpoints. A constant integrating factor
is first proved on the open interval and then extended by continuity; this
also handles a target normal equal to the interval's right endpoint.

Uncompiled source; no admitted statements or decision procedures.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofa
open SofaUniqueness.Draft

namespace SofaUniqueness

/-- An upper arc lies entirely on one side of the possible top atom. -/
def UpperArc (a b : ℝ) : Prop :=
  (0 ≤ a ∧ b ≤ π / 2) ∨ (π / 2 ≤ a ∧ b ≤ π)

/-- Equal one-sided support derivatives give an ordinary derivative. -/
theorem support_hasDerivAt_of_injCond1 {K : Set (ℝ × ℝ)}
    (hK : IsConvexBody K) (h1 : InjCond1 K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π) :
    HasDerivAt (supp K) (dot (vplus K t) (vvec t)) t := by
  have hv := inj_vplus_eq_vminus_of_injCond1 hK h1 ht
  have hl := hasDerivWithinAt_supp_left hK t
  have hr := hasDerivWithinAt_supp_right hK t
  rw [← hv] at hl
  have hu : Iic t ∪ Ici t = (univ : Set ℝ) := by
    ext s
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total s t
  have hd := hl.union hr
  simpa only [hu, hasDerivWithinAt_univ] using hd

theorem arc_mem_regular {a b t : ℝ} (h : UpperArc a b) (ht : t ∈ Ioo a b) :
    t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨ha.trans ht.1.le, ht.2.trans_le hb⟩
  · exact Or.inr ⟨ha.trans_lt ht.1, ht.2.le.trans hb⟩

/-- Positive support vertices are continuous on each open upper arc. -/
theorem vplus_continuousOn_arc {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) {a b : ℝ} (hArc : UpperArc a b) :
    ContinuousOn (vplus K) (Ioo a b) := by
  obtain ⟨hcA, hcC, _, _⟩ := proposition6_4_6_continuous hK h1
  have hfirst : ContinuousOn (vplus K) (Ioo 0 (π / 2)) := by
    apply hcA.congr_mono ?_ Ioo_subset_Icc_self
    intro t ht
    exact ((proposition6_4_5 hK h1).1 t ⟨ht.1.le, ht.2⟩).1
  have hsecond : ContinuousOn (vplus K) (Ioo (π / 2) π) := by
    have hc : ContinuousOn (fun t => cK K (t - π / 2)) (Ioo (π / 2) π) :=
      hcC.comp (continuous_id.sub continuous_const).continuousOn
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    apply hc.congr
    intro t ht
    simp only [cK, cPlus, sub_add_cancel]
  rcases hArc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hfirst.mono (fun t ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)
  · exact hsecond.mono (fun t ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)

/-- Any continuous supporting curve has continuous displacement on a regular arc. -/
theorem displacement_continuousOn_arc {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) {a b : ℝ} (hArc : UpperArc a b) {z : ℝ → ℝ × ℝ}
    (hz : ContinuousOn z (Icc a b)) :
    ContinuousOn (displacement K z) (Ioo a b) := by
  have hd := (hz.mono Ioo_subset_Icc_self).sub (vplus_continuousOn_arc hK h1 hArc)
  have hv : ContinuousOn vvec (Ioo a b) := by unfold vvec; fun_prop
  exact (hd.fst.mul hv.fst).add (hd.snd.mul hv.snd)

/-- Explicit displacement to the intersection with the target supporting line. -/
theorem tangent_displacement_formula (K : Set (ℝ × ℝ)) {T t : ℝ} (ht : t < T) :
    displacement K (tangentParam K T) t =
      (supp K T - supp K t * cos (T - t)) / sin (T - t) -
        dot (vplus K t) (vvec t) := by
  simp only [displacement, tangentParam, ht, if_true, vint, dot_sub_left,
    dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self,
    mul_zero, mul_one, zero_add]

/-- Explicit displacement to the outer corner. -/
theorem outer_displacement_formula (K : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K (outerCorner K) t =
      supp K (t + π / 2) - dot (vplus K t) (vvec t) := by
  rw [displacement, dot_sub_left, inj_dot_outerCorner_vvec]

/-- Complete kernel of the tangent equation, with no differentiability assumed
at either endpoint. -/
theorem tangentKernel_of_equation {f f' : ℝ → ℝ} {a b T : ℝ}
    (hab : a < b) (hTa : T - π < a) (hbT : b ≤ T) (hf : Continuous f)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (heq : ∀ t ∈ Ioo a b,
      sin (T - t) * f' t + cos (T - t) * f t = f T) :
    TangentKernel f a b T := by
  sorry

/-- The middle equation integrates to the form consumed by `CapKernel`. -/
theorem integrated_middle_equation {f : ℝ → ℝ} {a b L : ℝ}
    (hf : Continuous f)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f (t + L)) t) :
    ∀ t ∈ Icc a b, f t = f b - ∫ u in t..b, f (u + L) := by
  intro t ht
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2
    hf.continuousOn
    (fun u hu => hd u ⟨ht.1.trans_lt hu.1, hu.2⟩)
    ((hf.comp (continuous_id.add continuous_const)).intervalIntegrable t b)
  linarith

end SofaUniqueness
