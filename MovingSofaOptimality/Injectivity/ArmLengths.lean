module

public import MovingSofaOptimality.Angle.RightAngle
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The injectivity condition (§6.1) and arm lengths (§6.2)

Definitions 6.1.1–6.1.2 (`def:injectivity-condition`), 6.2.1 (`def:cap-tangent-arm-length`),
6.2.2 (one-sided derivatives, taken from Mathlib), Propositions 6.2.1–6.2.2, Theorem 6.2.3
(`thm:inner-corner-deriv`), Lemma 6.2.4 (`lem:arm-length-convolution`) and Theorem 6.2.5
(`thm:arm-length-differentiation`).

From this chapter on the rotation angle is `ω = π/2` (Definition 6.1.1,
`def:cap-space-right-angle`): the cap space `𝒦^c` is `capSpace (π/2)` and `𝒜` is `sofaArea (π/2)`.

**Reading of Proposition 6.2.2.** The paper writes `f^±_{K^m}(t) = g^∓_K(t)`; the reflection also
replaces `t` by `π/2 - t` (as Lemma 6.5.2 uses), and we state that.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

/-- Condition (1) of the injectivity condition: `σ_K = r_K(t) dt` on `[0, π/2)` and
`σ_K = s_K(t - π/2) dt` on `(π/2, π]` for measurable `r_K, s_K ≥ 0`. -/
def InjCond1 (K : Set (ℝ × ℝ)) : Prop :=
  ∃ r s : ℝ → ℝ, Measurable r ∧ Measurable s ∧ (∀ t, 0 ≤ r t) ∧ (∀ t, 0 ≤ s t) ∧
    (sigma K).restrict (Ico 0 (π / 2)) =
      (volume.restrict (Ico 0 (π / 2))).withDensity (fun t => ENNReal.ofReal (r t)) ∧
    (sigma K).restrict (Ioc (π / 2) π) =
      (volume.restrict (Ioc (π / 2) π)).withDensity (fun t => ENNReal.ofReal (s (t - π / 2)))

/-- Condition (2): the inner corner `x_K : [0, π/2] → ℝ²` is continuously differentiable. -/
def InjCond2 (K : Set (ℝ × ℝ)) : Prop := ContDiffOn ℝ 1 (innerCorner K) (Icc 0 (π / 2))

/-- Condition (3): `x_K'(t) · u_t < 0` and `x_K'(t) · v_t > 0` for `t ∈ (0, π/2)`. -/
def InjCond3 (K : Set (ℝ × ℝ)) : Prop :=
  ∀ t ∈ Ioo 0 (π / 2), dot (deriv (innerCorner K) t) (uvec t) < 0 ∧
    0 < dot (deriv (innerCorner K) t) (vvec t)

/-- A cap `K ∈ 𝒦^c` satisfies the injectivity condition (Definition 6.1.2,
`def:injectivity-condition`). -/
def SatisfiesInjectivity (K : Set (ℝ × ℝ)) : Prop := InjCond1 K ∧ InjCond2 K ∧ InjCond3 K

/-- The arm length `f_K⁺(t) = (y_K(t) - A_K⁺(t)) · v_t` (Definition 6.2.1). -/
noncomputable def fPlus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (outerCorner K t - aPlus K t) (vvec t)
/-- The arm length `f_K⁻(t) = (y_K(t) - A_K⁻(t)) · v_t`. -/
noncomputable def fMinus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  dot (outerCorner K t - aMinus K t) (vvec t)
/-- The arm length `g_K⁺(t) = (y_K(t) - C_K⁺(t)) · u_t`. -/
noncomputable def gPlus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (outerCorner K t - cPlus K t) (uvec t)
/-- The arm length `g_K⁻(t) = (y_K(t) - C_K⁻(t)) · u_t`. -/
noncomputable def gMinus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  dot (outerCorner K t - cMinus K t) (uvec t)

/-! ### Elementary identities for the arm lengths -/

/-- If `p · u_t = q · u_t`, then `p = q + ((p - q) · v_t) v_t`. -/
lemma inj_eq_add_smul_vvec {p q : ℝ × ℝ} {t : ℝ} (h : dot p (uvec t) = dot q (uvec t)) :
    p = q + dot (p - q) (vvec t) • vvec t :=
  sub_eq_iff_eq_add'.1 (sub_eq_smul_vvec h.symm)

/-- If `p · v_t = q · v_t`, then `p = q + ((p - q) · u_t) u_t`. -/
lemma inj_eq_add_smul_uvec {p q : ℝ × ℝ} {t : ℝ} (h : dot p (vvec t) = dot q (vvec t)) :
    p = q + dot (p - q) (uvec t) • uvec t := by
  have e := eq_dot_uvec_smul_add (p - q) t
  have h' : dot (p - q) (vvec t) = 0 := by rw [dot_sub_left, h, sub_self]
  rw [h', zero_smul, add_zero] at e
  rw [← e]; abel

/-- `y_K(t) · u_t = h_K(t)`. -/
lemma inj_dot_outerCorner_uvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (outerCorner K t) (uvec t) = supp K t := by
  rw [proposition2_2_2_outerCorner]
  simp [dot_add_left, dot_smul_left]

/-- `y_K(t) · v_t = h_K(t + π/2)`. -/
lemma inj_dot_outerCorner_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (outerCorner K t) (vvec t) = supp K (t + π / 2) := by
  rw [proposition2_2_2_outerCorner]
  simp [dot_add_left, dot_smul_left]

/-- `C_K⁺(t) · v_t = h_K(t + π/2)`. -/
lemma inj_dot_cPlus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (cPlus K t) (vvec t) = supp K (t + π / 2) := by
  rw [cPlus, ← uvec_add_pi_div_two, dot_vplus_uvec]

/-- `C_K⁻(t) · v_t = h_K(t + π/2)`. -/
lemma inj_dot_cMinus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (cMinus K t) (vvec t) = supp K (t + π / 2) := by
  rw [cMinus, ← uvec_add_pi_div_two, dot_vminus_uvec]

/-- `f_K⁺(t) = h_K(t + π/2) - v_K⁺(t) · v_t`. -/
lemma inj_fPlus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    fPlus K t = supp K (t + π / 2) - dot (vplus K t) (vvec t) := by
  rw [fPlus, dot_sub_left, inj_dot_outerCorner_vvec, aPlus]

/-- `f_K⁻(t) = h_K(t + π/2) - v_K⁻(t) · v_t`. -/
lemma inj_fMinus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    fMinus K t = supp K (t + π / 2) - dot (vminus K t) (vvec t) := by
  rw [fMinus, dot_sub_left, inj_dot_outerCorner_vvec, aMinus]

/-- `g_K⁺(t) = h_K(t) + v_K⁺(t + π/2) · v_{t + π/2}`. -/
lemma inj_gPlus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    gPlus K t = supp K t + dot (vplus K (t + π / 2)) (vvec (t + π / 2)) := by
  rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus, vvec_add_pi_div_two, dot_neg_right]
  ring

/-- `g_K⁻(t) = h_K(t) + v_K⁻(t + π/2) · v_{t + π/2}`. -/
lemma inj_gMinus_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    gMinus K t = supp K t + dot (vminus K (t + π / 2)) (vvec (t + π / 2)) := by
  rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec, cMinus, vvec_add_pi_div_two, dot_neg_right]
  ring

/-- **Proposition 6.2.1** (`pro:cap-tangent-arm-length`). `y_K(t) = A_K^±(t) + f_K^±(t) v_t` and
`y_K(t) = C_K^±(t) + g_K^±(t) u_t`. -/
theorem proposition6_2_1 {K : Set (ℝ × ℝ)} {t : ℝ} :
    outerCorner K t = aPlus K t + fPlus K t • vvec t ∧
      outerCorner K t = aMinus K t + fMinus K t • vvec t ∧
      outerCorner K t = cPlus K t + gPlus K t • uvec t ∧
      outerCorner K t = cMinus K t + gMinus K t • uvec t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inj_eq_add_smul_vvec (by rw [inj_dot_outerCorner_uvec, aPlus, dot_vplus_uvec])
  · exact inj_eq_add_smul_vvec (by rw [inj_dot_outerCorner_uvec, aMinus, dot_vminus_uvec])
  · exact inj_eq_add_smul_uvec (by rw [inj_dot_outerCorner_vvec, inj_dot_cPlus_vvec])
  · exact inj_eq_add_smul_uvec (by rw [inj_dot_outerCorner_vvec, inj_dot_cMinus_vvec])

/-- For `ω = π/2`, the mirror reflection `M_ω` is the reflection `(x, y) ↦ (-x, y)`. -/
lemma inj_mirror_pi_div_two (p : ℝ × ℝ) : mirror (π / 2) p = (-p.1, p.2) := by
  simp [mirror, show π / 2 + π / 2 = π by ring]

/-- `M_{π/2}` is additive. -/
lemma inj_mirror_sub (p q : ℝ × ℝ) :
    mirror (π / 2) p - mirror (π / 2) q = mirror (π / 2) (p - q) := by
  simp only [inj_mirror_pi_div_two, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
  congr 1; ring

/-- `M_{π/2} w · v_t = w · u_{π/2 - t}`. -/
lemma inj_dot_mirror_vvec (w : ℝ × ℝ) (t : ℝ) :
    dot (mirror (π / 2) w) (vvec t) = dot w (uvec (π / 2 - t)) := by
  simp only [inj_mirror_pi_div_two, dot, vvec, uvec, cos_pi_div_two_sub, sin_pi_div_two_sub]
  ring

/-- `M_{π/2} w · u_t = w · v_{π/2 - t}`. -/
lemma inj_dot_mirror_uvec (w : ℝ × ℝ) (t : ℝ) :
    dot (mirror (π / 2) w) (uvec t) = dot w (vvec (π / 2 - t)) := by
  simp only [inj_mirror_pi_div_two, dot, vvec, uvec, cos_pi_div_two_sub, sin_pi_div_two_sub]
  ring

/-- **Proposition 6.2.2** (`pro:cap-tangent-arm-mirror`), with `t` replaced by `π/2 - t` on the
right (see the module docstring). -/
theorem proposition6_2_2 {K : Set (ℝ × ℝ)} {t : ℝ} :
    fPlus (mirrorCap K (π / 2)) t = gMinus K (π / 2 - t) ∧
      fMinus (mirrorCap K (π / 2)) t = gPlus K (π / 2 - t) ∧
      gPlus (mirrorCap K (π / 2)) t = fMinus K (π / 2 - t) ∧
      gMinus (mirrorCap K (π / 2)) t = fPlus K (π / 2 - t) := by
  have hy := (proposition2_5_4_hallway (K := K) (ω := π / 2) t).2.2.1
  have hv := proposition2_5_4_vertices (K := K) (ω := π / 2) t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fPlus, hy, hv.1, inj_mirror_sub, inj_dot_mirror_vvec, gMinus]
  · rw [fMinus, hy, hv.2.1, inj_mirror_sub, inj_dot_mirror_vvec, gPlus]
  · rw [gPlus, hy, hv.2.2.1, inj_mirror_sub, inj_dot_mirror_uvec, fMinus]
  · rw [gMinus, hy, hv.2.2.2, inj_mirror_sub, inj_dot_mirror_uvec, fPlus]

/-- The derivative of `y_K(t) = h_K(t) u_t + h_K(t + π/2) v_t` from those of its coefficients. -/
lemma inj_hasDerivWithinAt_outerCorner {K : Set (ℝ × ℝ)} {s : Set ℝ} {t a b : ℝ}
    (ha : HasDerivWithinAt (supp K) a s t)
    (hb : HasDerivWithinAt (fun x => supp K (x + π / 2)) b s t) :
    HasDerivWithinAt (outerCorner K)
      ((a - supp K (t + π / 2)) • uvec t + (supp K t + b) • vvec t) s t := by
  have e : outerCorner K = fun x => supp K x • uvec x + supp K (x + π / 2) • vvec x := by
    funext x; exact proposition2_2_2_outerCorner K x
  rw [e]
  have h1 := ha.smul (hasDerivAt_uvec t).hasDerivWithinAt
  have h2 := hb.smul (hasDerivAt_vvec t).hasDerivWithinAt
  convert h1.add h2 using 1
  ext <;> simp <;> ring

/-- The derivative of `x_K(t) = y_K(t) - u_t - v_t`. -/
lemma inj_hasDerivWithinAt_innerCorner {K : Set (ℝ × ℝ)} {s : Set ℝ} {t : ℝ} {y' : ℝ × ℝ}
    (hy : HasDerivWithinAt (outerCorner K) y' s t) :
    HasDerivWithinAt (innerCorner K) (y' - vvec t + uvec t) s t := by
  have e : innerCorner K = fun x => outerCorner K x - uvec x - vvec x := by
    funext x
    rw [proposition2_2_2_innerCorner, proposition2_2_2_outerCorner]
    ext <;> simp <;> ring
  rw [e]
  convert (hy.sub (hasDerivAt_uvec t).hasDerivWithinAt).sub
    (hasDerivAt_vvec t).hasDerivWithinAt using 1
  abel

/-- **Theorem 6.2.3** (`thm:inner-corner-deriv`), right derivatives:
`∂⁺y_K(t) = -f_K⁺(t) u_t + g_K⁺(t) v_t` and `∂⁺x_K(t) = -(f_K⁺(t) - 1) u_t + (g_K⁺(t) - 1) v_t`.
The paper states this for `t ∈ [0, π/2)`; it holds at every `t`. -/
theorem theorem6_2_3_right {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} :
    HasDerivWithinAt (outerCorner K) (-fPlus K t • uvec t + gPlus K t • vvec t) (Ici t) t ∧
      HasDerivWithinAt (innerCorner K) (-(fPlus K t - 1) • uvec t + (gPlus K t - 1) • vvec t)
        (Ici t) t := by
  have hKc : IsConvexBody K := hK.2.1
  -- the right derivative of `h_K(· + π/2)` at `t`
  have hb : HasDerivWithinAt (fun x => supp K (x + π / 2))
      (dot (vplus K (t + π / 2)) (vvec (t + π / 2))) (Ici t) t := by
    have h1 := hasDerivWithinAt_supp_right hKc (t + π / 2)
    have h2 : HasDerivWithinAt (fun x : ℝ => x + π / 2) 1 (Ici t) t :=
      ((hasDerivAt_id t).add_const (π / 2)).hasDerivWithinAt
    have h := h1.comp t h2 (fun x hx => by simp only [mem_Ici] at hx ⊢; linarith)
    rwa [mul_one] at h
  have hy : HasDerivWithinAt (outerCorner K) (-fPlus K t • uvec t + gPlus K t • vvec t)
      (Ici t) t := by
    rw [show -fPlus K t = dot (vplus K t) (vvec t) - supp K (t + π / 2) by
      rw [inj_fPlus_eq]; ring, inj_gPlus_eq]
    exact inj_hasDerivWithinAt_outerCorner (hasDerivWithinAt_supp_right hKc t) hb
  refine ⟨hy, ?_⟩
  convert inj_hasDerivWithinAt_innerCorner hy using 1
  ext <;> simp <;> ring

/-- **Theorem 6.2.3**, left derivatives, with `f_K⁻` and `g_K⁻`. The paper states this for
`t ∈ (0, π/2]`; it holds at every `t`. -/
theorem theorem6_2_3_left {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} :
    HasDerivWithinAt (outerCorner K) (-fMinus K t • uvec t + gMinus K t • vvec t) (Iic t) t ∧
      HasDerivWithinAt (innerCorner K) (-(fMinus K t - 1) • uvec t + (gMinus K t - 1) • vvec t)
        (Iic t) t := by
  have hKc : IsConvexBody K := hK.2.1
  -- the left derivative of `h_K(· + π/2)` at `t`
  have hb : HasDerivWithinAt (fun x => supp K (x + π / 2))
      (dot (vminus K (t + π / 2)) (vvec (t + π / 2))) (Iic t) t := by
    have h1 := hasDerivWithinAt_supp_left hKc (t + π / 2)
    have h2 : HasDerivWithinAt (fun x : ℝ => x + π / 2) 1 (Iic t) t :=
      ((hasDerivAt_id t).add_const (π / 2)).hasDerivWithinAt
    have h := h1.comp t h2 (fun x hx => by simp only [mem_Iic] at hx ⊢; linarith)
    rwa [mul_one] at h
  have hy : HasDerivWithinAt (outerCorner K) (-fMinus K t • uvec t + gMinus K t • vvec t)
      (Iic t) t := by
    rw [show -fMinus K t = dot (vminus K t) (vvec t) - supp K (t + π / 2) by
      rw [inj_fMinus_eq]; ring, inj_gMinus_eq]
    exact inj_hasDerivWithinAt_outerCorner (hasDerivWithinAt_supp_left hKc t) hb
  refine ⟨hy, ?_⟩
  convert inj_hasDerivWithinAt_innerCorner hy using 1
  ext <;> simp <;> ring

/-- **Lemma 6.2.4** (`lem:arm-length-convolution`).
`g_K⁺(t) = ∫_{(t, t+π/2]} sin(u - t) σ_K(du)`. -/
theorem lemma6_2_4 {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {t : ℝ} :
    gPlus K t = ∫ u in Ioc t (t + π / 2), sin (u - t) ∂(sigma K) := by
  have hKc : IsConvexBody K := hK.2.1
  have hint : IntegrableOn vvec (Ioc t (t + π / 2)) (sigma K) :=
    continuous_vvec.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hs : IntegrableOn sin (Ioc t (t + π / 2)) (sigma K) :=
    (continuous_sin.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hc : IntegrableOn cos (Ioc t (t + π / 2)) (sigma K) :=
    (continuous_cos.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hv := vplus_sub_vplus hKc (show t ≤ t + π / 2 by linarith [pi_pos])
  have e1 : gPlus K t = -dot (vplus K (t + π / 2) - vplus K t) (uvec t) := by
    rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus, dot_sub_left, dot_vplus_uvec]; ring
  rw [e1, hv]
  simp only [dot, uvec]
  rw [fst_integral hint, snd_integral hint]
  simp only [vvec]
  simp_rw [sin_sub]
  rw [integral_sub (hs.mul_const _) (hc.mul_const _), integral_mul_const, integral_mul_const,
    integral_neg]
  ring

/-! ### Regularity of `f_K⁺` and its integrated derivative -/

/-- A difference of two functions of bounded variation has bounded variation. -/
lemma inj_boundedVariationOn_sub {f g : ℝ → ℝ} {s : Set ℝ} (hf : BoundedVariationOn f s)
    (hg : BoundedVariationOn g s) : BoundedVariationOn (fun x => f x - g x) s := by
  have key : eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
    apply iSup_le
    rintro ⟨n, u, hu, us⟩
    calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
        ≤ ∑ i ∈ Finset.range n,
            (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [sub_eq_add_neg, sub_eq_add_neg, ← edist_neg_neg (g (u (i + 1)))]
          exact edist_add_add_le _ _ _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩) key

/-- The right derivative `v_K⁺(t) · v_t` of `h_K` is the distribution function of `σ_K` minus
`∫₀ᵗ h_K`. -/
lemma inj_dot_vplus_vvec_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vplus K t) (vvec t) = sigmaFun K t - ∫ s in (0 : ℝ)..t, supp K s := by
  rw [sigmaFun]; ring

/-- The right derivative `s ↦ v_K⁺(s + c) · v_{s + c}` of `h_K(· + c)` is interval integrable. -/
lemma inj_intervalIntegrable_dvplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (c a b : ℝ) :
    IntervalIntegrable (fun s => dot (vplus K (s + c)) (vvec (s + c))) volume a b := by
  have h1 : IntervalIntegrable (fun s => sigmaFun K (s + c)) volume a b :=
    ((monotone_sigmaFun hK).comp fun x y hxy => by linarith).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => ∫ s in (0 : ℝ)..(t + c), supp K s) volume a b :=
    ((continuous_integral_supp hK).comp
      (continuous_id.add continuous_const)).intervalIntegrable a b
  simp_rw [inj_dot_vplus_vvec_eq]
  exact h1.sub h2

/-- The fundamental theorem of calculus for the support function:
`h_K(b) - h_K(a) = ∫_a^b v_K⁺(s) · v_s ds`. -/
lemma inj_supp_sub_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    supp K b - supp K a = ∫ s in a..b, dot (vplus K s) (vvec s) := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right hK.continuous_supp.continuousOn
  · intro x _
    exact (hasDerivWithinAt_supp_right hK x).mono Ioi_subset_Ici_self
  · simpa using inj_intervalIntegrable_dvplus hK 0 a b

/-- `g_K⁺` is interval integrable. -/
lemma inj_intervalIntegrable_gPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (gPlus K) volume a b := by
  rw [funext (inj_gPlus_eq K)]
  exact (hK.continuous_supp.intervalIntegrable a b).add
    (inj_intervalIntegrable_dvplus hK (π / 2) a b)

/-- `∫_a^b g_K⁺ = ∫_a^b h_K + h_K(b + π/2) - h_K(a + π/2)`. -/
lemma inj_integral_gPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    ∫ t in a..b, gPlus K t =
      (∫ t in a..b, supp K t) + (supp K (b + π / 2) - supp K (a + π / 2)) := by
  have hshift : ∫ t in a..b, dot (vplus K (t + π / 2)) (vvec (t + π / 2)) =
      supp K (b + π / 2) - supp K (a + π / 2) := by
    rw [intervalIntegral.integral_comp_add_right (fun s => dot (vplus K s) (vvec s)),
      inj_supp_sub_supp hK]
  simp_rw [inj_gPlus_eq]
  rw [intervalIntegral.integral_add (hK.continuous_supp.intervalIntegrable a b)
    (inj_intervalIntegrable_dvplus hK (π / 2) a b), hshift]

/-- The integrated form of Theorem 6.2.5:
`f_K⁺(b) - f_K⁺(a) = ∫_a^b g_K⁺ - σ_K((a, b])` for `a ≤ b`. -/
theorem fPlus_sub_fPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    fPlus K b - fPlus K a = (∫ t in a..b, gPlus K t) - (sigma K (Ioc a b)).toReal := by
  have hc := hK.continuous_supp
  have hsig : (sigma K (Ioc a b)).toReal = sigmaFun K b - sigmaFun K a := by
    rw [sigma_Ioc hK, ENNReal.toReal_ofReal (sub_nonneg.2 (monotone_sigmaFun hK hab))]
  have h3 := intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := volume) 0 b)
    (hc.intervalIntegrable 0 a)
  rw [inj_integral_gPlus hK, hsig, inj_fPlus_eq, inj_fPlus_eq, inj_dot_vplus_vvec_eq,
    inj_dot_vplus_vvec_eq]
  linarith

/-- The continuous part `h_K(t + π/2) + ∫₀ᵗ h_K` of `f_K⁺`. -/
lemma inj_fPlus_eq_sub_sigmaFun (K : Set (ℝ × ℝ)) (t : ℝ) :
    fPlus K t = (supp K (t + π / 2) + ∫ s in (0 : ℝ)..t, supp K s) - sigmaFun K t := by
  rw [inj_fPlus_eq, inj_dot_vplus_vvec_eq]; ring

/-- **Theorem 6.2.5** (`thm:arm-length-differentiation`), regularity: for a convex body `K`, `f_K⁺`
is right-continuous and of bounded variation on `[0, π/2]`. -/
theorem theorem6_2_5_regular {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    BoundedVariationOn (fPlus K) (Icc 0 (π / 2)) ∧
      ∀ t ∈ Ico 0 (π / 2), ContinuousWithinAt (fPlus K) (Ici t) t := by
  have hc := hK.continuous_supp
  set A : ℝ → ℝ := fun x => supp K (x + π / 2) + ∫ s in (0 : ℝ)..x, supp K s with hA
  have hfA : fPlus K = fun x => A x - sigmaFun K x := by
    funext x; exact inj_fPlus_eq_sub_sigmaFun K x
  have hAc : Continuous A :=
    (hc.comp (continuous_id.add continuous_const)).add (continuous_integral_supp hK)
  set φ : ℝ → ℝ := fun s => supp K s + dot (vplus K (s + π / 2)) (vvec (s + π / 2)) with hφ
  have hφi : ∀ a b, IntervalIntegrable φ volume a b := fun a b =>
    (hc.intervalIntegrable a b).add (inj_intervalIntegrable_dvplus hK (π / 2) a b)
  have hAint : ∀ x, A x = A 0 + ∫ s in (0 : ℝ)..x, φ s := by
    intro x
    simp only [hA, hφ]
    rw [intervalIntegral.integral_add (hc.intervalIntegrable 0 x)
      (inj_intervalIntegrable_dvplus hK (π / 2) 0 x),
      intervalIntegral.integral_comp_add_right (fun s => dot (vplus K s) (vvec s)),
      ← inj_supp_sub_supp hK]
    simp only [zero_add, intervalIntegral.integral_same]
    ring
  have hAac : AbsolutelyContinuousOnInterval A 0 (π / 2) := by
    rw [funext hAint]
    exact (LipschitzWith.const (A 0)).lipschitzOnWith.absolutelyContinuousOnInterval.add
      ((hφi 0 (π / 2)).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  refine ⟨?_, ?_⟩
  · rw [hfA]
    apply inj_boundedVariationOn_sub
    · have := hAac.boundedVariationOn
      rwa [uIcc_of_le (by positivity)] at this
    · have := ((monotone_sigmaFun hK).monotoneOn univ).locallyBoundedVariationOn 0 (π / 2)
        trivial trivial
      simpa using this
  · intro t _
    rw [hfA]
    exact hAc.continuousAt.continuousWithinAt.sub (continuousWithinAt_sigmaFun hK t)

/-- **Theorem 6.2.5** (`thm:arm-length-differentiation`). On `(0, π/2]`,
`d f_K⁺(t) = g_K⁺(t) dt - σ_K` as signed measures. -/
theorem theorem6_2_5 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    (lsMeasure (fPlus K) 0 (π / 2)).restrict (Ioc 0 (π / 2)) =
      (volume.restrict (Ioc 0 (π / 2))).withDensityᵥ (gPlus K) -
        ((sigma K).restrict (Ioc 0 (π / 2))).withDensityᵥ (fun _ => (1 : ℝ)) := by
  obtain ⟨hbv, hrc⟩ := theorem6_2_5_regular hK
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hgi : Integrable (gPlus K) (volume.restrict (Ioc 0 (π / 2))) :=
    (inj_intervalIntegrable_gPlus hK 0 (π / 2)).1
  have h1i : Integrable (fun _ => (1 : ℝ)) ((sigma K).restrict (Ioc 0 (π / 2))) :=
    integrableOn_const measure_Ioc_lt_top.ne
  -- both sides agree on every interval `(l, u]`, by the integrated form `fPlus_sub_fPlus`
  refine vectorMeasure_ext_Ioc _ _ fun l u _ => ?_
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc, sub_apply,
    withDensityᵥ_apply hgi measurableSet_Ioc, withDensityᵥ_apply h1i measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Ioc_inter_Ioc]
  rcases le_total (max l 0) (min u (π / 2)) with hxy | hxy
  · rw [lsMeasure_Ioc_of_le hpi (le_max_right _ _) hxy (min_le_right _ _) hbv hrc,
      fPlus_sub_fPlus hK hxy, intervalIntegral.integral_of_le hxy, integral_const, smul_eq_mul,
      mul_one, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  · rw [Ioc_eq_empty (not_lt.2 hxy)]
    simp

end MovingSofaOptimality
