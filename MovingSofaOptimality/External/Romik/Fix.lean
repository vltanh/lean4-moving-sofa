module

public import MovingSofaOptimality.External.Romik.Num
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The zero of the reduced system for Gerver's sofa

`rom_Hz (φ, θ) = 0` is the reduced form of Romik's system (see `MovingSofaOptimality.External.Romik`). With a
rational matrix `M ≈ DH(z*)⁻¹`, the map `G(z) = z - M H(z)` (`rom_Gz`) satisfies
`|∂G_i/∂z_j| ≤ (0.03, 0.012; 0.3, 0.16)` on the box `[0.039, 0.04] × [0.68, 0.69]` (interval
arithmetic in `MovingSofaOptimality.External.Romik.Num`), so it is a `1/2`-contraction there for the sup metric.
Hence `H` has at most one zero in the box (`rom_zero_unique`), and Banach's fixed point theorem on
the square of radius `10⁻¹⁰` around `(φ₀, θ₀) = (0.0391773648, 0.6813015094)`, where the residual
`M H(φ₀, θ₀)` is below `2 · 10⁻¹¹`, gives a zero there (`rom_exists_zero`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-- The reduced system `H(φ, θ)`. -/
noncomputable def rom_Hz (z : ℝ × ℝ) : ℝ × ℝ :=
  (rom_H1 z.1 z.2 (cos z.1) (sin z.1) (cos z.2) (sin z.2) π,
    rom_H2 z.1 z.2 (cos z.1) (sin z.1) (cos z.2) (sin z.2) π)

/-- The Newton-type map `G(z) = z - M H(z)`. -/
noncomputable def rom_Gz (z : ℝ × ℝ) : ℝ × ℝ :=
  (rom_G1 z.1 z.2 (cos z.1) (sin z.1) (cos z.2) (sin z.2) π,
    rom_G2 z.1 z.2 (cos z.1) (sin z.1) (cos z.2) (sin z.2) π)

/-- The box `[0.039, 0.04] × [0.68, 0.69]` of `GerverParams.InBox`. -/
def rom_box : Set (ℝ × ℝ) := Icc (0.039 : ℝ) 0.04 ×ˢ Icc (0.68 : ℝ) 0.69

/-- The square of radius `10⁻¹⁰` around `(φ₀, θ₀) = (0.0391773648, 0.6813015094)`. -/
def rom_tiny : Set (ℝ × ℝ) :=
  Icc (0.0391773647 : ℝ) 0.0391773649 ×ˢ Icc (0.6813015093 : ℝ) 0.6813015095

theorem rom_tiny_subset : rom_tiny ⊆ rom_box := by
  rintro z ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem rom_Gz_eq_iff (z : ℝ × ℝ) : rom_Gz z = z ↔ rom_Hz z = 0 := by
  simp only [rom_Gz, rom_Hz, rom_G1, rom_G2, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    constructor <;> ring

/-! ### Bounds on the partial derivatives of `G` on the box -/

theorem rom_G1φ_bound {x y : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) (hy : y ∈ Icc (0.68 : ℝ) 0.69) :
    |rom_G1φ x y (cos x) (sin x) (cos y) (sin y) π| ≤ 0.03 := by
  have h := rom_G1φ_box hx hy (rom_cos_box hx) (rom_sin_box hx) (rom_cos_box' hy)
    (rom_sin_box' hy) rom_pi_mem6
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

theorem rom_G1θ_bound {x y : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) (hy : y ∈ Icc (0.68 : ℝ) 0.69) :
    |rom_G1θ x y (cos x) (sin x) (cos y) (sin y) π| ≤ 0.012 := by
  have h := rom_G1θ_box hx hy (rom_cos_box hx) (rom_sin_box hx) (rom_cos_box' hy)
    (rom_sin_box' hy) rom_pi_mem6
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

theorem rom_G2φ_bound {x y : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) (hy : y ∈ Icc (0.68 : ℝ) 0.69) :
    |rom_G2φ x y (cos x) (sin x) (cos y) (sin y) π| ≤ 0.3 := by
  have h := rom_G2φ_box hx hy (rom_cos_box hx) (rom_sin_box hx) (rom_cos_box' hy)
    (rom_sin_box' hy) rom_pi_mem6
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

theorem rom_G2θ_bound {x y : ℝ} (hx : x ∈ Icc (0.039 : ℝ) 0.04) (hy : y ∈ Icc (0.68 : ℝ) 0.69) :
    |rom_G2θ x y (cos x) (sin x) (cos y) (sin y) π| ≤ 0.16 := by
  have h := rom_G2θ_box hx hy (rom_cos_box hx) (rom_sin_box hx) (rom_cos_box' hy)
    (rom_sin_box' hy) rom_pi_mem6
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-! ### `G` is a contraction on the box -/

/-- The mean value inequality on an interval. -/
theorem rom_mvt {f f' : ℝ → ℝ} {a b L x y : ℝ} (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ L) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ L * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hf t ht).hasDerivWithinAt) (fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht)
    (convex_Icc a b) hy hx
  simpa only [Real.norm_eq_abs] using this

theorem rom_G1_lip {z z' : ℝ × ℝ} (hz : z ∈ rom_box) (hz' : z' ∈ rom_box) :
    |(rom_Gz z).1 - (rom_Gz z').1| ≤ 0.03 * |z.1 - z'.1| + 0.012 * |z.2 - z'.2| := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz1', hz2'⟩ := hz'
  have e1 := rom_mvt (f := fun t => rom_G1 t z.2 (cos t) (sin t) (cos z.2) (sin z.2) π)
    (fun t _ => rom_G1_hasDerivAt_φ t z.2) (fun t ht => rom_G1φ_bound ht hz2) hz1 hz1'
  have e2 := rom_mvt (f := fun t => rom_G1 z'.1 t (cos z'.1) (sin z'.1) (cos t) (sin t) π)
    (fun t _ => rom_G1_hasDerivAt_θ z'.1 t) (fun t ht => rom_G1θ_bound hz1' ht) hz2 hz2'
  exact (abs_sub_le _ _ _).trans (add_le_add e1 e2)

theorem rom_G2_lip {z z' : ℝ × ℝ} (hz : z ∈ rom_box) (hz' : z' ∈ rom_box) :
    |(rom_Gz z).2 - (rom_Gz z').2| ≤ 0.3 * |z.1 - z'.1| + 0.16 * |z.2 - z'.2| := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz1', hz2'⟩ := hz'
  have e1 := rom_mvt (f := fun t => rom_G2 t z.2 (cos t) (sin t) (cos z.2) (sin z.2) π)
    (fun t _ => rom_G2_hasDerivAt_φ t z.2) (fun t ht => rom_G2φ_bound ht hz2) hz1 hz1'
  have e2 := rom_mvt (f := fun t => rom_G2 z'.1 t (cos z'.1) (sin z'.1) (cos t) (sin t) π)
    (fun t _ => rom_G2_hasDerivAt_θ z'.1 t) (fun t ht => rom_G2θ_bound hz1' ht) hz2 hz2'
  exact (abs_sub_le _ _ _).trans (add_le_add e1 e2)

theorem rom_Gz_dist_le {z z' : ℝ × ℝ} (hz : z ∈ rom_box) (hz' : z' ∈ rom_box) :
    dist (rom_Gz z) (rom_Gz z') ≤ 1 / 2 * dist z z' := by
  have h1 := rom_G1_lip hz hz'
  have h2 := rom_G2_lip hz hz'
  have d1 : |z.1 - z'.1| ≤ dist z z' := by
    rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
  have d2 : |z.2 - z'.2| ≤ dist z z' := by
    rw [Prod.dist_eq, ← Real.dist_eq (z.2)]; exact le_max_right _ _
  have a1 := abs_nonneg (z.1 - z'.1)
  have a2 := abs_nonneg (z.2 - z'.2)
  have e : dist (rom_Gz z) (rom_Gz z') =
      max |(rom_Gz z).1 - (rom_Gz z').1| |(rom_Gz z).2 - (rom_Gz z').2| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rw [e]
  exact max_le (by linarith) (by linarith)

/-! ### Uniqueness and existence of the zero -/

/-- `H` has at most one zero in the box. -/
theorem rom_zero_unique {z z' : ℝ × ℝ} (hz : z ∈ rom_box) (hz' : z' ∈ rom_box)
    (h : rom_Hz z = 0) (h' : rom_Hz z' = 0) : z = z' := by
  have e := rom_Gz_dist_le hz hz'
  rw [(rom_Gz_eq_iff z).2 h, (rom_Gz_eq_iff z').2 h'] at e
  have h0 : dist z z' = 0 := le_antisymm (by linarith [dist_nonneg (x := z) (y := z')]) dist_nonneg
  exact dist_eq_zero.1 h0

/-- The residual at `(φ₀, θ₀)`. -/
theorem rom_Gz_z0 :
    (rom_Gz ((0.0391773648 : ℝ), (0.6813015094 : ℝ))).1 ∈
        Icc (0.0391773648 - 0.000000000009915950597 : ℝ)
          (0.0391773648 - 0.0000000000099155784208) ∧
      (rom_Gz ((0.0391773648 : ℝ), (0.6813015094 : ℝ))).2 ∈
        Icc (0.6813015094 - 0.0000000000172760407234 : ℝ)
          (0.6813015094 - 0.0000000000172726825567) := by
  have h1 := rom_MH1_z0 (rom_iv_self _) (rom_iv_self _) rom_cos_φ₀ rom_sin_φ₀ rom_cos_θ₀ rom_sin_θ₀
    rom_pi_mem20
  have h2 := rom_MH2_z0 (rom_iv_self _) (rom_iv_self _) rom_cos_φ₀ rom_sin_φ₀ rom_cos_θ₀ rom_sin_θ₀
    rom_pi_mem20
  simp only [rom_Gz, rom_G1, rom_G2]
  simp only [rom_MH1, rom_MH2] at h1 h2
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

theorem rom_mapsTo_tiny : MapsTo rom_Gz rom_tiny rom_tiny := by
  intro z hz
  have hz0 : ((0.0391773648 : ℝ), (0.6813015094 : ℝ)) ∈ rom_tiny := by
    constructor <;> constructor <;> norm_num
  have h1 := rom_G1_lip (rom_tiny_subset hz) (rom_tiny_subset hz0)
  have h2 := rom_G2_lip (rom_tiny_subset hz) (rom_tiny_subset hz0)
  obtain ⟨r1, r2⟩ := rom_Gz_z0
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hz
  have b1 : |z.1 - 0.0391773648| ≤ 0.0000000001 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have b2 : |z.2 - 0.6813015094| ≤ 0.0000000001 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have c1 := abs_sub_le_iff.1 h1
  have c2 := abs_sub_le_iff.1 h2
  exact ⟨⟨by linarith [r1.1, r1.2], by linarith [r1.1, r1.2]⟩,
    ⟨by linarith [r2.1, r2.2], by linarith [r2.1, r2.2]⟩⟩

/-- `H` has a zero within `10⁻¹⁰` of `(φ₀, θ₀)`. -/
theorem rom_exists_zero : ∃ z ∈ rom_tiny, rom_Hz z = 0 := by
  have hz0 : ((0.0391773648 : ℝ), (0.6813015094 : ℝ)) ∈ rom_tiny := by
    constructor <;> constructor <;> norm_num
  have hcomplete : IsComplete rom_tiny := (isClosed_Icc.prod isClosed_Icc).isComplete
  have hcontr : ContractingWith (1 / 2) (rom_mapsTo_tiny.restrict rom_Gz rom_tiny rom_tiny) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply]
    have := rom_Gz_dist_le (rom_tiny_subset a.2) (rom_tiny_subset b.2)
    simpa using this
  obtain ⟨z, hz, hfix, -⟩ :=
    hcontr.exists_fixedPoint' hcomplete rom_mapsTo_tiny hz0 (edist_ne_top _ _)
  exact ⟨z, hz, (rom_Gz_eq_iff z).1 hfix⟩

end MovingSofaOptimality
