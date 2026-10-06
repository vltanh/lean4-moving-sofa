module

public import MovingSofaStability.PunctureMetric
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Interior retention on a compact rigid orbit

Uncompiled proof source. The conclusion is special to rigid copies of one fixed
compact set. It is false for arbitrary Hausdorff-close compact sets.

The proof takes subsequences of the cosine/sine coefficients and translations,
not of unrestricted real angles. No trivial-stabilizer assumption is needed.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology Metric
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev RotationShift := Point × Point

def rotationShift (g : Rigid) : RotationShift := ((cos g.angle, sin g.angle), g.shift)

def coefficientApply (z : RotationShift) (p : Point) : Point :=
  (z.1.1 * p.1 - z.1.2 * p.2 + z.2.1, z.1.2 * p.1 + z.1.1 * p.2 + z.2.2)

def coefficientInverse (z : RotationShift) (p : Point) : Point :=
  (z.1.1 * (p.1 - z.2.1) + z.1.2 * (p.2 - z.2.2),
    -z.1.2 * (p.1 - z.2.1) + z.1.1 * (p.2 - z.2.2))

@[simp] theorem coefficientApply_rotationShift (g : Rigid) (p : Point) :
    coefficientApply (rotationShift g) p = g p := rfl

@[simp] theorem coefficientInverse_rotationShift (g : Rigid) (p : Point) :
    coefficientInverse (rotationShift g) p = g.symm p := by
  ext <;> simp only [coefficientInverse, rotationShift, Rigid.symm, Rigid.apply,
    rot, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, cos_neg, sin_neg] <;> ring

/-- The limit of the matrix coefficients still defines a homeomorphism. -/
def coefficientHomeomorph (z : RotationShift) (h : z.1.1 ^ 2 + z.1.2 ^ 2 = 1) : Point ≃ₜ Point where
  toFun := coefficientApply z
  invFun := coefficientInverse z
  left_inv p := by
    ext <;> dsimp only [coefficientApply, coefficientInverse]
    · linear_combination p.1 * h
    · linear_combination p.2 * h
  right_inv p := by
    ext <;> dsimp only [coefficientApply, coefficientInverse]
    · linear_combination (p.1 - z.2.1) * h
    · linear_combination (p.2 - z.2.2) * h
  continuous_toFun := by unfold coefficientApply; fun_prop
  continuous_invFun := by unfold coefficientInverse; fun_prop

/-- A closed set contains a limiting point approximated by points of that set. -/
theorem closed_mem_of_euclidean_near {X : Set Point} (hX : IsClosed X) (hne : X.Nonempty)
    {x : ℕ → Point} {p : Point} {δ : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 p)) (hδ : Tendsto δ atTop (𝓝 0))
    (hnear : ∀ n, ∃ q ∈ X, euclideanDist (x n) q ≤ δ n) : p ∈ X := by
  have hupper : ∀ n, infDist (x n) X ≤ δ n := by
    intro n
    obtain ⟨q, hq, hd⟩ := hnear n
    have hm : dist (x n) q ≤ euclideanDist (x n) q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 _
    exact (infDist_le_dist_of_mem hq).trans (hm.trans hd)
  have hzero : Tendsto (fun n => infDist (x n) X) atTop (𝓝 0) :=
    squeeze_zero (fun _ => infDist_nonneg) hupper hδ
  have hlim := ((lipschitz_infDist_pt X).continuous.tendsto p).comp hx
  have he : infDist p X = 0 := tendsto_nhds_unique hlim hzero
  rw [← hX.closure_eq]
  exact (mem_closure_iff_infDist_zero hne).mpr he

/-- Closeness of a rigid image bounds its translation uniformly. -/
theorem rigid_shift_bound {X : Set Point} {R δ : ℝ} (hne : X.Nonempty)
    (hR : ∀ x ∈ X, ‖x‖ ≤ R) (hδ : δ ≤ 1) {g : Rigid}
    (hclose : EuclideanClose δ X (g '' X)) : ‖g.shift‖ ≤ 4 * R + 1 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq, hd⟩ := hclose.2 (g x) (mem_image_of_mem _ hx)
  have hnq : norm2 q ≤ 2 * R := (norm2_le_two_product_norm q).trans (by linarith [hR q hq])
  have hnx : norm2 (rot g.angle x) ≤ 2 * R := by
    rw [norm2_rot]
    exact (norm2_le_two_product_norm x).trans (by linarith [hR x hx])
  have he : g.shift = (g x - q) + q + -(rot g.angle x) := by
    simp only [Rigid.apply]
    abel
  calc
    ‖g.shift‖ ≤ norm2 g.shift := product_norm_le_norm2 _
    _ ≤ norm2 (g x - q) + norm2 q + norm2 (rot g.angle x) := by
      rw [he]
      exact (norm2_add_le _ _).trans (by
        rw [norm2_neg]
        exact add_le_add_right (norm2_add_le _ _) _)
    _ ≤ 4 * R + 1 := by
      change norm2 (g x - q) ≤ δ at hd
      linarith

/-- Every fixed interior point is retained by sufficiently close rigid copies.
No restriction on rotation angle, translation, or symmetries of X is imposed. -/
theorem rigid_copies_retain_interior {X : Set Point} (hX : IsCompact X)
    {p : Point} (hp : p ∈ interior X) :
    ∃ η : ℝ, 0 < η ∧ ∀ g : Rigid, ∀ δ : ℝ,
      δ < η → EuclideanClose δ X (g '' X) → p ∈ g '' X := by
  classical
  have hne : X.Nonempty := ⟨p, interior_subset hp⟩
  by_contra hnot
  have counter (η : ℝ) (hη : 0 < η) :
      ∃ g : Rigid, ∃ δ : ℝ, δ < η ∧ EuclideanClose δ X (g '' X) ∧ p ∉ g '' X := by
    by_contra hnone
    apply hnot
    refine ⟨η, hη, ?_⟩
    intro g δ hδη hclose
    by_contra hout
    exact hnone ⟨g, δ, hδη, hclose, hout⟩
  choose g δ hsmall hclose hout using
    fun n : ℕ => counter (1 / ((n : ℝ) + 1)) (by positivity)
  have hδnonneg : ∀ n, 0 ≤ δ n := by
    intro n
    obtain ⟨q, _, hd⟩ := hclose n |>.1 p (interior_subset hp)
    exact (euclideanDist_nonneg _ _).trans hd
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.add_const 1)
  have hδlim : Tendsto δ atTop (𝓝 0) := squeeze_zero hδnonneg (fun n => (hsmall n).le) hinv
  obtain ⟨R, hR⟩ := hX.isBounded.exists_norm_le
  let B : Set RotationShift := (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ closedBall (0 : Point) (4 * R + 1)
  have hB : IsCompact B := (isCompact_Icc.prod isCompact_Icc).prod isCompact_closedBall
  have hgB : ∀ n, rotationShift (g n) ∈ B := by
    intro n
    refine ⟨⟨⟨neg_one_le_cos _, cos_le_one _⟩, ⟨neg_one_le_sin _, sin_le_one _⟩⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    apply rigid_shift_bound hne hR _ (hclose n)
    have he : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      positivity
    exact (hsmall n).le.trans he
  obtain ⟨z, hzB, σ, hσ, hz⟩ := hB.tendsto_subseq hgB
  have hunit : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := by
    have hclosed : IsClosed {z : RotationShift | z.1.1 ^ 2 + z.1.2 ^ 2 = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    apply hclosed.mem_of_tendsto hz
    exact Eventually.of_forall fun n => cos_sq_add_sin_sq (g (σ n)).angle
  let F := coefficientHomeomorph z hunit
  have invmaps : ∀ x ∈ X, F.symm x ∈ X := by
    intro x hx
    have hcont : Continuous (fun z : RotationShift => coefficientInverse z x) := by
      unfold coefficientInverse
      fun_prop
    have hlim := (hcont.tendsto z).comp hz
    apply closed_mem_of_euclidean_near hX.isClosed hne hlim (hδlim.comp hσ.tendsto_atTop)
    intro n
    obtain ⟨_, ⟨q, hq, rfl⟩, hd⟩ := (hclose (σ n)).1 x hx
    refine ⟨q, hq, ?_⟩
    rw [coefficientInverse_rotationShift]
    have he := euclideanDist_rigid (g (σ n)) ((g (σ n)).symm x) q
    simpa only [Rigid.apply_symm_apply] using he.le.trans hd
  have hU : IsOpen (F.symm '' interior X) := F.symm.isOpenMap _ isOpen_interior
  have hUX : F.symm '' interior X ⊆ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact invmaps x (interior_subset hx)
  have hnhds : X ∈ 𝓝 (F.symm p) :=
    mem_of_superset (hU.mem_nhds (mem_image_of_mem _ hp)) hUX
  have hcont : Continuous (fun z : RotationShift => coefficientInverse z p) := by
    unfold coefficientInverse
    fun_prop
  have hev := ((hcont.tendsto z).comp hz).eventually hnhds
  obtain ⟨n, hn⟩ := hev.exists
  rw [coefficientInverse_rotationShift] at hn
  exact hout (σ n) ⟨(g (σ n)).symm p, hn, (g (σ n)).apply_symm_apply p⟩

end MovingSofaStability
