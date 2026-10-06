module

public import MovingSofaOptimality.Basic.Plane
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Planar convex bodies (§2.1)

Definitions `def:convex-body`, `def:support-function`, `def:supporting-line-half-plane`,
`def:width`, `def:convex-body-edge`, `def:convex-body-vertex`,
`def:convex-body-tangent-lines-intersection`, `def:hausdorff-distance`, and Theorem
`thm:limits-converging-to-vertex`.

The support function, supporting lines and half-planes are defined for every subset of the plane;
they have their intended meaning for nonempty compact sets.

The three non-public imports (Hahn–Banach separation, slopes, derivatives of `sin`/`cos`) are only
used inside proofs.

The file is organised as follows: basic properties of the support function (boundedness,
continuity, translation, the Hausdorff distance); edges and vertices (`e_K(t)` is the segment
`[v_K⁻(t), v_K⁺(t)]`); Theorem `thm:limits-converging-to-vertex`; the one-sided derivatives
`v_K^±(t) · v_t` of `h_K`.

Theorem `thm:limits-converging-to-vertex` is proved as in the paper, by its `ε`-triangle. For
`ε > 0`, the point `p = v_K⁺(t) + ε v_t` is not in `K`, so a short segment from `p` to a point `q`
in the direction `-u_t` misses `K` (`cb_segment`). The triangle `T` with vertices `v_K⁺(t)`,
`p` and `q` contains the points of `K` on its side of the line through `v_K⁺(t)` and `q`
(`cb_mem_triangle`), and for `s` slightly larger than `t` every point of `e_K(s)` is on that side
(`cb_better_mem_triangle`); the points of `T` are within `ε` of `v_K⁺(t)` (`cb_tendsto_core`).
The left limits follow by the symmetric argument, in the frame `(u_t, -v_t)`. The one-sided
derivatives of `h_K` follow from Theorem `thm:limits-converging-to-vertex`: the `v_t`-coordinate
of `v_K(t, s)` tends to that of `v_K⁺(t)`.
-/

@[expose] public section

open Real Set Filter Topology

namespace MovingSofaOptimality

/-! ### Definitions -/

/-- A planar convex body: a nonempty, compact and convex subset of the plane (`def:convex-body`).
Its interior may be empty. -/
def IsConvexBody (K : Set (ℝ × ℝ)) : Prop := K.Nonempty ∧ IsCompact K ∧ Convex ℝ K

/-- The support function `h_S(t) = sup {s · u_t : s ∈ S}` (`def:support-function`). -/
noncomputable def supp (S : Set (ℝ × ℝ)) (t : ℝ) : ℝ := sSup ((fun p => dot p (uvec t)) '' S)

/-- The supporting line `l_S(t) = l(t, h_S(t))` (`def:supporting-line-half-plane`). -/
def suppLine (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := line t (supp S t)

/-- The supporting half-plane `H_S(t) = H₋(t, h_S(t))` (`def:supporting-line-half-plane`). -/
def suppHalf (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := halfMinus t (supp S t)

/-- The width `h_S(t) + h_S(t + π)` of `S` in the direction `u_t` (`def:width`). -/
noncomputable def width (S : Set (ℝ × ℝ)) (t : ℝ) : ℝ := supp S t + supp S (t + π)

/-- The edge `e_K(t) = K ∩ l_K(t)` (`def:convex-body-edge`). It may be a single point. -/
def edge (K : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := K ∩ suppLine K t

/-- The vertex `v_K⁺(t)`: the endpoint of the edge `e_K(t)` farthest in the direction `v_t`
(`def:convex-body-vertex`). -/
noncomputable def vplus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ :=
  supp K t • uvec t + sSup ((fun p => dot p (vvec t)) '' edge K t) • vvec t

/-- The vertex `v_K⁻(t)`: the endpoint of the edge `e_K(t)` farthest in the direction `-v_t`
(`def:convex-body-vertex`). -/
noncomputable def vminus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ :=
  supp K t • uvec t + sInf ((fun p => dot p (vvec t)) '' edge K t) • vvec t

/-- The intersection `v_K(a, b) = l_K(a) ∩ l_K(b)` of two supporting lines, for `b ≠ a, a + π`
(`def:convex-body-tangent-lines-intersection`), given by its explicit formula. -/
noncomputable def vint (K : Set (ℝ × ℝ)) (a b : ℝ) : ℝ × ℝ :=
  supp K a • uvec a + ((supp K b - supp K a * cos (b - a)) / sin (b - a)) • vvec a

/-- The Hausdorff distance between convex bodies, in its support-function form
`d_H(K₁, K₂) = sup_t |h_{K₁}(t) - h_{K₂}(t)|` (`def:hausdorff-distance`, Schneider Lemma 1.8.14). -/
noncomputable def hausdorffDist (K₁ K₂ : Set (ℝ × ℝ)) : ℝ := ⨆ t : ℝ, |supp K₁ t - supp K₂ t|

/-- A sequence of convex bodies converges to `K` in the Hausdorff distance. -/
def HausdorffTendsto (Ks : ℕ → Set (ℝ × ℝ)) (K : Set (ℝ × ℝ)) : Prop :=
  Tendsto (fun n => hausdorffDist (Ks n) K) atTop (𝓝 0)

/-! ### Basic properties of the support function -/

lemma IsConvexBody.isClosed {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : IsClosed K :=
  hK.2.1.isClosed

lemma IsConvexBody.isBounded {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Bornology.IsBounded K :=
  hK.2.1.isBounded

private lemma cb_bddAbove {S : Set (ℝ × ℝ)} (hS : IsCompact S) (v : ℝ × ℝ) :
    BddAbove ((fun p => dot p v) '' S) :=
  hS.bddAbove_image (continuous_dot v).continuousOn

private lemma cb_bddBelow {S : Set (ℝ × ℝ)} (hS : IsCompact S) (v : ℝ × ℝ) :
    BddBelow ((fun p => dot p v) '' S) :=
  hS.bddBelow_image (continuous_dot v).continuousOn

/-- Every point `p` of a compact set `S` satisfies `p · u_t ≤ h_S(t)`. -/
lemma dot_le_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) {p : ℝ × ℝ} (hp : p ∈ S) (t : ℝ) :
    dot p (uvec t) ≤ supp S t :=
  le_csSup (cb_bddAbove hS _) (mem_image_of_mem _ hp)

/-- The supremum defining `h_S(t)` is attained for a nonempty compact `S`. -/
lemma exists_dot_eq_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ) :
    ∃ p ∈ S, dot p (uvec t) = supp S t :=
  (hS.image (continuous_dot (uvec t))).sSup_mem (hne.image _)

/-- If every point `p` of `S` satisfies `p · u_t ≤ c`, then `h_S(t) ≤ c`. -/
lemma supp_le_of_forall {S : Set (ℝ × ℝ)} (hne : S.Nonempty) {t c : ℝ}
    (h : ∀ p ∈ S, dot p (uvec t) ≤ c) : supp S t ≤ c :=
  csSup_le (hne.image _) (forall_mem_image.2 h)

/-- The support function is monotone in the set. -/
lemma supp_mono {S T : Set (ℝ × ℝ)} (hST : S ⊆ T) (hS : S.Nonempty) (hT : IsCompact T) (t : ℝ) :
    supp S t ≤ supp T t :=
  csSup_le_csSup (cb_bddAbove hT _) (hS.image _) (image_mono hST)

/-- If every point `p` of a compact set `S` satisfies `p · u_t ≤ c`, with equality at a point of
`S`, then `h_S(t) = c`. -/
lemma supp_eq_of_mem {S : Set (ℝ × ℝ)} (hS : IsCompact S) {t c : ℝ}
    (hle : ∀ p ∈ S, dot p (uvec t) ≤ c) {q : ℝ × ℝ} (hq : q ∈ S) (hqc : dot q (uvec t) = c) :
    supp S t = c :=
  le_antisymm (supp_le_of_forall ⟨q, hq⟩ hle) (hqc ▸ dot_le_supp hS hq t)

/-- A compact set `T ⊇ S` with `p · u_t ≤ h_S(t)` on `T` has `h_T(t) = h_S(t)`. -/
lemma supp_eq_of_squeeze {S T : Set (ℝ × ℝ)} (hST : S ⊆ T) (hS : S.Nonempty)
    (hT : IsCompact T) {t c : ℝ} (hSt : supp S t = c) (hT' : ∀ p ∈ T, dot p (uvec t) ≤ c) :
    supp T t = c :=
  le_antisymm (supp_le_of_forall (hS.mono hST) hT') (hSt ▸ supp_mono hST hS hT t)

lemma supp_add_two_pi (S : Set (ℝ × ℝ)) (t : ℝ) : supp S (t + 2 * π) = supp S t := by
  simp [supp, uvec_add_two_pi]

/-- The support function of a compact set is continuous: it is the supremum over a compact set of
a jointly continuous family. -/
lemma continuous_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    Continuous (supp S) := by
  have h : Continuous (fun x : ℝ × (ℝ × ℝ) => dot x.2 (uvec x.1)) := by
    simp only [dot, uvec]
    fun_prop
  exact hS.continuous_sSup (f := fun t p => dot p (uvec t)) h

lemma IsConvexBody.continuous_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Continuous (supp K) :=
  MovingSofaOptimality.continuous_supp hK.2.1

/-- The support function of a nonempty compact set is Lipschitz. -/
lemma exists_lipschitzWith_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ L, LipschitzWith L (supp S) := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  refine ⟨_, LipschitzWith.of_le_add_mul' (2 * R) fun s t => supp_le_of_forall hne fun p hp => ?_⟩
  -- `p · u_s - p · u_t ≤ 2 ‖p‖ ‖u_s - u_t‖ ≤ 2 R |s - t|`
  have h1 := dot_le_supp hS hp t
  have h2 := (le_abs_self _).trans (abs_dot_le p (uvec s - uvec t))
  have h3 : ‖uvec s - uvec t‖ ≤ dist s t := by
    simpa [← dist_eq_norm] using lipschitz_uvec.dist_le_mul s t
  rw [dot_sub_right] at h2
  nlinarith [hR p hp, norm_nonneg p, norm_nonneg (uvec s - uvec t)]

/-- A point lies in a closed convex set iff it lies in all of its supporting half-planes. -/
lemma mem_iff_forall_dot_le_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (p : ℝ × ℝ) :
    p ∈ K ↔ ∀ t, dot p (uvec t) ≤ supp K t := by
  refine ⟨fun hp t => dot_le_supp hK.2.1 hp t, fun h => ?_⟩
  by_contra hp
  -- separate `p` from `K` by a continuous linear functional `f`, which is `x ↦ x · n`
  obtain ⟨f, u, hfK, hfp⟩ := geometric_hahn_banach_closed_point hK.2.2 hK.isClosed hp
  set n : ℝ × ℝ := (f (1, 0), f (0, 1))
  have hf : ∀ x : ℝ × ℝ, f x = dot x n := by
    intro x
    have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
    simp [dot, n, smul_eq_mul]
  -- write `n` in polar form `n = ‖z‖ u_θ`, where `z = n₁ + n₂ i` and `θ = arg z`
  set z : ℂ := ⟨n.1, n.2⟩
  have hn : n = ‖z‖ • uvec (Complex.arg z) := by
    ext
    · simp only [Prod.smul_fst, uvec_fst, smul_eq_mul, Complex.norm_mul_cos_arg]; rfl
    · simp only [Prod.smul_snd, uvec_snd, smul_eq_mul, Complex.norm_mul_sin_arg]; rfl
  have hz : 0 < ‖z‖ := by
    refine norm_pos_iff.2 fun hz0 => ?_
    obtain ⟨a, ha⟩ := hK.1
    have h1 := hfK a ha
    rw [hf, hn, hz0, norm_zero, zero_smul, dot_zero_right] at h1 hfp
    linarith
  -- a point `a ∈ K` on the supporting line `l_K(θ)` gives `f p ≤ f a < u < f p`
  obtain ⟨a, ha, hae⟩ := exists_dot_eq_supp hK.2.1 hK.1 (Complex.arg z)
  have h1 := hfK a ha
  rw [hf, hn, dot_smul_right] at h1 hfp
  have h2 := mul_le_mul_of_nonneg_left (hae ▸ h (Complex.arg z)) hz.le
  linarith

/-- Two convex bodies with the same support function are equal. -/
lemma eq_of_supp_eq {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (h : ∀ t, supp K₁ t = supp K₂ t) : K₁ = K₂ := by
  ext p
  rw [mem_iff_forall_dot_le_supp h₁, mem_iff_forall_dot_le_supp h₂]
  simp only [h]

/-- Translating a set by `v` adds `v · u_t` to its support function. -/
lemma supp_translate (S : Set (ℝ × ℝ)) (v : ℝ × ℝ) (t : ℝ) (hS : IsCompact S)
    (hne : S.Nonempty) : supp ((fun p => p + v) '' S) t = supp S t + dot v (uvec t) := by
  have hS' : IsCompact ((fun p => p + v) '' S) :=
    hS.image (by fun_prop : Continuous fun p : ℝ × ℝ => p + v)
  apply le_antisymm
  · obtain ⟨q, ⟨p, hp, rfl⟩, hq⟩ := exists_dot_eq_supp hS' (hne.image _) t
    rw [← hq, dot_add_left]
    linarith [dot_le_supp hS hp t]
  · obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hS hne t
    rw [← hpe, ← dot_add_left]
    exact dot_le_supp hS' (mem_image_of_mem _ hp) t

/-- The support function of a nonempty compact set is bounded. -/
lemma exists_abs_supp_le {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ R, ∀ t, |supp S t| ≤ R := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  refine ⟨2 * R, fun t => ?_⟩
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hS hne t
  rw [← hpt]
  have h1 : |p.1| ≤ R := (norm_fst_le p).trans (hR p hp)
  have h2 : |p.2| ≤ R := (norm_snd_le p).trans (hR p hp)
  linarith [abs_dot_uvec_le p t]

/-- A convex body in `[-R, R] × [0, 1]` has supports of absolute value at most `R + 1`. -/
lemma abs_supp_le_box {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {R : ℝ}
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) (t : ℝ) : |supp K t| ≤ R + 1 := by
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  obtain ⟨hx, hy⟩ := hbox hp
  rw [← hpt]
  linarith [abs_dot_uvec_le p t, abs_le.2 hx, abs_le.2 ⟨by linarith [hy.1], hy.2⟩]

/-! ### The Hausdorff distance -/

/-- `|h_K(t) - h_{K'}(t)|` is at most the Hausdorff distance of `K` and `K'`. -/
lemma abs_supp_sub_le_hausdorffDist {K K' : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hK' : IsConvexBody K') (t : ℝ) : |supp K t - supp K' t| ≤ hausdorffDist K K' := by
  obtain ⟨R, hR⟩ := exists_abs_supp_le hK.2.1 hK.1
  obtain ⟨R', hR'⟩ := exists_abs_supp_le hK'.2.1 hK'.1
  refine le_ciSup (f := fun t => |supp K t - supp K' t|) ⟨R + R', ?_⟩ t
  rintro _ ⟨s, rfl⟩
  calc |supp K s - supp K' s| ≤ |supp K s| + |supp K' s| := abs_sub _ _
    _ ≤ R + R' := add_le_add (hR s) (hR' s)

lemma hausdorffDist_nonneg (K K' : Set (ℝ × ℝ)) : 0 ≤ hausdorffDist K K' :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- Hausdorff convergence of convex bodies gives pointwise convergence of the support functions. -/
lemma tendsto_supp {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)} (hKs : ∀ n, IsConvexBody (Ks n))
    (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) (t : ℝ) :
    Tendsto (fun n => supp (Ks n) t) atTop (𝓝 (supp K t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => abs_supp_sub_le_hausdorffDist (hKs n) hK t) hlim

/-! ### Edges and vertices -/

lemma mem_edge_iff {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} :
    p ∈ edge K t ↔ p ∈ K ∧ dot p (uvec t) = supp K t := Iff.rfl

lemma isCompact_edge {K : Set (ℝ × ℝ)} (hK : IsCompact K) (t : ℝ) :
    IsCompact (edge K t) :=
  hK.inter_right (isClosed_line t _)

private lemma cb_edge_nonempty {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    (edge K t).Nonempty :=
  let ⟨p, hp, hpe⟩ := exists_dot_eq_supp hK hne t
  ⟨p, mem_edge_iff.2 ⟨hp, hpe⟩⟩

/-- A point of the edge `e_K(t)` is determined by its `v_t`-coordinate. -/
private lemma cb_eq_of_mem_edge {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ edge K t) :
    p = supp K t • uvec t + dot p (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add p t]
  rw [(mem_edge_iff.1 hp).2]

lemma dot_vplus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vplus K t) (vvec t) = sSup ((fun p => dot p (vvec t)) '' edge K t) := by
  simp [vplus, dot_add_left, dot_smul_left]

lemma dot_vminus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vminus K t) (vvec t) = sInf ((fun p => dot p (vvec t)) '' edge K t) := by
  simp [vminus, dot_add_left, dot_smul_left]

private lemma cb_vplus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    vplus K t ∈ edge K t := by
  obtain ⟨p, hp, hpe⟩ := ((isCompact_edge hK t).image (continuous_dot (vvec t))).sSup_mem
    ((cb_edge_nonempty hK hne t).image _)
  rwa [show vplus K t = p by rw [cb_eq_of_mem_edge hp, vplus, ← hpe]]

private lemma cb_vminus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (t : ℝ) : vminus K t ∈ edge K t := by
  obtain ⟨p, hp, hpe⟩ := ((isCompact_edge hK t).image (continuous_dot (vvec t))).sInf_mem
    ((cb_edge_nonempty hK hne t).image _)
  rwa [show vminus K t = p by rw [cb_eq_of_mem_edge hp, vminus, ← hpe]]

/-- `v_K⁺(t)` is the farthest point of `e_K(t)` in the direction `v_t`. -/
lemma dot_le_dot_vplus {K : Set (ℝ × ℝ)} (hK : IsCompact K) {t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edge K t) : dot p (vvec t) ≤ dot (vplus K t) (vvec t) := by
  rw [dot_vplus_vvec]
  exact le_csSup (cb_bddAbove (isCompact_edge hK t) _) (mem_image_of_mem _ hp)

/-- `v_K⁻(t)` is the farthest point of `e_K(t)` in the direction `-v_t`. -/
lemma dot_vminus_le_dot {K : Set (ℝ × ℝ)} (hK : IsCompact K) {t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edge K t) : dot (vminus K t) (vvec t) ≤ dot p (vvec t) := by
  rw [dot_vminus_vvec]
  exact csInf_le (cb_bddBelow (isCompact_edge hK t) _) (mem_image_of_mem _ hp)

lemma vplus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) : vplus K t ∈ edge K t :=
  cb_vplus_mem_edge hK.2.1 hK.1 t

lemma vminus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    vminus K t ∈ edge K t :=
  cb_vminus_mem_edge hK.2.1 hK.1 t

/-- The edge `e_K(t)` is the segment `[v_K⁻(t), v_K⁺(t)]`. -/
lemma edge_eq_segment {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    edge K t = segment ℝ (vminus K t) (vplus K t) := by
  refine Subset.antisymm (fun p hp => ?_) ((hK.2.2.inter (convex_line t _)).segment_subset
    (vminus_mem_edge hK t) (vplus_mem_edge hK t))
  -- the points of `e_K(t)` are `h_K(t) u_t + d v_t` with `m ≤ d ≤ M`, `m, M` those of `v_K^±(t)`
  set m := dot (vminus K t) (vvec t)
  set M := dot (vplus K t) (vvec t)
  set d := dot p (vvec t)
  have hm : m ≤ d := dot_vminus_le_dot hK.2.1 hp
  have hM : d ≤ M := dot_le_dot_vplus hK.2.1 hp
  -- so `p = v_K⁻(t) + θ (v_K⁺(t) - v_K⁻(t))` with `θ = (d - m) / (M - m)` (and `θ = 0` if `m = M`)
  have hθ : (d - m) / (M - m) * (M - m) = d - m := div_mul_cancel_of_imp fun h => by linarith
  rw [segment_eq_image']
  refine ⟨(d - m) / (M - m), ⟨div_nonneg (by linarith) (by linarith),
    div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
  rw [cb_eq_of_mem_edge hp, cb_eq_of_mem_edge (vminus_mem_edge hK t),
    cb_eq_of_mem_edge (vplus_mem_edge hK t)]
  linear_combination (norm := module) hθ • vvec t

lemma dot_vplus_uvec (K : Set (ℝ × ℝ)) (t : ℝ) : dot (vplus K t) (uvec t) = supp K t := by
  simp [vplus, dot_add_left, dot_smul_left]

lemma dot_vminus_uvec (K : Set (ℝ × ℝ)) (t : ℝ) : dot (vminus K t) (uvec t) = supp K t := by
  simp [vminus, dot_add_left, dot_smul_left]

lemma dot_vminus_le_dot_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    dot (vminus K t) (vvec t) ≤ dot (vplus K t) (vvec t) :=
  dot_vminus_le_dot hK.2.1 (vplus_mem_edge hK t)

/-- `v_K(a, b)` lies on the supporting line `l_K(a)`. -/
lemma vint_mem_line_left (K : Set (ℝ × ℝ)) (a b : ℝ) : vint K a b ∈ suppLine K a := by
  simp [vint, suppLine, line, dot_add_left, dot_smul_left]

/-- `v_K(a, b)` lies on the supporting line `l_K(b)` when `sin (b - a) ≠ 0`. -/
lemma vint_mem_line_right (K : Set (ℝ × ℝ)) {a b : ℝ} (h : sin (b - a) ≠ 0) :
    vint K a b ∈ suppLine K b := by
  simp only [vint, suppLine, line, mem_ofPred_eq, dot_add_left, dot_smul_left, dot_uvec_uvec,
    dot_vvec_uvec']
  rw [div_mul_cancel₀ _ h, show a - b = -(b - a) by ring, cos_neg]
  ring

/-! ### Proof of Theorem `thm:limits-converging-to-vertex` -/

/-- The frame identity `p · u_s = cos (t - s) (p · u_t) + sin (t - s) (p · (-v_t))`. -/
private lemma cb_dot_uvec_left (x : ℝ × ℝ) (s t : ℝ) :
    dot x (uvec s) = cos (t - s) * dot x (uvec t) + sin (t - s) * dot x (-vvec t) := by
  rw [dot_uvec_eq_cos_add_sin x s t, dot_neg_right, ← neg_sub t s, cos_neg, sin_neg]; ring

/-- Decomposition in the frame `(u_t, -v_t)`. -/
private lemma cb_frame_left (x : ℝ × ℝ) (t : ℝ) :
    x = dot x (uvec t) • uvec t + dot x (-vvec t) • (-vvec t) := by
  rw [dot_neg_right, neg_smul_neg]
  exact eq_dot_uvec_smul_add x t

private lemma cb_dot_comm (p q : ℝ × ℝ) : dot p q = dot q p := by
  simp only [dot]; ring

private lemma cb_dot_uvec_self (t : ℝ) : dot (uvec t) (uvec t) = 1 := by
  rw [dot_uvec_uvec, sub_self, cos_zero]

private lemma cb_dot_vvec_self (t : ℝ) : dot (vvec t) (vvec t) = 1 := by
  rw [dot_vvec_vvec, sub_self, cos_zero]

private lemma cb_dot_neg_vvec_uvec (t : ℝ) : dot (-vvec t) (uvec t) = 0 := by
  rw [dot_neg_left, dot_vvec_uvec, neg_zero]

private lemma cb_dot_neg_vvec_self (t : ℝ) : dot (-vvec t) (-vvec t) = 1 := by
  rw [dot_neg_left, dot_neg_right, neg_neg, cb_dot_vvec_self]

/-- Convergence of points from the convergence of both coordinates in a frame `(u, v)`. -/
private lemma cb_tendsto_of_dot {u v P : ℝ × ℝ} (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    {ι : Type*} {l : Filter ι} {x : ι → ℝ × ℝ}
    (hu : Tendsto (fun i => dot (x i) u) l (𝓝 (dot P u)))
    (hv : Tendsto (fun i => dot (x i) v) l (𝓝 (dot P v))) : Tendsto x l (𝓝 P) := by
  have h := (hu.smul_const u).add (hv.smul_const v)
  rw [← huv P] at h
  exact Tendsto.congr (fun i => (huv (x i)).symm) h

/-- The segment of the paper's proof, in an orthonormal frame `(u, v)`: `(u_t, v_t)` for the right
limits, `(u_t, -v_t)` for the left limits. Let `P` be the point of the closed set `K` farthest in
the direction `v` among the points farthest in the direction `u` (for the right limits, `v_K⁺(t)`).
For `ε > 0` the point `p = P + ε v` is not in `K`, and as the complement of `K` is open, for some
`0 < ε' ≤ ε` the segment from `p` to `q = p - ε' u` misses `K`. In coordinates: a point of `K` with
`v`-coordinate `P · v + ε` does not have its `u`-coordinate in `[P · u - ε', P · u]`. -/
private lemma cb_segment {K : Set (ℝ × ℝ)} (hK : IsClosed K) {u v P : ℝ × ℝ}
    (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    (huu : dot u u = 1) (hvu : dot v u = 0) (hvv : dot v v = 1)
    (hmax : ∀ x ∈ K, dot x u = dot P u → dot x v ≤ dot P v) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' > 0, ε' ≤ ε ∧ ∀ x ∈ K, dot x v = dot P v + ε → dot P u - ε' ≤ dot x u →
      dot P u < dot x u := by
  -- the points `g μ = (P · u - μ) u + (P · v + ε) v` of the line through `p` parallel to `u`
  set g : ℝ → ℝ × ℝ := fun μ => (dot P u - μ) • u + (dot P v + ε) • v with hg
  have hgu : ∀ μ, dot (g μ) u = dot P u - μ := fun μ => by
    simp only [hg, dot_add_left, dot_smul_left, huu, hvu]; ring
  have hgv : ∀ μ, dot (g μ) v = dot P v + ε := fun μ => by
    simp only [hg, dot_add_left, dot_smul_left, hvv, cb_dot_comm u v, hvu]; ring
  -- `p = g 0` is not in `K`: it is as far as `P` in the direction `u`, and farther in the
  -- direction `v`
  have hp : g 0 ∉ K := fun h => by
    have h' := hmax _ h (by rw [hgu, sub_zero])
    rw [hgv] at h'
    linarith
  -- the complement of `K` is open, so it contains the points `g μ` with `μ` near `0`
  have hg_cont : Continuous g := by rw [hg]; fun_prop
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (hg_cont.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hp))
  refine ⟨min ε (r / 2), lt_min hε (half_pos hr), min_le_left _ _, fun x hx hxv hxu => ?_⟩
  by_contra hxP
  push Not at hxP
  -- `x = g μ` with `μ = P · u - x · u ∈ [0, ε']`: a point of the segment from `p` to `q`
  have hx' : x = g (dot P u - dot x u) := by
    conv_lhs => rw [huv x]
    simp only [hg, hxv, sub_sub_cancel]
  have hμ : dot P u - dot x u ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [min_le_right ε (r / 2)]
  exact hball hμ (hx' ▸ hx)

/-- The triangle of the paper's proof contains the part of `K` on its side of the line through
`P` and `q`. In coordinates relative to `P`, with `a = (r - P) · u` and `b = (r - P) · v`, that
side is the half-plane `H_T : ε a + ε' b ≥ 0`, and the triangle `T` with vertices `P`, `p`, `q` is
`H_T ∩ {a ≤ 0, b ≤ ε}`. Every point `r` of the convex set `K` has `a ≤ 0`; if `r ∈ H_T` had `b > ε`,
the point `P + (ε / b) (r - P)` of the segment from `P` to `r`, which lies in `K`, would be a point of
the segment from `p` to `q`, which misses `K`. -/
private lemma cb_mem_triangle {K : Set (ℝ × ℝ)} (hKc : Convex ℝ K) {u v P : ℝ × ℝ} (hP : P ∈ K)
    (hle : ∀ x ∈ K, dot x u ≤ dot P u) {ε ε' : ℝ} (hε : 0 < ε)
    (hseg : ∀ x ∈ K, dot x v = dot P v + ε → dot P u - ε' ≤ dot x u → dot P u < dot x u)
    {r : ℝ × ℝ} (hr : r ∈ K) (hT : 0 ≤ ε * (dot r u - dot P u) + ε' * (dot r v - dot P v)) :
    dot r v - dot P v ≤ ε := by
  by_contra hb
  push Not at hb
  have hb0 : 0 < dot r v - dot P v := hε.trans hb
  have ha : dot r u - dot P u ≤ 0 := sub_nonpos.2 (hle r hr)
  -- the point `y = P + μ (r - P)`, with `μ = ε / b ∈ (0, 1)`, lies in `K` and has `b`-coordinate `ε`
  set μ := ε / (dot r v - dot P v) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg hε.le hb0.le
  have hμ1 : μ ≤ 1 := (div_le_one hb0).2 hb.le
  have hμb : μ * (dot r v - dot P v) = ε := by rw [hμ]; field_simp
  have hy : P + μ • (r - P) ∈ K := hKc.add_smul_sub_mem hP hr ⟨hμ0, hμ1⟩
  have hyu : dot (P + μ • (r - P)) u = dot P u + μ * (dot r u - dot P u) := by
    rw [dot_add_left, dot_smul_left, dot_sub_left]
  have hyv : dot (P + μ • (r - P)) v = dot P v + ε := by
    rw [dot_add_left, dot_smul_left, dot_sub_left, hμb]
  -- its `a`-coordinate `μ a` lies in `[-ε', 0]`, since `ε a ≥ -ε' b`
  have hμa : -ε' ≤ μ * (dot r u - dot P u) := by
    have h1 : μ * (-(ε' * (dot r v - dot P v))) ≤ μ * (ε * (dot r u - dot P u)) :=
      mul_le_mul_of_nonneg_left (by linarith) hμ0
    have h2 : μ * (-(ε' * (dot r v - dot P v))) = -(ε' * (μ * (dot r v - dot P v))) := by ring
    rw [h2, hμb] at h1
    by_contra hcon
    push Not at hcon
    have h3 := mul_lt_mul_of_pos_left hcon hε
    linarith
  -- so `y` is a point of the segment from `p` to `q`, which misses `K`
  have h := hseg _ hy hyv (by rw [hyu]; linarith)
  rw [hyu] at h
  linarith [mul_nonpos_of_nonneg_of_nonpos hμ0 ha]

/-- The edges of `K` in directions close to `u` lie in the triangle of the paper's proof. Let the
direction `c u + d v`, with `d > 0` and `d ε < c ε'`, turn from `u` towards `v` by less than the
angle of `T` at `P`. A point `z ∈ K` that does at least as well as `P` in that direction is not
beyond the line through `P` and `q`, where every point of `K` does worse than `P`; so `z ∈ H_T`,
and `z ∈ T` by `cb_mem_triangle`. The points of `T` are within `ε'` of `P` in the direction `u`
and within `ε` in the direction `v`. -/
private lemma cb_better_mem_triangle {K : Set (ℝ × ℝ)} (hKc : Convex ℝ K) {u v P : ℝ × ℝ}
    (hP : P ∈ K) (hle : ∀ x ∈ K, dot x u ≤ dot P u) {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (hseg : ∀ x ∈ K, dot x v = dot P v + ε → dot P u - ε' ≤ dot x u → dot P u < dot x u)
    {c d : ℝ} (hd : 0 < d) (hcd : d * ε < c * ε') {z : ℝ × ℝ} (hz : z ∈ K)
    (hzP : c * dot P u + d * dot P v ≤ c * dot z u + d * dot z v) :
    |dot z u - dot P u| ≤ ε' ∧ |dot z v - dot P v| ≤ ε := by
  have ha : dot z u - dot P u ≤ 0 := sub_nonpos.2 (hle z hz)
  have hab : 0 ≤ c * (dot z u - dot P u) + d * (dot z v - dot P v) := by linarith
  -- `z ∈ H_T`: if `ε a + ε' b < 0`, then `c a + d b ≥ 0` would force `a (c ε' - d ε) > 0`
  have hT : 0 ≤ ε * (dot z u - dot P u) + ε' * (dot z v - dot P v) := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hε'.le hab, mul_neg_of_pos_of_neg hd h,
      mul_nonpos_of_nonpos_of_nonneg ha (sub_nonneg.2 hcd.le)]
  have hb := cb_mem_triangle hKc hP hle hε hseg hz hT
  -- so `-ε' ≤ a ≤ 0` and `0 ≤ b ≤ ε`
  have hb0 : 0 ≤ dot z v - dot P v := by nlinarith [mul_nonneg hε.le (neg_nonneg.2 ha)]
  have ha0 : -ε' ≤ dot z u - dot P u := by nlinarith [mul_le_mul_of_nonneg_left hb hε'.le]
  exact ⟨abs_le.2 ⟨ha0, by linarith⟩, abs_le.2 ⟨by linarith, hb⟩⟩

/-- The core of Theorem `thm:limits-converging-to-vertex`, by the paper's `ε`-triangle, in an
orthonormal frame `(u, v)`: `(u_t, v_t)` for the right limits and, by the symmetric argument,
`(u_t, -v_t)` for the left limits. Let `P` be the point of the closed convex set `K` farthest in the
direction `v` among those farthest in the direction `u`. If the points `w i ∈ K` do at least as well
as `P` in the direction `c i • u + d i • v`, where `c i → 1` and `d i → 0⁺`, then `w i → P`. Given
`ε > 0`, take the segment of `cb_segment`; eventually the direction turns from `u` by less than the
angle of the triangle `T` at `P`, so `w i ∈ T` (`cb_better_mem_triangle`), and the points of `T` are
within `ε` of `P` in both coordinates. -/
private lemma cb_tendsto_core {K : Set (ℝ × ℝ)} (hKcl : IsClosed K) (hKc : Convex ℝ K)
    {u v P : ℝ × ℝ} (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    (huu : dot u u = 1) (hvu : dot v u = 0) (hvv : dot v v = 1)
    (hP : P ∈ K) (hle : ∀ x ∈ K, dot x u ≤ dot P u)
    (hmax : ∀ x ∈ K, dot x u = dot P u → dot x v ≤ dot P v)
    {ι : Type*} {l : Filter ι} {c d : ι → ℝ} {w : ι → ℝ × ℝ}
    (hc : Tendsto c l (𝓝 1)) (hd : Tendsto d l (𝓝 0)) (hdpos : ∀ᶠ i in l, 0 < d i)
    (hwK : ∀ᶠ i in l, w i ∈ K)
    (hw : ∀ᶠ i in l, c i * dot P u + d i * dot P v ≤ c i * dot (w i) u + d i * dot (w i) v) :
    Tendsto w l (𝓝 P) := by
  have key : ∀ ε > 0, ∀ᶠ i in l,
      |dot (w i) u - dot P u| ≤ ε ∧ |dot (w i) v - dot P v| ≤ ε := by
    intro ε hε
    obtain ⟨ε', hε', hε'ε, hseg⟩ := cb_segment hKcl huv huu hvu hvv hmax hε
    have hc' : ∀ᶠ i in l, 1 / 2 < c i := hc.eventually (lt_mem_nhds (by norm_num))
    have hd' : ∀ᶠ i in l, d i < ε' / (2 * ε) := hd.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hc', hd', hdpos, hwK, hw] with i hci hdi hdi0 hwi hwi'
    have hcd : d i * ε < c i * ε' := by
      rw [lt_div_iff₀ (by positivity)] at hdi
      nlinarith [mul_lt_mul_of_pos_right hci hε']
    obtain ⟨h1, h2⟩ := cb_better_mem_triangle hKc hP hle hε hε' hseg hdi0 hcd hwi hwi'
    exact ⟨h1.trans hε'ε, h2⟩
  refine cb_tendsto_of_dot huv (Metric.tendsto_nhds.2 fun ε hε => ?_)
    (Metric.tendsto_nhds.2 fun ε hε => ?_)
  · filter_upwards [key (ε / 2) (half_pos hε)] with i hi
    rw [Real.dist_eq]
    linarith [hi.1]
  · filter_upwards [key (ε / 2) (half_pos hε)] with i hi
    rw [Real.dist_eq]
    linarith [hi.2]

/-- The intersection of the two supporting lines in the core's frame: if `F i = w i · (c i • u +
d i • v)` is the support value in that direction, then `(F i - (P · u) c i) / d i → P · v`. This
is the `v`-coordinate of the point where the line `x · (c i • u + d i • v) = F i` meets the line
`x · u = P · u` through `P`. That point lies between `P` and `p`, as in the paper: it is not behind
`P`, as `P ∈ K`, and not beyond `w i`, which lies in the triangle `T` and tends to `P`. -/
private lemma cb_coef_core {K : Set (ℝ × ℝ)} (hKcl : IsClosed K) (hKc : Convex ℝ K)
    {u v P : ℝ × ℝ} (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    (huu : dot u u = 1) (hvu : dot v u = 0) (hvv : dot v v = 1)
    (hP : P ∈ K) (hle : ∀ x ∈ K, dot x u ≤ dot P u)
    (hmax : ∀ x ∈ K, dot x u = dot P u → dot x v ≤ dot P v)
    {ι : Type*} {l : Filter ι} {c d F : ι → ℝ} {w : ι → ℝ × ℝ}
    (hc : Tendsto c l (𝓝 1)) (hd : Tendsto d l (𝓝 0)) (hdpos : ∀ᶠ i in l, 0 < d i)
    (hwK : ∀ᶠ i in l, w i ∈ K)
    (hF : ∀ᶠ i in l, F i = c i * dot (w i) u + d i * dot (w i) v)
    (hFP : ∀ᶠ i in l, c i * dot P u + d i * dot P v ≤ F i) :
    Tendsto (fun i => (F i - dot P u * c i) / d i) l (𝓝 (dot P v)) := by
  have hw : Tendsto w l (𝓝 P) := by
    refine cb_tendsto_core hKcl hKc huv huu hvu hvv hP hle hmax hc hd hdpos hwK ?_
    filter_upwards [hF, hFP] with i h1 h2 using h1 ▸ h2
  have hwv : Tendsto (fun i => dot (w i) v) l (𝓝 (dot P v)) :=
    ((continuous_dot v).tendsto P).comp hw
  have hc' : ∀ᶠ i in l, 0 < c i := hc.eventually (lt_mem_nhds (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwv ?_ ?_
  · filter_upwards [hFP, hdpos] with i h1 hdi
    rw [le_div_iff₀ hdi]
    linarith
  · filter_upwards [hF, hdpos, hc', hwK] with i h1 hdi hci hi
    rw [div_le_iff₀ hdi, h1]
    have := mul_le_mul_of_nonneg_left (hle _ hi) hci.le
    linarith

private lemma cb_tendsto_cos_right (t : ℝ) : Tendsto (fun s => cos (s - t)) (𝓝[>] t) (𝓝 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds <|
    (by fun_prop : Continuous fun s => cos (s - t)).tendsto' t 1 (by simp)

private lemma cb_tendsto_sin_right (t : ℝ) : Tendsto (fun s => sin (s - t)) (𝓝[>] t) (𝓝 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds <|
    (by fun_prop : Continuous fun s => sin (s - t)).tendsto' t 0 (by simp)

private lemma cb_tendsto_cos_left (t : ℝ) : Tendsto (fun s => cos (t - s)) (𝓝[<] t) (𝓝 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds <|
    (by fun_prop : Continuous fun s => cos (t - s)).tendsto' t 1 (by simp)

private lemma cb_tendsto_sin_left (t : ℝ) : Tendsto (fun s => sin (t - s)) (𝓝[<] t) (𝓝 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds <|
    (by fun_prop : Continuous fun s => sin (t - s)).tendsto' t 0 (by simp)

private lemma cb_sin_pos_right (t : ℝ) : ∀ᶠ s in 𝓝[>] t, 0 < sin (s - t) := by
  filter_upwards [Ioo_mem_nhdsGT (show t < t + π by linarith [pi_pos])] with s hs
  exact sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])

private lemma cb_sin_pos_left (t : ℝ) : ∀ᶠ s in 𝓝[<] t, 0 < sin (t - s) := by
  filter_upwards [Ioo_mem_nhdsLT (show t - π < t by linarith [pi_pos])] with s hs
  exact sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])

/-- Right limits: every choice of points `w s ∈ e_K(s)` converges to `v_K⁺(t)` as `s → t⁺`. A point
of `e_K(s)` does at least as well as `v_K⁺(t)` in the direction `u_s = cos (s - t) u_t +
sin (s - t) v_t`. -/
private lemma cb_tendsto_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ)
    {w : ℝ → ℝ × ℝ} (hw : ∀ s, w s ∈ edge K s) : Tendsto w (𝓝[>] t) (𝓝 (vplus K t)) := by
  have hP := vplus_mem_edge hK t
  refine cb_tendsto_core hK.isClosed hK.2.2 (fun x => eq_dot_uvec_smul_add x t)
    (cb_dot_uvec_self t) (dot_vvec_uvec t) (cb_dot_vvec_self t) hP.1
    (fun x hx => by rw [dot_vplus_uvec]; exact dot_le_supp hK.2.1 hx t)
    (fun x hx hxu => dot_le_dot_vplus hK.2.1 (mem_edge_iff.2 ⟨hx, by rw [hxu, dot_vplus_uvec]⟩))
    (cb_tendsto_cos_right t) (cb_tendsto_sin_right t) (cb_sin_pos_right t)
    (Eventually.of_forall fun s => (hw s).1) (Eventually.of_forall fun s => ?_)
  rw [← dot_uvec_eq_cos_add_sin, ← dot_uvec_eq_cos_add_sin, (hw s).2]
  exact dot_le_supp hK.2.1 hP.1 s

/-- Left limits, by the symmetric argument in the frame `(u_t, -v_t)`: every choice of points
`w s ∈ e_K(s)` converges to `v_K⁻(t)` as `s → t⁻`. -/
private lemma cb_tendsto_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ)
    {w : ℝ → ℝ × ℝ} (hw : ∀ s, w s ∈ edge K s) : Tendsto w (𝓝[<] t) (𝓝 (vminus K t)) := by
  have hP := vminus_mem_edge hK t
  refine cb_tendsto_core hK.isClosed hK.2.2 (fun x => cb_frame_left x t)
    (cb_dot_uvec_self t) (cb_dot_neg_vvec_uvec t) (cb_dot_neg_vvec_self t) hP.1
    (fun x hx => by rw [dot_vminus_uvec]; exact dot_le_supp hK.2.1 hx t)
    (fun x hx hxu => by
      rw [dot_neg_right, dot_neg_right, neg_le_neg_iff]
      exact dot_vminus_le_dot hK.2.1 (mem_edge_iff.2 ⟨hx, by rw [hxu, dot_vminus_uvec]⟩))
    (cb_tendsto_cos_left t) (cb_tendsto_sin_left t) (cb_sin_pos_left t)
    (Eventually.of_forall fun s => (hw s).1) (Eventually.of_forall fun s => ?_)
  rw [← cb_dot_uvec_left, ← cb_dot_uvec_left, (hw s).2]
  exact dot_le_supp hK.2.1 hP.1 s

/-- The `v_t`-coordinate of `v_K(s, t)`, read off the two lines `l_K(s)` and `l_K(t)` through it:
`v_K(s, t) · (-v_t) = (h(s) - h(t) cos (t - s)) / sin (t - s)` when `sin (t - s) ≠ 0`. -/
private lemma cb_dot_vint_left (K : Set (ℝ × ℝ)) {s t : ℝ} (hs : sin (t - s) ≠ 0) :
    dot (vint K s t) (-vvec t) = (supp K s - supp K t * cos (t - s)) / sin (t - s) := by
  have h1 : dot (vint K s t) (uvec s) = supp K s := vint_mem_line_left K s t
  have h2 : dot (vint K s t) (uvec t) = supp K t := vint_mem_line_right K hs
  rw [cb_dot_uvec_left _ s t, h2] at h1
  rw [← h1]
  field_simp
  ring

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), right limits. For a convex body `K` and
an angle `t`, the vertices `v_K^±(s)` and the intersections `v_K(t, s)` converge to `v_K⁺(t)` as
`s → t⁺`. In particular `v_K⁺` is right-continuous. -/
theorem tendsto_vplus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vplus K) (𝓝[>] t) (𝓝 (vplus K t)) :=
  cb_tendsto_right hK t (vplus_mem_edge hK)

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), right limits: `v_K⁻(s) → v_K⁺(t)` as
`s → t⁺`. -/
theorem tendsto_vminus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[>] t) (𝓝 (vplus K t)) :=
  cb_tendsto_right hK t (vminus_mem_edge hK)

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), right limits: `v_K(t, s) → v_K⁺(t)` as
`s → t⁺`. -/
theorem tendsto_vint_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun s => vint K t s) (𝓝[>] t) (𝓝 (vplus K t)) := by
  refine cb_tendsto_of_dot (fun x => eq_dot_uvec_smul_add x t) ?_ ?_
  · rw [dot_vplus_uvec]
    refine tendsto_const_nhds.congr (fun s => ?_)
    exact (vint_mem_line_left K t s).symm
  · -- the `v_t`-coordinate `(h(s) - h(t) cos (s - t)) / sin (s - t)` of `v_K(t, s)`
    have hP := cb_vplus_mem_edge hK.2.1 hK.1 t
    have h := cb_coef_core hK.isClosed hK.2.2 (fun x => eq_dot_uvec_smul_add x t)
      (cb_dot_uvec_self t) (dot_vvec_uvec t) (cb_dot_vvec_self t) hP.1
      (fun x hx => by rw [dot_vplus_uvec]; exact dot_le_supp hK.2.1 hx t)
      (fun x hx hxu => dot_le_dot_vplus hK.2.1
        (mem_edge_iff.2 ⟨hx, by rw [hxu, dot_vplus_uvec]⟩))
      (cb_tendsto_cos_right t) (cb_tendsto_sin_right t) (cb_sin_pos_right t)
      (F := supp K) (w := vplus K)
      (Eventually.of_forall fun s => (vplus_mem_edge hK s).1)
      (Eventually.of_forall fun s => by
        rw [← dot_uvec_eq_cos_add_sin, (vplus_mem_edge hK s).2])
      (Eventually.of_forall fun s => by
        rw [← dot_uvec_eq_cos_add_sin]; exact dot_le_supp hK.2.1 hP.1 s)
    rw [dot_vplus_uvec] at h
    refine h.congr (fun s => ?_)
    simp [vint, dot_add_left, dot_smul_left]

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), left limits: `v_K⁺(s) → v_K⁻(t)` as
`s → t⁻`. -/
theorem tendsto_vplus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vplus K) (𝓝[<] t) (𝓝 (vminus K t)) :=
  cb_tendsto_left hK t (vplus_mem_edge hK)

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), left limits: `v_K⁻(s) → v_K⁻(t)` as
`s → t⁻`; so `v_K⁻` is left-continuous. -/
theorem tendsto_vminus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[<] t) (𝓝 (vminus K t)) :=
  cb_tendsto_left hK t (vminus_mem_edge hK)

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), left limits: `v_K(s, t) → v_K⁻(t)` as
`s → t⁻`. -/
theorem tendsto_vint_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun s => vint K s t) (𝓝[<] t) (𝓝 (vminus K t)) := by
  refine cb_tendsto_of_dot (fun x => cb_frame_left x t) ?_ ?_
  · rw [dot_vminus_uvec]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [cb_sin_pos_left t] with s hs
    exact (vint_mem_line_right K hs.ne').symm
  · -- the `(-v_t)`-coordinate `(h(s) - h(t) cos (t - s)) / sin (t - s)` of `v_K(s, t)`
    have hP := cb_vminus_mem_edge hK.2.1 hK.1 t
    have h := cb_coef_core hK.isClosed hK.2.2 (fun x => cb_frame_left x t)
      (cb_dot_uvec_self t) (cb_dot_neg_vvec_uvec t) (cb_dot_neg_vvec_self t) hP.1
      (fun x hx => by rw [dot_vminus_uvec]; exact dot_le_supp hK.2.1 hx t)
      (fun x hx hxu => by
        rw [dot_neg_right, dot_neg_right, neg_le_neg_iff]
        exact dot_vminus_le_dot hK.2.1 (mem_edge_iff.2 ⟨hx, by rw [hxu, dot_vminus_uvec]⟩))
      (cb_tendsto_cos_left t) (cb_tendsto_sin_left t) (cb_sin_pos_left t)
      (F := supp K) (w := vminus K)
      (Eventually.of_forall fun s => (vminus_mem_edge hK s).1)
      (Eventually.of_forall fun s => by
        rw [← cb_dot_uvec_left, (vminus_mem_edge hK s).2])
      (Eventually.of_forall fun s => by
        rw [← cb_dot_uvec_left]; exact dot_le_supp hK.2.1 hP.1 s)
    rw [dot_vminus_uvec] at h
    refine h.congr' ?_
    filter_upwards [cb_sin_pos_left t] with s hs using (cb_dot_vint_left K hs.ne').symm

/-! ### One-sided derivatives of the support function -/

private lemma cb_tendsto_sin_div : Tendsto (fun e : ℝ => sin e / e) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope
  rw [cos_zero] at h
  refine h.congr (fun e => ?_)
  simp [slope_def_field]

private lemma cb_tendsto_cos_sub_div : Tendsto (fun e : ℝ => (cos e - 1) / e) (𝓝[≠] 0) (𝓝 0) := by
  have h := (Real.hasDerivAt_cos 0).tendsto_slope
  rw [sin_zero, neg_zero] at h
  refine h.congr (fun e => ?_)
  simp [slope_def_field]

private lemma cb_tendsto_sub (t : ℝ) : Tendsto (fun s => s - t) (𝓝[≠] t) (𝓝[≠] 0) := by
  have h := ((Homeomorph.subRight t).map_punctured_nhds_eq t).le
  rwa [Homeomorph.subRight_apply, sub_self] at h

/-- The support function has right derivative `v_K⁺(t) · v_t`. -/
theorem hasDerivWithinAt_supp_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivWithinAt (supp K) (dot (vplus K t) (vvec t)) (Ici t) t := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  -- slope = (sin δ / δ) · (v_t-coordinate of `v_K(t, s)`) + h(t) (cos δ - 1) / δ, `δ = s - t`
  have hsub := (cb_tendsto_sub t).mono_left (nhdsGT_le_nhdsNE t)
  have h1 := cb_tendsto_sin_div.comp hsub
  have h2 := cb_tendsto_cos_sub_div.comp hsub
  -- the `v_t`-coordinate of `v_K(t, s)` tends to `v_K⁺(t) · v_t` (Theorem 2.1.3)
  have hc : Tendsto (fun s => (supp K s - supp K t * cos (s - t)) / sin (s - t)) (𝓝[>] t)
      (𝓝 (dot (vplus K t) (vvec t))) :=
    (((continuous_dot (vvec t)).tendsto _).comp (tendsto_vint_right hK t)).congr fun s => by
      simp [vint, dot_add_left, dot_smul_left]
  have h := (h1.mul hc).add (h2.const_mul (supp K t))
  rw [one_mul, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [cb_sin_pos_right t, self_mem_nhdsWithin] with s hs hst
  have hst' : s - t ≠ 0 := sub_ne_zero.2 (ne_of_gt hst)
  simp only [Function.comp, slope_def_field]
  field_simp
  ring

/-- The support function has left derivative `v_K⁻(t) · v_t`. -/
theorem hasDerivWithinAt_supp_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivWithinAt (supp K) (dot (vminus K t) (vvec t)) (Iic t) t := by
  rw [← hasDerivWithinAt_Iio_iff_Iic, hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  -- slope = (sin δ / δ) · (`v_t`-coordinate of `v_K(s, t)`) + h(t) (cos δ - 1) / δ, `δ = s - t`
  have hsub := (cb_tendsto_sub t).mono_left (nhdsLT_le_nhdsNE t)
  have h1 := cb_tendsto_sin_div.comp hsub
  have h2 := cb_tendsto_cos_sub_div.comp hsub
  -- the `(-v_t)`-coordinate of `v_K(s, t)` tends to `v_K⁻(t) · (-v_t)` (Theorem 2.1.3)
  have hc : Tendsto (fun s => (supp K s - supp K t * cos (t - s)) / sin (t - s)) (𝓝[<] t)
      (𝓝 (dot (vminus K t) (-vvec t))) := by
    refine (((continuous_dot (-vvec t)).tendsto _).comp (tendsto_vint_left hK t)).congr' ?_
    filter_upwards [cb_sin_pos_left t] with s hs using cb_dot_vint_left K hs.ne'
  have h := ((h1.mul hc).neg).add (h2.const_mul (supp K t))
  rw [one_mul, mul_zero, add_zero, dot_neg_right, neg_neg] at h
  refine h.congr' ?_
  filter_upwards [cb_sin_pos_left t, self_mem_nhdsWithin] with s hs hst
  have hts : t - s ≠ 0 := sub_ne_zero.2 (ne_of_gt (mem_Iio.1 hst))
  have hs' : sin (t - s) ≠ 0 := hs.ne'
  simp only [Function.comp, slope_def_field]
  rw [show s - t = -(t - s) by ring, sin_neg, cos_neg]
  field_simp
  ring

/-- If the support function agrees on a left neighbourhood of `t` with a function differentiable at
`t`, then `v_K⁻(t) · v_t` is its derivative. -/
lemma dot_vminus_vvec_of_hasDerivAt {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t g' : ℝ}
    {G : ℝ → ℝ} (hG : HasDerivAt G g' t) (heq : supp K =ᶠ[𝓝[≤] t] G) (hval : supp K t = G t) :
    dot (vminus K t) (vvec t) = g' :=
  (uniqueDiffWithinAt_Iic t).eq_deriv _ (hasDerivWithinAt_supp_left hK t)
    (hG.hasDerivWithinAt.congr_of_eventuallyEq heq hval)

/-- If the support function agrees on a right neighbourhood of `t` with a function differentiable
at `t`, then `v_K⁺(t) · v_t` is its derivative. -/
lemma dot_vplus_vvec_of_hasDerivAt {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t g' : ℝ}
    {G : ℝ → ℝ} (hG : HasDerivAt G g' t) (heq : supp K =ᶠ[𝓝[≥] t] G) (hval : supp K t = G t) :
    dot (vplus K t) (vvec t) = g' :=
  (uniqueDiffWithinAt_Ici t).eq_deriv _ (hasDerivWithinAt_supp_right hK t)
    (hG.hasDerivWithinAt.congr_of_eventuallyEq heq hval)

end MovingSofaOptimality
