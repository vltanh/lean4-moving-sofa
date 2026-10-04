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

Theorem `thm:limits-converging-to-vertex` is proved by compactness rather than by the paper's
`ε`-triangle: for `s → t⁺`, any point `w` of `e_K(s)` satisfies `w · u_s ≥ v_K⁺(t) · u_s`, which
forces `w · u_t → h_K(t)` and `w · v_t ≥ v_K⁺(t) · v_t`, so every cluster point of `w` lies on
`e_K(t)` and is at least as far as `v_K⁺(t)` in the direction `v_t`, hence equals `v_K⁺(t)`
(`cb_tendsto_core`). The one-sided derivatives of `h_K` follow from Theorem
`thm:limits-converging-to-vertex`: the `v_t`-coordinate of `v_K(t, s)` tends to that of `v_K⁺(t)`.
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

/-- Convergence of points from the convergence of both coordinates in a frame `(u, v)`. -/
private lemma cb_tendsto_of_dot {u v P : ℝ × ℝ} (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    {ι : Type*} {l : Filter ι} {x : ι → ℝ × ℝ}
    (hu : Tendsto (fun i => dot (x i) u) l (𝓝 (dot P u)))
    (hv : Tendsto (fun i => dot (x i) v) l (𝓝 (dot P v))) : Tendsto x l (𝓝 P) := by
  have h := (hu.smul_const u).add (hv.smul_const v)
  rw [← huv P] at h
  exact Tendsto.congr (fun i => (huv (x i)).symm) h

/-- The core of Theorem `thm:limits-converging-to-vertex`, for a compact set `K` and a frame
`(u, v)`. Let `P ∈ K` maximize `· u` over `K`, and among those maximizers maximize `· v`. If the
points `w i ∈ K` do at least as well as `P` in the direction `c i • u + d i • v`, where `c i → 1`
and `d i → 0⁺`, then `w i → P`. Every cluster point `q` of `w` lies in `K`, maximizes `· u` and
satisfies `q · v ≥ P · v`, hence equals `P`. -/
private lemma cb_tendsto_core {K : Set (ℝ × ℝ)} (hK : IsCompact K) {u v P : ℝ × ℝ}
    (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    (hP : P ∈ K) (hle : ∀ x ∈ K, dot x u ≤ dot P u)
    (hmax : ∀ x ∈ K, dot x u = dot P u → dot x v ≤ dot P v)
    {ι : Type*} {l : Filter ι} {c d : ι → ℝ} {w : ι → ℝ × ℝ}
    (hc : Tendsto c l (𝓝 1)) (hd : Tendsto d l (𝓝 0)) (hdpos : ∀ᶠ i in l, 0 < d i)
    (hwK : ∀ᶠ i in l, w i ∈ K)
    (hw : ∀ᶠ i in l, c i * dot P u + d i * dot P v ≤ c i * dot (w i) u + d i * dot (w i) v) :
    Tendsto w l (𝓝 P) := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ K, |dot x v| ≤ R := by
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_dot v).continuousOn
    exact ⟨R, fun x hx => by simpa [Real.norm_eq_abs] using hR x hx⟩
  have hc' : ∀ᶠ i in l, 1 / 2 < c i := hc.eventually (lt_mem_nhds (by norm_num))
  -- the `u`-coordinate converges: `0 ≤ P · u - w · u ≤ 4 R d`
  have ha : Tendsto (fun i => dot P u - dot (w i) u) l (𝓝 0) := by
    have hup : Tendsto (fun i => 4 * R * d i) l (𝓝 0) := by simpa using hd.const_mul (4 * R)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hwK] with i hi
      linarith [hle _ hi]
    · filter_upwards [hwK, hw, hdpos, hc'] with i hi hwi hdi hci
      have h1 := hle _ hi
      have h2 : dot (w i) v - dot P v ≤ 2 * R := by
        have h3 := hR _ hi
        have h4 := hR _ hP
        rw [abs_le] at h3 h4
        linarith
      nlinarith [mul_nonneg (sub_nonneg.2 hci.le) (sub_nonneg.2 h1),
        mul_nonneg hdi.le (sub_nonneg.2 h2)]
  -- the `v`-coordinate is eventually at least that of `P`
  have hb : ∀ᶠ i in l, dot P v ≤ dot (w i) v := by
    filter_upwards [hwK, hw, hdpos, hc'] with i hi hwi hdi hci
    have h1 := hle _ hi
    by_contra hcon
    have hcon' := not_le.1 hcon
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ c i by linarith) (sub_nonneg.2 h1),
      mul_pos hdi (sub_pos.2 hcon')]
  apply hK.tendsto_nhds_of_unique_mapClusterPt hwK
  intro q hqK hq
  have hqu : dot q u = dot P u := by
    have h1 : MapClusterPt (dot P u - dot q u) l (fun i => dot P u - dot (w i) u) :=
      hq.continuousAt_comp (f := fun x => dot P u - dot x u)
        (continuous_const.sub (continuous_dot u)).continuousAt
    have h2 : ClusterPt (dot P u - dot q u) (𝓝 0) := h1.clusterPt.mono ha
    have h3 : dot P u - dot q u = 0 := by
      by_contra hne
      exact clusterPt_iff_not_disjoint.1 h2 (disjoint_nhds_nhds.2 hne)
    linarith
  have hqv : dot P v ≤ dot q v :=
    (isClosed_le continuous_const (continuous_dot v)).mem_of_mapClusterPt hq hb
  have hqv' := hmax q hqK hqu
  rw [huv q, huv P, hqu, le_antisymm hqv' hqv]

/-- The support-function form of the core: if `F i = w i · (c i • u + d i • v)` is the support
value in that direction, then `(F i - (P · u) c i) / d i → P · v`. This is the `v`-coordinate of the
intersection of the two supporting lines. -/
private lemma cb_coef_core {K : Set (ℝ × ℝ)} (hK : IsCompact K) {u v P : ℝ × ℝ}
    (huv : ∀ x : ℝ × ℝ, x = dot x u • u + dot x v • v)
    (hP : P ∈ K) (hle : ∀ x ∈ K, dot x u ≤ dot P u)
    (hmax : ∀ x ∈ K, dot x u = dot P u → dot x v ≤ dot P v)
    {ι : Type*} {l : Filter ι} {c d F : ι → ℝ} {w : ι → ℝ × ℝ}
    (hc : Tendsto c l (𝓝 1)) (hd : Tendsto d l (𝓝 0)) (hdpos : ∀ᶠ i in l, 0 < d i)
    (hwK : ∀ᶠ i in l, w i ∈ K)
    (hF : ∀ᶠ i in l, F i = c i * dot (w i) u + d i * dot (w i) v)
    (hFP : ∀ᶠ i in l, c i * dot P u + d i * dot P v ≤ F i) :
    Tendsto (fun i => (F i - dot P u * c i) / d i) l (𝓝 (dot P v)) := by
  have hw : Tendsto w l (𝓝 P) := by
    refine cb_tendsto_core hK huv hP hle hmax hc hd hdpos hwK ?_
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

/-- Right limits for a compact set: every choice of points `w s ∈ e_K(s)` converges to `v_K⁺(t)` as
`s → t⁺`. -/
private lemma cb_tendsto_right {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ)
    {w : ℝ → ℝ × ℝ} (hw : ∀ s, w s ∈ edge K s) : Tendsto w (𝓝[>] t) (𝓝 (vplus K t)) := by
  have hP := cb_vplus_mem_edge hK hne t
  refine cb_tendsto_core hK (fun x => eq_dot_uvec_smul_add x t) hP.1
    (fun x hx => by rw [dot_vplus_uvec]; exact dot_le_supp hK hx t)
    (fun x hx hxu => dot_le_dot_vplus hK (mem_edge_iff.2 ⟨hx, by rw [hxu, dot_vplus_uvec]⟩))
    (cb_tendsto_cos_right t) (cb_tendsto_sin_right t) (cb_sin_pos_right t)
    (Eventually.of_forall fun s => (hw s).1) (Eventually.of_forall fun s => ?_)
  rw [← dot_uvec_eq_cos_add_sin, ← dot_uvec_eq_cos_add_sin, (hw s).2]
  exact dot_le_supp hK hP.1 s

/-- Left limits for a compact set: every choice of points `w s ∈ e_K(s)` converges to `v_K⁻(t)` as
`s → t⁻`. -/
private lemma cb_tendsto_left {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ)
    {w : ℝ → ℝ × ℝ} (hw : ∀ s, w s ∈ edge K s) : Tendsto w (𝓝[<] t) (𝓝 (vminus K t)) := by
  have hP := cb_vminus_mem_edge hK hne t
  refine cb_tendsto_core hK (fun x => cb_frame_left x t) hP.1
    (fun x hx => by rw [dot_vminus_uvec]; exact dot_le_supp hK hx t)
    (fun x hx hxu => by
      rw [dot_neg_right, dot_neg_right, neg_le_neg_iff]
      exact dot_vminus_le_dot hK (mem_edge_iff.2 ⟨hx, by rw [hxu, dot_vminus_uvec]⟩))
    (cb_tendsto_cos_left t) (cb_tendsto_sin_left t) (cb_sin_pos_left t)
    (Eventually.of_forall fun s => (hw s).1) (Eventually.of_forall fun s => ?_)
  rw [← cb_dot_uvec_left, ← cb_dot_uvec_left, (hw s).2]
  exact dot_le_supp hK hP.1 s

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
  cb_tendsto_right hK.2.1 hK.1 t (vplus_mem_edge hK)

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), right limits: `v_K⁻(s) → v_K⁺(t)` as
`s → t⁺`. -/
theorem tendsto_vminus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[>] t) (𝓝 (vplus K t)) :=
  cb_tendsto_right hK.2.1 hK.1 t (vminus_mem_edge hK)

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
    have h := cb_coef_core hK.2.1 (fun x => eq_dot_uvec_smul_add x t) hP.1
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
  cb_tendsto_left hK.2.1 hK.1 t (vplus_mem_edge hK)

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), left limits: `v_K⁻(s) → v_K⁻(t)` as
`s → t⁻`; so `v_K⁻` is left-continuous. -/
theorem tendsto_vminus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[<] t) (𝓝 (vminus K t)) :=
  cb_tendsto_left hK.2.1 hK.1 t (vminus_mem_edge hK)

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
    have h := cb_coef_core hK.2.1 (fun x => cb_frame_left x t) hP.1
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
