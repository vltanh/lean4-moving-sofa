module

public import MovingSofa.Basic.Plane
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Planar convex bodies (§2.1)

Definitions `def:convex-body`, `def:support-function`, `def:supporting-line-half-plane`, `def:width`,
`def:convex-body-edge`, `def:convex-body-vertex`, `def:convex-body-tangent-lines-intersection`,
`def:hausdorff-distance`, and Theorem `thm:limits-converging-to-vertex`.

The support function, supporting lines and half-planes are defined for every subset of the plane;
they have their intended meaning for nonempty compact sets.
-/

@[expose] public section

open Real Set Filter Topology

namespace MovingSofa

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

lemma dot_le_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) {p : ℝ × ℝ} (hp : p ∈ S) (t : ℝ) :
    dot p (uvec t) ≤ supp S t := by
  sorry

lemma exists_dot_eq_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ) :
    ∃ p ∈ S, dot p (uvec t) = supp S t := by
  sorry

lemma supp_mono {S T : Set (ℝ × ℝ)} (hST : S ⊆ T) (hS : S.Nonempty) (hT : IsCompact T) (t : ℝ) :
    supp S t ≤ supp T t := by
  sorry

lemma supp_add_two_pi (S : Set (ℝ × ℝ)) (t : ℝ) : supp S (t + 2 * π) = supp S t := by
  simp [supp, uvec_add_two_pi]

lemma continuous_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) :
    Continuous (supp S) := by
  sorry

/-- A point lies in a closed convex set iff it lies in all of its supporting half-planes. -/
lemma mem_iff_forall_dot_le_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (p : ℝ × ℝ) :
    p ∈ K ↔ ∀ t, dot p (uvec t) ≤ supp K t := by
  sorry

/-- Two convex bodies with the same support function are equal. -/
lemma eq_of_supp_eq {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (h : ∀ t, supp K₁ t = supp K₂ t) : K₁ = K₂ := by
  sorry

lemma supp_translate (S : Set (ℝ × ℝ)) (v : ℝ × ℝ) (t : ℝ) (hS : IsCompact S)
    (hne : S.Nonempty) : supp ((fun p => p + v) '' S) t = supp S t + dot v (uvec t) := by
  sorry

/-! ### Edges and vertices -/

lemma vplus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) : vplus K t ∈ edge K t := by
  sorry

lemma vminus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) : vminus K t ∈ edge K t := by
  sorry

lemma edge_eq_segment {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    edge K t = segment ℝ (vminus K t) (vplus K t) := by
  sorry

lemma dot_vplus_uvec (K : Set (ℝ × ℝ)) (t : ℝ) : dot (vplus K t) (uvec t) = supp K t := by
  simp [vplus, dot_add_left, dot_smul_left]

lemma dot_vminus_uvec (K : Set (ℝ × ℝ)) (t : ℝ) : dot (vminus K t) (uvec t) = supp K t := by
  simp [vminus, dot_add_left, dot_smul_left]

lemma dot_vminus_le_dot_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    dot (vminus K t) (vvec t) ≤ dot (vplus K t) (vvec t) := by
  sorry

lemma vint_mem_line_left (K : Set (ℝ × ℝ)) (a b : ℝ) : vint K a b ∈ suppLine K a := by
  simp [vint, suppLine, line, dot_add_left, dot_smul_left]

lemma vint_mem_line_right (K : Set (ℝ × ℝ)) {a b : ℝ} (h : sin (b - a) ≠ 0) :
    vint K a b ∈ suppLine K b := by
  sorry

/-- **Theorem `thm:limits-converging-to-vertex`** (right limits). For a convex body `K` and an angle
`t`, the vertices `v_K^±(s)` and the intersections `v_K(t, s)` converge to `v_K⁺(t)` as `s → t⁺`.
In particular `v_K⁺` is right-continuous. -/
theorem tendsto_vplus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vplus K) (𝓝[>] t) (𝓝 (vplus K t)) := by
  sorry

theorem tendsto_vminus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[>] t) (𝓝 (vplus K t)) := by
  sorry

theorem tendsto_vint_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun s => vint K t s) (𝓝[>] t) (𝓝 (vplus K t)) := by
  sorry

/-- **Theorem `thm:limits-converging-to-vertex`** (left limits). -/
theorem tendsto_vplus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vplus K) (𝓝[<] t) (𝓝 (vminus K t)) := by
  sorry

theorem tendsto_vminus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[<] t) (𝓝 (vminus K t)) := by
  sorry

theorem tendsto_vint_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun s => vint K s t) (𝓝[<] t) (𝓝 (vminus K t)) := by
  sorry

/-- The support function has right derivative `v_K⁺(t) · v_t`. -/
theorem hasDerivWithinAt_supp_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivWithinAt (supp K) (dot (vplus K t) (vvec t)) (Ici t) t := by
  sorry

/-- The support function has left derivative `v_K⁻(t) · v_t`. -/
theorem hasDerivWithinAt_supp_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivWithinAt (supp K) (dot (vminus K t) (vvec t)) (Iic t) t := by
  sorry

end MovingSofa
