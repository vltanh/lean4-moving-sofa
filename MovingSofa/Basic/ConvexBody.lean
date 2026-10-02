module

public import MovingSofa.Basic.Plane
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Planar convex bodies (§2.1)

Definitions `def:convex-body`, `def:support-function`, `def:supporting-line-half-plane`, `def:width`,
`def:convex-body-edge`, `def:convex-body-vertex`, `def:convex-body-tangent-lines-intersection`,
`def:hausdorff-distance`, and Theorem `thm:limits-converging-to-vertex`.

The support function, supporting lines and half-planes are defined for every subset of the plane;
they have their intended meaning for nonempty compact sets.

The three non-public imports (Hahn–Banach separation, slopes, derivatives of `sin`/`cos`) are only
used inside proofs.

Theorem `thm:limits-converging-to-vertex` is proved by compactness rather than by the paper's
`ε`-triangle: for `s → t⁺`, any point `w` of `e_K(s)` satisfies `w · u_s ≥ v_K⁺(t) · u_s`, which forces
`w · u_t → h_K(t)` and `w · v_t ≥ v_K⁺(t) · v_t`, so every cluster point of `w` lies on `e_K(t)` and is
at least as far as `v_K⁺(t)` in the direction `v_t`, hence equals `v_K⁺(t)` (`cb_tendsto_core`). The
one-sided derivatives of `h_K` follow from the limit of the `v_t`-coordinate of `v_K(t, s)`.
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

/-- `p ↦ p · v` is continuous. -/
private lemma cb_continuous_dot (v : ℝ × ℝ) : Continuous (fun p : ℝ × ℝ => dot p v) := by
  simp only [dot]
  fun_prop

private lemma cb_bddAbove {S : Set (ℝ × ℝ)} (hS : IsCompact S) (v : ℝ × ℝ) :
    BddAbove ((fun p => dot p v) '' S) :=
  hS.bddAbove_image (cb_continuous_dot v).continuousOn

private lemma cb_bddBelow {S : Set (ℝ × ℝ)} (hS : IsCompact S) (v : ℝ × ℝ) :
    BddBelow ((fun p => dot p v) '' S) :=
  hS.bddBelow_image (cb_continuous_dot v).continuousOn

lemma dot_le_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) {p : ℝ × ℝ} (hp : p ∈ S) (t : ℝ) :
    dot p (uvec t) ≤ supp S t := by
  exact le_csSup (cb_bddAbove hS _) (mem_image_of_mem _ hp)

lemma exists_dot_eq_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ) :
    ∃ p ∈ S, dot p (uvec t) = supp S t := by
  exact (hS.image (cb_continuous_dot (uvec t))).sSup_mem (hne.image _)

lemma supp_mono {S T : Set (ℝ × ℝ)} (hST : S ⊆ T) (hS : S.Nonempty) (hT : IsCompact T) (t : ℝ) :
    supp S t ≤ supp T t := by
  exact csSup_le_csSup (cb_bddAbove hT _) (hS.image _) (image_mono hST)

lemma supp_add_two_pi (S : Set (ℝ × ℝ)) (t : ℝ) : supp S (t + 2 * π) = supp S t := by
  simp [supp, uvec_add_two_pi]

lemma continuous_supp {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    Continuous (supp S) := by
  -- the supremum of a jointly continuous family over a compact set is continuous (`hne` is not
  -- needed)
  have h : Continuous (fun x : ℝ × (ℝ × ℝ) => dot x.2 (uvec x.1)) := by
    simp only [dot, uvec]
    fun_prop
  exact hS.continuous_sSup (f := fun t p => dot p (uvec t)) h

/-- A point lies in a closed convex set iff it lies in all of its supporting half-planes. -/
lemma mem_iff_forall_dot_le_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (p : ℝ × ℝ) :
    p ∈ K ↔ ∀ t, dot p (uvec t) ≤ supp K t := by
  refine ⟨fun hp t => dot_le_supp hK.2.1 hp t, fun h => ?_⟩
  by_contra hp
  -- separate `p` from `K` by a continuous linear functional `f`
  obtain ⟨f, u, hfK, hfp⟩ := geometric_hahn_banach_closed_point hK.2.2 hK.isClosed hp
  set n : ℝ × ℝ := (f (1, 0), f (0, 1)) with hn
  have hf : ∀ x : ℝ × ℝ, f x = dot x n := by
    intro x
    have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
    simp [dot, n, smul_eq_mul]
  -- write the normal vector `n` in polar form `n = ‖z‖ • u_θ`
  set z : ℂ := ⟨n.1, n.2⟩ with hz
  have hz0 : z ≠ 0 := by
    intro hz0
    have hn0 : n = 0 := by
      have h1 : z.re = 0 := by rw [hz0]; rfl
      have h2 : z.im = 0 := by rw [hz0]; rfl
      ext
      · exact h1
      · exact h2
    obtain ⟨a, ha⟩ := hK.1
    have h1 := hfK a ha
    rw [hf, hn0, dot_zero_right] at h1 hfp
    linarith
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hn' : n = ‖z‖ • uvec (Complex.arg z) := by
    ext
    · simp only [Prod.smul_fst, uvec_fst, smul_eq_mul, Complex.norm_mul_cos_arg]
      rfl
    · simp only [Prod.smul_snd, uvec_snd, smul_eq_mul, Complex.norm_mul_sin_arg]
      rfl
  obtain ⟨a, ha, hae⟩ := exists_dot_eq_supp hK.2.1 hK.1 (Complex.arg z)
  have h1 := hfK a ha
  have h2 := h (Complex.arg z)
  rw [hf, hn', dot_smul_right] at h1 hfp
  rw [← hae] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hr.le
  linarith

/-- Two convex bodies with the same support function are equal. -/
lemma eq_of_supp_eq {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (h : ∀ t, supp K₁ t = supp K₂ t) : K₁ = K₂ := by
  ext p
  rw [mem_iff_forall_dot_le_supp h₁, mem_iff_forall_dot_le_supp h₂]
  simp only [h]

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

/-! ### Edges and vertices -/

private lemma cb_isClosed_line (t h : ℝ) : IsClosed (line t h) :=
  isClosed_eq (cb_continuous_dot _) continuous_const

private lemma cb_convex_line (t h : ℝ) : Convex ℝ (line t h) := by
  intro x hx y hy a b _ _ hab
  simp only [line, mem_ofPred_eq] at *
  rw [dot_add_left, dot_smul_left, dot_smul_left, hx, hy]
  linear_combination h * hab

private lemma cb_isCompact_edge {K : Set (ℝ × ℝ)} (hK : IsCompact K) (t : ℝ) :
    IsCompact (edge K t) :=
  hK.inter_right (cb_isClosed_line t _)

private lemma cb_mem_edge {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ K)
    (h : dot p (uvec t) = supp K t) : p ∈ edge K t :=
  ⟨hp, h⟩

private lemma cb_dot_eq_of_mem_edge {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ edge K t) :
    dot p (uvec t) = supp K t :=
  hp.2

private lemma cb_edge_nonempty {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    (edge K t).Nonempty := by
  obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp hK hne t
  exact ⟨p, hp, hpe⟩

/-- A point of the edge `e_K(t)` is determined by its `v_t`-coordinate. -/
private lemma cb_eq_of_mem_edge {K : Set (ℝ × ℝ)} {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ edge K t) :
    p = supp K t • uvec t + dot p (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add p t]
  rw [cb_dot_eq_of_mem_edge hp]

private lemma cb_dot_vplus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vplus K t) (vvec t) = sSup ((fun p => dot p (vvec t)) '' edge K t) := by
  simp [vplus, dot_add_left, dot_smul_left]

private lemma cb_dot_vminus_vvec (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vminus K t) (vvec t) = sInf ((fun p => dot p (vvec t)) '' edge K t) := by
  simp [vminus, dot_add_left, dot_smul_left]

private lemma cb_vplus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    vplus K t ∈ edge K t := by
  obtain ⟨p, hp, hpe⟩ := ((cb_isCompact_edge hK t).image (cb_continuous_dot (vvec t))).sSup_mem
    ((cb_edge_nonempty hK hne t).image _)
  have : vplus K t = p := by
    rw [cb_eq_of_mem_edge hp, vplus, ← hpe]
  rw [this]
  exact hp

private lemma cb_vminus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (t : ℝ) : vminus K t ∈ edge K t := by
  obtain ⟨p, hp, hpe⟩ := ((cb_isCompact_edge hK t).image (cb_continuous_dot (vvec t))).sInf_mem
    ((cb_edge_nonempty hK hne t).image _)
  have : vminus K t = p := by
    rw [cb_eq_of_mem_edge hp, vminus, ← hpe]
  rw [this]
  exact hp

/-- `v_K⁺(t)` is the farthest point of `e_K(t)` in the direction `v_t`. -/
private lemma cb_le_dot_vplus {K : Set (ℝ × ℝ)} (hK : IsCompact K) {t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edge K t) : dot p (vvec t) ≤ dot (vplus K t) (vvec t) := by
  rw [cb_dot_vplus_vvec]
  exact le_csSup (cb_bddAbove (cb_isCompact_edge hK t) _) (mem_image_of_mem _ hp)

/-- `v_K⁻(t)` is the farthest point of `e_K(t)` in the direction `-v_t`. -/
private lemma cb_dot_vminus_le {K : Set (ℝ × ℝ)} (hK : IsCompact K) {t : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edge K t) : dot (vminus K t) (vvec t) ≤ dot p (vvec t) := by
  rw [cb_dot_vminus_vvec]
  exact csInf_le (cb_bddBelow (cb_isCompact_edge hK t) _) (mem_image_of_mem _ hp)

lemma vplus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) : vplus K t ∈ edge K t := by
  exact cb_vplus_mem_edge hK.2.1 hK.1 t

lemma vminus_mem_edge {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) : vminus K t ∈ edge K t := by
  exact cb_vminus_mem_edge hK.2.1 hK.1 t

lemma edge_eq_segment {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    edge K t = segment ℝ (vminus K t) (vplus K t) := by
  apply Subset.antisymm
  · intro p hp
    have hm := cb_dot_vminus_le hK.2.1 hp
    have hM := cb_le_dot_vplus hK.2.1 hp
    have hpe := cb_eq_of_mem_edge hp
    have hme := cb_eq_of_mem_edge (vminus_mem_edge hK t)
    have hMe := cb_eq_of_mem_edge (vplus_mem_edge hK t)
    set m := dot (vminus K t) (vvec t)
    set M := dot (vplus K t) (vvec t)
    set d := dot p (vvec t)
    rcases eq_or_lt_of_le (hm.trans hM) with hmM | hmM
    · have hd : d = m := le_antisymm (hmM ▸ hM) hm
      have : p = vminus K t := by rw [hpe, hme, hd]
      rw [this]
      exact left_mem_segment ℝ _ _
    · have hMm : 0 < M - m := sub_pos.2 hmM
      have hab : (M - d) / (M - m) + (d - m) / (M - m) = 1 := by
        rw [← add_div, div_eq_one_iff_eq hMm.ne']
        ring
      have hcoef : (M - d) / (M - m) * m + (d - m) / (M - m) * M = d := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hMm.ne']
        ring
      refine ⟨(M - d) / (M - m), (d - m) / (M - m), div_nonneg (by linarith) hMm.le,
        div_nonneg (by linarith) hMm.le, hab, ?_⟩
      rw [hpe, hme, hMe]
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination (supp K t * (uvec t).1) * hab + (vvec t).1 * hcoef
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination (supp K t * (uvec t).2) * hab + (vvec t).2 * hcoef
  · exact (hK.2.2.inter (cb_convex_line t _)).segment_subset (vminus_mem_edge hK t)
      (vplus_mem_edge hK t)

lemma dot_vplus_uvec (K : Set (ℝ × ℝ)) (t : ℝ) : dot (vplus K t) (uvec t) = supp K t := by
  simp [vplus, dot_add_left, dot_smul_left]

lemma dot_vminus_uvec (K : Set (ℝ × ℝ)) (t : ℝ) : dot (vminus K t) (uvec t) = supp K t := by
  simp [vminus, dot_add_left, dot_smul_left]

lemma dot_vminus_le_dot_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    dot (vminus K t) (vvec t) ≤ dot (vplus K t) (vvec t) := by
  exact cb_dot_vminus_le hK.2.1 (vplus_mem_edge hK t)

lemma vint_mem_line_left (K : Set (ℝ × ℝ)) (a b : ℝ) : vint K a b ∈ suppLine K a := by
  simp [vint, suppLine, line, dot_add_left, dot_smul_left]

lemma vint_mem_line_right (K : Set (ℝ × ℝ)) {a b : ℝ} (h : sin (b - a) ≠ 0) :
    vint K a b ∈ suppLine K b := by
  simp only [vint, suppLine, line, mem_ofPred_eq, dot_add_left, dot_smul_left, dot_uvec_uvec,
    dot_vvec_uvec']
  rw [div_mul_cancel₀ _ h, show a - b = -(b - a) by ring, cos_neg]
  ring

/-! ### Proof of Theorem `thm:limits-converging-to-vertex` -/

/-- The frame identity `p · u_s = cos (s - t) (p · u_t) + sin (s - t) (p · v_t)`. -/
private lemma cb_dot_uvec_right (x : ℝ × ℝ) (s t : ℝ) :
    dot x (uvec s) = cos (s - t) * dot x (uvec t) + sin (s - t) * dot x (vvec t) := by
  conv_lhs => rw [show s = (s - t) + t by ring]
  simp only [dot, uvec, vvec, cos_add, sin_add]
  ring

/-- The frame identity `p · u_s = cos (t - s) (p · u_t) + sin (t - s) (p · (-v_t))`. -/
private lemma cb_dot_uvec_left (x : ℝ × ℝ) (s t : ℝ) :
    dot x (uvec s) = cos (t - s) * dot x (uvec t) + sin (t - s) * dot x (-vvec t) := by
  conv_lhs => rw [show s = t - (t - s) by ring]
  simp only [dot, uvec, vvec, cos_sub, sin_sub, Prod.fst_neg, Prod.snd_neg]
  ring

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
points `w i ∈ K` do at least as well as `P` in the direction `c i • u + d i • v`, where `c i → 1` and
`d i → 0⁺`, then `w i → P`. Every cluster point `q` of `w` lies in `K`, maximizes `· u` and satisfies
`q · v ≥ P · v`, hence equals `P`. -/
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
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (cb_continuous_dot v).continuousOn
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
        (continuous_const.sub (cb_continuous_dot u)).continuousAt
    have h2 : ClusterPt (dot P u - dot q u) (𝓝 0) := h1.clusterPt.mono ha
    have h3 : dot P u - dot q u = 0 := by
      by_contra hne
      exact clusterPt_iff_not_disjoint.1 h2 (disjoint_nhds_nhds.2 hne)
    linarith
  have hqv : dot P v ≤ dot q v :=
    (isClosed_le continuous_const (cb_continuous_dot v)).mem_of_mapClusterPt hq hb
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
    filter_upwards [hF, hFP] with i h1 h2
    rw [← h1]
    exact h2
  have hwv : Tendsto (fun i => dot (w i) v) l (𝓝 (dot P v)) :=
    ((cb_continuous_dot v).tendsto P).comp hw
  have hc' : ∀ᶠ i in l, 0 < c i := hc.eventually (lt_mem_nhds (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwv ?_ ?_
  · filter_upwards [hFP, hdpos] with i h1 hdi
    rw [le_div_iff₀ hdi]
    linarith
  · filter_upwards [hF, hdpos, hc', hwK] with i h1 hdi hci hi
    rw [div_le_iff₀ hdi, h1]
    have := mul_le_mul_of_nonneg_left (hle _ hi) hci.le
    linarith

private lemma cb_tendsto_cos_right (t : ℝ) : Tendsto (fun s => cos (s - t)) (𝓝[>] t) (𝓝 1) := by
  have h : Continuous (fun s => cos (s - t)) := by fun_prop
  simpa using (h.tendsto t).mono_left nhdsWithin_le_nhds

private lemma cb_tendsto_sin_right (t : ℝ) : Tendsto (fun s => sin (s - t)) (𝓝[>] t) (𝓝 0) := by
  have h : Continuous (fun s => sin (s - t)) := by fun_prop
  simpa using (h.tendsto t).mono_left nhdsWithin_le_nhds

private lemma cb_tendsto_cos_left (t : ℝ) : Tendsto (fun s => cos (t - s)) (𝓝[<] t) (𝓝 1) := by
  have h : Continuous (fun s => cos (t - s)) := by fun_prop
  simpa using (h.tendsto t).mono_left nhdsWithin_le_nhds

private lemma cb_tendsto_sin_left (t : ℝ) : Tendsto (fun s => sin (t - s)) (𝓝[<] t) (𝓝 0) := by
  have h : Continuous (fun s => sin (t - s)) := by fun_prop
  simpa using (h.tendsto t).mono_left nhdsWithin_le_nhds

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
    (fun x hx hxu => cb_le_dot_vplus hK (cb_mem_edge hx (by rw [hxu, dot_vplus_uvec])))
    (cb_tendsto_cos_right t) (cb_tendsto_sin_right t) (cb_sin_pos_right t)
    (Eventually.of_forall fun s => (hw s).1) (Eventually.of_forall fun s => ?_)
  rw [← cb_dot_uvec_right, ← cb_dot_uvec_right, cb_dot_eq_of_mem_edge (hw s)]
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
      exact cb_dot_vminus_le hK (cb_mem_edge hx (by rw [hxu, dot_vminus_uvec])))
    (cb_tendsto_cos_left t) (cb_tendsto_sin_left t) (cb_sin_pos_left t)
    (Eventually.of_forall fun s => (hw s).1) (Eventually.of_forall fun s => ?_)
  rw [← cb_dot_uvec_left, ← cb_dot_uvec_left, cb_dot_eq_of_mem_edge (hw s)]
  exact dot_le_supp hK hP.1 s

/-- The `v_t`-coordinate `(h(s) - h(t) cos (s - t)) / sin (s - t)` of `v_K(t, s)` tends to
`v_K⁺(t) · v_t` as `s → t⁺`. -/
private lemma cb_coef_right {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (fun s => (supp K s - supp K t * cos (s - t)) / sin (s - t)) (𝓝[>] t)
      (𝓝 (dot (vplus K t) (vvec t))) := by
  have hP := cb_vplus_mem_edge hK hne t
  have h := cb_coef_core hK (fun x => eq_dot_uvec_smul_add x t) hP.1
    (fun x hx => by rw [dot_vplus_uvec]; exact dot_le_supp hK hx t)
    (fun x hx hxu => cb_le_dot_vplus hK (cb_mem_edge hx (by rw [hxu, dot_vplus_uvec])))
    (cb_tendsto_cos_right t) (cb_tendsto_sin_right t) (cb_sin_pos_right t)
    (F := supp K) (w := vplus K)
    (Eventually.of_forall fun s => (cb_vplus_mem_edge hK hne s).1)
    (Eventually.of_forall fun s => by
      rw [← cb_dot_uvec_right, cb_dot_eq_of_mem_edge (cb_vplus_mem_edge hK hne s)])
    (Eventually.of_forall fun s => by
      rw [← cb_dot_uvec_right]; exact dot_le_supp hK hP.1 s)
  rwa [dot_vplus_uvec] at h

/-- The mirror statement: `(h(s) - h(t) cos (t - s)) / sin (t - s) → v_K⁻(t) · (-v_t)` as
`s → t⁻`. -/
private lemma cb_coef_left {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (fun s => (supp K s - supp K t * cos (t - s)) / sin (t - s)) (𝓝[<] t)
      (𝓝 (dot (vminus K t) (-vvec t))) := by
  have hP := cb_vminus_mem_edge hK hne t
  have h := cb_coef_core hK (fun x => cb_frame_left x t) hP.1
    (fun x hx => by rw [dot_vminus_uvec]; exact dot_le_supp hK hx t)
    (fun x hx hxu => by
      rw [dot_neg_right, dot_neg_right, neg_le_neg_iff]
      exact cb_dot_vminus_le hK (cb_mem_edge hx (by rw [hxu, dot_vminus_uvec])))
    (cb_tendsto_cos_left t) (cb_tendsto_sin_left t) (cb_sin_pos_left t)
    (F := supp K) (w := vminus K)
    (Eventually.of_forall fun s => (cb_vminus_mem_edge hK hne s).1)
    (Eventually.of_forall fun s => by
      rw [← cb_dot_uvec_left, cb_dot_eq_of_mem_edge (cb_vminus_mem_edge hK hne s)])
    (Eventually.of_forall fun s => by
      rw [← cb_dot_uvec_left]; exact dot_le_supp hK hP.1 s)
  rwa [dot_vminus_uvec] at h

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), right limits. For a convex body `K` and an angle
`t`, the vertices `v_K^±(s)` and the intersections `v_K(t, s)` converge to `v_K⁺(t)` as `s → t⁺`.
In particular `v_K⁺` is right-continuous. -/
theorem tendsto_vplus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vplus K) (𝓝[>] t) (𝓝 (vplus K t)) := by
  exact cb_tendsto_right hK.2.1 hK.1 t (vplus_mem_edge hK)

theorem tendsto_vminus_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[>] t) (𝓝 (vplus K t)) := by
  exact cb_tendsto_right hK.2.1 hK.1 t (vminus_mem_edge hK)

theorem tendsto_vint_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun s => vint K t s) (𝓝[>] t) (𝓝 (vplus K t)) := by
  refine cb_tendsto_of_dot (fun x => eq_dot_uvec_smul_add x t) ?_ ?_
  · rw [dot_vplus_uvec]
    refine tendsto_const_nhds.congr (fun s => ?_)
    exact (vint_mem_line_left K t s).symm
  · refine (cb_coef_right hK.2.1 hK.1 t).congr (fun s => ?_)
    simp [vint, dot_add_left, dot_smul_left]

/-- **Theorem 2.1.3** (`thm:limits-converging-to-vertex`), left limits. -/
theorem tendsto_vplus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vplus K) (𝓝[<] t) (𝓝 (vminus K t)) := by
  exact cb_tendsto_left hK.2.1 hK.1 t (vplus_mem_edge hK)

theorem tendsto_vminus_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (vminus K) (𝓝[<] t) (𝓝 (vminus K t)) := by
  exact cb_tendsto_left hK.2.1 hK.1 t (vminus_mem_edge hK)

theorem tendsto_vint_left {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    Tendsto (fun s => vint K s t) (𝓝[<] t) (𝓝 (vminus K t)) := by
  refine cb_tendsto_of_dot (fun x => cb_frame_left x t) ?_ ?_
  · rw [dot_vminus_uvec]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [cb_sin_pos_left t] with s hs
    exact (vint_mem_line_right K hs.ne').symm
  · refine (cb_coef_left hK.2.1 hK.1 t).congr' ?_
    filter_upwards [cb_sin_pos_left t] with s hs
    -- `v_K(s, t)` lies on both `l_K(s)` and `l_K(t)`, which determines its `v_t`-coordinate
    have h1 : dot (vint K s t) (uvec s) = supp K s := vint_mem_line_left K s t
    have h2 : dot (vint K s t) (uvec t) = supp K t := vint_mem_line_right K hs.ne'
    rw [cb_dot_uvec_left _ s t, h2] at h1
    rw [← h1]
    field_simp
    ring

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

private lemma cb_tendsto_sub_right (t : ℝ) : Tendsto (fun s => s - t) (𝓝[>] t) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Continuous (fun s : ℝ => s - t) := by fun_prop
    simpa using (h.tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_ne_zero.2 (ne_of_gt hs)

private lemma cb_tendsto_sub_left (t : ℝ) : Tendsto (fun s => s - t) (𝓝[<] t) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Continuous (fun s : ℝ => s - t) := by fun_prop
    simpa using (h.tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_ne_zero.2 (ne_of_lt hs)

/-- The support function has right derivative `v_K⁺(t) · v_t`. -/
theorem hasDerivWithinAt_supp_right {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivWithinAt (supp K) (dot (vplus K t) (vvec t)) (Ici t) t := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  -- slope = (sin δ / δ) · (v_t-coordinate of `v_K(t, s)`) + h(t) (cos δ - 1) / δ, `δ = s - t`
  have h1 := cb_tendsto_sin_div.comp (cb_tendsto_sub_right t)
  have h2 := cb_tendsto_cos_sub_div.comp (cb_tendsto_sub_right t)
  have h := (h1.mul (cb_coef_right hK.2.1 hK.1 t)).add (h2.const_mul (supp K t))
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
  have h1 := cb_tendsto_sin_div.comp (cb_tendsto_sub_left t)
  have h2 := cb_tendsto_cos_sub_div.comp (cb_tendsto_sub_left t)
  have h := ((h1.mul (cb_coef_left hK.2.1 hK.1 t)).neg).add (h2.const_mul (supp K t))
  rw [one_mul, mul_zero, add_zero, dot_neg_right, neg_neg] at h
  refine h.congr' ?_
  filter_upwards [cb_sin_pos_left t, self_mem_nhdsWithin] with s hs hst
  have hts : t - s ≠ 0 := sub_ne_zero.2 (ne_of_gt (mem_Iio.1 hst))
  have hs' : sin (t - s) ≠ 0 := hs.ne'
  simp only [Function.comp, slope_def_field]
  rw [show s - t = -(t - s) by ring, sin_neg, cos_neg]
  field_simp
  ring

end MovingSofa
