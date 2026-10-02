module

public import MovingSofa.Sofa.Defs

/-!
# Caps and niches: definitions (§2.4, §2.5)

Definitions 2.4.1 (`def:cap`), 2.4.2 (`def:cap-space`), 2.4.4 (`def:fan`), 2.4.5 (`def:niche`),
2.5.1–2.5.6 (vertices, upper boundary, wedges, wedge endpoints and gaps, mirror reflection), and
2.5.8 (`def:sofa-area-functional`).
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- `K` is an intersection of closed half-planes whose normal angles lie in `A`. -/
def IsHalfPlaneInter (K : Set (ℝ × ℝ)) (A : Set ℝ) : Prop :=
  ∃ (ι : Type) (t c : ι → ℝ), (∀ i, t i ∈ A) ∧ K = ⋂ i, halfMinus (t i) (c i)

/-- A cap with rotation angle `ω ∈ (0, π/2]` (Definition 2.4.1, `def:cap`): a convex body `K` with
`h_K(ω) = h_K(π/2) = 1`, `h_K(ω + π) = h_K(3π/2) = 0`, which is an intersection of closed half-planes
with normal angles in `J_ω ∪ {ω + π, 3π/2}`. -/
def IsCap (K : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ω ∈ Ioc 0 (π / 2) ∧ IsConvexBody K ∧ supp K ω = 1 ∧ supp K (π / 2) = 1 ∧
    supp K (ω + π) = 0 ∧ supp K (3 * π / 2) = 0 ∧
    IsHalfPlaneInter K (jSet ω ∪ {ω + π, 3 * π / 2})

/-- The space of caps `𝒦_ω^c` with rotation angle `ω` (Definition 2.4.2, `def:cap-space`). -/
def capSpace (ω : ℝ) : Set (Set (ℝ × ℝ)) := {K | IsCap K ω}

/-- The fan `F_ω = H₊(ω, 0) ∩ H₊(π/2, 0)` (Definition 2.4.4, `def:fan`). -/
def fan (ω : ℝ) : Set (ℝ × ℝ) := halfPlus ω 0 ∩ halfPlus (π / 2) 0

/-- The niche `𝒩(K) = F_ω ∩ ⋃_{t ∈ (0, ω)} Q_K⁻(t)` of a cap (Definition 2.4.5, `def:niche`). -/
def niche (K : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) := fan ω ∩ ⋃ t ∈ Ioo 0 ω, qMinus K t

/-- The vertex `A_K⁺(t) = v_K⁺(t)` (Definition 2.5.1, `def:cap-vertices`). -/
noncomputable def aPlus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := vplus K t
/-- The vertex `A_K⁻(t) = v_K⁻(t)`. -/
noncomputable def aMinus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := vminus K t
/-- The vertex `C_K⁺(t) = v_K⁺(t + π/2)`. -/
noncomputable def cPlus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := vplus K (t + π / 2)
/-- The vertex `C_K⁻(t) = v_K⁻(t + π/2)`. -/
noncomputable def cMinus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := vminus K (t + π / 2)

/-- The upper boundary `δK = ⋃_{t ∈ [0, ω + π/2]} e_K(t)` of a cap
(Definition 2.5.2, `def:upper-boundary-of-cap`). -/
def upperBoundary (K : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) := ⋃ t ∈ Icc 0 (ω + π / 2), edge K t

/-- The wedge `T_K(t) = F_ω ∩ Q_K⁻(t)` (Definition 2.5.3, `def:wedge`). -/
def wedge (K : Set (ℝ × ℝ)) (ω t : ℝ) : Set (ℝ × ℝ) := fan ω ∩ qMinus K t

/-- `W_K(t)`, the intersection of the lines `b_K(t)` and `l(π/2, 0)` (Definition 2.5.4,
`def:wedge-endpoints`), by its explicit formula. -/
noncomputable def wedgeW (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := ((supp K t - 1) / cos t, 0)

/-- `Z_K(t)`, the intersection of the lines `d_K(t)` and `l(ω, 0)` (Definition 2.5.4), by its
explicit formula. -/
noncomputable def wedgeZ (K : Set (ℝ × ℝ)) (ω t : ℝ) : ℝ × ℝ :=
  ((supp K (t + π / 2) - 1) / cos (ω - t)) • vvec ω

/-- The right wedge gap `w_K(t) = (A_K⁻(0) - W_K(t)) · u_0` (Definition 2.5.5,
`def:wedge-side-lengths`). -/
noncomputable def wedgeGapW (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (aMinus K 0 - wedgeW K t) (uvec 0)

/-- The left wedge gap `z_K(t) = (C_K⁺(ω) - Z_K(t)) · v_ω` (Definition 2.5.5). -/
noncomputable def wedgeGapZ (K : Set (ℝ × ℝ)) (ω t : ℝ) : ℝ :=
  dot (cPlus K ω - wedgeZ K ω t) (vvec ω)

/-- The reflection `M_ω` across the line through `O` and `o_ω` (Definition 2.5.6,
`def:mirror-reflection`). That line has angle `π/4 + ω/2`. -/
noncomputable def mirror (ω : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cos (π / 2 + ω) * p.1 + sin (π / 2 + ω) * p.2, sin (π / 2 + ω) * p.1 - cos (π / 2 + ω) * p.2)

/-- The mirror reflection `K^m = M_ω(K)` of a cap (Definition 2.5.6). -/
def mirrorCap (K : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) := mirror ω '' K

/-- The sofa area functional `𝒜_ω(K) = |K| - |𝒩(K)|` (Definition 2.5.8, `def:sofa-area-functional`). -/
noncomputable def sofaArea (ω : ℝ) (K : Set (ℝ × ℝ)) : ℝ := area K - area (niche K ω)

end MovingSofa
