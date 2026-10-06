module

public import MovingSofaUniqueness.Rigidity
public import MovingSofaUniqueness.Maximizing

/-!
# A second proof of optimality, from Baek's bound

The second proof of Baek's optimality theorem of the manuscript `docs/paper` (`rem:second`), and
the uniqueness theorem from it, without Baek's Theorem 1.1.1. A maximizing right-angle cap `K`
satisfies the injectivity condition and `|G| ≤ 𝒜(K) ≤ 𝒬(K, B_K, D_K) ≤ 𝒬(K_G, B_G, D_G) = |G|`, by
Baek's bound for `𝒬` (`right_angle_maximizer_value`); the equality analysis of
`MovingSofaUniqueness.Rigidity` then makes `K` a horizontal translate of Gerver's cap
(`right_angle_maximizer_eq_gerver`). The assembly of `MovingSofaUniqueness.Maximizing` turns these
two facts into optimality (`gerver_sofa_optimal`) and uniqueness (`image_eq_gerver_of_volume_eq`).

The declarations are in the namespace `MovingSofaUniqueness.MaximizerRoute`. The module does not
import `MovingSofaUniqueness.Main`, whose results use Baek's theorem; it imports Baek's
`MovingSofaOptimality.Main` (through `Rigidity`) for Corollary 8.5.8, which that module shares with
Theorem 1.1.1. `scripts/AuditMaximizerRoute.lean` checks that this proof does not use Theorem 1.1.1.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- `rem:second` of the manuscript `docs/paper`: a maximizing right-angle cap has the sofa area
of Gerver's sofa, as `|G| ≤ 𝒜(K) ≤ 𝒬(K, B_K, D_K) ≤ 𝒬(K_G, B_G, D_G) = |G|` (Baek's Theorems
8.2.4, 8.1.8 and 8.4.6 and Corollary 8.5.8). -/
theorem right_angle_maximizer_value {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MaximizingValue P := by
  intro K hK hmax
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hKi := isKi_of_maximizes hP hbox hK hmax
  have hbound := theorem8_2_4 hbox.1 hKi
  have hQ := corollary8_5_8 hP hbox (theorem8_1_8 hbox.1 hKi)
  have hGQ := theorem8_4_6 hP hbox
  have hGA := GerverParams.gm_sofaArea_cap hP hbox
  linarith

/-- `rem:second` of the manuscript `docs/paper`, by the equality analysis: a maximizing right-angle
cap is a horizontal translate `K_G + (a, 0)` of Gerver's cap, and its sofa is `G + (a, 0)`, by
`prop:kernel` and `lem:translate` of the manuscript. -/
theorem right_angle_maximizer_eq_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) : MaximizingShape P := by
  intro K hK hmax
  have hKi := isKi_of_maximizes hP hbox hK hmax
  have hvalue := right_angle_maximizer_value hP hbox K hK hmax
  have hmid := ki_maximizer_equality_conditions hP hbox hKi hvalue (1 / 2)
    (by constructor <;> norm_num)
  have hker := capKernel_of_triple_midpoint (GerverParams.gm_φ_mem_Ioo hP hbox)
    (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hKi) hmid
  change CapKernel P.φ (fun t => supp K t - supp P.cap t) at hker
  let a := -(supp K π - supp P.cap π)
  have hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp P.cap t = a * cos t :=
    hker.eq_horizontal_translation (GerverParams.gm_φ_mem_Ioo hP hbox)
  have hGcap := GerverParams.gm_isCap hP hbox
  refine ⟨a, cap_eq_translate_of_upper_support hK hGcap a hsupp, ?_⟩
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  rw [hGset]
  exact sofa_eq_translate_of_upper_support hK hGcap a hsupp

/-- `thm:unified-optimality` (c) of the manuscript `docs/paper`, by the second proof: every cap of
every rotation angle has sofa area at most `|G|`. -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {C : Set Plane} {ω : ℝ} (hC : IsCap C ω) : sofaArea ω C ≤ area (gerverSofa P) :=
  Maximizing.cap_area_le_gerver hP hbox (right_angle_maximizer_value hP hbox) hC

/-- `thm:unified-optimality` (a) of the manuscript `docs/paper`, by the second proof: the
maximizing right-angle caps are the horizontal translates of Gerver's cap. -/
theorem right_angle_maximizes_iff_translate_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    MaximizesCap (π / 2) K ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap :=
  Maximizing.right_angle_maximizes_iff_translate_gerver hP hbox
    (right_angle_maximizer_value hP hbox) (right_angle_maximizer_eq_gerver hP hbox) hK

/-- `thm:unified-optimality` (a) of the manuscript `docs/paper`, by the second proof: a right-angle
cap has sofa area `|G|` if and only if it is a horizontal translate of Gerver's cap. -/
theorem right_angle_sofaArea_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    sofaArea (π / 2) K = area (gerverSofa P) ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap :=
  Maximizing.right_angle_sofaArea_eq_gerver_iff hP hbox
    (right_angle_maximizer_value hP hbox) (right_angle_maximizer_eq_gerver hP hbox) hK

/-- **The second proof of optimality** (`rem:second` of the manuscript `docs/paper`): Gerver's
sofa is a moving sofa, and every moving sofa has area at most that of Gerver's sofa. This is the
statement of Baek's Theorem 1.1.1, proved without it. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  Maximizing.gerver_sofa_optimal hP hbox (right_angle_maximizer_value hP hbox)

/-- **The uniqueness of Gerver's sofa** (`thm:main` of the manuscript `docs/paper`), from the
second proof of optimality. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S)
    (heq : volume S = volume (gerverSofa P)) : ∃ g : Rigid, g '' S = gerverSofa P :=
  Maximizing.image_eq_gerver_of_volume_eq hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS heq

/-- A moving sofa has the area of Gerver's sofa if and only if a rigid map takes it onto Gerver's
sofa, from the second proof. -/
theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P :=
  Maximizing.volume_eq_gerver_iff hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS

/-- Gerver's sofa is a moving sofa, every moving sofa has area at most that of Gerver's sofa, and
equality holds exactly for the rigid images of Gerver's sofa: `thm:main` of the manuscript
`docs/paper`, from the second proof (`rem:second`). -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) :=
  Maximizing.gerver_sofa_optimal_and_unique hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox)

/-- `cor:all` of the manuscript `docs/paper`, from the second proof: a moving sofa has maximal
area if and only if a rigid map takes it onto Gerver's sofa. -/
theorem isMaximal_iff_image_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    (∀ S', MovingSofaOptimality.IsMovingSofa S' → volume S' ≤ volume S) ↔
      ∃ g : Rigid, g '' S = gerverSofa P :=
  Maximizing.isMaximal_iff_image_eq_gerver hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS

end MovingSofaUniqueness.MaximizerRoute
