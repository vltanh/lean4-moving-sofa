module

public import MovingSofaExtremal.Main
public import MovingSofaStability.GlobalStability

/-!
# Optimality, uniqueness and stability from one certificate

The coercive certificate (`MovingSofaStability.coercive_certificate`) bounds Baek's upper bound
`𝒬` by `|G|` on the enlarged domain of triples, and bounds the distance from the cap of a triple
to a translate of Gerver's cap by `(2 / cos φ) √(|G| - 𝒬)`. The three theorems follow from it:

* optimality, as a maximizing right-angle cap has `|G| ≤ A(K) ≤ 𝒬(ξ_K) ≤ |G|`
  (`gerver_sofa_optimal`);
* uniqueness, as such a cap has `𝒬(ξ_K) = |G|`, hence distance zero from a translate of Gerver's
  cap (`translate_eq_gerver_of_volume_eq`);
* stability, as a cap near Gerver's has `A(K) ≤ 𝒬(ξ_K) ≤ |G|` and lies within
  `(2 / cos φ) √(|G| - A(K))` of a translate of Gerver's cap, and a sofa of small deficit enters
  that neighborhood by compactness and the uniqueness above
  (`MovingSofaStability.unrestricted_stability`, `MovingSofaStability.terminal_angle_stability`).

None of these proofs uses Baek's Theorem 1.1.1, his results on balanced caps, or the modules of
the first proof of uniqueness; `scripts/AuditCoerciveRoute.lean` checks this.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

/-- **Optimality, uniqueness and stability of Gerver's sofa.** Gerver's sofa `G` is a moving sofa;
every moving sofa has area at most `|G|`; the moving sofas of area `|G|` are the translates of `G`;
a moving sofa whose area is `|G| - ε`, with `ε` small, lies after a translation within Euclidean
Hausdorff distance `C √ε` of `G`, and its symmetric difference with `G` has area at most
`C' √ε`; and if it moves with an angle `ω ∈ [arccos (5/11), π/2]`, then `π/2 - ω ≤ C'' ε`. -/
theorem gerver_sofa_optimal_unique_stable {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ v : Plane, Rigid.translate v '' S = gerverSofa P)) ∧
      MovingSofaStability.UnrestrictedStability P ∧
      MovingSofaStability.TerminalAngleStability P := by
  obtain ⟨hG, hle⟩ := gerver_sofa_optimal hP hbox
  refine ⟨hG, hle, fun S hS => ⟨translate_eq_gerver_of_volume_eq hP hbox hS, ?_⟩,
    MovingSofaStability.unrestricted_stability hP hbox,
    MovingSofaStability.terminal_angle_stability hP hbox⟩
  rintro ⟨v, hv⟩
  rw [← (Rigid.translate v).volume_image S, hv]

end MovingSofaExtremal
