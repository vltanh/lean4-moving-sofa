module

public import Mathlib
public import MovingSofaBridge.Defs

/-!
# The definitions of the certificate's Challenge

The definitions that the certificate entry (`Challenge.lean`) needs for the certificate, beyond
those of `MovingSofaBridge.Defs`: convex bodies, caps, the surface area measure, curve areas, Baek's
upper bound `𝒬`, the enlarged domain `T̄` of triples, and Gerver's cap and its horizontal
translates. Each restates, in Mathlib's vocabulary and with the constants of
`MovingSofaBridge.Defs`, the definition of the same name in `MovingSofaOptimality` or
`MovingSofaStability`, with the same body, with four exceptions. `gerverCap` is the library's
`GerverParams.cap`, `innerCorner` writes `(0, 0)` for the library's `xL`, and `upperQ` writes
`(volume K).toReal` for the library's `area K`; these three are equal to the library's by
definition. The fourth is the surface area measure `sigma`, below. `Challenge.lean` may not import
the project, so `scripts/sync_challenge_defs.py` copies the marked block into it verbatim, after the
blocks of `MovingSofaBridge.Defs`. The solution of the certificate entry (`Solution.lean`) uses the
constants defined here, so Comparator sees the same constants in the Challenge and in the Solution,
and `MovingSofaExtremal.Certificate` proves that they agree with the library's.

**The surface area measure.** `σ_K` is the Lebesgue–Stieltjes measure of
`G_K(t) = ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K` (manuscript, Definition 2.1 (c); formally `σ_K = h_K'' + h_K`).
The library's `MovingSofaOptimality.sigma` takes this measure when `K` is a convex body, with the
library's proofs that `G_K` is then monotone and right-continuous, and Lebesgue measure otherwise. A
Challenge cannot contain the library's proofs, so `sigma` takes it when `G_K` is monotone and
right-continuous, and Lebesgue measure otherwise. The two agree on convex bodies
(`Certificate.sigma_eq_lib`), but can differ on other sets: on `∅`, `G_K = 0` and `sigma` is the
zero measure, while the library's is Lebesgue measure; on a set of two points, `sigma` has atoms.
The certificate's statements apply `sigma` only to the tails `B` and `D` of a triple, which
`InWideL` makes convex bodies.

Before the block, a command gives Lean's cache of auxiliary theorems the state it has in the
Challenge after the definitions of `MovingSofaBridge.Defs`, so that the block elaborates to the
same terms here as there.
-/

@[expose] public section

/- Lean turns the proofs inside a definition, such as the proof of `Nat.AtLeastTwo 2` behind the
numeral `2 : ℝ`, into auxiliary theorems, and reuses an auxiliary theorem with the same statement
made earlier in the same module; `.olean` files do not store this cache. In
`Challenge.lean`, the definitions of `MovingSofaBridge.Defs` (all of its blocks) precede the
certificate's in one module, so the certificate's definitions reuse their auxiliary theorems, such
as `Baek.GerverParams.x₁._proof_1` for `2` and
`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec._proof_1` for `3`. This command puts the
auxiliary theorems of `MovingSofaBridge.Defs`, which all come from those definitions, into the
cache, so
that the definitions below elaborate to the same terms as in the Challenge, which Comparator
requires. `scripts/sync_challenge_defs.py` checks that the Challenge keeps this order. -/
open Lean Meta in
run_meta do
  let env ← getEnv
  let some idx := env.getModuleIdx? `MovingSofaBridge.Defs
    | throwError "MovingSofaBridge.Defs is not imported"
  for n in env.header.moduleData[idx.toNat]!.constNames do
    if n.components.any (·.toString.startsWith "_proof") then
      let ci ← getConstInfo n
      modifyEnv fun env => auxLemmasExt.modifyState env fun s =>
        { s with lemmas := s.lemmas.insert ⟨ci.type, false, false⟩ (n, ci.levelParams) }

-- BEGIN CERTIFICATE DEFINITIONS
open Real Set MeasureTheory

noncomputable section

namespace Certificate

open Baek

/-! ### Convex bodies -/

/-- The line `l(t, h) = {p : ⟨p, u_t⟩ = h}` with normal angle `t` (Baek, Definition 2.1.4). -/
def line (t h : ℝ) : Set (ℝ × ℝ) := {p | dot p (uvec t) = h}

/-- The closed half-plane `H₋(t, h) = {p : ⟨p, u_t⟩ ≤ h}` (Baek, Definition 2.1.5). -/
def halfMinus (t h : ℝ) : Set (ℝ × ℝ) := {p | dot p (uvec t) ≤ h}

/-- A convex body: a nonempty, compact and convex subset of the plane (Baek, Definition 2.1.1). -/
def IsConvexBody (K : Set (ℝ × ℝ)) : Prop := K.Nonempty ∧ IsCompact K ∧ Convex ℝ K

/-- The support function `h_S(t) = sup {⟨p, u_t⟩ : p ∈ S}` (Baek, Definition 2.1.6). -/
def supp (S : Set (ℝ × ℝ)) (t : ℝ) : ℝ := sSup ((fun p => dot p (uvec t)) '' S)

/-- The supporting line `l_S(t) = l(t, h_S(t))` (Baek, Definition 2.1.7). -/
def suppLine (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := line t (supp S t)

/-- The edge `e_K(t) = K ∩ l_K(t)` (Baek, Definition 2.1.9). -/
def edge (K : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := K ∩ suppLine K t

/-- The vertex `v_K⁺(t) = h_K(t) u_t + (sup {⟨p, v_t⟩ : p ∈ e_K(t)}) v_t`, the end of `e_K(t)`
farthest in the direction `v_t` (Baek, Definition 2.1.10). -/
def vplus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ :=
  supp K t • uvec t + sSup ((fun p => dot p (vvec t)) '' edge K t) • vvec t

/-- The vertex `v_K⁻(t) = h_K(t) u_t + (inf {⟨p, v_t⟩ : p ∈ e_K(t)}) v_t`, the end of `e_K(t)`
farthest in the direction `-v_t` (Baek, Definition 2.1.10). -/
def vminus (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ :=
  supp K t • uvec t + sInf ((fun p => dot p (vvec t)) '' edge K t) • vvec t

/-- The distribution function `G_K(t) = ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K` of the surface area measure
(manuscript, Definition 2.1). -/
def sigmaFun (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  dot (vplus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s

open Classical in
/-- The surface area measure `σ_K` (Baek, Definition 2.1.13; manuscript, Definition 2.1 (c)): the
Lebesgue–Stieltjes measure of `G_K`, formally `σ_K = h_K'' + h_K`, when `G_K` is monotone and
right-continuous, and Lebesgue measure otherwise. The library's `MovingSofaOptimality.sigma` tests
instead whether `K` is a convex body. The two agree on convex bodies, where `G_K` has both
properties, but can differ on other sets, such as `∅` (where `sigma` is zero) or a set of two
points. The statements apply `sigma` only to the tails `B` and `D` of a triple, which `InWideL`
makes convex bodies. -/
def sigma (K : Set (ℝ × ℝ)) : Measure ℝ :=
  if h : Monotone (sigmaFun K) ∧ ∀ x, ContinuousWithinAt (sigmaFun K) (Ici x) x then
    ({ toFun := sigmaFun K, mono' := h.1, right_continuous' := h.2 } : StieltjesFunction ℝ).measure
  else StieltjesFunction.id.measure

/-! ### Caps -/

/-- `K` is an intersection of closed half-planes `H₋(t, c)` with normal angles `t ∈ A`, as in Baek's
Definition 2.4.1. -/
def IsHalfPlaneInter (K : Set (ℝ × ℝ)) (A : Set ℝ) : Prop :=
  ∃ (ι : Type) (t c : ι → ℝ), (∀ i, t i ∈ A) ∧ K = ⋂ i, halfMinus (t i) (c i)

/-- The set `J_ω = [0, ω] ∪ [π/2, ω + π/2]` (Baek, Definition 2.3.11). -/
def jSet (ω : ℝ) : Set ℝ := Icc 0 ω ∪ Icc (π / 2) (ω + π / 2)

/-- A cap with rotation angle `ω ∈ (0, π/2]` (Baek, Definition 2.4.1): a convex body `K` with
`h_K(ω) = h_K(π/2) = 1` and `h_K(ω + π) = h_K(3π/2) = 0` that is an intersection of closed
half-planes with normal angles in `J_ω ∪ {ω + π, 3π/2}`. -/
def IsCap (K : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ω ∈ Ioc 0 (π / 2) ∧ IsConvexBody K ∧ supp K ω = 1 ∧ supp K (π / 2) = 1 ∧
    supp K (ω + π) = 0 ∧ supp K (3 * π / 2) = 0 ∧
    IsHalfPlaneInter K (jSet ω ∪ {ω + π, 3 * π / 2})

/-- The horizontal strip `H = ℝ × [0, 1]` (Baek, Definition 2.3.2). -/
def hStrip : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The vertical strip `V = [0, 1] × ℝ` (Baek, Definition 2.3.2). -/
def vStrip : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1}

/-- The rotated strip `V_ω = R_ω(V) = {p : 0 ≤ ⟨p, u_ω⟩ ≤ 1}` (Baek, Definition 2.3.2). -/
def vStripRot (ω : ℝ) : Set (ℝ × ℝ) := rot ω '' vStrip

/-- The parallelogram `P_ω = H ∩ V_ω` (Baek, Definition 2.3.5). -/
def para (ω : ℝ) : Set (ℝ × ℝ) := hStrip ∩ vStripRot ω

/-- The rigid motion `f_{S,t}(p) = R_t p + (h_S(t) - 1) u_t + (h_S(t + π/2) - 1) v_t`, which maps
the hallway onto the supporting hallway `L_S(t)` (Baek, Definition 2.2.2). -/
def hallwayMap (S : Set (ℝ × ℝ)) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  rot t p + (supp S t - 1) • uvec t + (supp S (t + π / 2) - 1) • vvec t

/-- The closed quarter-plane `Q_L⁺ = (-∞, 1]²` (Baek, Definition 2.2.1). -/
def qPlusL : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- The closed quarter-plane `Q_S⁺(t) = f_{S,t}(Q_L⁺)` (Baek, Definition 2.2.3), which is
`H_S(t) ∩ H_S(t + π/2)` (Baek, Proposition 2.2.2). -/
def qPlus (S : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := hallwayMap S t '' qPlusL

/-- The cap `𝒞(S) = P_ω ∩ ⋂_{t ∈ [0, ω]} Q_S⁺(t)` of `S` (Baek, Definition 2.3.10). -/
def capOf (S : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) := para ω ∩ ⋂ t ∈ Icc 0 ω, qPlus S t

/-- The inner corner `𝐱_S(t) = f_{S,t}(O) = (h_S(t) - 1) u_t + (h_S(t + π/2) - 1) v_t` of the
supporting hallway (Baek, Definition 2.2.3). -/
def innerCorner (S : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := hallwayMap S t (0, 0)

/-! ### Curve areas -/

/-- `½ ∫_{(a,b)} h_K dσ_K`: for a convex body `K` and `a < b < a + π`, the curve area of the arc of
the boundary of `K` from `v_K⁺(a)` to `v_K⁻(b)` (Baek, Theorem 7.3.2). -/
def convexCurveArea (K : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in Ioo a b, supp K t ∂(sigma K)

/-- The function `f` restricted to `[a, b]` and extended by constants outside (for Baek's
Definition 5.1.3). -/
def clampFun {α : Type*} (f : ℝ → α) (a b : ℝ) (t : ℝ) : α := f (max a (min b t))

open Classical in
/-- The Lebesgue–Stieltjes measure `df` of `f` on `[a, b]` (Baek, Definition 5.1.3): the vector
measure of the clamped function if it has bounded variation (otherwise `0`). Baek's definition
assumes `f` right-continuous; Mathlib's construction uses the right limits of `f`, which are its
values when `f` is right-continuous. The statements use it only for the inner corner `𝐱_K` of a
cap, a continuous curve. -/
def lsMeasure {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : ℝ → E) (a b : ℝ) :
    VectorMeasure ℝ E :=
  if h : BoundedVariationOn (clampFun f a b) univ then h.vectorMeasure else 0

/-- The cross product `p × q = p₁ q₂ - p₂ q₁` (Baek, Definition 7.2.4). -/
def cross (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

/-- The cross product as a continuous bilinear map, the pairing in `∫ p × dμ` (for Baek's
Definition 7.2.6). -/
def crossCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => LinearMap.toContinuousLinearMap
        { toFun := fun q => cross p q
          map_add' := fun q r => by simp only [cross, Prod.fst_add, Prod.snd_add]; ring
          map_smul' := fun a q => by
            simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun p r => ContinuousLinearMap.ext fun q => by
        simp only [cross, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          add_apply, Prod.fst_add, Prod.snd_add]; ring
      map_smul' := fun a p => ContinuousLinearMap.ext fun q => by
        simp only [cross, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          RingHom.id_apply]; ring }

/-- The bilinear form `½ ∫_a^b x₁(t) × dx₂(t)` of the proof of Baek's Proposition 7.2.2, whose
diagonal is the curve area. -/
def curveBilin (x₁ x₂ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ᵛ t in Icc a b, x₁ t ∂[crossCLM; lsMeasure x₂ a b]

/-- The curve area `𝒥(𝐱) = ½ ∫_a^b 𝐱(t) × d𝐱(t)` of a curve `𝐱` on `[a, b]` (Baek, Definition
7.2.6). -/
def curveArea (x : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ := curveBilin x x a b

/-- The curve area `𝒥([p, q]) = (p × q)/2` of the segment from `p` to `q` (Baek, Definition
7.2.8). -/
def segArea (p q : ℝ × ℝ) : ℝ := cross p q / 2

/-! ### Baek's upper bound on the enlarged domain -/

/-- The point `X_B = v_B⁺(π + φ^R)`, where `φ^R = φ` (Baek, Definition 8.2.1). -/
def xB (φ : ℝ) (B : Set (ℝ × ℝ)) : ℝ × ℝ := vplus B (π + φ)

/-- The point `Y_D = v_D⁻(3π/2 + φ^L)`, where `φ^L = π/2 - φ` (Baek, Definition 8.2.1). -/
def yD (φ : ℝ) (D : Set (ℝ × ℝ)) : ℝ × ℝ := vminus D (3 * π / 2 + (π / 2 - φ))

/-- The inner corner `𝐱_K^R = 𝐱_K(φ^R)` (Baek, Definition 8.1.5). -/
def xRight (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ × ℝ := innerCorner K φ

/-- The inner corner `𝐱_K^L = 𝐱_K(φ^L)` (Baek, Definition 8.1.5). -/
def xLeft (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ × ℝ := innerCorner K (π / 2 - φ)

/-- Baek's upper bound (Baek, Definition 8.2.2; manuscript, Equation (10.1))
`𝒬(K, B, D) = |K| + ½ ∫_{(3π/2, 3π/2 + φ^L)} h_D dσ_D + 𝒥([Y_D, 𝐱_K(φ^L)]) - 𝒥(𝐱_K|_{[φ^R, φ^L]})
+ 𝒥([𝐱_K(φ^R), X_B]) + ½ ∫_{(π + φ^R, 3π/2)} h_B dσ_B`. -/
def upperQ (φ : ℝ) (K B D : Set (ℝ × ℝ)) : ℝ :=
  (volume K).toReal + convexCurveArea D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) +
    segArea (yD φ D) (xLeft φ K) - curveArea (innerCorner K) φ (π / 2 - φ) +
    segArea (xRight φ K) (xB φ B) + convexCurveArea B (π + φ) (3 * π / 2)

/-- The enlarged domain `T̄` (manuscript, Section 10): Baek's triples `(K, B, D)` (Baek, Definition
8.1.3), with `K` a cap with rotation angle `π/2` in place of `K ∈ 𝒦ⁱ`. `B` and `D` are convex bodies
in `K`, `h_K(t) + h_B(π + t) ≤ 1` on `[φ^R, π/2]` and `h_K(π/2 + t) + h_D(3π/2 + t) ≤ 1` on
`[0, φ^L]`, with equality at the ends. -/
def InWideL (φ : ℝ) (K B D : Set (ℝ × ℝ)) : Prop :=
  IsCap K (π / 2) ∧ IsConvexBody B ∧ IsConvexBody D ∧ B ⊆ K ∧ D ⊆ K ∧
    (∀ t ∈ Icc φ (π / 2), supp K t + supp B (π + t) ≤ 1) ∧
    supp K φ + supp B (π + φ) = 1 ∧ supp K (π / 2) + supp B (π + π / 2) = 1 ∧
    (∀ t ∈ Icc 0 (π / 2 - φ), supp K (π / 2 + t) + supp D (3 * π / 2 + t) ≤ 1) ∧
    supp K (π / 2 + 0) + supp D (3 * π / 2 + 0) = 1 ∧
    supp K (π / 2 + (π / 2 - φ)) + supp D (3 * π / 2 + (π / 2 - φ)) = 1

/-! ### Gerver's cap -/

/-- Gerver's cap `K_G = 𝒞(G)`, the cap of Gerver's sofa `G` with rotation angle `π/2` (manuscript,
Fact 2.35). -/
def gerverCap (P : GerverParams) : Set (ℝ × ℝ) := capOf (gerverSofa P) (π / 2)

/-- The horizontal translation `(h_{K₀}(π) - h_{K₁}(π), 0)`, which gives `K₀` the leftmost abscissa
of `K₁`; for `K₀ = K_G` and `K₁ = K` it is `(s_K, 0)` (manuscript, Section 10). -/
def capReferenceShift (K₀ K₁ : Set (ℝ × ℝ)) : ℝ × ℝ := (-(supp K₁ π - supp K₀ π), 0)

/-- The translate of `K₀` with the leftmost abscissa of `K₁`; for `K₀ = K_G` and `K₁ = K` it is
`K_G + (s_K, 0)`. -/
def shiftedReferenceCap (K₀ K₁ : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (fun p => p + capReferenceShift K₀ K₁) '' K₀

end Certificate

end
-- END CERTIFICATE DEFINITIONS
