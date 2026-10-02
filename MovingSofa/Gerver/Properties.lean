module

public import MovingSofa.Optimality.Variation

/-!
# Gerver's sofa (§8.4)

Definitions 8.4.1 (`def:gerver-intervals`), 8.4.2–8.4.3 (the curves `𝐱, 𝐀, 𝐁, 𝐂, 𝐃`, in
`MovingSofa.Gerver.Defs`), 8.4.7 (`def:interval-j`); Theorems 8.4.1 (`thm:gerver-monotone`), 8.4.2
(`thm:gerver-odes`), 8.4.3 (`thm:gerver-left-right`), Proposition 8.4.4 (`pro:measure-translation`),
Theorems 8.4.5–8.4.6, and Theorem 6.1.2 (`thm:injectivity-gerver`).

Throughout, `P` is a solution of Romik's system in the box of `GerverParams.InBox`, `G` is
`gerverSofa P`, `K = 𝓒(G)` its cap, and `φ = P.φ`, `θ = P.θ`.

**Theorem 8.4.1.** The paper states it without proof (its Remark 8.4.1 notes that the properties are
verified numerically and assumed in the earlier literature). Part (2), that the niche is the region
enclosed by the curves `𝐁` (reversed), `𝐱|_{[t_1, t_4]}`, `𝐃` (reversed) and a segment of the `x`-axis,
is stated here as what the paper uses from it: the curves lie on the boundary of the niche, and the
area of the niche is `𝒥(𝐱|_{[t_1,t_4]}) - 𝒥(𝐁) - 𝒥(𝐃)`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

namespace GerverParams

variable (P : GerverParams)

/-- The partition `(t_0, …, t_5) = (0, φ, θ, π/2 - θ, π/2 - φ, π/2)` (Definition 8.4.1). -/
noncomputable def tPt : ℕ → ℝ
  | 0 => 0
  | 1 => P.φ
  | 2 => P.θ
  | 3 => π / 2 - P.θ
  | 4 => π / 2 - P.φ
  | _ => π / 2

/-- The cap `K = 𝓒(G)` of Gerver's sofa. -/
def cap : Set (ℝ × ℝ) := capOf (gerverSofa P) (π / 2)

/-- The contact path `𝐀` of Gerver's rotation path (Definition 8.4.3). -/
noncomputable def curveA (t : ℝ) : ℝ × ℝ := contactA P.path t
/-- The contact path `𝐁` on `[t_3, t_5]` (Definition 8.4.3). -/
noncomputable def curveB (t : ℝ) : ℝ × ℝ := contactB P.path t
/-- The contact path `𝐂` (Definition 8.4.3). -/
noncomputable def curveC (t : ℝ) : ℝ × ℝ := contactC P.path t
/-- The contact path `𝐃` on `[t_0, t_2]` (Definition 8.4.3). -/
noncomputable def curveD (t : ℝ) : ℝ × ℝ := contactD P.path t

end GerverParams

open GerverParams

/-- **Theorem 8.4.1** (`thm:gerver-monotone`): Gerver's sofa is a monotone sofa, and (1) its cap has
vertices `A_K(t) = 𝐀(t)`, `C_K(t) = 𝐂(t)` and inner corner `𝐱_K(t) = 𝐱(t)` for `t ∈ [0, π/2]`. -/
theorem theorem8_4_1_monotone {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IsMonotoneSofa (gerverSofa P) (π / 2) ∧
      ∀ t ∈ Icc 0 (π / 2), aK P.cap t = P.curveA t ∧ cK P.cap t = P.curveC t ∧
        innerCorner P.cap t = P.path t := by
  sorry

/-- **Theorem 8.4.1** (2), as used by the paper (see the module docstring): the curves `𝐁`,
`𝐱|_{[t_1, t_4]}`, `𝐃` lie on the boundary of the niche, with matching endpoints
`𝐁(t_3) = 𝐱(t_1)` and `𝐱(t_4) = 𝐃(t_2)`, `𝐃(t_0)` and `𝐁(t_5)` on the `x`-axis, and
`|𝒩(K)| = 𝒥(𝐱|_{[t_1, t_4]}) - 𝒥(𝐁|_{[t_3, t_5]}) - 𝒥(𝐃|_{[t_0, t_2]})`. -/
theorem theorem8_4_1_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 3) (P.tPt 5), P.curveB t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      (∀ t ∈ Icc (P.tPt 1) (P.tPt 4), P.path t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      (∀ t ∈ Icc (P.tPt 0) (P.tPt 2), P.curveD t ∈ closure (niche P.cap (π / 2)) \ niche P.cap (π / 2)) ∧
      P.curveB (P.tPt 3) = P.path (P.tPt 1) ∧ P.path (P.tPt 4) = P.curveD (P.tPt 2) ∧
      (P.curveD (P.tPt 0)).2 = 0 ∧ (P.curveB (P.tPt 5)).2 = 0 ∧
      area (niche P.cap (π / 2)) = curveArea P.path (P.tPt 1) (P.tPt 4) -
        curveArea P.curveB (P.tPt 3) (P.tPt 5) - curveArea P.curveD (P.tPt 0) (P.tPt 2) := by
  sorry

/-- **Theorem 8.4.1** (3): `b⃗_K(t)` passes through `𝐁(t)` for `t ∈ [t_3, t_5]`, and `d⃗_K(t)` through
`𝐃(t)` for `t ∈ [t_0, t_2]`. -/
theorem theorem8_4_1_walls {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 3) (P.tPt 5), P.curveB t ∈ wallBVec P.cap t) ∧
      ∀ t ∈ Icc (P.tPt 0) (P.tPt 2), P.curveD t ∈ wallDVec P.cap t := by
  sorry

/-- **Theorem 8.4.1** (4): `𝐁'(t)` is a negative multiple of `v_t` and `𝐃'(t)` a positive multiple of
`u_t`, on the open phases where these curves are differentiable. -/
theorem theorem8_4_1_tangents {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 3) (P.tPt 5), t ≠ P.tPt 4 →
        ∃ c < 0, HasDerivAt P.curveB (c • vvec t) t) ∧
      ∀ t ∈ Ioo (P.tPt 0) (P.tPt 2), t ≠ P.tPt 1 → ∃ c > 0, HasDerivAt P.curveD (c • uvec t) t := by
  sorry

/-- **Theorem 8.4.2** (`thm:gerver-odes`): Romik's balancing ODEs on the open phases. -/
theorem theorem8_4_2 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 0) (P.tPt 1),
        dot (deriv P.curveA t) (vvec t) = 0 ∧
        dot (-deriv P.curveC t) (uvec t) = dot (deriv P.curveD t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 1) (P.tPt 2),
        dot (deriv P.curveA t) (vvec t) = dot (deriv P.path t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = dot (deriv P.curveD t - deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 2) (P.tPt 3),
        dot (deriv P.curveA t) (vvec t) = dot (deriv P.path t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = dot (-deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 3) (P.tPt 4),
        dot (deriv P.curveA t) (vvec t) = dot (-deriv P.curveB t + deriv P.path t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = dot (-deriv P.path t) (uvec t)) ∧
      (∀ t ∈ Ioo (P.tPt 4) (P.tPt 5),
        dot (deriv P.curveA t) (vvec t) = dot (-deriv P.curveB t) (vvec t) ∧
        dot (-deriv P.curveC t) (uvec t) = 0) := by
  sorry

/-- **Theorem 6.1.2** (`thm:injectivity-gerver`). The cap of Gerver's sofa satisfies the injectivity
condition. -/
theorem theorem6_1_2 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    SatisfiesInjectivity P.cap := by
  sorry

/-- Gerver's sofa has area at least `2.2` (its area is `2.2195…`; Romik, Section 8 of the companion
package). -/
theorem gerverSofa_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    2.2 ≤ area (gerverSofa P) := by
  sorry

/-- **Theorem 8.4.3** (`thm:gerver-left-right`) (1): `𝐃(t) = v_{D_K}^±(3π/2 + t)` on `(t_0, t_2)` and
`𝐁(t) = v_{B_K}^±(π + t)` on `(t_3, t_5)`. -/
theorem theorem8_4_3_one {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Ioo (P.tPt 0) (P.tPt 2), P.curveD t = vplus (leftBody P.φ P.cap) (3 * π / 2 + t) ∧
        P.curveD t = vminus (leftBody P.φ P.cap) (3 * π / 2 + t)) ∧
      ∀ t ∈ Ioo (P.tPt 3) (P.tPt 5), P.curveB t = vplus (rightBody P.φ P.cap) (π + t) ∧
        P.curveB t = vminus (rightBody P.φ P.cap) (π + t) := by
  sorry

/-- **Theorem 8.4.3** (2): `𝐱_K^L = Y_{D_K} = 𝐃(t_2)` and `𝐝_{D_K}` is the curve `𝐃`;
`𝐱_K^R = X_{B_K} = 𝐁(t_3)` (the paper writes `𝐃(t_3)`) and `𝐛_{B_K}` is the curve `𝐁`. -/
theorem theorem8_4_3_two {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    xLeft P.φ P.cap = yD P.φ (leftBody P.φ P.cap) ∧ yD P.φ (leftBody P.φ P.cap) = P.curveD (P.tPt 2) ∧
      tailD P.φ (leftBody P.φ P.cap) = P.curveD '' Icc (P.tPt 0) (P.tPt 2) ∧
      xRight P.φ P.cap = xB P.φ (rightBody P.φ P.cap) ∧
      xB P.φ (rightBody P.φ P.cap) = P.curveB (P.tPt 3) ∧
      tailB P.φ (rightBody P.φ P.cap) = P.curveB '' Icc (P.tPt 3) (P.tPt 5) := by
  sorry

/-- **Theorem 8.4.3** (3): `h_K(π/2 + t) + h_{D_K}(3π/2 + t) = 1` on `[t_0, t_2]` and
`h_K(t) + h_{B_K}(π + t) = 1` on `[t_3, t_5]`. -/
theorem theorem8_4_3_three {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ t ∈ Icc (P.tPt 0) (P.tPt 2),
        supp P.cap (π / 2 + t) + supp (leftBody P.φ P.cap) (3 * π / 2 + t) = 1) ∧
      ∀ t ∈ Icc (P.tPt 3) (P.tPt 5), supp P.cap t + supp (rightBody P.φ P.cap) (π + t) = 1 := by
  sorry

/-- **Proposition 8.4.4** (`pro:measure-translation`): the surface area measures of `K`, `B_K`, `D_K`
in terms of the boundary curves. -/
theorem proposition8_4_4 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (sigma P.cap).restrict (Ico 0 (π / 2)) =
        (volume.restrict (Ico 0 (π / 2))).withDensity
          (fun t => ENNReal.ofReal (dot (deriv P.curveA t) (vvec t))) ∧
      (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (P.tPt 3) (P.tPt 5)) =
        (volume.restrict (Ico (P.tPt 3) (P.tPt 5))).withDensity
          (fun t => ENNReal.ofReal (dot (-deriv P.curveB t) (vvec t))) ∧
      (sigma P.cap).restrict (Ioc (π / 2) π) =
        (volume.restrict (Ioc (π / 2) π)).withDensity
          (fun t => ENNReal.ofReal (dot (-deriv P.curveC (t - π / 2)) (uvec (t - π / 2)))) ∧
      (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (P.tPt 0) (P.tPt 2)) =
        (volume.restrict (Ioc (P.tPt 0) (P.tPt 2))).withDensity
          (fun t => ENNReal.ofReal (dot (deriv P.curveD t) (uvec t))) := by
  sorry

/-- The intervals `J_i = [t_{i-1}, t_i)` for `1 ≤ i ≤ 5` and `J_i = π - J_{11 - i}` for `6 ≤ i ≤ 10`
(Definition 8.4.7, `def:interval-j`). -/
noncomputable def GerverParams.jInt (P : GerverParams) (i : ℕ) : Set ℝ :=
  if i ≤ 5 then Ico (P.tPt (i - 1)) (P.tPt i)
  else (fun s => π - s) '' Ico (P.tPt (10 - i)) (P.tPt (11 - i))

/-- **Theorem 8.4.5** (`thm:upper-bound-q-gerver`): Romik's ODEs as equalities of measures. -/
theorem theorem8_4_5 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (sigma P.cap).restrict (P.jInt 1) = 0 ∧
      (sigma P.cap).restrict (P.jInt 2 ∪ P.jInt 3) = (iota P.cap).restrict (P.jInt 2 ∪ P.jInt 3) ∧
      (sigma P.cap).restrict (P.jInt 4) =
        (sigmaBreve (rightBody P.φ P.cap)).restrict (P.jInt 4) + (iota P.cap).restrict (P.jInt 4) ∧
      (sigma P.cap).restrict (P.jInt 5) = (sigmaBreve (rightBody P.φ P.cap)).restrict (P.jInt 5) ∧
      (sigma P.cap).restrict (P.jInt 6) = (sigmaBreve (leftBody P.φ P.cap)).restrict (P.jInt 6) ∧
      (sigma P.cap).restrict (P.jInt 7) =
        (sigmaBreve (leftBody P.φ P.cap)).restrict (P.jInt 7) + (iota P.cap).restrict (P.jInt 7) ∧
      (sigma P.cap).restrict (P.jInt 8 ∪ P.jInt 9) = (iota P.cap).restrict (P.jInt 8 ∪ P.jInt 9) ∧
      (sigma P.cap).restrict (P.jInt 10) = 0 := by
  sorry

/-- **Theorem 8.4.6** (`thm:upper-bound-q-gerver-match`). `𝒜(K) = 𝒬(K, B_K, D_K)` for the cap of
Gerver's sofa. -/
theorem theorem8_4_6 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    sofaArea (π / 2) P.cap = upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) := by
  sorry

end MovingSofa
