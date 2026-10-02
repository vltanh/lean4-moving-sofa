module

public import MovingSofa.Balanced.MaximumPolygonCap
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Balanced maximum sofas (§3.5)

Definitions 3.5.1–3.5.3, Proposition 3.5.1, Theorem 3.5.2 (`thm:balanced-maximum-cap`), Lemma 3.5.3
(`lem:hausdorff-distance-containment`), Theorems 3.5.4–3.5.6.
-/

@[expose] public section

open Real Set Filter Topology

namespace MovingSofa

/-- The uniform angle set `Θ_{ω,n} = {iω/n : 1 ≤ i < n}` with `n ≥ 2` intervals
(Definition 3.5.1, `def:uniform-angle-set`). -/
noncomputable def uniformAngleSet (ω : ℝ) (hω : ω ∈ Ioc 0 (π / 2)) (n : ℕ) (hn : 2 ≤ n) :
    AngleSet where
  ω := ω
  angles := (Finset.Ioo 0 n).image (fun i : ℕ => (i : ℝ) * ω / n)
  hω := hω
  nonempty := ⟨((1 : ℕ) : ℝ) * ω / n, Finset.mem_image.2 ⟨1, by simp; omega, rfl⟩⟩
  subset := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_Ioo] at ht
    obtain ⟨i, ⟨hi0, hin⟩, rfl⟩ := ht
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hi : (0 : ℝ) < i := by exact_mod_cast hi0
    have hin' : (i : ℝ) < n := by exact_mod_cast hin
    constructor
    · exact div_pos (mul_pos hi hω.1) hn'
    · rw [div_lt_iff₀ hn']; nlinarith [hω.1]

/-- The uniform angle set `Θ_{ω,n}` with `n = 2^(k+1)` intervals, a power of two larger than one. -/
noncomputable def dyadicAngleSet (ω : ℝ) (hω : ω ∈ Ioc 0 (π / 2)) (k : ℕ) : AngleSet :=
  uniformAngleSet ω hω (2 ^ (k + 1)) (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))

/-- A balanced maximum cap with rotation angle `ω` (Definition 3.5.2, `def:balanced-maximum-cap`): a
cap `K_ω` which is the Hausdorff limit of maximum polygon caps `K_i` with uniform angle sets
`Θ_{ω, n_i}`, where `1 < n_1 < n_2 < ⋯` are powers of two (here `n_i = 2^(k_i + 1)`). -/
def IsBalancedMaxCap (K : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ∃ hω : ω ∈ Ioc 0 (π / 2), IsCap K ω ∧
    ∃ (k : ℕ → ℕ) (Ks : ℕ → Set (ℝ × ℝ)), StrictMono k ∧
      (∀ i, IsMaxPolygonCap (dyadicAngleSet ω hω (k i)) (Ks i)) ∧ HausdorffTendsto Ks K

/-- **Proposition 3.5.1** (`pro:balanced-maximum-cap-mirror`). The mirror reflection of a balanced
maximum cap is a balanced maximum cap. -/
theorem proposition3_5_1 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) :
    IsBalancedMaxCap (mirrorCap K ω) ω := by
  sorry

/-- **Theorem 3.5.2** (`thm:balanced-maximum-cap`). A balanced maximum cap exists for every
`ω ∈ (0, π/2]`. -/
theorem theorem3_5_2 {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) : ∃ K, IsBalancedMaxCap K ω := by
  sorry

/-- **Lemma 3.5.3** (`lem:hausdorff-distance-containment`). Hausdorff limits of nested bounded sets
are nested, when the limit of the larger sets is compact. -/
theorem lemma3_5_3 {X Y : Set (ℝ × ℝ)} {Xs Ys : ℕ → Set (ℝ × ℝ)}
    (hX : Bornology.IsBounded X) (hXne : X.Nonempty) (hYc : IsCompact Y) (hYne : Y.Nonempty)
    (hXs : ∀ i, Bornology.IsBounded (Xs i) ∧ (Xs i).Nonempty)
    (hYs : ∀ i, Bornology.IsBounded (Ys i) ∧ (Ys i).Nonempty)
    (hXlim : Tendsto (fun i => Metric.hausdorffDist (Xs i) X) atTop (𝓝 0))
    (hYlim : Tendsto (fun i => Metric.hausdorffDist (Ys i) Y) atTop (𝓝 0))
    (hsub : ∀ i, Xs i ⊆ Ys i) : X ⊆ Y := by
  sorry

/-- **Theorem 3.5.4** (`thm:limiting-maximum-cap-connected`). A balanced maximum cap contains its
niche. -/
theorem theorem3_5_4 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) : niche K ω ⊆ K := by
  sorry

/-- **Theorem 3.5.5** (`thm:limiting-maximum-cap-max`). A balanced maximum cap maximizes the sofa area
functional `𝒜_ω` over all caps with rotation angle `ω`. -/
theorem theorem3_5_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) :
    ∀ K', IsCap K' ω → sofaArea ω K' ≤ sofaArea ω K := by
  sorry

/-- A balanced maximum sofa: a monotone sofa whose cap is a balanced maximum cap
(Definition 3.5.3, `def:balanced-maximum-sofa`). -/
def IsBalancedMaxSofa (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  IsMonotoneSofa S ω ∧ IsBalancedMaxCap (capOf S ω) ω

/-- **Theorem 3.5.6** (`thm:limiting-maximum-sofa`). A balanced maximum sofa `S_ω = K_ω \ 𝒩(K_ω)`
exists, and it has the maximum area among the moving sofas with rotation angle `ω ∈ (0, π/2]`. -/
theorem theorem3_5_6 {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    ∃ K, IsBalancedMaxCap K ω ∧ IsBalancedMaxSofa (K \ niche K ω) ω ∧
      capOf (K \ niche K ω) ω = K ∧
      ∀ S, IsMovingSofaWithAngle S ω → area S ≤ area (K \ niche K ω) := by
  sorry

end MovingSofa
