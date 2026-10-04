module

public import MovingSofaOptimality.Balanced.MaximumPolygonCap
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Group.Measure

/-!
# Balanced maximum sofas (§3.5)

Definitions 3.5.1–3.5.3, Proposition 3.5.1, Theorem 3.5.2 (`thm:balanced-maximum-cap`), Lemma 3.5.3
(`lem:hausdorff-distance-containment`), Theorems 3.5.4–3.5.6.

**Proofs.** Theorem 3.5.2 uses the Blaschke selection theorem (`mpc_blaschke`, proved in
`MaxPolygonCapExists` for Theorem 3.4.3); the limit is a cap because the support functions of the
approximating polygon caps are "linear" on the gaps of `J_ω ∪ {ω + π, 3π/2}` (`mpc_gap_limit`).
Theorem 3.5.4 applies Lemma 3.5.3 pointwise, as E8 repairs the paper's step: a point of the niche
lies in the open quarter-planes `Q_K⁻(t)` for a dyadic `t`, hence in the polygon niches of the
approximating caps for all large `i` (`mpc_niche_eventually`); the caps converge also in Mathlib's
`Metric.hausdorffDist`, used by Lemma 3.5.3 (`mpc_tendsto_metric_hausdorffDist`, by one direction of
Schneider's Lemma 1.8.14). Theorem 3.5.5 follows the paper's double limit: `|K_i| → |K|`
(`mpc_tendsto_area`), `|𝒩_{Θ_m}(K_i)| → |𝒩_{Θ_m}(K)|` as `i → ∞` (`mpc_tendsto_area_polyNiche`), and
`|𝒩_{Θ_m}(K)| → |𝒩(K)|` as `m → ∞`.
-/

@[expose] public section

open Real Set Filter Topology

namespace MovingSofaOptimality

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

/-! ### Dyadic angle sets -/

/-- The dyadic angles are the `iω/2^(k+1)`, `0 < i < 2^(k+1)`. -/
lemma mpc_mem_dyadic {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (k : ℕ) (s : ℝ) :
    s ∈ (dyadicAngleSet ω hω k).angles ↔
      ∃ i : ℕ, 0 < i ∧ i < 2 ^ (k + 1) ∧ s = i * ω / 2 ^ (k + 1) := by
  simp only [dyadicAngleSet, uniformAngleSet, Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    exact ⟨i, h1, h2, by push_cast; ring⟩
  · rintro ⟨i, h1, h2, rfl⟩
    exact ⟨i, ⟨h1, h2⟩, by push_cast; ring⟩

/-- The dyadic angle sets increase with `k`. -/
lemma mpc_dyadic_mono {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {k k' : ℕ} (hkk : k ≤ k') :
    (dyadicAngleSet ω hω k).angles ⊆ (dyadicAngleSet ω hω k').angles := by
  intro s hs
  rw [mpc_mem_dyadic] at hs ⊢
  obtain ⟨i, h1, h2, rfl⟩ := hs
  refine ⟨i * 2 ^ (k' - k), by positivity, ?_, ?_⟩
  · have : 2 ^ (k' + 1) = 2 ^ (k + 1) * 2 ^ (k' - k) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    exact Nat.mul_lt_mul_of_pos_right h2 (by positivity)
  · have : (2 : ℝ) ^ (k' + 1) = 2 ^ (k + 1) * 2 ^ (k' - k) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    push_cast
    field_simp

/-- The dyadic angles are dense in `(0, ω)`. -/
lemma mpc_dyadic_dense {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {t : ℝ} (ht : t ∈ Ioo 0 ω) {η : ℝ}
    (hη : 0 < η) : ∃ k, ∃ s ∈ (dyadicAngleSet ω hω k).angles, |s - t| < η := by
  have hω0 : 0 < ω := hω.1
  have ht0 : 0 < t := ht.1
  obtain ⟨k, hk⟩ := exists_nat_gt (max (ω / η) (ω / t))
  set N : ℕ := 2 ^ (k + 1) with hN
  have hkN : (k : ℝ) < N := by
    have : k < N := lt_trans (Nat.lt_succ_self k) (Nat.lt_two_pow_self)
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by positivity
  have hN1 : ω / η < N := lt_of_le_of_lt (le_max_left _ _) (hk.trans hkN)
  have hN2 : ω / t < N := lt_of_le_of_lt (le_max_right _ _) (hk.trans hkN)
  set x : ℝ := t * N / ω with hx
  have hx0 : 0 ≤ x := by positivity
  set j : ℕ := ⌊x⌋₊ with hj
  have hj1 : (j : ℝ) ≤ x := Nat.floor_le hx0
  have hj2 : x < j + 1 := Nat.lt_floor_add_one x
  have hx1 : 1 < x := by
    rw [hx, lt_div_iff₀ hω0, one_mul]
    rw [div_lt_iff₀ ht0] at hN2
    linarith
  have hjpos : 0 < j := by
    rw [hj, Nat.floor_pos]; exact hx1.le
  have hxN : x < N := by
    rw [hx, div_lt_iff₀ hω0]
    nlinarith [ht.2]
  have hjN : j < N := by
    have : (j : ℝ) < N := lt_of_le_of_lt hj1 hxN
    exact_mod_cast this
  refine ⟨k, j * ω / 2 ^ (k + 1), (mpc_mem_dyadic hω k _).2 ⟨j, hjpos, hjN, rfl⟩, ?_⟩
  have hN' : ((2 : ℝ) ^ (k + 1)) = N := by rw [hN]; push_cast; ring
  rw [hN']
  have f1 : (j : ℝ) * ω ≤ t * N := by
    have := hj1; rw [hx, le_div_iff₀ hω0] at this; linarith
  have f2 : t * N < (j + 1) * ω := by
    have := hj2; rw [hx, div_lt_iff₀ hω0] at this; linarith
  have e1 : (j : ℝ) * ω / N ≤ t := by
    rw [div_le_iff₀ hNpos]; linarith
  have e2 : t - j * ω / N < ω / N := by
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hNpos]; linarith
  have e3 : ω / N < η := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hη] at hN1
    linarith
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- A balanced maximum cap with rotation angle `ω` (Definition 3.5.2, `def:balanced-maximum-cap`): a
cap `K_ω` which is the Hausdorff limit of maximum polygon caps `K_i` with uniform angle sets
`Θ_{ω, n_i}`, where `1 < n_1 < n_2 < ⋯` are powers of two (here `n_i = 2^(k_i + 1)`). -/
def IsBalancedMaxCap (K : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ∃ hω : ω ∈ Ioc 0 (π / 2), IsCap K ω ∧
    ∃ (k : ℕ → ℕ) (Ks : ℕ → Set (ℝ × ℝ)), StrictMono k ∧
      (∀ i, IsMaxPolygonCap (dyadicAngleSet ω hω (k i)) (Ks i)) ∧ HausdorffTendsto Ks K

/-! ### Mirror reflections of balanced maximum caps -/

/-- The mirror reflection `M_ω` preserves the Hausdorff distance. -/
lemma mpc_hausdorffDist_mirror (ω : ℝ) (A B : Set (ℝ × ℝ)) :
    hausdorffDist (mirrorCap A ω) (mirrorCap B ω) = hausdorffDist A B := by
  simp only [hausdorffDist, proposition2_5_4_supp]
  exact (Equiv.subLeft (ω + π / 2)).iSup_comp (g := fun t => |supp A t - supp B t|)

/-- The dyadic angle sets are symmetric: `Θ_{ω,n}^m = Θ_{ω,n}`. -/
lemma mpc_dyadic_mirror {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (k : ℕ) :
    (dyadicAngleSet ω hω k).mirror = dyadicAngleSet ω hω k := by
  have hω' : (dyadicAngleSet ω hω k).ω = ω := rfl
  -- `iω/n ↦ ω - iω/n = (n - i)ω/n`
  have hsymm : ∀ s ∈ (dyadicAngleSet ω hω k).angles, ω - s ∈ (dyadicAngleSet ω hω k).angles := by
    intro s hs
    rw [mpc_mem_dyadic] at hs ⊢
    obtain ⟨i, h1, h2, rfl⟩ := hs
    refine ⟨2 ^ (k + 1) - i, by omega, by omega, ?_⟩
    rw [Nat.cast_sub h2.le]
    push_cast
    field_simp
  have key : (dyadicAngleSet ω hω k).mirror.angles = (dyadicAngleSet ω hω k).angles := by
    ext s
    rw [mpc_mem_mirror_angles, hω']
    exact ⟨fun h => by simpa using hsymm _ h, hsymm s⟩
  cases h : dyadicAngleSet ω hω k
  rw [h] at key
  simp only [AngleSet.mirror] at key ⊢
  simp only [AngleSet.mk.injEq, true_and]
  exact key

/-- **Proposition 3.5.1** (`pro:balanced-maximum-cap-mirror`). The mirror reflection of a balanced
maximum cap is a balanced maximum cap. -/
theorem proposition3_5_1 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) :
    IsBalancedMaxCap (mirrorCap K ω) ω := by
  obtain ⟨hω, hcap, k, Ks, hk, hmax, hlim⟩ := hK
  refine ⟨hω, proposition2_5_4_isCap hcap, k, fun i => mirrorCap (Ks i) ω, hk, fun i => ?_, ?_⟩
  · have := lemma3_4_1 (hmax i)
    rwa [mpc_dyadic_mirror] at this
  · simpa only [HausdorffTendsto, mpc_hausdorffDist_mirror] using hlim

/-! ### Limits of polygon caps -/

/-- The cap angles lie in `(0, 3π/2]`. -/
lemma mpc_capAngles_bounds {Θ : AngleSet} {c : ℝ} (hc : c ∈ Θ.capAngles) :
    0 < c ∧ c ≤ 3 * π / 2 := by
  have hω0 := mpc_omega_pos Θ
  have hω2 := mpc_omega_le Θ
  rcases mpc_capAngles_cases hc with h | rfl | rfl
  · exact ⟨(mpc_diamond_bounds h).1, by linarith [mpc_diamond_lt_pi h, pi_pos]⟩
  · exact ⟨by linarith [pi_pos], by linarith⟩
  · exact ⟨by linarith [pi_pos], le_rfl⟩

/-- The support function of a limit of polygon caps is "linear" on the gaps of their normal
angles. -/
lemma mpc_gap_limit {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsPolygonCap (Θs i) (Ks i)) {L : Set (ℝ × ℝ)} (hL : IsConvexBody L)
    (hlim : HausdorffTendsto Ks L) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * π)
    (hba : b - a < π) (hgap : ∀ i, ∀ c ∈ (Θs i).capAngles, c ≤ a ∨ b ≤ c) {r : ℝ}
    (hr1 : a ≤ r) (hr2 : r ≤ b) :
    sin (b - a) * supp L r = sin (b - r) * supp L a + sin (r - a) * supp L b := by
  have hKb : ∀ i, IsConvexBody (Ks i) := fun i => (hKs i).1.2.1
  have hid : ∀ i, sin (b - a) * supp (Ks i) r =
      sin (b - r) * supp (Ks i) a + sin (r - a) * supp (Ks i) b := by
    intro i
    obtain ⟨q, -, hqa, hqb, -, -, hqx, -⟩ := mpc_polycap_corner (hKs i) hab hba (by
      intro c hc
      have hcb := mpc_capAngles_bounds hc
      rcases hgap i c hc with h | h
      · right; exact ⟨by linarith, h⟩
      · left; exact ⟨h, by linarith⟩)
    rw [← hqx r hr1 hr2, ← hqa, ← hqb]
    exact dot_uvec_comb q a b r
  have t1 := (tendsto_supp hKb hL hlim r).const_mul (sin (b - a))
  have t2 := ((tendsto_supp hKb hL hlim a).const_mul (sin (b - r))).add
    ((tendsto_supp hKb hL hlim b).const_mul (sin (r - a)))
  exact tendsto_nhds_unique (t1.congr hid) t2

/-- In a gap `[a, b]` of the normal angles of polygon caps `K_i → L`, a point satisfying the
supporting constraints of `L` at `a` and at `b` satisfies those at every angle in between. -/
private lemma mpc_dot_le_supp_of_gap {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsPolygonCap (Θs i) (Ks i)) {L : Set (ℝ × ℝ)} (hL : IsConvexBody L)
    (hlim : HausdorffTendsto Ks L) {a b r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * π)
    (hba : b - a < π) (hgap : ∀ i, ∀ c ∈ (Θs i).capAngles, c ≤ a ∨ b ≤ c) {p : ℝ × ℝ}
    (hpa : dot p (uvec a) ≤ supp L a) (hpb : dot p (uvec b) ≤ supp L b) (hr1 : a ≤ r)
    (hr2 : r ≤ b) : dot p (uvec r) ≤ supp L r := by
  have hsab : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) hba
  have hs1 : 0 ≤ sin (b - r) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ sin (r - a) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  refine le_of_mul_le_mul_left ?_ hsab
  rw [dot_uvec_comb p a b r, mpc_gap_limit hKs hL hlim ha hab hb hba hgap hr1 hr2]
  exact add_le_add (mul_le_mul_of_nonneg_left hpa hs1) (mul_le_mul_of_nonneg_left hpb hs2)

/-- A Hausdorff limit of polygon caps with rotation angle `ω` is a cap. -/
lemma mpc_limit_isCap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {Θs : ℕ → AngleSet}
    (hΘ : ∀ i, (Θs i).ω = ω) {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsPolygonCap (Θs i) (Ks i))
    {L : Set (ℝ × ℝ)} (hL : IsConvexBody L) (hlim : HausdorffTendsto Ks L) : IsCap L ω := by
  have hKb : ∀ i, IsConvexBody (Ks i) := fun i => (hKs i).1.2.1
  -- the values `h(ω) = h(π/2) = 1` and `h(ω + π) = h(3π/2) = 0` pass to the limit
  have hconst : ∀ t c, (∀ i, supp (Ks i) t = c) → supp L t = c := fun t c h =>
    tendsto_nhds_unique ((tendsto_supp hKb hL hlim t).congr h) tendsto_const_nhds
  obtain ⟨hω0, hω2⟩ := hω
  have hpi := pi_pos
  refine ⟨⟨hω0, hω2⟩, hL, hconst _ _ fun i => hΘ i ▸ (hKs i).1.2.2.1,
    hconst _ _ fun i => (hKs i).1.2.2.2.1, hconst _ _ fun i => hΘ i ▸ (hKs i).1.2.2.2.2.1,
    hconst _ _ fun i => (hKs i).1.2.2.2.2.2.1, ?_⟩
  -- `L` is the intersection of its supporting half-planes with normal angles in
  -- `A = J_ω ∪ {ω + π, 3π/2}`: a point `p` satisfying these constraints lies in `L`
  set A := jSet ω ∪ {ω + π, 3 * π / 2} with hA
  refine ⟨A, fun s => s.1, fun s => supp L s.1, fun s => s.2, ?_⟩
  ext p
  simp only [mem_iInter, halfMinus, mem_ofPred_eq]
  refine ⟨fun hp s => dot_le_supp hL.2.1 hp s.1, fun hp => ?_⟩
  have hpA : ∀ s ∈ A, dot p (uvec s) ≤ supp L s := fun s hs => hp ⟨s, hs⟩
  rw [mem_iff_forall_dot_le_supp hL]
  have hAcase : ∀ c ∈ A, (0 ≤ c ∧ c ≤ ω) ∨ (π / 2 ≤ c ∧ c ≤ ω + π / 2) ∨ c = ω + π ∨
      c = 3 * π / 2 := by
    rintro c ((h | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (mem_singleton_iff.1 h)))
  -- in a gap `[a, b]` of `A`, hence of the normal angles of every `K_i`, the constraints at `a`
  -- and `b` imply those in between
  have hgap : ∀ {a b r : ℝ}, 0 ≤ a → a < b → b ≤ 2 * π → b - a < π →
      (∀ c ∈ A, c ≤ a ∨ b ≤ c) → dot p (uvec a) ≤ supp L a → dot p (uvec b) ≤ supp L b →
      a ≤ r → r ≤ b → dot p (uvec r) ≤ supp L r := fun ha hab hb hba hg =>
    mpc_dot_le_supp_of_gap hKs hL hlim ha hab hb hba fun i c hc =>
      hg c (by have := nef_capAngles_subset (Θs i) hc; rwa [hΘ i] at this)
  -- reduce the angle modulo `2π` to `r' ∈ [0, 2π)`
  intro r
  set r' := toIcoMod two_pi_pos 0 r with hr'
  obtain ⟨h0, h2π⟩ := toIcoMod_mem_Ico two_pi_pos 0 r
  rw [zero_add] at h2π
  have hu : uvec r' = uvec r := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, r' = r - k * (2 * π) := ⟨toIcoDiv two_pi_pos 0 r, by
      rw [hr', toIcoMod, zsmul_eq_mul]⟩
    rw [hk]
    simp [uvec, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]
  have hsupp : supp L r' = supp L r := by simp only [supp, hu]
  rw [← hu, ← hsupp]
  -- `r'` lies in `[0, ω]` or `[π/2, ω + π/2]`, which are in `A`, or in one of the gaps
  -- `[ω, π/2]`, `[ω + π/2, ω + π]`, `[ω + π, 3π/2]`, `[3π/2, 2π]` of `A`
  have h0A : 0 ∈ A := Or.inl (Or.inl ⟨le_rfl, hω0.le⟩)
  have hωA : ω ∈ A := Or.inl (Or.inl ⟨hω0.le, le_rfl⟩)
  have hπA : π / 2 ∈ A := Or.inl (Or.inr ⟨le_rfl, by linarith⟩)
  have hωπA : ω + π / 2 ∈ A := Or.inl (Or.inr ⟨by linarith, le_rfl⟩)
  have hA3 : ω + π ∈ A := Or.inr (Or.inl rfl)
  have hA4 : 3 * π / 2 ∈ A := Or.inr (Or.inr rfl)
  by_cases c1 : r' ≤ ω
  · exact hpA _ (Or.inl (Or.inl ⟨h0, c1⟩))
  push Not at c1
  by_cases c2 : r' < π / 2
  · refine hgap hω0.le (c1.trans c2) (by linarith) (by linarith) (fun c hc => ?_) (hpA _ hωA)
      (hpA _ hπA) c1.le c2.le
    rcases hAcase c hc with ⟨-, h⟩ | ⟨h, -⟩ | rfl | rfl
    all_goals first | (left; linarith) | (right; linarith)
  push Not at c2
  by_cases c3 : r' ≤ ω + π / 2
  · exact hpA _ (Or.inl (Or.inr ⟨c2, c3⟩))
  push Not at c3
  by_cases c4 : r' ≤ ω + π
  · refine hgap (by linarith) (by linarith) (by linarith) (by linarith) (fun c hc => ?_)
      (hpA _ hωπA) (hpA _ hA3) c3.le c4
    rcases hAcase c hc with ⟨-, h⟩ | ⟨-, h⟩ | rfl | rfl
    all_goals first | (left; linarith) | (right; linarith)
  push Not at c4
  by_cases c5 : r' ≤ 3 * π / 2
  · refine hgap (by linarith) (c4.trans_le c5) (by linarith) (by linarith) (fun c hc => ?_)
      (hpA _ hA3) (hpA _ hA4) c4.le c5
    rcases hAcase c hc with ⟨-, h⟩ | ⟨-, h⟩ | rfl | rfl
    all_goals first | (left; linarith) | (right; linarith)
  push Not at c5
  -- the last gap ends at `2π ≡ 0`
  have hb : dot p (uvec (2 * π)) ≤ supp L (2 * π) := by
    rw [show (2 : ℝ) * π = 0 + 2 * π by ring, uvec_add_two_pi, supp_add_two_pi]
    exact hpA 0 h0A
  refine hgap (by linarith) (by linarith) le_rfl (by linarith) (fun c hc => ?_) (hpA _ hA4) hb
    c5.le h2π.le
  rcases hAcase c hc with ⟨-, h⟩ | ⟨-, h⟩ | rfl | rfl
  all_goals left; linarith

/-- **Theorem 3.5.2** (`thm:balanced-maximum-cap`). A balanced maximum cap exists for every
`ω ∈ (0, π/2]`. -/
theorem theorem3_5_2 {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) : ∃ K, IsBalancedMaxCap K ω := by
  classical
  -- maximum polygon caps `K_m` for the dyadic angle sets (Theorem 3.4.3)
  choose Ks hKs using fun m => theorem3_4_3 (dyadicAngleSet ω hω m)
  -- `ω/2` is a common angle, and `𝒜(K_m) > 0`, so the widths `w_{K_m}(0)` are bounded
  -- (Lemma 3.4.2)
  have ht₀ : ∀ m, ω / 2 ∈ (dyadicAngleSet ω hω m).angles := by
    intro m
    refine (mpc_mem_dyadic hω m _).2 ⟨2 ^ m, by positivity, ?_, ?_⟩
    · exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
    · push_cast; field_simp; ring
  obtain ⟨c, hc, hcK⟩ := lemma3_4_2 hω ⟨half_pos hω.1, half_lt_self hω.1⟩
  have hpos : ∀ m, 0 < polyArea (dyadicAngleSet ω hω m) (Ks m) := by
    intro m
    obtain ⟨hK₁, -, hN₁, harea₁⟩ := mpc_K1 (dyadicAngleSet ω hω m)
    have h := (hKs m).2.2 _ hK₁
    rw [theorem3_2_3 hK₁, hN₁] at h
    simp only [area, MeasureTheory.measure_empty, ENNReal.toReal_zero, sub_zero] at h
    simp only [area] at harea₁
    linarith
  have hw : ∀ m, width (Ks m) 0 ≤ c := fun m => hcK _ rfl (ht₀ m) _ (hKs m).1 (hpos m)
  set R := |(oPt ω).1| + c with hR
  -- each `K_m` contains `o_ω` and has width at most `c` along `u_0`, so all of them lie in a
  -- fixed box, and the Blaschke selection theorem applies
  have hbox : ∀ m, Ks m ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
    intro m p hp
    have hKc := (hKs m).1.1.2.1.2.1
    have ho : oPt ω ∈ Ks m := (hKs m).2.1
    have e1 := dot_le_supp hKc hp 0
    have e2 := dot_le_supp hKc ho π
    have e3 := dot_le_supp hKc hp π
    have e4 := dot_le_supp hKc ho 0
    rw [dot_uvec_zero] at e1 e4
    rw [dot_uvec_pi] at e2 e3
    have hwm := hw m
    rw [width, zero_add] at hwm
    have a1 := neg_abs_le (oPt ω).1
    have a2 := le_abs_self (oPt ω).1
    exact ⟨⟨by linarith, by linarith⟩, (hKs m).1.1.snd_nonneg hp,
      (hKs m).1.1.snd_le_one hp⟩
  obtain ⟨L, hLb, -, φ, hφ, hlim⟩ := mpc_blaschke (fun m => (hKs m).1.1.2.1)
    (isCompact_Icc.prod isCompact_Icc) hbox
  exact ⟨L, hω, mpc_limit_isCap hω (fun i => rfl) (fun i => (hKs (φ i)).1) hLb hlim, φ,
    Ks ∘ φ, hφ, fun i => hKs (φ i), hlim⟩

/-- **Lemma 3.5.3** (`lem:hausdorff-distance-containment`). Hausdorff limits of nested bounded sets
are nested, when the limit of the larger sets is compact. -/
theorem lemma3_5_3 {X Y : Set (ℝ × ℝ)} {Xs Ys : ℕ → Set (ℝ × ℝ)}
    (hX : Bornology.IsBounded X) (hXne : X.Nonempty) (hYc : IsCompact Y) (hYne : Y.Nonempty)
    (hXs : ∀ i, Bornology.IsBounded (Xs i) ∧ (Xs i).Nonempty)
    (hYs : ∀ i, Bornology.IsBounded (Ys i) ∧ (Ys i).Nonempty)
    (hXlim : Tendsto (fun i => Metric.hausdorffDist (Xs i) X) atTop (𝓝 0))
    (hYlim : Tendsto (fun i => Metric.hausdorffDist (Ys i) Y) atTop (𝓝 0))
    (hsub : ∀ i, Xs i ⊆ Ys i) : X ⊆ Y := by
  intro p hp
  rw [← hYc.isClosed.closure_eq, Metric.mem_closure_iff_infDist_zero hYne]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) Metric.infDist_nonneg
  obtain ⟨i, hi1, hi2⟩ : ∃ i, Metric.hausdorffDist (Xs i) X < ε / 2 ∧
      Metric.hausdorffDist (Ys i) Y < ε / 2 :=
    ((hXlim.eventually (gt_mem_nhds (half_pos hε))).and
      (hYlim.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hfin1 : Metric.hausdorffEDist X (Xs i) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hXne (hXs i).2 hX (hXs i).1
  obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp
    (by rwa [Metric.hausdorffDist_comm]) hfin1
  have hfin2 : Metric.hausdorffEDist (Ys i) Y ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hYs i).2 hYne (hYs i).1 hYc.isBounded
  have h3 : Metric.infDist q Y ≤ Metric.hausdorffDist (Ys i) Y :=
    Metric.infDist_le_hausdorffDist_of_mem (hsub i hq) hfin2
  have h4 : Metric.infDist p Y ≤ Metric.infDist q Y + dist p q :=
    Metric.infDist_le_infDist_add_dist
  linarith

open Pointwise in
/-- A point `p` of a convex body `A` lies within `d = sup_t |h_A(t) - h_B(t)|` of a point of the
convex body `B`, in the max metric of `ℝ × ℝ`. As in Schneider's proof of his Lemma 1.8.14, with
the ball of the max metric: `p` lies in every supporting half-plane of the convex body
`B + B̄(0, d)`, as `p · u_t ≤ h_A(t) ≤ h_B(t) + d` and `d u_t ∈ B̄(0, d)`, hence in this body. -/
private lemma mpc_exists_dist_le_hausdorffDist {A B : Set (ℝ × ℝ)} (hA : IsConvexBody A)
    (hB : IsConvexBody B) {p : ℝ × ℝ} (hp : p ∈ A) : ∃ q ∈ B, dist p q ≤ hausdorffDist A B := by
  have hd := hausdorffDist_nonneg A B
  have hC : IsConvexBody (B + Metric.closedBall 0 (hausdorffDist A B)) :=
    ⟨hB.1.add (Metric.nonempty_closedBall.2 hd), hB.2.1.add (isCompact_closedBall 0 _),
      hB.2.2.add (convex_closedBall 0 _)⟩
  have hpC : p ∈ B + Metric.closedBall 0 (hausdorffDist A B) := by
    refine (mem_iff_forall_dot_le_supp hC p).2 fun t => ?_
    obtain ⟨b, hb, hbt⟩ := exists_dot_eq_supp hB.2.1 hB.1 t
    have hw : hausdorffDist A B • uvec t ∈ Metric.closedBall 0 (hausdorffDist A B) := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hd]
      exact mul_le_of_le_one_right hd (norm_uvec_le t)
    have h1 := dot_le_supp hC.2.1 (Set.add_mem_add hb hw) t
    rw [dot_add_left, dot_smul_left, dot_uvec_uvec, sub_self, cos_zero, mul_one, hbt] at h1
    linarith [dot_le_supp hA.2.1 hp t, (abs_le.1 (abs_supp_sub_le_hausdorffDist hA hB t)).2]
  obtain ⟨q, hq, w, hw, rfl⟩ := Set.mem_add.1 hpC
  exact ⟨q, hq, by rwa [dist_eq_norm, add_sub_cancel_left, ← mem_closedBall_zero_iff]⟩

/-- One direction of Schneider's Lemma 1.8.14 (`d_H(A, B) = sup_t |h_A(t) - h_B(t)|` in the
Euclidean metric), on which the paper's reading of `d_H` rests: for convex bodies, Mathlib's
`Metric.hausdorffDist` for the max metric of `ℝ × ℝ`, which Lemma 3.5.3 uses, is at most
`sup_t |h_A(t) - h_B(t)|`. -/
private lemma mpc_metric_hausdorffDist_le {A B : Set (ℝ × ℝ)} (hA : IsConvexBody A)
    (hB : IsConvexBody B) : Metric.hausdorffDist A B ≤ hausdorffDist A B :=
  Metric.hausdorffDist_le_of_mem_dist (hausdorffDist_nonneg A B)
    (fun _ hp => mpc_exists_dist_le_hausdorffDist hA hB hp) fun _ hp => by
      obtain ⟨q, hq, h⟩ := mpc_exists_dist_le_hausdorffDist hB hA hp
      exact ⟨q, hq, h.trans_eq (iSup_congr fun t => abs_sub_comm _ _)⟩

/-- Convex bodies `K_i → K` in `sup_t |h_{K_i}(t) - h_K(t)|` converge to `K` in the Hausdorff
distance of Lemma 3.5.3 (`mpc_metric_hausdorffDist_le`). -/
private lemma mpc_tendsto_metric_hausdorffDist {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) :
    Tendsto (fun i => Metric.hausdorffDist (Ks i) K) atTop (𝓝 0) :=
  squeeze_zero (fun _ => Metric.hausdorffDist_nonneg)
    (fun i => mpc_metric_hausdorffDist_le (hKs i) hK) hlim

/-- A point of the niche of the limit `K` of convex bodies `K_i` lies in the polygon niches
`𝒩_{Θ_{k_i}}(K_i)` for all large `i`: the quarter-planes `Q_K⁻(t)` are open conditions on the
support function, and the dyadic angles are dense in `(0, ω)`. -/
lemma mpc_niche_eventually {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {K : Set (ℝ × ℝ)}
    (hK : IsConvexBody K) {k : ℕ → ℕ} (hk : StrictMono k) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) {p : ℝ × ℝ}
    (hp : p ∈ niche K ω) :
    ∀ᶠ i in atTop, p ∈ polyNiche (dyadicAngleSet ω hω (k i)) (Ks i) := by
  obtain ⟨hpf, hpq⟩ := hp
  obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hpq
  rw [proposition2_2_2_qMinus] at hq
  obtain ⟨hq1 : dot p (uvec t) < supp K t - 1,
    hq2 : dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1⟩ := hq
  -- the margin `f(s)` of `p` inside `Q_K⁻(s)` is continuous in `s` and positive at `t`
  set f : ℝ → ℝ := fun s => min (supp K s - 1 - dot p (uvec s))
    (supp K (s + π / 2) - 1 - dot p (uvec (s + π / 2))) with hf
  have hfc : Continuous f := by
    have := continuous_supp hK.2.1
    simp only [hf, dot, uvec]
    fun_prop
  have hft : 0 < f t := lt_min (by linarith) (by linarith)
  -- so it exceeds `f(t)/2` at a dyadic angle `s` near `t`
  obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff.1
    (continuousAt_const.eventually_lt hfc.continuousAt (half_lt_self hft))
  obtain ⟨m, s, hs, hst⟩ := mpc_dyadic_dense hω ht hη
  obtain ⟨hfs, hgs⟩ := lt_min_iff.1 (hηs (show dist s t < η by rwa [Real.dist_eq]))
  -- and `h_{K_i}` is within `f(t)/2` of `h_K` for all large `i`
  filter_upwards [mpc_supp_uniform hK hKs hlim (half_pos hft),
    hk.tendsto_atTop.eventually_ge_atTop m] with i hi hki
  refine ⟨hpf, mem_iUnion₂.2 ⟨s, mpc_dyadic_mono hω hki hs, ?_⟩⟩
  rw [proposition2_2_2_qMinus]
  have e1 := abs_lt.1 (hi s)
  have e2 := abs_lt.1 (hi (s + π / 2))
  exact ⟨show dot p (uvec s) < supp (Ks i) s - 1 by linarith,
    show dot p (uvec (s + π / 2)) < supp (Ks i) (s + π / 2) - 1 by linarith⟩

/-- **Theorem 3.5.4** (`thm:limiting-maximum-cap-connected`). A balanced maximum cap contains its
niche.

As in the paper, with the repair of E8: the paper applies Lemma 3.5.3 to
`𝒩_{Θ_j}(K_i) ⊆ K_i`, with `𝒩_{Θ_j}(K_i) → 𝒩_{Θ_j}(K)`, a convergence that need not hold, but
the lemma only needs each point of `𝒩_{Θ_j}(K)` to lie in `𝒩_{Θ_j}(K_i)` for large `i`. So each
point `p` of `𝒩(K)` lies in `𝒩_{Θ_{k_i}}(K_i) ⊆ K_i` (Theorem 3.4.10) for all large `i`
(`mpc_niche_eventually`: `p ∈ 𝒩_{Θ_j}(K)` for some `j`, and the quarter-planes `Q⁻` are open), and
Lemma 3.5.3 applied to the singletons `{p} ⊆ K_i` puts `p` in `K`. -/
theorem theorem3_5_4 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) : niche K ω ⊆ K := by
  obtain ⟨hω, hcap, k, Ks, hk, hmax, hlim⟩ := hK
  have hKs : ∀ i, IsConvexBody (Ks i) := fun i => (hmax i).1.1.2.1
  intro p hp
  -- `p ∈ 𝒩_{Θ_{k_i}}(K_i) ⊆ K_i` (Theorem 3.4.10) for all `i ≥ N`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (mpc_niche_eventually hω hcap.2.1 hk hKs hlim hp)
  -- Lemma 3.5.3 for `{p} ⊆ K_{i + N}`, where `{p} → {p}` and `K_{i + N} → K`
  refine lemma3_5_3 (X := {p}) (Y := K) (Xs := fun _ => {p}) (Ys := fun i => Ks (i + N))
    Bornology.isBounded_singleton (singleton_nonempty p) hcap.2.1.2.1 hcap.2.1.1
    (fun _ => ⟨Bornology.isBounded_singleton, singleton_nonempty p⟩)
    (fun i => ⟨(hKs (i + N)).isBounded, (hKs (i + N)).1⟩) (by simp)
    ((mpc_tendsto_metric_hausdorffDist hcap.2.1 hKs hlim).comp (tendsto_add_atTop_nat N))
    (fun i => singleton_subset_iff.2 (theorem3_4_10 (hmax (i + N)) (hN _ (Nat.le_add_left N i))))
    (mem_singleton p)

/-- `|𝒩_{Θ_m}(K)| → |𝒩(K)|` as `m → ∞`, for the dyadic angle sets `Θ_m = Θ_{ω, 2^(k_m + 1)}`
(proof of Theorem 3.5.5): the polygon niches `𝒩_{Θ_m}(K) ⊆ 𝒩(K)` increase to `𝒩(K)`, as each point
of `𝒩(K)` lies in `Q_K⁻(t)` for a dyadic angle `t` (the proof of Theorem 3.5.4 notes
`⋃_j 𝒩_{Θ_j}(K) = 𝒩(K)`; `mpc_niche_eventually` for the constant sequence `K`). -/
private lemma mpc_tendsto_area_polyNiche_dyadic {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {K : Set (ℝ × ℝ)} (hK : IsCap K ω) {k : ℕ → ℕ} (hk : StrictMono k) :
    Tendsto (fun m => area (polyNiche (dyadicAngleSet ω hω (k m)) K)) atTop
      (𝓝 (area (niche K ω))) := by
  have hsub : ∀ m, polyNiche (dyadicAngleSet ω hω (k m)) K ⊆ niche K ω := by
    rintro m p ⟨hf, hu⟩
    obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hu
    exact ⟨hf, mem_iUnion₂.2 ⟨t, (dyadicAngleSet ω hω (k m)).subset t ht, hq⟩⟩
  have hconst : HausdorffTendsto (fun _ => K) K := by
    simp [HausdorffTendsto, hausdorffDist]
  have hfin : MeasureTheory.volume (niche K ω) ≠ ⊤ :=
    (nef_niche_isBounded hK).measure_lt_top.ne
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => Eventually.of_forall fun m =>
    (ENNReal.toReal_mono hfin (MeasureTheory.measure_mono (hsub m))).trans_lt hx⟩
  filter_upwards [mpc_area_lsc
    (fun p hp => mpc_niche_eventually hω hK.2.1 hk (fun _ => hK.2.1) hconst hp)
    (nef_niche_isBounded hK) (Eventually.of_forall hsub) (half_pos (sub_pos.2 hx))] with m hm
  linarith

/-- **Theorem 3.5.5** (`thm:limiting-maximum-cap-max`). A balanced maximum cap maximizes the sofa
area functional `𝒜_ω` over all caps with rotation angle `ω`.

As in the paper, `𝒜_{Θ_i}(K_i) → 𝒜_ω(K)`: `|K_i| → |K|` (Schneider, Theorem 1.8.20;
`mpc_tendsto_area`); `lim sup |𝒩_{Θ_i}(K_i)| ≤ |𝒩(K)|`, since `𝒜_{Θ_i}(K_i) ≥ 𝒜_{Θ_i}(K) ≥ 𝒜_ω(K)`
(Definition 3.4.1, Theorem 3.2.3); and `lim inf |𝒩_{Θ_i}(K_i)| ≥ |𝒩(K)|` by the double limit through
`|𝒩_{Θ_m}(K_i)| → |𝒩_{Θ_m}(K)|` as `i → ∞` (`mpc_tendsto_area_polyNiche`, as `h_{K_i} → h_K`) and
`|𝒩_{Θ_m}(K)| → |𝒩(K)|` as `m → ∞`. Then `𝒜_ω(K') ≤ 𝒜_{Θ_i}(K') ≤ 𝒜_{Θ_i}(K_i)` for every cap
`K'`. The inner limit is one of areas, which holds also when a wedge is empty for `K` but not for
the `K_i`, the case that breaks the Hausdorff convergence of the niches in Theorem 3.5.4 (E8). -/
theorem theorem3_5_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) :
    ∀ K', IsCap K' ω → sofaArea ω K' ≤ sofaArea ω K := by
  obtain ⟨hω, hcap, k, Ks, hk, hmax, hlim⟩ := hK
  have hKs : ∀ i, IsConvexBody (Ks i) := fun i => (hmax i).1.1.2.1
  -- `𝒜_ω(K') ≤ 𝒜_Θ(𝓒_Θ(K')) ≤ 𝒜_Θ(K_i) = |K_i| - |𝒩_Θ(K_i)|` for `Θ = Θ_{k_i}`
  have hbound : ∀ K', IsCap K' ω → ∀ i, sofaArea ω K' ≤
      area (Ks i) - area (polyNiche (dyadicAngleSet ω hω (k i)) (Ks i)) := by
    intro K' hK' i
    set Θ := dyadicAngleSet ω hω (k i)
    have h1 : sofaArea ω K' ≤ polyArea Θ K' := theorem3_2_3_le (Θ := Θ) hK'
    have hpc := proposition3_2_1 (Θ := Θ) hK'
    have h2 : polyArea Θ K' = polyArea Θ (polyCap Θ K') := by
      unfold polyArea
      rw [proposition3_2_1_fix hpc.2, ← (proposition3_2_2 (Θ := Θ) hK').1]
    have h3 := (hmax i).2.2 _ hpc.2
    have h4 : polyArea Θ (Ks i) = area (Ks i) - area (polyNiche Θ (Ks i)) :=
      theorem3_2_3 (hmax i).1
    linarith
  have hsofa : sofaArea ω K = area K - area (niche K ω) := rfl
  -- `|K_i| → |K|`
  have harea := mpc_tendsto_area hcap.2.1 hKs hlim
  -- `|𝒩_{Θ_i}(K_i)| → |𝒩(K)|`
  have hniche : Tendsto (fun i => area (polyNiche (dyadicAngleSet ω hω (k i)) (Ks i))) atTop
      (𝓝 (area (niche K ω))) := by
    refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · -- `lim inf`: fix `m` with `|𝒩_{Θ_m}(K)| > x`; then `|𝒩_{Θ_m}(K_i)| > x` for large `i`, and
      -- `𝒩_{Θ_m}(K_i) ⊆ 𝒩_{Θ_i}(K_i)` for `i ≥ m`
      obtain ⟨m, hm⟩ :=
        ((mpc_tendsto_area_polyNiche_dyadic hω hcap hk).eventually (lt_mem_nhds hx)).exists
      filter_upwards [(mpc_tendsto_area_polyNiche (Θ := dyadicAngleSet ω hω (k m))
        (tendsto_supp hKs hcap.2.1 hlim)).eventually (lt_mem_nhds hm),
        eventually_ge_atTop m] with i hi him
      have hsub : polyNiche (dyadicAngleSet ω hω (k m)) (Ks i) ⊆
          polyNiche (dyadicAngleSet ω hω (k i)) (Ks i) := by
        rintro p ⟨hf, hu⟩
        obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hu
        exact ⟨hf, mem_iUnion₂.2 ⟨t, mpc_dyadic_mono hω (hk.monotone him) ht, hq⟩⟩
      exact hi.trans_le (ENNReal.toReal_mono
        (mpc_polyNiche_isBounded _ _).measure_lt_top.ne (MeasureTheory.measure_mono hsub))
    · -- `lim sup`: `|𝒩_{Θ_i}(K_i)| ≤ |K_i| - 𝒜_ω(K)`, and `|K_i| → |K|`
      filter_upwards [harea.eventually (gt_mem_nhds
        (show area K < area K + (x - area (niche K ω)) by linarith))] with i hi
      linarith [hbound K hcap i]
  -- `𝒜_{Θ_i}(K_i) → 𝒜_ω(K)`, and `𝒜_ω(K') ≤ 𝒜_{Θ_i}(K_i)` for every cap `K'`
  have hlimA : Tendsto (fun i => area (Ks i) -
      area (polyNiche (dyadicAngleSet ω hω (k i)) (Ks i))) atTop (𝓝 (sofaArea ω K)) := by
    rw [hsofa]
    exact harea.sub hniche
  exact fun K' hK' => ge_of_tendsto' hlimA (hbound K' hK')

/-- A translate of a moving sofa with rotation angle `ω` is a moving sofa with rotation angle
`ω`. -/
lemma mpc_isMovingSofaWithAngle_translate {S : Set (ℝ × ℝ)} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) (v : ℝ × ℝ) :
    IsMovingSofaWithAngle ((fun p => p + v) '' S) ω := by
  obtain ⟨hcl, hconn, θ, c, hm⟩ := hS
  refine ⟨?_, hconn.image _ (by fun_prop : Continuous fun p : ℝ × ℝ => p + v).continuousOn, θ,
    fun s => c s - rot (θ s) v, ?_⟩
  · rw [image_add_right]; exact hcl.preimage (by fun_prop)
  · have key : ∀ s, ∀ p, rot (θ s) (p + v) + (c s - rot (θ s) v) = rot (θ s) p + c s := by
      intro s p; rw [rot_add_vec]; abel
    have hrot : ContinuousOn (fun s => rot (θ s) v) (Icc 0 1) :=
      (by simp only [rot]; fun_prop : Continuous fun t => rot t v).comp_continuousOn
        hm.continuousOn_angle
    refine ⟨hm.continuousOn_angle, hm.continuousOn_shift.sub hrot, hm.angle_zero, hm.angle_one,
      ?_, ?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩; rw [key]; exact hm.start p hp
    · rintro s hs _ ⟨p, hp, rfl⟩; rw [key]; exact hm.inside s hs p hp
    · rintro _ ⟨p, hp, rfl⟩; rw [key]; exact hm.finish p hp

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
  obtain ⟨K, hK⟩ := theorem3_5_2 hω
  have hcap : IsCap K ω := hK.2.1
  obtain ⟨S, hS, hSK⟩ := (theorem2_5_9 hcap).2 (theorem3_5_4 hK)
  have hSeq : S = K \ niche K ω := by
    have := theorem2_4_3 hS
    rwa [hSK] at this
  have hval : sofaArea ω K = area (K \ niche K ω) := by
    have := theorem2_5_10 hS
    rw [hSK] at this
    rw [this, hSeq]
  refine ⟨K, hK, ⟨hSeq ▸ hS, by rw [← hSeq, hSK]; exact hK⟩, by rw [← hSeq, hSK], ?_⟩
  intro S' hS'
  obtain ⟨v, hv⟩ := proposition2_3_1_exists hω hS'
  have hS'' := mpc_isMovingSofaWithAngle_translate hS' v
  have harea := (area_image_add S' v).symm
  obtain ⟨hM, hstd, hsub⟩ := theorem2_3_2 hω hS'' hv
  have hmono : IsMonotoneSofa (monotonization ((fun p => p + v) '' S') ω) ω :=
    ⟨hω, _, hS'', hv, rfl⟩
  have hbdd : Bornology.IsBounded (monotonization ((fun p => p + v) '' S') ω) :=
    isBounded_of_isMovingSofa ⟨ω, hM⟩
  have h1 : area ((fun p => p + v) '' S') ≤ area (monotonization ((fun p => p + v) '' S') ω) :=
    ENNReal.toReal_mono hbdd.measure_lt_top.ne (MeasureTheory.measure_mono hsub)
  have h2 := theorem2_5_10 hmono
  have h3 := theorem3_5_5 hK _ (theorem2_4_1 hω hM hstd)
  rw [harea]
  linarith

end MovingSofaOptimality
