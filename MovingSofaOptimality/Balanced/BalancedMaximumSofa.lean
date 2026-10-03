module

public import MovingSofaOptimality.Balanced.MaximumPolygonCap
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Closeds

/-!
# Balanced maximum sofas (§3.5)

Definitions 3.5.1–3.5.3, Proposition 3.5.1, Theorem 3.5.2 (`thm:balanced-maximum-cap`), Lemma 3.5.3
(`lem:hausdorff-distance-containment`), Theorems 3.5.4–3.5.6.

**Proofs.** Theorem 3.5.2 uses the Blaschke selection theorem (`mpc_blaschke`), obtained from the
compactness of the nonempty compact subsets of a compact set in the Hausdorff metric together with
the estimate `|h_A - h_B| ≤ 2 d_H(A, B)` (sup metric on `ℝ × ℝ`); the limit is a cap because the
support functions of the approximating polygon caps are "linear" on the gaps of
`J_ω ∪ {ω + π, 3π/2}` (`mpc_gap_limit`). Theorems 3.5.4 and 3.5.5 do not need Lemma 3.5.3: a point of
the niche lies in the open quarter-planes `Q_K⁻(t)` for a dyadic `t`, hence in the polygon niches of
the approximating caps (`mpc_niche_eventually`); the area is upper semicontinuous under Hausdorff
convergence (`mpc_area_usc`) and lower semicontinuous along eventual membership (`mpc_area_lsc`).
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

lemma mpc_mem_dyadic {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (k : ℕ) (s : ℝ) :
    s ∈ (dyadicAngleSet ω hω k).angles ↔
      ∃ i : ℕ, 0 < i ∧ i < 2 ^ (k + 1) ∧ s = i * ω / 2 ^ (k + 1) := by
  simp only [dyadicAngleSet, uniformAngleSet, Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    exact ⟨i, h1, h2, by push_cast; ring⟩
  · rintro ⟨i, h1, h2, rfl⟩
    exact ⟨i, ⟨h1, h2⟩, by push_cast; ring⟩

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


/-- The support function of the mirror image. -/
lemma mpc_supp_mirror (ω : ℝ) (S : Set (ℝ × ℝ)) (t : ℝ) :
    supp (mirror ω '' S) t = supp S (π / 2 + ω - t) := by
  simp only [supp, Set.image_image, mpc_dot_mirror]

lemma mpc_hausdorffDist_mirror (ω : ℝ) (A B : Set (ℝ × ℝ)) :
    hausdorffDist (mirror ω '' A) (mirror ω '' B) = hausdorffDist A B := by
  simp only [hausdorffDist, mpc_supp_mirror]
  exact (Equiv.subLeft (π / 2 + ω)).iSup_comp (g := fun t => |supp A t - supp B t|)

lemma mpc_dyadic_mirror {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) (k : ℕ) :
    (dyadicAngleSet ω hω k).mirror = dyadicAngleSet ω hω k := by
  have hω' : (dyadicAngleSet ω hω k).ω = ω := rfl
  have key : (dyadicAngleSet ω hω k).mirror.angles = (dyadicAngleSet ω hω k).angles := by
    ext s
    rw [mpc_mem_mirror_angles, hω', mpc_mem_dyadic, mpc_mem_dyadic]
    constructor
    · rintro ⟨i, h1, h2, h3⟩
      refine ⟨2 ^ (k + 1) - i, by omega, by omega, ?_⟩
      have : ((2 ^ (k + 1) - i : ℕ) : ℝ) = 2 ^ (k + 1) - i := by
        rw [Nat.cast_sub h2.le]; push_cast; ring
      rw [this]
      have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
      rw [eq_div_iff hpos.ne'] at h3
      field_simp
      linear_combination -h3
    · rintro ⟨i, h1, h2, h3⟩
      refine ⟨2 ^ (k + 1) - i, by omega, by omega, ?_⟩
      have : ((2 ^ (k + 1) - i : ℕ) : ℝ) = 2 ^ (k + 1) - i := by
        rw [Nat.cast_sub h2.le]; push_cast; ring
      rw [this, h3]
      have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
      field_simp
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
    rw [mpc_dyadic_mirror] at this
    exact this
  · unfold HausdorffTendsto
    simp only [mirrorCap, mpc_hausdorffDist_mirror]
    exact hlim

/-! ### Blaschke selection and limits of polygon caps -/


/-- Support functions are controlled by the (Mathlib) Hausdorff distance. -/
lemma mpc_supp_le_add_hausdorff {A B : Set (ℝ × ℝ)} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (t : ℝ) :
    supp A t ≤ supp B t + 2 * Metric.hausdorffDist A B := by
  have hfin := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hAne hBne hA.isBounded
    hB.isBounded
  apply csSup_le (hAne.image _)
  rintro _ ⟨p, hp, rfl⟩
  apply le_of_forall_pos_lt_add
  intro δ hδ
  obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp
    (lt_add_of_pos_right (Metric.hausdorffDist A B) (half_pos hδ)) hfin
  have h1 := dot_le_supp hB hq t
  have h2 := mpc_abs_dot_uvec_le (p - q) t
  have hpq' : dist p q = max (dist p.1 q.1) (dist p.2 q.2) := Prod.dist_eq
  have h3 : |(p - q).1| ≤ dist p q := by
    rw [Prod.fst_sub, ← Real.dist_eq, hpq']; exact le_max_left _ _
  have h4 : |(p - q).2| ≤ dist p q := by
    rw [Prod.snd_sub, ← Real.dist_eq, hpq']; exact le_max_right _ _
  have h5 : dot p (uvec t) = dot q (uvec t) + dot (p - q) (uvec t) := by
    rw [dot_sub_left]; ring
  dsimp only
  linarith [le_abs_self (dot (p - q) (uvec t))]

open TopologicalSpace in
/-- **Blaschke selection theorem** for convex bodies in a compact set, with convergence of the
support functions. -/
lemma mpc_blaschke {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsConvexBody (Ks i)) {B : Set (ℝ × ℝ)}
    (hB : IsCompact B) (hsub : ∀ i, Ks i ⊆ B) :
    ∃ L, IsConvexBody L ∧ L ⊆ B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ HausdorffTendsto (Ks ∘ φ) L := by
  set C : ℕ → NonemptyCompacts (ℝ × ℝ) := fun i => ⟨⟨Ks i, (hKs i).2.1⟩, (hKs i).1⟩ with hC
  set S := {D : NonemptyCompacts (ℝ × ℝ) | (D : Set (ℝ × ℝ)) ⊆ B}
  have hS : TotallyBounded S :=
    NonemptyCompacts.totallyBounded_subsets_of_totallyBounded hB.totallyBounded
  have hSc : IsCompact (closure S) :=
    (TotallyBounded.closure hS).isCompact_of_isComplete isClosed_closure.isComplete
  obtain ⟨Lc, -, φ, hφ, hlim⟩ := hSc.tendsto_subseq
    (fun i => subset_closure (show C i ∈ S from hsub i))
  set L : Set (ℝ × ℝ) := (Lc : Set (ℝ × ℝ)) with hLdef
  have hLc : IsCompact L := Lc.isCompact
  have hLne : L.Nonempty := Lc.nonempty
  have hd : Tendsto (fun i => Metric.hausdorffDist (Ks (φ i)) L) atTop (𝓝 0) := by
    have := tendsto_iff_dist_tendsto_zero.1 hlim
    simpa [NonemptyCompacts.dist_eq, hC] using this
  have hfin : ∀ i, Metric.hausdorffEDist (Ks (φ i)) L ≠ ⊤ := fun i =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hKs _).1 hLne (hKs _).2.1.isBounded
      hLc.isBounded
  have hLB : L ⊆ B := by
    intro p hp
    rw [← hB.isClosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨i, hi⟩ := (hd.eventually (gt_mem_nhds hε)).exists
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hp hi (hfin i)
    exact ⟨q, hsub _ hq, by rw [dist_comm]; exact hpq⟩
  have hLconv : Convex ℝ L := by
    intro p hp q hq a b ha hb hab
    rw [← hLc.isClosed.closure_eq, Metric.mem_closure_iff_infDist_zero hLne]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) Metric.infDist_nonneg
    obtain ⟨i, hi⟩ := (hd.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))).exists
    obtain ⟨p', hp', hpp'⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hp hi (hfin i)
    obtain ⟨q', hq', hqq'⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hq hi (hfin i)
    have hm' : a • p' + b • q' ∈ Ks (φ i) := (hKs _).2.2 hp' hq' ha hb hab
    have h1 : Metric.infDist (a • p' + b • q') L ≤ Metric.hausdorffDist (Ks (φ i)) L :=
      Metric.infDist_le_hausdorffDist_of_mem hm' (hfin i)
    have h2 : dist (a • p + b • q) (a • p' + b • q') ≤ a * dist p' p + b * dist q' q := by
      rw [dist_eq_norm, show a • p + b • q - (a • p' + b • q') = a • (p - p') + b • (q - q') by
        simp only [smul_sub]; abel]
      calc ‖a • (p - p') + b • (q - q')‖ ≤ ‖a • (p - p')‖ + ‖b • (q - q')‖ := norm_add_le _ _
        _ = a * dist p' p + b * dist q' q := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb, ← dist_eq_norm, ← dist_eq_norm, dist_comm p, dist_comm q]
    have h3 := Metric.infDist_le_infDist_add_dist (x := a • p + b • q) (y := a • p' + b • q')
      (s := L)
    have h4 : a * dist p' p + b * dist q' q ≤ ε / 2 := by
      have e1 := mul_le_mul_of_nonneg_left hpp'.le ha
      have e2 := mul_le_mul_of_nonneg_left hqq'.le hb
      have e3 : a * (ε / 2) + b * (ε / 2) = ε / 2 := by rw [← add_mul, hab, one_mul]
      linarith
    linarith
  have hLb : IsConvexBody L := ⟨hLne, hLc, hLconv⟩
  refine ⟨L, hLb, hLB, φ, hφ, ?_⟩
  -- the support functions converge
  have hbridge : ∀ i, hausdorffDist (Ks (φ i)) L ≤ 2 * Metric.hausdorffDist (Ks (φ i)) L := by
    intro i
    apply ciSup_le
    intro t
    rw [abs_le]
    have e1 := mpc_supp_le_add_hausdorff (hKs (φ i)).2.1 (hKs (φ i)).1 hLc hLne t
    have e2 := mpc_supp_le_add_hausdorff hLc hLne (hKs (φ i)).2.1 (hKs (φ i)).1 t
    rw [Metric.hausdorffDist_comm] at e2
    constructor <;> linarith
  have hnn : ∀ i, 0 ≤ hausdorffDist (Ks (φ i)) L := fun i =>
    (abs_nonneg _).trans (le_ciSup (mpc_bddAbove_abs_supp_sub (hKs (φ i)).2.1 (hKs (φ i)).1
      hLc hLne) 0)
  have h2 : Tendsto (fun i => 2 * Metric.hausdorffDist (Ks (φ i)) L) atTop (𝓝 0) := by
    simpa using hd.const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 hnn hbridge

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
    exact mpc_dot_uvec_comb q a b r
  have t1 := (mpc_supp_tendsto hL hKb hlim r).const_mul (sin (b - a))
  have t2 := ((mpc_supp_tendsto hL hKb hlim a).const_mul (sin (b - r))).add
    ((mpc_supp_tendsto hL hKb hlim b).const_mul (sin (r - a)))
  exact tendsto_nhds_unique (t1.congr hid) t2

/-- A Hausdorff limit of polygon caps with rotation angle `ω` is a cap. -/
lemma mpc_limit_isCap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {Θs : ℕ → AngleSet}
    (hΘ : ∀ i, (Θs i).ω = ω) {Ks : ℕ → Set (ℝ × ℝ)} (hKs : ∀ i, IsPolygonCap (Θs i) (Ks i))
    {L : Set (ℝ × ℝ)} (hL : IsConvexBody L) (hlim : HausdorffTendsto Ks L) : IsCap L ω := by
  have hKb : ∀ i, IsConvexBody (Ks i) := fun i => (hKs i).1.2.1
  have hconst : ∀ t c, (∀ i, supp (Ks i) t = c) → supp L t = c := by
    intro t c h
    have := mpc_supp_tendsto hL hKb hlim t
    simp only [h] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hω0 := hω.1
  have hω2 := hω.2
  refine ⟨hω, hL, hconst _ _ fun i => by have := (hKs i).1.2.2.1; rwa [hΘ i] at this,
    hconst _ _ fun i => (hKs i).1.2.2.2.1,
    hconst _ _ fun i => by have := (hKs i).1.2.2.2.2.1; rwa [hΘ i] at this,
    hconst _ _ fun i => (hKs i).1.2.2.2.2.2.1, ?_⟩
  -- `L` is the intersection of its supporting half-planes with normal angles in `A`
  set A := jSet ω ∪ {ω + π, 3 * π / 2} with hA
  refine ⟨A, fun s => s.1, fun s => supp L s.1, fun s => s.2, ?_⟩
  ext p
  simp only [mem_iInter, halfMinus, mem_ofPred_eq]
  refine ⟨fun hp s => dot_le_supp hL.2.1 hp s.1, fun hp => ?_⟩
  have hpA : ∀ s ∈ A, dot p (uvec s) ≤ supp L s := fun s hs => hp ⟨s, hs⟩
  rw [mem_iff_forall_dot_le_supp hL]
  -- the normal angles of the polygon caps avoid the gaps of `A`
  have hcap : ∀ i, ∀ c ∈ (Θs i).capAngles, c ∈ A := by
    intro i c hc
    have := mpc_capAngles_subset (Θs i) hc
    rwa [hΘ i] at this
  have hgapA : ∀ {a b : ℝ}, (∀ c ∈ A, c ≤ a ∨ b ≤ c) →
      ∀ i, ∀ c ∈ (Θs i).capAngles, c ≤ a ∨ b ≤ c := fun h i c hc => h c (hcap i c hc)
  -- the gap estimate
  have hgapEst : ∀ {a b r : ℝ}, 0 ≤ a → a < b → b ≤ 2 * π → b - a < π →
      (∀ c ∈ A, c ≤ a ∨ b ≤ c) → dot p (uvec a) ≤ supp L a → dot p (uvec b) ≤ supp L b →
      a ≤ r → r ≤ b → dot p (uvec r) ≤ supp L r := by
    intro a b r ha hab hb hba hg hpa hpb hr1 hr2
    have hid := mpc_gap_limit hKs hL hlim ha hab hb hba (hgapA hg) hr1 hr2
    have hsab : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) hba
    have hs1 : 0 ≤ sin (b - r) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hs2 : 0 ≤ sin (r - a) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcomb := mpc_dot_uvec_comb p a b r
    have : sin (b - a) * dot p (uvec r) ≤ sin (b - a) * supp L r := by
      rw [hcomb, hid]
      nlinarith [mul_le_mul_of_nonneg_left hpa hs1, mul_le_mul_of_nonneg_left hpb hs2]
    exact le_of_mul_le_mul_left this hsab
  have hJ1 : ∀ s, 0 ≤ s → s ≤ ω → s ∈ A := fun s h1 h2 => Or.inl (Or.inl ⟨h1, h2⟩)
  have hJ2 : ∀ s, π / 2 ≤ s → s ≤ ω + π / 2 → s ∈ A := fun s h1 h2 => Or.inl (Or.inr ⟨h1, h2⟩)
  have hA3 : ω + π ∈ A := Or.inr (Or.inl rfl)
  have hA4 : 3 * π / 2 ∈ A := Or.inr (Or.inr rfl)
  have hAbounds : ∀ c ∈ A, 0 ≤ c ∧ c ≤ 3 * π / 2 := by
    rintro c ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h | h)
    · exact ⟨h1, by linarith [pi_pos]⟩
    · exact ⟨by linarith [pi_pos], by linarith⟩
    · rw [mem_singleton_iff.1 h] at *; exact ⟨by linarith [pi_pos], by linarith⟩
    · rw [mem_singleton_iff.1 h]; exact ⟨by linarith [pi_pos], le_rfl⟩
  have hAcase : ∀ c ∈ A, (0 ≤ c ∧ c ≤ ω) ∨ (π / 2 ≤ c ∧ c ≤ ω + π / 2) ∨ c = ω + π ∨
      c = 3 * π / 2 := by
    rintro c ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h | h)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inl (mem_singleton_iff.1 h)))
    · exact Or.inr (Or.inr (Or.inr (mem_singleton_iff.1 h)))
  -- reduce the angle modulo `2π`
  intro r
  set r' := toIcoMod two_pi_pos 0 r with hr'
  have hr'mem := toIcoMod_mem_Ico two_pi_pos 0 r
  rw [zero_add] at hr'mem
  have hu : uvec r' = uvec r := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, r' = r - k * (2 * π) := ⟨toIcoDiv two_pi_pos 0 r, by
      rw [hr', toIcoMod, zsmul_eq_mul]⟩
    rw [hk]
    simp [uvec, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]
  have hsupp : supp L r' = supp L r := by simp only [supp, hu]
  rw [← hu, ← hsupp]
  obtain ⟨h0, h2π⟩ := hr'mem
  -- the cases
  by_cases c1 : r' ≤ ω
  · exact hpA _ (hJ1 _ h0 c1)
  by_cases c2 : r' < π / 2
  · push Not at c1
    exact hgapEst hω0.le (by linarith) (by linarith [pi_pos]) (by linarith [pi_pos])
      (fun c hc => by
        rcases hAcase c hc with h | h | rfl | rfl
        · exact Or.inl h.2
        · exact Or.inr h.1
        · exact Or.inr (by linarith [pi_pos])
        · exact Or.inr (by linarith [pi_pos]))
      (hpA _ (hJ1 _ hω0.le le_rfl)) (hpA _ (hJ2 _ le_rfl (by linarith))) c1.le c2.le
  by_cases c3 : r' ≤ ω + π / 2
  · push Not at c2
    exact hpA _ (hJ2 _ c2 c3)
  by_cases c4 : r' ≤ ω + π
  · push Not at c3
    exact hgapEst (by linarith [pi_pos]) (by linarith [pi_pos]) (by linarith [pi_pos])
      (by linarith [pi_pos])
      (fun c hc => by
        rcases hAcase c hc with h | h | rfl | rfl
        · exact Or.inl (by linarith [pi_pos])
        · exact Or.inl h.2
        · exact Or.inr le_rfl
        · exact Or.inr (by linarith [pi_pos]))
      (hpA _ (hJ2 _ (by linarith) le_rfl)) (hpA _ hA3) c3.le c4
  by_cases c5 : r' ≤ 3 * π / 2
  · push Not at c4
    exact hgapEst (by linarith [pi_pos]) (by linarith [pi_pos]) (by linarith [pi_pos])
      (by linarith [pi_pos])
      (fun c hc => by
        rcases hAcase c hc with h | h | rfl | rfl
        · exact Or.inl (by linarith [pi_pos])
        · exact Or.inl (by linarith [pi_pos])
        · exact Or.inl le_rfl
        · exact Or.inr le_rfl)
      (hpA _ hA3) (hpA _ hA4) c4.le c5
  · push Not at c5
    have hb : dot p (uvec (2 * π)) ≤ supp L (2 * π) := by
      have h := hpA 0 (hJ1 0 le_rfl hω0.le)
      rw [show (2 : ℝ) * π = 0 + 2 * π by ring, uvec_add_two_pi, supp_add_two_pi]
      exact h
    exact hgapEst (by linarith [pi_pos]) (by linarith [pi_pos]) le_rfl (by linarith [pi_pos])
      (fun c hc => Or.inl (hAbounds c hc).2) (hpA _ hA4) hb c5.le h2π.le

/-- **Theorem 3.5.2** (`thm:balanced-maximum-cap`). A balanced maximum cap exists for every
`ω ∈ (0, π/2]`. -/
theorem theorem3_5_2 {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) : ∃ K, IsBalancedMaxCap K ω := by
  classical
  choose Ks hKs using fun m => theorem3_4_3 (dyadicAngleSet ω hω m)
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
  have hbox : ∀ m, Ks m ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
    intro m p hp
    have hKc := (hKs m).1.1.2.1.2.1
    have ho : oPt ω ∈ Ks m := (hKs m).2.1
    have e1 := dot_le_supp hKc hp 0
    have e2 := dot_le_supp hKc ho π
    have e3 := dot_le_supp hKc hp π
    have e4 := dot_le_supp hKc ho 0
    rw [mpc_dot_uvec_zero] at e1 e4
    rw [mpc_dot_uvec_pi] at e2 e3
    have hwm := hw m
    rw [width, zero_add] at hwm
    have a1 := neg_abs_le (oPt ω).1
    have a2 := le_abs_self (oPt ω).1
    exact ⟨⟨by linarith, by linarith⟩, (mpc_cap_nonneg (hKs m).1.1 hp).1,
      (mpc_cap_le_one (hKs m).1.1 hp).2⟩
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

/-- A point of the niche of the limit `K` of convex bodies `K_i` lies in the polygon niches
`𝒩_{Θ_{k_i}}(K_i)` for all large `i`: the quarter-planes `Q_K⁻(t)` are open conditions on the support
function, and the dyadic angles are dense in `(0, ω)`. -/
lemma mpc_niche_eventually {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) {K : Set (ℝ × ℝ)}
    (hK : IsConvexBody K) {k : ℕ → ℕ} (hk : StrictMono k) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ i, IsConvexBody (Ks i)) (hlim : HausdorffTendsto Ks K) {p : ℝ × ℝ}
    (hp : p ∈ niche K ω) :
    ∀ᶠ i in atTop, p ∈ polyNiche (dyadicAngleSet ω hω (k i)) (Ks i) := by
  obtain ⟨hpf, hpq⟩ := hp
  obtain ⟨t, ht, hq⟩ := mem_iUnion₂.1 hpq
  rw [proposition2_2_2_qMinus] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hq1' : dot p (uvec t) < supp K t - 1 := hq1
  have hq2' : dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := hq2
  set f : ℝ → ℝ := fun s => supp K s - 1 - dot p (uvec s) with hf
  set g : ℝ → ℝ := fun s => supp K (s + π / 2) - 1 - dot p (uvec (s + π / 2)) with hg
  have hsc := continuous_supp hK.2.1
  have hfc : Continuous f := by
    simp only [hf, dot, uvec]
    exact (hsc.sub continuous_const).sub (by fun_prop)
  have hgc : Continuous g := by
    simp only [hg, dot, uvec]
    exact ((hsc.comp (continuous_id.add continuous_const)).sub continuous_const).sub (by fun_prop)
  set δ := min (f t) (g t) / 2 with hδ_def
  have hft : 0 < f t := by simp only [hf]; linarith
  have hgt : 0 < g t := by simp only [hg]; linarith
  have hδ : 0 < δ := by positivity
  have hδf : δ < f t := by
    have := min_le_left (f t) (g t); simp only [hδ_def]; linarith
  have hδg : δ < g t := by
    have := min_le_right (f t) (g t); simp only [hδ_def]; linarith
  have hev : ∀ᶠ s in 𝓝 t, δ < f s ∧ δ < g s :=
    (continuousAt_const.eventually_lt hfc.continuousAt hδf).and
      (continuousAt_const.eventually_lt hgc.continuousAt hδg)
  obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨m, s, hs, hst⟩ := mpc_dyadic_dense hω ht hη
  obtain ⟨hfs, hgs⟩ := hηs (show dist s t < η by rwa [Real.dist_eq])
  filter_upwards [mpc_supp_uniform hK hKs hlim hδ,
    hk.tendsto_atTop.eventually_ge_atTop m] with i hi hki
  refine ⟨hpf, mem_iUnion₂.2 ⟨s, mpc_dyadic_mono hω hki hs, ?_⟩⟩
  rw [proposition2_2_2_qMinus]
  have e1 := abs_lt.1 (hi s)
  have e2 := abs_lt.1 (hi (s + π / 2))
  simp only [hf, hg] at hfs hgs
  constructor
  · show dot p (uvec s) < supp (Ks i) s - 1
    linarith
  · show dot p (uvec (s + π / 2)) < supp (Ks i) (s + π / 2) - 1
    linarith

/-- **Theorem 3.5.4** (`thm:limiting-maximum-cap-connected`). A balanced maximum cap contains its
niche. -/
theorem theorem3_5_4 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) : niche K ω ⊆ K := by
  obtain ⟨hω, hcap, k, Ks, hk, hmax, hlim⟩ := hK
  have hKs : ∀ i, IsConvexBody (Ks i) := fun i => (hmax i).1.1.2.1
  intro p hp
  apply mpc_mem_of_eventually_mem hcap.2.1 hKs hlim
  filter_upwards [mpc_niche_eventually hω hcap.2.1 hk hKs hlim hp] with i hi
  exact theorem3_4_10 (hmax i) hi

/-- **Theorem 3.5.5** (`thm:limiting-maximum-cap-max`). A balanced maximum cap maximizes the sofa area
functional `𝒜_ω` over all caps with rotation angle `ω`. -/
theorem theorem3_5_5 {K : Set (ℝ × ℝ)} {ω : ℝ} (hK : IsBalancedMaxCap K ω) :
    ∀ K', IsCap K' ω → sofaArea ω K' ≤ sofaArea ω K := by
  have hN := theorem3_5_4 hK
  obtain ⟨hω, hcap, k, Ks, hk, hmax, hlim⟩ := hK
  have hKs : ∀ i, IsConvexBody (Ks i) := fun i => (hmax i).1.1.2.1
  intro K' hK'
  have hbound : ∀ i, sofaArea ω K' ≤
      area (Ks i) - area (polyNiche (dyadicAngleSet ω hω (k i)) (Ks i)) := by
    intro i
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
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev1 := mpc_area_usc hcap.2.1 hKs hlim (half_pos hε)
  have hNs : ∀ᶠ i in atTop,
      polyNiche (dyadicAngleSet ω hω (k i)) (Ks i) ⊆ mpcOuter univ (supp K) 1 := by
    filter_upwards [mpc_eventually_subset_outer hcap.2.1 hKs hlim one_pos] with i hi
    exact (theorem3_4_10 (hmax i)).trans hi
  have hev2 := mpc_area_lsc (N := niche K ω)
    (fun p hp => mpc_niche_eventually hω hcap.2.1 hk hKs hlim hp)
    (mpc_isBounded_outer hcap.2.1 1) hNs (half_pos hε)
  obtain ⟨i, hi1, hi2⟩ := (hev1.and hev2).exists
  have := hbound i
  have e : sofaArea ω K = area K - area (niche K ω) := rfl
  rw [e]
  linarith

/-- Translations preserve the area. -/
lemma mpc_volume_preimage_add (S : Set (ℝ × ℝ)) (v : ℝ × ℝ) :
    MeasureTheory.volume ((fun p => p + v) ⁻¹' S) = MeasureTheory.volume S := by
  have : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).IsAddRightInvariant :=
    (inferInstance : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      MeasureTheory.volume).IsAddRightInvariant)
  exact MeasureTheory.measure_preimage_add_right _ v S

/-- A translate of a moving sofa with rotation angle `ω` is a moving sofa with rotation angle `ω`. -/
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
  have harea : area S' = area ((fun p => p + v) '' S') := by
    simp only [area]
    rw [image_add_right, mpc_volume_preimage_add]
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
