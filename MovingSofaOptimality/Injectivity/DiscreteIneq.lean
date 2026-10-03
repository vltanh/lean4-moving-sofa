module

public import MovingSofaOptimality.Injectivity.ArmLengths
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The inequality on maximum polygon caps (§6.3)

Definitions 6.3.1–6.3.4, Lemmas 6.3.1 (`lem:leg-bounded`), 6.3.2 (`lem:leg-computation`) and
Theorem 6.3.3 (`thm:balanced-discrete-ineq`).

The uniform angle sets `Θ_n` of Definition 6.3.1 with `n = 2^(k+1)` are `dyadicAngleSet (π/2) _ k`,
and a "maximum polygon cap with `n` steps of step size `δ = (π/2)/n`" (Definition 6.3.2) is a
maximum polygon cap with that angle set.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace MovingSofaOptimality

lemma pi_div_two_mem_Ioc : π / 2 ∈ Ioc 0 (π / 2) := ⟨by positivity, le_rfl⟩

/-- The uniform angle set `Θ_n` of rotation angle `π/2` with `n = 2^(k+1)` steps
(Definition 6.3.1, `def:right-angle-set`). -/
noncomputable def rightAngleSet (k : ℕ) : AngleSet := dyadicAngleSet (π / 2) pi_div_two_mem_Ioc k

/-- The step size `δ = (π/2)/n` with `n = 2^(k+1)` (Definition 6.3.2). -/
noncomputable def stepSize (k : ℕ) : ℝ := (π / 2) / 2 ^ (k + 1)

/-! ### Consecutive normal angles of a convex body -/

/-- A sufficient condition for an angle `x` to lie outside `(a, b)` modulo `2π`, in the form used
below. -/
lemma inj_not_between {x a b : ℝ}
    (h : (a - π ≤ x ∧ x ≤ a) ∨ (b ≤ x ∧ x ≤ b + π) ∨ (a + π ≤ x ∧ x ≤ a + 2 * π) ∨
      (b - 2 * π ≤ x ∧ x ≤ b - π)) :
    ¬ (0 < sin (x - a) ∧ sin (x - b) < 0) := by
  rintro ⟨h1, h2⟩
  rcases h with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
  · have := sin_nonpos_of_nonpos_of_neg_pi_le (x := x - a) (by linarith) (by linarith)
    linarith
  · have := sin_nonneg_of_nonneg_of_le_pi (x := x - b) (by linarith) (by linarith)
    linarith
  · have e : sin (x - a) = -sin (x - a - π) := by
      rw [sin_sub_pi]; ring
    have := sin_nonneg_of_nonneg_of_le_pi (x := x - a - π) (by linarith) (by linarith)
    linarith
  · have e : sin (x - b) = -sin (x - b + π) := by
      rw [sin_add_pi]; ring
    have := sin_nonpos_of_nonpos_of_neg_pi_le (x := x - b + π) (by linarith) (by linarith)
    linarith

/-- **Vertices between consecutive normal angles.** Let `K` be a convex body which is an
intersection of closed half-planes, none of whose normal angles lies strictly between `a` and `b`
(in the sense of `inj_not_between`), where `a < b < a + π`. Then the supporting lines `l_K(a)` and
`l_K(b)` meet at a point `q = v_K(a, b)` of `K`, which is the vertex `v_K⁺(a) = v_K⁻(b)` and the
only point of `e_K(s)` for `s ∈ (a, b)`. -/
lemma inj_consecutive {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {ι : Type} {t c : ι → ℝ}
    (hKe : K = ⋂ i, halfMinus (t i) (c i)) {a b : ℝ} (hab : a < b) (hba : b < a + π)
    (hA : ∀ i, ¬ (0 < sin (t i - a) ∧ sin (t i - b) < 0)) :
    vint K a b ∈ K ∧ vplus K a = vint K a b ∧ vminus K b = vint K a b ∧
      ∀ s ∈ Ioo a b, supp K s = dot (vint K a b) (uvec s) ∧ vplus K s = vint K a b ∧
        vminus K s = vint K a b := by
  set q := vint K a b with hq
  have hsab : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsba : sin (a - b) = -sin (b - a) := by rw [← sin_neg, neg_sub]
  have hqa : dot q (uvec a) = supp K a := vint_mem_line_left K a b
  have hqb : dot q (uvec b) = supp K b := vint_mem_line_right K hsab.ne'
  obtain ⟨Pa, hPaK, hPa⟩ := exists_dot_eq_supp hK.2.1 hK.1 a
  obtain ⟨Pb, hPbK, hPb⟩ := exists_dot_eq_supp hK.2.1 hK.1 b
  -- `q ∈ K`
  have hqK : q ∈ K := by
    rw [hKe, mem_iInter]
    intro i
    by_contra hcon
    simp only [halfMinus, mem_ofPred_eq, not_le] at hcon
    have hPai : Pa ∈ halfMinus (t i) (c i) := by rw [hKe] at hPaK; exact mem_iInter.1 hPaK i
    have hPbi : Pb ∈ halfMinus (t i) (c i) := by rw [hKe] at hPbK; exact mem_iInter.1 hPbK i
    simp only [halfMinus, mem_ofPred_eq] at hPai hPbi
    -- `Pa = q + α v_a` with `α ≤ 0`
    have ea := inj_eq_add_smul_vvec (p := Pa) (q := q) (t := a) (by rw [hPa, hqa])
    have eb := inj_eq_add_smul_vvec (p := Pb) (q := q) (t := b) (by rw [hPb, hqb])
    set α := dot (Pa - q) (vvec a)
    set β := dot (Pb - q) (vvec b)
    have h1 : dot Pa (uvec b) ≤ supp K b := dot_le_supp hK.2.1 hPaK b
    have h2 : dot Pb (uvec a) ≤ supp K a := dot_le_supp hK.2.1 hPbK a
    rw [ea, dot_add_left, dot_smul_left, dot_vvec_uvec', hqb] at h1
    rw [eb, dot_add_left, dot_smul_left, dot_vvec_uvec', hqa] at h2
    rw [ea, dot_add_left, dot_smul_left, dot_vvec_uvec'] at hPai
    rw [eb, dot_add_left, dot_smul_left, dot_vvec_uvec'] at hPbi
    rw [hsba] at h2
    have hα : α ≤ 0 := by nlinarith
    have hβ : 0 ≤ β := by nlinarith
    apply hA i
    constructor
    · by_contra hneg
      rw [not_lt] at hneg
      nlinarith
    · by_contra hneg
      rw [not_lt] at hneg
      nlinarith
  -- every point `p` of `K` satisfies `p · u_s ≤ q · u_s` for `s ∈ [a, b]`
  have hle : ∀ s ∈ Icc a b, ∀ p ∈ K, dot p (uvec s) ≤ dot q (uvec s) := by
    intro s hs p hp
    have hs1 : 0 ≤ sin (b - s) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.2])
      (by linarith [hs.1])
    have hs2 : 0 ≤ sin (s - a) := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1])
      (by linarith [hs.2])
    have hpa : dot p (uvec a) ≤ dot q (uvec a) := hqa ▸ dot_le_supp hK.2.1 hp a
    have hpb : dot p (uvec b) ≤ dot q (uvec b) := hqb ▸ dot_le_supp hK.2.1 hp b
    have c1 := dot_uvec_comb p a b s
    have c2 := dot_uvec_comb q a b s
    have : sin (b - a) * dot p (uvec s) ≤ sin (b - a) * dot q (uvec s) := by
      rw [c1, c2]
      exact add_le_add (mul_le_mul_of_nonneg_left hpa hs1) (mul_le_mul_of_nonneg_left hpb hs2)
    exact le_of_mul_le_mul_left this hsab
  have hsupp : ∀ s ∈ Icc a b, supp K s = dot q (uvec s) := by
    intro s hs
    obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hK.2.1 hK.1 s
    exact le_antisymm (hps ▸ hle s hs p hp) (dot_le_supp hK.2.1 hqK s)
  -- the edges
  have hedge_a : ∀ p ∈ edge K a, dot p (vvec a) ≤ dot q (vvec a) := by
    rintro p ⟨hp, hpl⟩
    have hpa : dot p (uvec a) = dot q (uvec a) := by rw [hqa]; exact hpl
    have e := inj_eq_add_smul_vvec hpa
    have h1 : dot p (uvec b) ≤ dot q (uvec b) := hqb ▸ dot_le_supp hK.2.1 hp b
    rw [e, dot_add_left, dot_smul_left, dot_vvec_uvec'] at h1
    have h3 : dot (p - q) (vvec a) ≤ 0 := by nlinarith
    rw [dot_sub_left] at h3; linarith
  have hedge_b : ∀ p ∈ edge K b, dot q (vvec b) ≤ dot p (vvec b) := by
    rintro p ⟨hp, hpl⟩
    have hpb : dot p (uvec b) = dot q (uvec b) := by rw [hqb]; exact hpl
    have e := inj_eq_add_smul_vvec hpb
    have h1 : dot p (uvec a) ≤ dot q (uvec a) := hqa ▸ dot_le_supp hK.2.1 hp a
    rw [e, dot_add_left, dot_smul_left, dot_vvec_uvec', hsba] at h1
    have h3 : 0 ≤ dot (p - q) (vvec b) := by nlinarith
    rw [dot_sub_left] at h3; linarith
  have hq_edge : ∀ s ∈ Icc a b, q ∈ edge K s := fun s hs =>
    ⟨hqK, by simp only [suppLine, line, mem_ofPred_eq]; exact (hsupp s hs).symm⟩
  -- `q` is recovered from its coordinates
  have hq_eq : ∀ s ∈ Icc a b, supp K s • uvec s + dot q (vvec s) • vvec s = q := by
    intro s hs
    rw [hsupp s hs]; exact (eq_dot_uvec_smul_add q s).symm
  have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  refine ⟨hqK, ?_, ?_, ?_⟩
  · rw [vplus]
    have : sSup ((fun p => dot p (vvec a)) '' edge K a) = dot q (vvec a) :=
      IsGreatest.csSup_eq ⟨⟨q, hq_edge a ha_mem, rfl⟩, by rintro _ ⟨p, hp, rfl⟩; exact hedge_a p hp⟩
    rw [this, hq_eq a ha_mem]
  · rw [vminus]
    have : sInf ((fun p => dot p (vvec b)) '' edge K b) = dot q (vvec b) :=
      IsLeast.csInf_eq ⟨⟨q, hq_edge b hb_mem, rfl⟩, by rintro _ ⟨p, hp, rfl⟩; exact hedge_b p hp⟩
    rw [this, hq_eq b hb_mem]
  · intro s hs
    have hsI : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
    -- the edge `e_K(s)` is `{q}`
    have hsing : edge K s = {q} := by
      ext p
      simp only [mem_singleton_iff]
      constructor
      · rintro ⟨hp, hpl⟩
        have hps : dot p (uvec s) = dot q (uvec s) := by
          rw [← hsupp s hsI]; exact hpl
        have hs1 : 0 < sin (b - s) := sin_pos_of_pos_of_lt_pi (by linarith [hs.2])
          (by linarith [hs.1])
        have hs2 : 0 < sin (s - a) := sin_pos_of_pos_of_lt_pi (by linarith [hs.1])
          (by linarith [hs.2])
        have hpa : dot p (uvec a) ≤ dot q (uvec a) := hqa ▸ dot_le_supp hK.2.1 hp a
        have hpb : dot p (uvec b) ≤ dot q (uvec b) := hqb ▸ dot_le_supp hK.2.1 hp b
        have c1 := dot_uvec_comb p a b s
        have c2 := dot_uvec_comb q a b s
        have hpa' : dot p (uvec a) = dot q (uvec a) := by nlinarith
        have hpb' : dot p (uvec b) = dot q (uvec b) := by nlinarith
        exact eq_of_dot_uvec_eq hsab.ne' hpa' hpb'
      · rintro rfl; exact hq_edge s hsI
    refine ⟨hsupp s hsI, ?_, ?_⟩
    · rw [vplus, hsing, image_singleton, csSup_singleton, hq_eq s hsI]
    · rw [vminus, hsing, image_singleton, csInf_singleton, hq_eq s hsI]

/-! ### The uniform angle sets `Θ_n` -/

lemma inj_stepSize_pos (k : ℕ) : 0 < stepSize k := by unfold stepSize; positivity

/-- The step sizes tend to zero along every strictly increasing sequence of levels. -/
lemma tendsto_stepSize {k : ℕ → ℕ} (hk : StrictMono k) :
    Tendsto (fun n => stepSize (k n)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => (2 : ℝ) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)
  exact (tendsto_const_nhds.div_atTop hpow).comp hk.tendsto_atTop

lemma inj_two_pow_mul_stepSize (k : ℕ) : (2 : ℝ) ^ (k + 1) * stepSize k = π / 2 := by
  unfold stepSize; field_simp

/-- `δ ≤ π/4`. -/
lemma inj_stepSize_le (k : ℕ) : stepSize k ≤ π / 4 := by
  have h := inj_two_pow_mul_stepSize k
  have h2 : (2 : ℝ) ≤ 2 ^ (k + 1) := le_self_pow₀ one_le_two (Nat.succ_ne_zero k)
  have hd := inj_stepSize_pos k
  nlinarith [pi_pos]

@[simp] lemma inj_rightAngleSet_ω (k : ℕ) : (rightAngleSet k).ω = π / 2 := rfl

/-- `Θ_n = {jδ : 0 < j < n}`. -/
lemma inj_mem_angles {k : ℕ} {t : ℝ} :
    t ∈ (rightAngleSet k).angles ↔ ∃ j : ℕ, 0 < j ∧ j < 2 ^ (k + 1) ∧ t = j * stepSize k := by
  change t ∈ (Finset.Ioo 0 (2 ^ (k + 1))).image
    (fun i : ℕ => (i : ℝ) * (π / 2) / ((2 ^ (k + 1) : ℕ) : ℝ)) ↔ _
  simp only [Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    refine ⟨j, h1, h2, ?_⟩
    unfold stepSize; push_cast; ring
  · rintro ⟨j, h1, h2, rfl⟩
    refine ⟨j, ⟨h1, h2⟩, ?_⟩
    unfold stepSize; push_cast; ring

/-- The normal angles of a polygon cap with angle set `Θ_n` are the multiples `jδ` of the step
size in `[δ, π]`, and `3π/2`. -/
lemma inj_capAngles {k : ℕ} {x : ℝ} (hx : x ∈ (rightAngleSet k).capAngles) :
    (∃ j : ℕ, 1 ≤ j ∧ j + 1 ≤ 2 * 2 ^ (k + 1) ∧ x = j * stepSize k) ∨ x = 3 * π / 2 := by
  have hn := inj_two_pow_mul_stepSize k
  simp only [AngleSet.capAngles, AngleSet.diamond, inj_rightAngleSet_ω, mem_union, mem_image,
    Finset.mem_coe, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with ((hx | ⟨y, hy, rfl⟩) | hx | hx) | hx | hx
  · obtain ⟨j, h1, h2, rfl⟩ := inj_mem_angles.1 hx
    exact Or.inl ⟨j, h1, by omega, rfl⟩
  · obtain ⟨j, h1, h2, rfl⟩ := inj_mem_angles.1 hy
    have := @Nat.one_le_two_pow (k + 1)
    refine Or.inl ⟨j + 2 ^ (k + 1), by omega, by omega, ?_⟩
    push_cast; rw [← hn]; ring
  · have := @Nat.one_le_two_pow (k + 1)
    refine Or.inl ⟨2 ^ (k + 1), Nat.one_le_two_pow, by omega, ?_⟩
    push_cast; rw [hx, ← hn]
  · have := @Nat.one_le_two_pow (k + 1)
    refine Or.inl ⟨2 ^ (k + 1), Nat.one_le_two_pow, by omega, ?_⟩
    push_cast; rw [hx, ← hn]
  · right; rw [hx]; ring
  · right; exact hx

/-- `inj_consecutive` for a polygon cap with angle set `Θ_n` and two consecutive angles
`a = mδ`, `a + δ` of the grid `δℤ ∩ [0, π]`. -/
lemma inj_polygon_consecutive {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {m : ℕ} (hm : m + 1 ≤ 2 * 2 ^ (k + 1)) {a : ℝ} (ha : a = m * stepSize k) :
    vint K a (a + stepSize k) ∈ K ∧ vplus K a = vint K a (a + stepSize k) ∧
      vminus K (a + stepSize k) = vint K a (a + stepSize k) ∧
      ∀ s ∈ Ioo a (a + stepSize k), supp K s = dot (vint K a (a + stepSize k)) (uvec s) ∧
        vplus K s = vint K a (a + stepSize k) ∧ vminus K s = vint K a (a + stepSize k) := by
  obtain ⟨ι, t, c, ht, hKe⟩ := hK.2
  have hδ := inj_stepSize_pos k
  have hδ4 := inj_stepSize_le k
  have hn := inj_two_pow_mul_stepSize k
  have hm' : (m : ℝ) + 1 ≤ 2 * 2 ^ (k + 1) := by exact_mod_cast hm
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haπ : a + stepSize k ≤ π := by rw [ha]; nlinarith
  refine inj_consecutive hK.1.2.1 hKe (by linarith) (by linarith [pi_pos]) (fun i => ?_)
  apply inj_not_between
  rcases inj_capAngles (ht i) with ⟨j, hj1, hj2, hj⟩ | h3
  · have hj2' : (j : ℝ) + 1 ≤ 2 * 2 ^ (k + 1) := by exact_mod_cast hj2
    have hjδ : t i ≤ π - stepSize k := by rw [hj]; nlinarith
    have hj0 : stepSize k ≤ t i := by
      rw [hj]; have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      nlinarith
    rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · left
      have : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 hjm
      refine ⟨by linarith, ?_⟩
      rw [hj, ha]; nlinarith
    · right; left
      have : (m : ℝ) + 1 ≤ j := by exact_mod_cast hjm
      refine ⟨?_, by linarith⟩
      rw [hj, ha]; nlinarith
  · rw [h3]
    rcases Nat.lt_or_ge m (2 ^ (k + 1)) with hmn | hmn
    · right; right; left
      have : (m : ℝ) + 1 ≤ 2 ^ (k + 1) := by exact_mod_cast hmn
      constructor
      · rw [ha]; nlinarith
      · linarith [pi_pos]
    · right; left
      have : (2 : ℝ) ^ (k + 1) ≤ m := by exact_mod_cast hmn
      constructor
      · linarith
      · rw [ha]; nlinarith

/-- For a polygon cap with angle set `Θ_n`, the edge `e_K(0)` is a single point. -/
lemma inj_polygon_vplus_zero {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K) :
    vplus K 0 = vminus K 0 := by
  obtain ⟨ι, t, c, ht, hKe⟩ := hK.2
  have hδ := inj_stepSize_pos k
  have hδ4 := inj_stepSize_le k
  have hn := inj_two_pow_mul_stepSize k
  have h := inj_consecutive (a := -(π / 2)) (b := stepSize k) hK.1.2.1 hKe
    (by linarith [pi_pos]) (by linarith [pi_pos]) (fun i => ?_)
  · obtain ⟨-, -, -, h4⟩ := h
    have h0 := h4 0 ⟨by linarith [pi_pos], hδ⟩
    rw [h0.2.1, h0.2.2]
  · apply inj_not_between
    rcases inj_capAngles (ht i) with ⟨j, hj1, hj2, hj⟩ | h3
    · right; left
      have hj2' : (j : ℝ) + 1 ≤ 2 * 2 ^ (k + 1) := by exact_mod_cast hj2
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      constructor
      · rw [hj]; nlinarith
      · rw [hj]; nlinarith
    · right; right; left
      rw [h3]; constructor <;> linarith [pi_pos]

/-- For a cap with rotation angle `π/2`, the endpoints of the supporting lines `l_K(-π/2)` and
`l_K(0)` meet at `A_K⁻(0) = (h_K(0), 0)`, which is also `v_K⁺(s)` for `s ∈ [-π/2, 0)`. -/
lemma inj_cap_consecutive {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    vminus K 0 = (supp K 0, 0) ∧ vplus K (-(π / 2)) = (supp K 0, 0) ∧
      ∀ s ∈ Ioo (-(π / 2)) 0, vplus K s = (supp K 0, 0) := by
  obtain ⟨ι, t, c, ht, hKe⟩ := hK.2.2.2.2.2.2
  have hq : vint K (-(π / 2)) 0 = (supp K 0, 0) := by
    have h1 : supp K (-(π / 2)) = 0 := by
      rw [← supp_add_two_pi, show -(π / 2) + 2 * π = 3 * π / 2 by ring]; exact hK.2.2.2.2.2.1
    simp [vint, h1, uvec, vvec]
  have h := inj_consecutive (a := -(π / 2)) (b := 0) hK.2.1 hKe
    (by linarith [pi_pos]) (by linarith [pi_pos]) (fun i => ?_)
  · rw [hq] at h
    exact ⟨h.2.2.1, h.2.1, fun s hs => (h.2.2.2 s hs).2.1⟩
  · apply inj_not_between
    have hti := ht i
    simp only [jSet, mem_union, mem_Icc, mem_insert_iff, mem_singleton_iff] at hti
    rcases hti with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h3 | h3
    · right; left; constructor <;> linarith [pi_pos]
    · right; left; constructor <;> linarith [pi_pos]
    · right; right; left; rw [h3]; constructor <;> linarith [pi_pos]
    · right; right; left; rw [h3]; constructor <;> linarith [pi_pos]

/-! ### Atoms of the surface area measure -/

/-- If `v_K⁺(t) = v_K⁻(t)`, then `σ_K` has no atom at `t`. -/
lemma inj_sigmaAt_eq_zero {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ}
    (h : vplus K t = vminus K t) : sigmaAt K t = 0 := by
  rw [sigmaAt_eq_dot_sub hK, h, sub_self]

/-- If `v_K⁺(t) = v_K⁻(t)`, then `σ_K({t}) = 0`. -/
lemma inj_sigma_singleton_eq_zero {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ}
    (h : vplus K t = vminus K t) : sigma K {t} = 0 := by
  have h0 := inj_sigmaAt_eq_zero hK h
  rw [sigmaAt, ENNReal.toReal_eq_zero_iff] at h0
  exact h0.resolve_right measure_singleton_lt_top.ne

/-- The half-plane `H_K^b(t) = H₊(t, h_K(t) - 1)` above the inner wall `b_K(t)`
(Definition 6.3.3, `def:upper-half-planes`). -/
def halfB (K : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := halfPlus t (supp K t - 1)

/-- The half-plane `H_K^d(t) = H₊(t + π/2, h_K(t + π/2) - 1)` above the inner wall `d_K(t)`
(Definition 6.3.3). -/
def halfD (K : Set (ℝ × ℝ)) (t : ℝ) : Set (ℝ × ℝ) := halfPlus (t + π / 2) (supp K (t + π / 2) - 1)

/-! ### Lemma 6.3.1 -/

/-- A cap with rotation angle `π/2` lies in the strip `H = ℝ × [0, 1]`. -/
lemma inj_cap_strip {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {p : ℝ × ℝ} (hp : p ∈ K) :
    0 ≤ p.2 ∧ p.2 ≤ 1 :=
  (mem_para_iff.1 (hK.subset_para hp)).1

/-- `|w|² = (w · u_t)² + (w · v_t)²`. -/
lemma inj_dot_self_eq (w : ℝ × ℝ) (t : ℝ) :
    dot w w = dot w (uvec t) ^ 2 + dot w (vvec t) ^ 2 := by
  simp only [dot, uvec, vvec]
  linear_combination (-(w.1 ^ 2 + w.2 ^ 2)) * sin_sq_add_cos_sq t

/-- The coordinates of `v_K⁺(t) - C_K⁺(t)` in the frame `u_t, v_t` are `(g_K⁺(t), -f_K⁺(t))`. -/
lemma inj_dot_vplus_sub_cPlus (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vplus K t - cPlus K t) (uvec t) = gPlus K t ∧
      dot (vplus K t - cPlus K t) (vvec t) = -fPlus K t := by
  constructor
  · rw [gPlus, dot_sub_left, dot_sub_left, inj_dot_outerCorner_uvec, dot_vplus_uvec]
  · rw [inj_fPlus_eq, dot_sub_left, inj_dot_cPlus_vvec]; ring

/-- The coordinates of `v_K⁻(t) - C_K⁻(t)` in the frame `u_t, v_t` are `(g_K⁻(t), -f_K⁻(t))`. -/
lemma inj_dot_vminus_sub_cMinus (K : Set (ℝ × ℝ)) (t : ℝ) :
    dot (vminus K t - cMinus K t) (uvec t) = gMinus K t ∧
      dot (vminus K t - cMinus K t) (vvec t) = -fMinus K t := by
  constructor
  · rw [gMinus, dot_sub_left, dot_sub_left, inj_dot_outerCorner_uvec, dot_vminus_uvec]
  · rw [inj_fMinus_eq, dot_sub_left, inj_dot_cMinus_vvec]; ring

/-- The arm lengths `f_K^±` and `g_K^±` are nonnegative. -/
lemma inj_arm_nonneg {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    0 ≤ fPlus K t ∧ 0 ≤ fMinus K t ∧ 0 ≤ gPlus K t ∧ 0 ≤ gMinus K t := by
  have hA := (vplus_mem_edge hK t).1
  have hA' := (vminus_mem_edge hK t).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inj_fPlus_eq]
    have := dot_le_supp hK.2.1 hA (t + π / 2)
    rw [uvec_add_pi_div_two] at this; linarith
  · rw [inj_fMinus_eq]
    have := dot_le_supp hK.2.1 hA' (t + π / 2)
    rw [uvec_add_pi_div_two] at this; linarith
  · rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec]
    have := dot_le_supp hK.2.1 (vplus_mem_edge hK (t + π / 2)).1 t
    rw [cPlus]; linarith
  · rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec]
    have := dot_le_supp hK.2.1 (vminus_mem_edge hK (t + π / 2)).1 t
    rw [cMinus]; linarith

/-- If the diameter of a convex body is at most `5` in the sense `|p - q|² ≤ 25`, its arm lengths
are at most `5`. -/
lemma inj_arm_le_of_diam {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hd : ∀ p ∈ K, ∀ q ∈ K, dot (p - q) (p - q) ≤ 25) (t : ℝ) :
    fPlus K t ≤ 5 ∧ fMinus K t ≤ 5 ∧ gPlus K t ≤ 5 ∧ gMinus K t ≤ 5 := by
  have hA := (vplus_mem_edge hK t).1
  have hA' := (vminus_mem_edge hK t).1
  have hC := (vplus_mem_edge hK (t + π / 2)).1
  have hC' := (vminus_mem_edge hK (t + π / 2)).1
  have e1 := inj_dot_self_eq (vplus K t - cPlus K t) t
  have e2 := inj_dot_self_eq (vminus K t - cMinus K t) t
  rw [(inj_dot_vplus_sub_cPlus K t).1, (inj_dot_vplus_sub_cPlus K t).2] at e1
  rw [(inj_dot_vminus_sub_cMinus K t).1, (inj_dot_vminus_sub_cMinus K t).2] at e2
  have d1 := hd _ hA _ hC
  have d2 := hd _ hA' _ hC'
  rw [cPlus] at e1; rw [cMinus] at e2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **Lemma 6.3.1** (`lem:leg-bounded`). A maximum polygon cap with `n` steps has diameter at most
`5`; consequently its arm lengths are at most `5`. -/
theorem lemma6_3_1 {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) :
    (∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ 5) ∧
      ∀ t ∈ Icc 0 (π / 2), fPlus K t ≤ 5 ∧ fMinus K t ≤ 5 ∧ gPlus K t ≤ 5 ∧ gMinus K t ≤ 5 := by
  have hcap : IsCap K (π / 2) := hK.1.1
  have hKc : IsConvexBody K := hcap.2.1
  have hδ := inj_stepSize_pos k
  have hn := inj_two_pow_mul_stepSize k
  -- `π/4 ∈ Θ_n`
  have hπ4 : π / 4 ∈ (rightAngleSet k).angles := by
    refine inj_mem_angles.2 ⟨2 ^ k, by positivity, by
      rw [pow_succ]; have := @Nat.one_le_two_pow k; omega, ?_⟩
    have : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [this] at hn
    push_cast; linarith
  -- the inner corner `x_K(π/4)` has height at most one
  set X := innerCorner K (π / 4) with hXdef
  have hX : X = (supp K (π / 4) - 1) • uvec (π / 4) + (supp K (π / 4 + π / 2) - 1) • vvec (π / 4) :=
    proposition2_2_2_innerCorner K (π / 4)
  have hXu : dot X (uvec (π / 4)) = supp K (π / 4) - 1 := by
    rw [hX]; simp [dot_add_left, dot_smul_left]
  have hXv : dot X (vvec (π / 4)) = supp K (π / 4 + π / 2) - 1 := by
    rw [hX]; simp [dot_add_left, dot_smul_left]
  have hs4 : 0 < sin (π / 4) := by rw [sin_pi_div_four]; positivity
  have hc4 : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
  have hX2 : X.2 ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    set ε := (X.2 - 1) / 2 with hε
    set p : ℝ × ℝ := (X.1, X.2 - ε) with hp
    have hdotp : ∀ w : ℝ × ℝ, dot p w = dot X w - ε * w.2 := by
      intro w; simp only [dot, hp]; ring
    have hpN : p ∈ polyNiche (rightAngleSet k) K := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [halfPlus, mem_ofPred_eq, inj_rightAngleSet_ω, dot, uvec,
          cos_pi_div_two, sin_pi_div_two]
        linarith
      · simp only [halfPlus, mem_ofPred_eq, dot, uvec, cos_pi_div_two, sin_pi_div_two]
        linarith
      · rw [mem_iUnion₂]
        refine ⟨π / 4, hπ4, ?_⟩
        rw [proposition2_2_2_qMinus]
        refine ⟨?_, ?_⟩
        · simp only [halfMinusOpen, mem_ofPred_eq]
          rw [hdotp, hXu]
          simp only [uvec_snd]
          nlinarith
        · simp only [halfMinusOpen, mem_ofPred_eq]
          rw [hdotp, uvec_add_pi_div_two, hXv]
          simp only [vvec_snd]
          nlinarith
    have := (inj_cap_strip hcap (theorem3_4_10 hK hpN)).2
    simp only [hp] at this
    linarith
  -- the diameter bound: every point of `K` lies at most `1` beyond `x_K(π/4)` in the directions
  -- `u_{π/4}` and `v_{π/4}`, and in the strip `0 ≤ y ≤ 1`
  have hdiam : ∀ p ∈ K, ∀ q ∈ K, dot (p - q) (p - q) ≤ 25 := by
    have hb : ∀ p ∈ K, dot p (uvec (π / 4)) ≤ dot X (uvec (π / 4)) + 1 ∧
        dot p (vvec (π / 4)) ≤ dot X (vvec (π / 4)) + 1 := by
      intro p hp
      refine ⟨?_, ?_⟩
      · rw [hXu]; linarith [dot_le_supp hKc.2.1 hp (π / 4)]
      · rw [hXv, ← uvec_add_pi_div_two]; linarith [dot_le_supp hKc.2.1 hp (π / 4 + π / 2)]
    intro p hp q hq
    obtain ⟨hp1, hp2⟩ := hb p hp
    obtain ⟨hq1, hq2⟩ := hb q hq
    have sp := inj_cap_strip hcap hp
    have sq := inj_cap_strip hcap hq
    simp only [dot, uvec, vvec, sin_pi_div_four, cos_pi_div_four] at hp1 hp2 hq1 hq2
    set r := √2 / 2 with hr
    have hr0 : 0 < r := by positivity
    have hr2 : r ^ 2 = 1 / 2 := by
      rw [hr, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have hr34 : r < 3 / 4 := by nlinarith
    have hrX : r * X.2 ≤ r := mul_le_of_le_one_right hr0.le hX2
    have hp0 := mul_nonneg hr0.le sp.1
    have hq0 := mul_nonneg hr0.le sq.1
    -- `r |p.1 - q.1| ≤ 2r + 2`, so `(p.1 - q.1)² ≤ (2 + 2√2)² = 12 + 16r`
    have hD1 : r * (p.1 - q.1) ≤ 2 * r + 2 := by linarith
    have hD2 : r * (q.1 - p.1) ≤ 2 * r + 2 := by linarith
    have hD : (p.1 - q.1) ^ 2 ≤ 12 + 16 * r := by
      have h := sq_le_sq' (by linarith) hD1
      have e : (2 * r + 2) ^ 2 = 6 + 8 * r := by ring_nf; rw [hr2]; ring
      rw [mul_pow, hr2, e] at h
      linarith
    have hE : (p.2 - q.2) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).2 (abs_le.2 ⟨by linarith, by linarith⟩)
    simp only [dot, Prod.fst_sub, Prod.snd_sub, ← pow_two]
    linarith
  refine ⟨fun p hp q hq => ?_, fun t _ => inj_arm_le_of_diam hKc hdiam t⟩
  rw [norm2, Real.sqrt_le_iff]
  exact ⟨by norm_num, (hdiam p hp q hq).trans (by norm_num)⟩

/-! ### Lemma 6.3.2 -/

/-- The half-line `b⃗_K(t)` in the coordinates `(h_K(t) - 1) u_t + s v_t` of the line `b_K(t)`. -/
lemma inj_mem_wallBVec {K : Set (ℝ × ℝ)} {t s : ℝ} :
    (supp K t - 1) • uvec t + s • vvec t ∈ wallBVec K t ↔ s ≤ supp K (t + π / 2) - 1 := by
  simp only [mpc_mem_wallBVec, uvec_add_pi_div_two, dot_add_left, dot_smul_left, dot_uvec_self,
    dot_vvec_uvec, dot_uvec_vvec, dot_vvec_self, mul_one, mul_zero, add_zero, zero_add, true_and]

lemma inj_wall_dot_uvec (c t u s : ℝ) :
    dot (c • uvec t + s • vvec t) (uvec u) = c * cos (t - u) + s * sin (u - t) := by
  rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']

lemma inj_wall_dot_vvec (c t u s : ℝ) :
    dot (c • uvec t + s • vvec t) (vvec u) = c * sin (t - u) + s * cos (t - u) := by
  rw [dot_add_left, dot_smul_left, dot_smul_left, dot_uvec_vvec', dot_vvec_vvec]

/-- When the point `(h_K(t) - 1) u_t + s v_t` of the line `b_K(t)` lies in `H_K^d(u)`. -/
lemma inj_mem_halfD {K : Set (ℝ × ℝ)} {t u s : ℝ} :
    (supp K t - 1) • uvec t + s • vvec t ∈ halfD K u ↔
      supp K (u + π / 2) - 1 ≤ (supp K t - 1) * sin (t - u) + s * cos (t - u) := by
  simp only [halfD, halfPlus, mem_ofPred_eq, uvec_add_pi_div_two, inj_wall_dot_vvec]

/-- When the point `(h_K(t) - 1) u_t + s v_t` of the line `b_K(t)` lies in `H_K^b(u)`. -/
lemma inj_mem_halfB {K : Set (ℝ × ℝ)} {t u s : ℝ} :
    (supp K t - 1) • uvec t + s • vvec t ∈ halfB K u ↔
      supp K u - 1 ≤ (supp K t - 1) * cos (t - u) + s * sin (u - t) := by
  simp only [halfB, halfPlus, mem_ofPred_eq, inj_wall_dot_uvec]

/-- Trigonometric facts about the step size `δ ∈ (0, π/4]`. -/
lemma inj_step_trig (k : ℕ) :
    0 < cos (stepSize k) ∧ 0 < sin (stepSize k) ∧ 0 < tan (stepSize k) ∧
      0 < tan (stepSize k / 2) ∧
      tan (stepSize k / 2) * sin (stepSize k) = 1 - cos (stepSize k) := by
  have hδ := inj_stepSize_pos k
  have hδ4 := inj_stepSize_le k
  have hc : 0 < cos (stepSize k) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs : 0 < sin (stepSize k) := sin_pos_of_pos_of_lt_pi hδ (by linarith [pi_pos])
  have hc2 : 0 < cos (stepSize k / 2) :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs2 : 0 < sin (stepSize k / 2) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  refine ⟨hc, hs, ?_, ?_, tan_half_mul_sin hc2.ne'⟩
  · rw [tan_eq_sin_div_cos]; positivity
  · rw [tan_eq_sin_div_cos]; positivity

/-- The vertices at the angle `t ∈ Θ_n` of a polygon cap with angle set `Θ_n`, as intersections of
consecutive supporting lines. -/
lemma inj_polygon_vertices_at {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    vminus K t = vint K (t - stepSize k) t ∧ vplus K t = vint K t (t + stepSize k) ∧
      cMinus K t = vint K (t + π / 2 - stepSize k) (t + π / 2) ∧
      cPlus K t = vint K (t + π / 2) (t + π / 2 + stepSize k) := by
  obtain ⟨j, hj0, hjn, rfl⟩ := inj_mem_angles.1 ht
  have hn := inj_two_pow_mul_stepSize k
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (inj_polygon_consecutive hK (m := j') (by omega)
      (a := ((j' + 1 : ℕ) : ℝ) * stepSize k - stepSize k) (by push_cast; ring)).2.2.1
    rwa [sub_add_cancel] at h
  · exact (inj_polygon_consecutive hK (m := j' + 1) (by omega) rfl).2.1
  · have h := (inj_polygon_consecutive hK (m := 2 ^ (k + 1) + j') (by omega)
      (a := ((j' + 1 : ℕ) : ℝ) * stepSize k + π / 2 - stepSize k)
      (by rw [← hn]; push_cast; ring)).2.2.1
    rwa [sub_add_cancel] at h
  · exact (inj_polygon_consecutive hK (m := 2 ^ (k + 1) + (j' + 1)) (by omega)
      (a := ((j' + 1 : ℕ) : ℝ) * stepSize k + π / 2) (by rw [← hn]; push_cast; ring)).2.1

/-- `g_K⁻(t)` and `g_K⁺(t)` at `t ∈ Θ_n` in terms of the support function. -/
lemma inj_polygon_g_eq {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    gMinus K t = supp K t - supp K (t + π / 2 - stepSize k) * sin (stepSize k) +
        (supp K (t + π / 2) - supp K (t + π / 2 - stepSize k) * cos (stepSize k)) /
          sin (stepSize k) * cos (stepSize k) ∧
      gPlus K t = supp K t + (supp K (t + π / 2 + stepSize k) -
        supp K (t + π / 2) * cos (stepSize k)) / sin (stepSize k) := by
  obtain ⟨-, -, hV1, hV2⟩ := inj_polygon_vertices_at hK ht
  constructor
  · rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec, hV1, vint, dot_add_left, dot_smul_left,
      dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
    have e1 : t + π / 2 - stepSize k - t = π / 2 - stepSize k := by ring
    have e2 : t - (t + π / 2 - stepSize k) = -(π / 2 - stepSize k) := by ring
    have e3 : t + π / 2 - (t + π / 2 - stepSize k) = stepSize k := by ring
    rw [e1, e2, e3, cos_pi_div_two_sub, sin_neg, sin_pi_div_two_sub]
    ring
  · rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, hV2, vint, dot_add_left, dot_smul_left,
      dot_smul_left, dot_uvec_uvec, dot_vvec_uvec']
    have e1 : t + π / 2 - t = π / 2 := by ring
    have e2 : t - (t + π / 2) = -(π / 2) := by ring
    have e3 : t + π / 2 + stepSize k - (t + π / 2) = stepSize k := by ring
    rw [e1, e2, e3, cos_pi_div_two, sin_neg, sin_pi_div_two]
    ring

/-- The parameters of `b⃗_K(t) ∩ H_K^d(t - δ)`. -/
lemma inj_param_minus {K : Set (ℝ × ℝ)} {t δ : ℝ} (hc : 0 < cos δ) :
    {s | (supp K t - 1) • uvec t + s • vvec t ∈ wallBVec K t ∩ halfD K (t - δ)} =
      Icc ((supp K (t + π / 2 - δ) - 1 - (supp K t - 1) * sin δ) / cos δ)
        (supp K (t + π / 2) - 1) := by
  ext s
  simp only [mem_ofPred_eq, mem_inter_iff, inj_mem_wallBVec, inj_mem_halfD, mem_Icc]
  have e1 : t - δ + π / 2 = t + π / 2 - δ := by ring
  have e2 : t - (t - δ) = δ := by ring
  rw [e1, e2, div_le_iff₀ hc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The parameters of `b⃗_K(t) ∩ H_K^d(t + δ)`. -/
lemma inj_param_plus {K : Set (ℝ × ℝ)} {t δ : ℝ} (hc : 0 < cos δ) :
    {s | (supp K t - 1) • uvec t + s • vvec t ∈ wallBVec K t ∩ halfD K (t + δ)} =
      Icc ((supp K (t + π / 2 + δ) - 1 + (supp K t - 1) * sin δ) / cos δ)
        (supp K (t + π / 2) - 1) := by
  ext s
  simp only [mem_ofPred_eq, mem_inter_iff, inj_mem_wallBVec, inj_mem_halfD, mem_Icc]
  have e1 : t + δ + π / 2 = t + π / 2 + δ := by ring
  have e2 : t - (t + δ) = -δ := by ring
  rw [e1, e2, sin_neg, cos_neg, div_le_iff₀ hc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The length of the parameter interval of `inj_param_minus` at `t ∈ Θ_n`. -/
lemma inj_param_minus_length {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    supp K (t + π / 2) - 1 - (supp K (t + π / 2 - stepSize k) - 1 -
        (supp K t - 1) * sin (stepSize k)) / cos (stepSize k) =
      tan (stepSize k) * (gMinus K t - 1 + tan (stepSize k / 2)) := by
  obtain ⟨hc, hs, -, -, hT⟩ := inj_step_trig k
  rw [(inj_polygon_g_eq hK ht).1, tan_eq_sin_div_cos (stepSize k)]
  have hsc := sin_sq_add_cos_sq (stepSize k)
  generalize supp K (t + π / 2 - stepSize k) = A
  generalize supp K (t + π / 2) = B
  generalize supp K t = H
  field_simp
  linear_combination (-1) * hT + A * hsc

/-- The length of the parameter interval of `inj_param_plus` at `t ∈ Θ_n`. -/
lemma inj_param_plus_length {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    supp K (t + π / 2) - 1 - (supp K (t + π / 2 + stepSize k) - 1 +
        (supp K t - 1) * sin (stepSize k)) / cos (stepSize k) =
      tan (stepSize k) * (1 - gPlus K t + tan (stepSize k / 2)) := by
  obtain ⟨hc, hs, -, -, hT⟩ := inj_step_trig k
  rw [(inj_polygon_g_eq hK ht).2, tan_eq_sin_div_cos (stepSize k)]
  generalize supp K (t + π / 2 + stepSize k) = B'
  generalize supp K (t + π / 2) = B
  generalize supp K t = H
  field_simp
  linear_combination (-1) * hT

/-- **Lemma 6.3.2** (`lem:leg-computation`). For a maximum polygon cap with step size `δ` and
`t ∈ Θ`: (1) `𝓗¹(b⃗_K(t) ∩ H_K^d(t - δ)) = tan δ · max(0, g_K⁻(t) - 1 + tan(δ/2))` and
(2) `𝓗¹(b⃗_K(t) ∩ H_K^d(t + δ)) = tan δ · max(0, 1 - g_K⁺(t) + tan(δ/2))`. -/
theorem lemma6_3_2 {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {t : ℝ}
    (ht : t ∈ (rightAngleSet k).angles) :
    lineLength t (supp K t - 1) (wallBVec K t ∩ halfD K (t - stepSize k)) =
        tan (stepSize k) * max 0 (gMinus K t - 1 + tan (stepSize k / 2)) ∧
      lineLength t (supp K t - 1) (wallBVec K t ∩ halfD K (t + stepSize k)) =
        tan (stepSize k) * max 0 (1 - gPlus K t + tan (stepSize k / 2)) := by
  obtain ⟨hc, -, htan, -, -⟩ := inj_step_trig k
  constructor
  · rw [lineLength, inj_param_minus hc, Real.volume_Icc, ENNReal.toReal_ofReal',
      inj_param_minus_length hK.1 ht, mul_max_of_nonneg _ _ htan.le, mul_zero, max_comm]
  · rw [lineLength, inj_param_plus hc, Real.volume_Icc, ENNReal.toReal_ofReal',
      inj_param_plus_length hK.1 ht, mul_max_of_nonneg _ _ htan.le, mul_zero, max_comm]

/-- `k₀(x) = max(|x - 1|, (|x - 1| + 1)/2)` (Definition 6.3.4, `def:magic-function`). -/
noncomputable def k0 (x : ℝ) : ℝ := max |x - 1| ((|x - 1| + 1) / 2)

/-- `m₀(x) = x - k₀(x)` (Definition 6.3.4). -/
noncomputable def m0 (x : ℝ) : ℝ := x - k0 x

/-! ### Theorem 6.3.3 -/

lemma inj_k0_nonneg (x : ℝ) : 0 ≤ k0 x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

/-- `tan x ≤ x + x²` for `x ∈ [0, π/4]`. -/
lemma inj_tan_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π / 4) : tan x ≤ x + x ^ 2 := by
  have hx1 : x ≤ 1 := by linarith [pi_le_four]
  have hc : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
  have hcpos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs : sin x ≤ x := sin_le h0
  rw [tan_eq_sin_div_cos, div_le_iff₀ hcpos]
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-- The predecessor `t - δ` of `t ∈ Θ_n` is in `Θ_n` or is `0`. -/
lemma inj_angles_pred {k : ℕ} {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    t - stepSize k ∈ (rightAngleSet k).angles ∨ t - stepSize k = 0 := by
  obtain ⟨j, hj0, hjn, rfl⟩ := inj_mem_angles.1 ht
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j' with rfl | hj'
  · right; push_cast; ring
  · left; exact inj_mem_angles.2 ⟨j', hj', by omega, by push_cast; ring⟩

/-- The successor `t + δ` of `t ∈ Θ_n` is in `Θ_n` or is `π/2`. -/
lemma inj_angles_succ {k : ℕ} {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    t + stepSize k ∈ (rightAngleSet k).angles ∨ t + stepSize k = π / 2 := by
  obtain ⟨j, hj0, hjn, rfl⟩ := inj_mem_angles.1 ht
  have hn := inj_two_pow_mul_stepSize k
  rcases Nat.lt_or_ge (j + 1) (2 ^ (k + 1)) with hj | hj
  · left; exact inj_mem_angles.2 ⟨j + 1, by omega, hj, by push_cast; ring⟩
  · right
    have : j + 1 = 2 ^ (k + 1) := by omega
    have h' : ((j : ℝ) + 1) = 2 ^ (k + 1) := by exact_mod_cast this
    rw [← hn, ← h']; ring

/-- A point of the boundary of the polygon niche lies in the closed upper half-plane. -/
lemma inj_frontier_niche_snd {Θ : AngleSet} (hω : Θ.ω = π / 2) {K : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    (hx : x ∈ frontier (polyNiche Θ K)) : 0 ≤ x.2 := by
  have hsub : polyNiche Θ K ⊆ {p : ℝ × ℝ | 0 ≤ p.2} := by
    rintro p ⟨⟨hp, -⟩, -⟩
    simpa [halfPlus, dot, uvec, hω] using hp
  exact closure_minimal hsub (isClosed_le continuous_const continuous_snd)
    (frontier_subset_closure hx)

/-- A point `x` of the boundary of the polygon niche above the `x`-axis is not in any of the open
quadrants `Q_K⁻(u)` for `u ∈ Θ ∪ {0, π/2}`. -/
lemma inj_not_mem_qMinus {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {x : ℝ × ℝ} (hx : x ∈ frontier (polyNiche (rightAngleSet k) K)) (hx2 : 0 < x.2) {u : ℝ}
    (hu : u ∈ (rightAngleSet k).angles ∨ u = 0 ∨ u = π / 2) : x ∉ qMinus K u := by
  intro hxq
  have hcap : IsCap K (π / 2) := hK.1
  rcases hu with hu | rfl | rfl
  · apply hx.2
    rw [mem_interior]
    refine ⟨{p : ℝ × ℝ | 0 < p.2} ∩ qMinus K u, ?_, ?_, ⟨hx2, hxq⟩⟩
    · rintro p ⟨hp2, hpq⟩
      have hp2' : (0 : ℝ) ≤ p.2 := le_of_lt hp2
      refine ⟨⟨?_, ?_⟩, mem_iUnion₂.2 ⟨u, hu, hpq⟩⟩ <;>
        simpa [halfPlus, dot, uvec] using hp2'
    · exact (isOpen_lt continuous_const continuous_snd).inter (ms_isOpen_qMinus K u)
  · rw [proposition2_2_2_qMinus] at hxq
    have h := hxq.2
    simp only [halfMinusOpen, mem_ofPred_eq, zero_add, hcap.2.2.2.1, dot, uvec, cos_pi_div_two,
      sin_pi_div_two] at h
    linarith
  · rw [proposition2_2_2_qMinus] at hxq
    have h := hxq.1
    simp only [halfMinusOpen, mem_ofPred_eq, hcap.2.2.2.1, dot, uvec, cos_pi_div_two,
      sin_pi_div_two] at h
    linarith

/-- `σ_K(t)` in terms of the parameters of `b_K(t) ∩ H_K^b(t - δ) ∩ H_K^b(t + δ)`. -/
lemma inj_polygon_sigmaAt_eq {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    ((supp K t - 1) * cos (stepSize k) - supp K (t - stepSize k) + 1) / sin (stepSize k) -
        (supp K (t + stepSize k) - 1 - (supp K t - 1) * cos (stepSize k)) / sin (stepSize k) =
      2 * tan (stepSize k / 2) - sigmaAt K t := by
  obtain ⟨hc, hs, -, -, hT⟩ := inj_step_trig k
  obtain ⟨hV3, hV4, -, -⟩ := inj_polygon_vertices_at hK ht
  have hsc := sin_sq_add_cos_sq (stepSize k)
  rw [sigmaAt_eq_dot_sub hK.1.2.1, hV3, hV4, vint, vint, dot_add_left, dot_add_left,
    dot_smul_left, dot_smul_left, dot_smul_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self,
    dot_uvec_vvec', dot_vvec_vvec]
  have e1 : t + stepSize k - t = stepSize k := by ring
  have e2 : t - (t - stepSize k) = stepSize k := by ring
  have e3 : t - stepSize k - t = -stepSize k := by ring
  rw [e1, e2, e3, sin_neg, cos_neg]
  generalize supp K t = H
  generalize supp K (t - stepSize k) = A
  generalize supp K (t + stepSize k) = B
  field_simp
  linear_combination (-2) * hT + A * hsc

/-- The geometric bound in the proof of Theorem 6.3.3: `σ_K(t) = 𝓗¹(X)` is at most
`𝓗¹(b⃗_K(t) ∩ R) + 𝓗¹(b_K(t) ∩ S)`. -/
lemma inj_sigmaAt_le_geom {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    sigmaAt K t ≤
      max (max (tan (stepSize k) * (gMinus K t - 1 + tan (stepSize k / 2)))
        (tan (stepSize k) * (1 - gPlus K t + tan (stepSize k / 2)))) 0 +
      max (2 * tan (stepSize k / 2) - sigmaAt K t) 0 := by
  obtain ⟨hc, hs, htan, hT0, hT⟩ := inj_step_trig k
  have hKp : IsPolygonCap (rightAngleSet k) K := hK.1
  have hcap : IsCap K (π / 2) := hKp.1
  have htI := (rightAngleSet k).subset t ht
  simp only [inj_rightAngleSet_ω] at htI
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htI.1, pi_pos], htI.2⟩
  have hbal : sigmaAt K t = tau (rightAngleSet k) K t :=
    theorem3_4_9 hK t (Or.inl (Or.inl ht))
  have hlen := (lemma3_4_5_one hKp ht).2.1
  -- the bounds of the parameter intervals
  set s₀ := supp K (t + π / 2) - 1 with hs₀
  set s₁ := (supp K (t + π / 2 - stepSize k) - 1 - (supp K t - 1) * sin (stepSize k)) /
    cos (stepSize k) with hs₁
  set s₁' := (supp K (t + π / 2 + stepSize k) - 1 + (supp K t - 1) * sin (stepSize k)) /
    cos (stepSize k) with hs₁'
  set sp := (supp K (t + stepSize k) - 1 - (supp K t - 1) * cos (stepSize k)) / sin (stepSize k)
    with hsp
  set sm := ((supp K t - 1) * cos (stepSize k) - supp K (t - stepSize k) + 1) / sin (stepSize k)
    with hsm
  set z₀ := -((supp K t - 1) * sin t) / cos t with hz₀
  set P := {s : ℝ | (supp K t - 1) • uvec t + s • vvec t ∈
    frontier (polyNiche (rightAngleSet k) K) ∩ wallBVec K t} with hP
  have hσ : sigmaAt K t = (volume P).toReal := by rw [hbal, ← hlen, lineLength]
  -- the inclusion
  have hincl : P ⊆ ((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) ∪ {z₀} := by
    intro s hsP
    obtain ⟨hxF, hxW⟩ := hsP
    have hsW : s ≤ s₀ := inj_mem_wallBVec.1 hxW
    by_cases hD1 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K (t - stepSize k)
    · have : s ∈ Icc s₁ s₀ := by
        rw [← inj_param_minus hc]; exact ⟨hxW, hD1⟩
      exact Or.inl (Or.inl (Or.inl ⟨le_trans (min_le_left _ _) this.1, this.2⟩))
    by_cases hD2 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K (t + stepSize k)
    · have : s ∈ Icc s₁' s₀ := by
        rw [← inj_param_plus hc]; exact ⟨hxW, hD2⟩
      exact Or.inl (Or.inl (Or.inl ⟨le_trans (min_le_right _ _) this.1, this.2⟩))
    by_cases hD0 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K t
    · rw [inj_mem_halfD, sub_self, sin_zero, cos_zero] at hD0
      exact Or.inl (Or.inl (Or.inr (le_antisymm hsW (by linarith))))
    have hx2 := inj_frontier_niche_snd (inj_rightAngleSet_ω k) hxF
    have hx2e : ((supp K t - 1) • uvec t + s • vvec t).2 = (supp K t - 1) * sin t + s * cos t := by
      simp [uvec, vvec]
    rcases hx2.lt_or_eq with hx2 | hx2
    · left; right
      have hB : ∀ u, (u ∈ (rightAngleSet k).angles ∨ u = 0 ∨ u = π / 2) →
          (supp K t - 1) • uvec t + s • vvec t ∉ halfD K u →
          (supp K t - 1) • uvec t + s • vvec t ∈ halfB K u := by
        intro u hu hnD
        have hq := inj_not_mem_qMinus hKp hxF hx2 hu
        rw [proposition2_2_2_qMinus] at hq
        simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, not_and_or, not_lt] at hq
        rcases hq with hq | hq
        · exact hq
        · exact absurd hq hnD
      have h1 := hB (t + stepSize k) ((inj_angles_succ ht).elim Or.inl (fun h => Or.inr (Or.inr h)))
        hD2
      have h2 := hB (t - stepSize k) ((inj_angles_pred ht).elim Or.inl (fun h => Or.inr (Or.inl h)))
        hD1
      rw [inj_mem_halfB] at h1 h2
      have e1 : t - (t + stepSize k) = -stepSize k := by ring
      have e2 : t + stepSize k - t = stepSize k := by ring
      have e3 : t - (t - stepSize k) = stepSize k := by ring
      have e4 : t - stepSize k - t = -stepSize k := by ring
      rw [e1, e2, cos_neg] at h1
      rw [e3, e4, sin_neg] at h2
      constructor
      · rw [hsp, div_le_iff₀ hs]; linarith
      · rw [hsm, le_div_iff₀ hs]; linarith
    · right
      rw [mem_singleton_iff, hz₀, eq_div_iff hct.ne']
      rw [hx2e] at hx2; linarith
  -- the measure bound
  have hvol : volume P ≤ ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp) := by
    calc volume P ≤ volume (((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) ∪ {z₀}) :=
          measure_mono hincl
      _ ≤ volume ((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) + volume ({z₀} : Set ℝ) :=
          measure_union_le _ _
      _ ≤ (volume (Icc (min s₁ s₁') s₀) + volume ({s₀} : Set ℝ)) + volume (Icc sp sm) + 0 := by
          rw [measure_singleton]
          gcongr
          exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp) := by
          rw [measure_singleton, Real.volume_Icc, Real.volume_Icc, add_zero, add_zero]
  have hreal : sigmaAt K t ≤ max (s₀ - min s₁ s₁') 0 + max (sm - sp) 0 := by
    rw [hσ]
    calc (volume P).toReal ≤ (ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp)).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
            hvol
      _ = _ := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rw [← max_sub_sub_left, inj_param_minus_length hKp ht, inj_param_plus_length hKp ht,
    inj_polygon_sigmaAt_eq hKp ht] at hreal
  exact hreal

/-- **Theorem 6.3.3** (`thm:balanced-discrete-ineq`). There is an absolute constant `C` such that
every maximum polygon cap `K` with `n` steps of step size `δ` satisfies
`σ_K(t) ≤ k₀(g_K⁺(t)) δ + C δ²` for every `t ∈ {0} ∪ Θ_n`. -/
theorem theorem6_3_3 : ∃ C : ℝ, ∀ k : ℕ, ∀ K, IsMaxPolygonCap (rightAngleSet k) K →
    ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
      sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 := by
  refine ⟨7, fun k K hK t ht => ?_⟩
  have hKc : IsConvexBody K := hK.1.1.2.1
  have hδ := inj_stepSize_pos k
  have hδ4 := inj_stepSize_le k
  rcases ht with rfl | ht
  · rw [inj_sigmaAt_eq_zero hKc (inj_polygon_vplus_zero hK.1)]
    have := inj_k0_nonneg (gPlus K 0)
    positivity
  · have hgeom := inj_sigmaAt_le_geom hK ht
    have htI := (rightAngleSet k).subset t ht
    simp only [inj_rightAngleSet_ω] at htI
    -- bounds on the arm lengths
    have hg5 := (lemma6_3_1 hK).2 t ⟨htI.1.le, htI.2.le⟩
    have hg0 := inj_arm_nonneg hKc t
    -- `g_K⁻(t) ≤ g_K⁺(t)`
    have hgmp : gMinus K t ≤ gPlus K t := by
      have h := (proposition2_1_2 hKc (t + π / 2)).2
      have hσ0 : 0 ≤ sigmaAt K (t + π / 2) := ENNReal.toReal_nonneg
      rw [gMinus, gPlus, dot_sub_left, dot_sub_left, cPlus, cMinus, h, dot_add_left, dot_smul_left,
        vvec_add_pi_div_two, dot_neg_left, dot_uvec_self]
      linarith
    -- bounds on `tan δ` and `tan (δ/2)`
    obtain ⟨-, -, htan0, hT0, -⟩ := inj_step_trig k
    have htan := inj_tan_le hδ.le hδ4
    have hT := inj_tan_le (x := stepSize k / 2) (by linarith) (by linarith)
    have hδ1 : stepSize k ≤ 1 := by linarith [pi_le_four]
    set δ := stepSize k with hδdef
    set T := tan (δ / 2) with hTdef
    set M := |gPlus K t - 1| with hM
    have hM4 : M ≤ 4 := by rw [hM, abs_le]; constructor <;> linarith [hg0.2.2.1, hg5.2.2.1]
    have hM0 : 0 ≤ M := abs_nonneg _
    have hMg : gMinus K t - 1 ≤ M := le_trans (by linarith) (le_abs_self (gPlus K t - 1))
    have hMg' : 1 - gPlus K t ≤ M := by rw [hM, abs_sub_comm]; exact le_abs_self _
    -- the first term
    have hfirst : max (max (tan δ * (gMinus K t - 1 + T)) (tan δ * (1 - gPlus K t + T))) 0 ≤
        δ * M + 6 * δ ^ 2 := by
      have hb : tan δ * (M + T) ≤ δ * M + 6 * δ ^ 2 := by
        have h1 : tan δ * (M + T) ≤ (δ + δ ^ 2) * (M + δ) := by
          apply mul_le_mul htan (by nlinarith) (by positivity) (by positivity)
        nlinarith
      refine max_le (max_le ?_ ?_) (by positivity)
      · exact le_trans (mul_le_mul_of_nonneg_left (by linarith) htan0.le) hb
      · exact le_trans (mul_le_mul_of_nonneg_left (by linarith) htan0.le) hb
    have hk0 : M ≤ k0 (gPlus K t) := le_max_left _ _
    have hk0' : (M + 1) / 2 ≤ k0 (gPlus K t) := le_max_right _ _
    rcases le_total (2 * T - sigmaAt K t) 0 with h2 | h2
    · rw [max_eq_right h2] at hgeom
      nlinarith
    · rw [max_eq_left h2] at hgeom
      nlinarith

end MovingSofaOptimality
