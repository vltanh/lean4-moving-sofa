module

public import MovingSofaStability.InteriorBalls

/-!
# Interior balls for a Lipschitz roof under a fixed ceiling

Uncompiled proof source. This is the elementary geometric ingredient for the
middle part of Gerver's sofa. It does not infer the absence of cusps merely
from a piecewise-smooth parametrization: the horizontal Lipschitz estimate and
the positive gap below the ceiling are explicit hypotheses.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

theorem norm2_le_abs_add (p : Point) : norm2 p ≤ |p.1| + |p.2| := by
  have hs := norm2_sq p
  simp only [dot] at hs
  have hprod := mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2)
  nlinarith [norm2_nonneg p, abs_nonneg p.1, abs_nonneg p.2, sq_abs p.1, sq_abs p.2]

def roofStrip (a b : ℝ) (γ : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ γ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- A low point can be shifted up and toward the farther side to make room for a ball. -/
theorem roofStrip_low_ball {a b H L : ℝ} {γ : ℝ → ℝ}
    (hab : a < b) (hH : H < 1) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|)
    {p : Point} (hp : p ∈ roofStrip a b γ) (hpy : p.2 ≤ (1 + H) / 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρwidth : ρ ≤ b - a) (hρheight : ρ ≤ (1 - H) / 2) :
    ∃ z, euclideanBall z (ρ / (4 * (L + 2))) ⊆
      roofStrip a b γ ∩ euclideanBall p ρ := by
  let w := ρ / (4 * (L + 2))
  have hw : 0 < w := by dsimp [w]; positivity
  have hwid : 4 * (L + 2) * w = ρ := by
    dsimp [w]
    field_simp
  have hw8 : 8 * w ≤ ρ := by nlinarith
  have hspace : 6 * w ≤ b - a := by linarith
  have hvertical : (3 * L + 3) * w ≤ ρ := by nlinarith
  have hdist : (3 * L + 5) * w ≤ ρ := by nlinarith
  let x := if p.1 ≤ (a + b) / 2 then p.1 + 2 * w else p.1 - 2 * w
  let z : Point := (x, p.2 + (3 * L + 2) * w)
  have hx : |x - p.1| = 2 * w := by
    dsimp [x]
    split_ifs
    · rw [add_sub_cancel_left, abs_of_pos (by positivity)]
    · have he : p.1 - 2 * w - p.1 = -(2 * w) := by ring
      rw [he, abs_neg, abs_of_pos (by positivity)]
  have hxleft : a + w ≤ x := by
    dsimp [x]
    split_ifs with hmid
    · linarith [hp.1.1]
    · have hgt := not_le.mp hmid
      linarith
  have hxright : x + w ≤ b := by
    dsimp [x]
    split_ifs with hmid
    · linarith
    · linarith [hp.1.2]
  refine ⟨z, ?_⟩
  intro q hq
  change euclideanDist z q ≤ w at hq
  have hdx : |z.1 - q.1| ≤ w := (abs_fst_le_norm2 (z - q)).trans hq
  have hdy : |z.2 - q.2| ≤ w := (abs_snd_le_norm2 (z - q)).trans hq
  have hqxl : a ≤ q.1 := by
    have := (abs_le.mp hdx).2
    change x - q.1 ≤ w at this
    linarith
  have hqxr : q.1 ≤ b := by
    have := (abs_le.mp hdx).1
    change -w ≤ x - q.1 at this
    linarith
  have hqx : q.1 ∈ Icc a b := ⟨hqxl, hqxr⟩
  have hqpx : |q.1 - p.1| ≤ 3 * w := by
    have he : q.1 - p.1 = (q.1 - x) + (x - p.1) := by ring
    rw [he]
    have hdx' : |q.1 - x| ≤ w := by simpa only [z, abs_sub_comm] using hdx
    exact (abs_add_le _ _).trans (by rw [hx]; linarith)
  have hglip := hLip q.1 hqx p.1 hp.1
  have hgupper : γ q.1 ≤ γ p.1 + 3 * L * w := by
    have h := (le_abs_self _).trans (hglip.trans
      (mul_le_mul_of_nonneg_left hqpx hL))
    nlinarith
  have hqbottom : γ q.1 ≤ q.2 := by
    have hy := (abs_le.mp hdy).2
    change p.2 + (3 * L + 2) * w - q.2 ≤ w at hy
    nlinarith [hp.2.1]
  have hqtop : q.2 ≤ 1 := by
    have hy := (abs_le.mp hdy).1
    change -w ≤ p.2 + (3 * L + 2) * w - q.2 at hy
    nlinarith
  have hpz : euclideanDist p z ≤ (3 * L + 4) * w := by
    change norm2 (p - z) ≤ _
    have h := norm2_le_abs_add (p - z)
    have he₁ : |p.1 - z.1| = 2 * w := by simpa only [z, abs_sub_comm] using hx
    have he₂ : |p.2 - z.2| = (3 * L + 2) * w := by
      change |p.2 - (p.2 + (3 * L + 2) * w)| = _
      rw [show p.2 - (p.2 + (3 * L + 2) * w) = -((3 * L + 2) * w) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    rw [he₁, he₂] at h
    nlinarith
  exact ⟨⟨hqx, hqbottom, hqtop⟩,
    (euclideanDist_triangle p z q).trans (by nlinarith)⟩

/-- The whole epigraph strip has uniform balls when its roof stays below one. -/
theorem roofStrip_hasInteriorBalls {a b H L : ℝ} {γ : ℝ → ℝ}
    (hab : a < b) (hH : H < 1) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|)
    (hheight : ∀ x ∈ Icc a b, γ x ≤ H) :
    ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ HasInteriorBalls (roofStrip a b γ) κ r₀ := by
  let R : Set Point := Icc a b ×ˢ Icc H 1
  have hR : IsConvexBody R :=
    ⟨⟨(a, H), ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hH.le⟩⟩⟩,
      isCompact_Icc.prod isCompact_Icc, convex_Icc.prod convex_Icc⟩
  have hRint : (interior R).Nonempty := by
    have hsub : Ioo a b ×ˢ Ioo H 1 ⊆ R := fun p hp =>
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    have hi := interior_maximal hsub (isOpen_Ioo.prod isOpen_Ioo)
    refine ⟨((a + b) / 2, (H + 1) / 2), hi ?_⟩
    constructor <;> constructor <;> dsimp <;> linarith
  have hRE : R ⊆ roofStrip a b γ := by
    intro p hp
    exact ⟨hp.1, (hheight p.1 hp.1).trans hp.2.1, hp.2.2⟩
  obtain ⟨κR, rR, hκR, hrR, hballsR⟩ := convexBody_hasInteriorBalls hR hRint
  let κ := min κR (1 / (4 * (L + 2)))
  let r₀ := min rR (min (b - a) ((1 - H) / 2))
  have hκ : 0 < κ := lt_min hκR (by positivity)
  have hr₀ : 0 < r₀ := lt_min hrR (lt_min (sub_pos.mpr hab) (by linarith))
  refine ⟨κ, r₀, hκ, hr₀, ?_⟩
  intro p hp ρ hρ hρmax
  by_cases hlow : p.2 ≤ (1 + H) / 2
  · obtain ⟨z, hz⟩ := roofStrip_low_ball hab hH hL hLip hp hlow hρ
      (hρmax.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hρmax.trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨z, ?_⟩
    intro q hq
    apply hz
    have hk := mul_le_mul_of_nonneg_right (min_le_right κR (1 / (4 * (L + 2)))) hρ.le
    have he : 1 / (4 * (L + 2)) * ρ = ρ / (4 * (L + 2)) := by ring
    exact hq.trans (hk.trans_eq he)
  · have hpR : p ∈ R := ⟨hp.1, by constructor <;> linarith [hp.2.2, not_le.mp hlow]⟩
    obtain ⟨z, hz⟩ := hballsR p hpR ρ hρ (hρmax.trans (min_le_left _ _))
    refine ⟨z, ?_⟩
    intro q hq
    have hqR := hz (hq.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ.le))
    exact ⟨hRE hqR.1, hqR.2⟩

end MovingSofaStability
