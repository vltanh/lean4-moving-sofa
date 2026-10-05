module

public import MovingSofaUniqueness.Rigid

/-!
# Euclidean distance for the actual sofa sets

Uncompiled proof source. The ambient product `Real × Real` has the sup metric;
Baek's `hausdorffDist` is a support-function expression for convex bodies and
would identify a nonconvex sofa with its convex hull. Neither is silently used
as the actual-set Euclidean Hausdorff distance here.

`EuclideanClose r S T` expresses both directed distance bounds by witnesses.
For nonempty compact sets this is precisely Euclidean Hausdorff distance at
most r. The witness form is also useful in the geometric recovery argument.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev Point := ℝ × ℝ

/-- Euclidean point distance, using the repository's separate Euclidean norm. -/
def euclideanDist (p q : Point) : ℝ := norm2 (p - q)

theorem norm2_nonneg (p : Point) : 0 ≤ norm2 p := Real.sqrt_nonneg _

theorem norm2_sq (p : Point) : norm2 p ^ 2 = dot p p := by
  apply Real.sq_sqrt
  dsimp [dot]
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

@[simp] theorem norm2_zero : norm2 (0 : Point) = 0 := by
  simp [norm2, dot]

@[simp] theorem norm2_neg (p : Point) : norm2 (-p) = norm2 p := by
  unfold norm2
  congr 1
  simp only [dot, Prod.fst_neg, Prod.snd_neg]
  ring

theorem dot_le_norm2_mul (p q : Point) : dot p q ≤ norm2 p * norm2 q := by
  have hp := norm2_sq p
  have hq := norm2_sq q
  have hpn := norm2_nonneg p
  have hqn := norm2_nonneg q
  have hsq : dot p q ^ 2 ≤ (norm2 p * norm2 q) ^ 2 := by
    rw [mul_pow, hp, hq]
    dsimp [dot]
    nlinarith [sq_nonneg (p.1 * q.2 - p.2 * q.1)]
  have hprod : 0 ≤ norm2 p * norm2 q := mul_nonneg hpn hqn
  nlinarith

/-- Euclidean triangle inequality, not the triangle inequality of the product norm. -/
theorem norm2_add_le (p q : Point) : norm2 (p + q) ≤ norm2 p + norm2 q := by
  have hp := norm2_sq p
  have hq := norm2_sq q
  have hdot := dot_le_norm2_mul p q
  have hsym : dot q p = dot p q := by unfold dot; ring
  change Real.sqrt (dot (p + q) (p + q)) ≤ norm2 p + norm2 q
  apply (Real.sqrt_le_left (add_nonneg (norm2_nonneg p) (norm2_nonneg q))).2
  rw [dot_add_left, dot_add_right, dot_add_right, hsym]
  nlinarith

@[simp] theorem norm2_rot (a : ℝ) (p : Point) : norm2 (rot a p) = norm2 p := by
  unfold norm2
  congr 1
  calc
    dot (rot a p) (rot a p) =
        (cos a ^ 2 + sin a ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by
      unfold dot rot
      ring
    _ = dot p p := by rw [cos_sq_add_sin_sq]; unfold dot; ring

@[simp] theorem norm2_uvec (t : ℝ) : norm2 (uvec t) = 1 := by
  simp [norm2, dot_uvec_self]

theorem dot_uvec_le_norm2 (p : Point) (t : ℝ) : dot p (uvec t) ≤ norm2 p := by
  simpa only [norm2_uvec, mul_one] using dot_le_norm2_mul p (uvec t)

theorem euclideanDist_nonneg (p q : Point) : 0 ≤ euclideanDist p q :=
  norm2_nonneg _

@[simp] theorem euclideanDist_self (p : Point) : euclideanDist p p = 0 := by
  simp [euclideanDist]

theorem euclideanDist_comm (p q : Point) : euclideanDist p q = euclideanDist q p := by
  unfold euclideanDist
  rw [show p - q = -(q - p) by abel, norm2_neg]

theorem euclideanDist_triangle (p q r : Point) :
    euclideanDist p r ≤ euclideanDist p q + euclideanDist q r := by
  unfold euclideanDist
  rw [show p - r = (p - q) + (q - r) by abel]
  exact norm2_add_le _ _

@[simp] theorem euclideanDist_eq_zero_iff (p q : Point) : euclideanDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hs := norm2_sq (p - q)
    change norm2 (p - q) = 0 at h
    rw [h] at hs
    have hcoords : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 0 := by
      dsimp [dot] at hs
      nlinarith
    apply Prod.ext
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    · nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  · rintro rfl
    exact euclideanDist_self p

@[simp] theorem euclideanDist_rigid (g : Rigid) (p q : Point) :
    euclideanDist (g p) (g q) = euclideanDist p q := by
  have h : g p - g q = rot g.angle (p - q) := by
    ext <;> simp [Rigid.apply, rot] <;> ring
  unfold euclideanDist
  rw [h, norm2_rot]

/-- Directed Euclidean distance bound with an actual point witness. -/
def DirectedClose (r : ℝ) (S T : Set Point) : Prop :=
  ∀ p ∈ S, ∃ q ∈ T, euclideanDist p q ≤ r

/-- Euclidean Hausdorff bound for actual sets, rather than their support functions. -/
def EuclideanClose (r : ℝ) (S T : Set Point) : Prop :=
  DirectedClose r S T ∧ DirectedClose r T S

theorem DirectedClose.mono {r R : ℝ} {S T : Set Point}
    (h : DirectedClose r S T) (hr : r ≤ R) : DirectedClose R S T := by
  intro p hp
  obtain ⟨q, hq, hd⟩ := h p hp
  exact ⟨q, hq, hd.trans hr⟩

theorem DirectedClose.trans {r s : ℝ} {S T U : Set Point}
    (hST : DirectedClose r S T) (hTU : DirectedClose s T U) :
    DirectedClose (r + s) S U := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hST p hp
  obtain ⟨u, hu, hqu⟩ := hTU q hq
  exact ⟨u, hu, (euclideanDist_triangle p q u).trans (add_le_add hpq hqu)⟩

theorem EuclideanClose.refl (S : Set Point) {r : ℝ} (hr : 0 ≤ r) :
    EuclideanClose r S S := by
  have h : DirectedClose r S S := fun p hp => ⟨p, hp, by simpa using hr⟩
  exact ⟨h, h⟩

theorem EuclideanClose.symm {r : ℝ} {S T : Set Point} (h : EuclideanClose r S T) :
    EuclideanClose r T S := ⟨h.2, h.1⟩

theorem EuclideanClose.mono {r R : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (hr : r ≤ R) : EuclideanClose R S T :=
  ⟨h.1.mono hr, h.2.mono hr⟩

theorem EuclideanClose.trans {r s : ℝ} {S T U : Set Point}
    (hST : EuclideanClose r S T) (hTU : EuclideanClose s T U) :
    EuclideanClose (r + s) S U := by
  refine ⟨hST.1.trans hTU.1, ?_⟩
  simpa only [add_comm] using hTU.2.trans hST.2

/-- Zero radius recovers equality of actual sets, even when they are nonconvex. -/
theorem EuclideanClose.eq_of_zero {S T : Set Point} (h : EuclideanClose 0 S T) : S = T := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨q, hq, hd⟩ := h.1 p hp
    have he := (euclideanDist_eq_zero_iff p q).1
      (le_antisymm hd (euclideanDist_nonneg p q))
    simpa only [he] using hq
  · intro q hq
    obtain ⟨p, hp, hd⟩ := h.2 q hq
    have he := (euclideanDist_eq_zero_iff q p).1
      (le_antisymm hd (euclideanDist_nonneg q p))
    simpa only [he] using hp

theorem DirectedClose.rigid_image {r : ℝ} {S T : Set Point}
    (h : DirectedClose r S T) (g : Rigid) : DirectedClose r (g '' S) (g '' T) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hd⟩ := h p hp
  exact ⟨g q, mem_image_of_mem _ hq, by simpa using hd⟩

theorem EuclideanClose.rigid_image {r : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (g : Rigid) : EuclideanClose r (g '' S) (g '' T) :=
  ⟨h.1.rigid_image g, h.2.rigid_image g⟩

/-- Actual-set closeness controls every support value. The converse is not
claimed for nonconvex sets. -/
theorem EuclideanClose.abs_supp_sub_le {r : ℝ} {S T : Set Point}
    (h : EuclideanClose r S T) (hS : IsCompact S) (hT : IsCompact T)
    (hneS : S.Nonempty) (hneT : T.Nonempty) (t : ℝ) :
    |supp S t - supp T t| ≤ r := by
  have forward {A B : Set Point} (ha : IsCompact A) (hb : IsCompact B)
      (hne : A.Nonempty) (hab : DirectedClose r A B) : supp A t - supp B t ≤ r := by
    obtain ⟨p, hp, he⟩ := exists_dot_eq_supp ha hne t
    obtain ⟨q, hq, hd⟩ := hab p hp
    have hqle := dot_le_supp hb hq t
    have hproj := dot_uvec_le_norm2 (p - q) t
    rw [dot_sub_left] at hproj
    change norm2 (p - q) ≤ r at hd
    linarith
  have h₁ := forward hS hT hneS h.1
  have h₂ := forward hT hS hneT h.2
  exact abs_le.2 ⟨by linarith, h₁⟩

end MovingSofaStability
