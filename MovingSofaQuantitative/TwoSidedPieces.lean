module

public import MovingSofaQuantitative.HermiteSpline

/-!
# Two-sided calculus for matched interpolation pieces

Uncompiled proof source. Values of a right-assigned join are differentiated
from the left only when the values at the joint agree. A genuinely C1 join
also matches first derivatives. Second derivatives may have distinct one-sided
values, which must be retained when reflecting a support perturbation.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology

namespace MovingSofaQuantitative

def leftJoin (a : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ a then f t else g t

/-- The left derivative of a right-assigned continuous join uses the left
piece at the knot, not the value selected by the right branch for derivatives. -/
theorem leftDeriv_rightJoin {a : ℝ} {f g df dg : ℝ → ℝ}
    (hmatch : f a = g a)
    (hf : ∀ t, HasDerivWithinAt f (df t) (Iio t) t)
    (hg : ∀ t, HasDerivWithinAt g (dg t) (Iio t) t) (t : ℝ) :
    HasDerivWithinAt (rightJoin a f g) (leftJoin a df dg t) (Iio t) t := by
  unfold leftJoin
  by_cases ht : t ≤ a
  · rw [if_pos ht]
    apply (hf t).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [rightJoin, if_pos (hu.trans_le ht)]
    · rcases ht.lt_or_eq with h | rfl
      · simp only [rightJoin, if_pos h]
      · simp only [rightJoin, lt_self_iff_false, if_false, hmatch]
  · rw [if_neg ht]
    have hlt : a < t := not_le.mp ht
    apply (hg t).congr_of_eventuallyEq
    · have hn : Ioi a ∈ 𝓝[Iio t] t :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hlt)
      filter_upwards [hn] with u hu
      simp only [rightJoin, if_neg (not_lt.mpr hu.le)]
    · simp only [rightJoin, if_neg (not_lt.mpr hlt.le)]

/-- Exact matching of value and derivative makes the join differentiable at
its knot. The proof combines the two half-neighborhoods, not a guessed API. -/
theorem hasDerivAt_rightJoin {a : ℝ} {f g df dg : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (hv : f a = g a) (hd : df a = dg a) (t : ℝ) :
    HasDerivAt (rightJoin a f g) (rightJoin a df dg t) t := by
  rcases lt_trichotomy t a with h | rfl | h
  · rw [rightJoin, if_pos h]
    apply (hf t).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds h] with u hu
    simp only [rightJoin, if_pos hu]
  · have hleft : HasDerivWithinAt (rightJoin a f g) (dg a) (Iic a) a := by
      have hi := leftDeriv_rightJoin hv
        (fun u => (hf u).hasDerivWithinAt) (fun u => (hg u).hasDerivWithinAt) a
      simp only [leftJoin, if_pos le_rfl, hd] at hi
      have he : Iic a = insert a (Iio a) := by ext u; simp; exact le_iff_lt_or_eq
      rw [he]
      exact hi.insert
    have hright : HasDerivWithinAt (rightJoin a f g) (dg a) (Ici a) a := by
      have hi := rightDeriv_rightJoin
        (fun u => (hf u).hasDerivWithinAt) (fun u => (hg u).hasDerivWithinAt) a
      simp only [rightJoin, lt_self_iff_false, if_false] at hi
      have he : Ici a = insert a (Ioi a) := by
        ext u
        simp only [mem_Ici, mem_insert_iff, mem_Ioi]
        exact le_iff_eq_or_lt
      rw [he]
      exact hi.insert
    have hboth := hleft.union hright
    have he : Iic a ∪ Ici a = (univ : Set ℝ) := by
      ext u
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total u a
    rw [he] at hboth
    simpa only [rightJoin, lt_self_iff_false, if_false] using hboth.hasDerivAt (by simp)
  · rw [rightJoin, if_neg (not_lt.mpr h.le)]
    apply (hg t).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds h] with u hu
    simp only [rightJoin, if_neg (not_lt.mpr hu.le)]

/-- The left curvature selector keeps the previous cubic at a knot. -/
def hermiteChainSecondLeft : List HermiteNode → ℝ → ℝ
  | [] => fun _ => 0
  | [_] => fun _ => 0
  | a :: b :: xs => leftJoin b.position (a.segmentSecond b) (hermiteChainSecondLeft (b :: xs))

/-- Every ordered Hermite chain is genuinely differentiable, with its recorded
continuous first derivative. -/
theorem hermiteChain_hasDerivAt (xs : List HermiteNode) (h : OrderedNodes xs) (t : ℝ) :
    HasDerivAt (hermiteChain xs) (hermiteChainFirst xs t) t := by
  revert h
  induction xs using List.twoStepInduction generalizing t with
  | nil => intro _; exact hasDerivAt_const t 0
  | singleton a => intro _; exact a.derivative_affine t
  | cons_cons a b xs ih₁ ih₂ =>
      intro h
      have hab : a.position < b.position :=
        (List.pairwise_cons.mp h).1 b (List.mem_cons_self _ _)
      have htail : OrderedNodes (b :: xs) := (List.pairwise_cons.mp h).2
      apply hasDerivAt_rightJoin (fun u => a.derivative_segment b u)
      · intro u
        first | exact ih₂ u htail | exact ih₁ u htail
      · rw [HermiteNode.segment_right a b hab, hermiteChain_first_node b xs htail]
      · rw [HermiteNode.segmentFirst_right a b hab, hermiteChainFirst_first_node b xs htail]

/-- Reflection uses this left second derivative, not the right-selected one. -/
theorem hermiteChain_first_leftDeriv (xs : List HermiteNode) (h : OrderedNodes xs) (t : ℝ) :
    HasDerivWithinAt (hermiteChainFirst xs) (hermiteChainSecondLeft xs t) (Iio t) t := by
  revert h
  induction xs using List.twoStepInduction generalizing t with
  | nil => intro _; exact (hasDerivAt_const t 0).hasDerivWithinAt
  | singleton a => intro _; exact (hasDerivAt_const t a.slope).hasDerivWithinAt
  | cons_cons a b xs ih₁ ih₂ =>
      intro h
      have hab : a.position < b.position :=
        (List.pairwise_cons.mp h).1 b (List.mem_cons_self _ _)
      have htail : OrderedNodes (b :: xs) := (List.pairwise_cons.mp h).2
      apply leftDeriv_rightJoin
      · rw [HermiteNode.segmentFirst_right a b hab, hermiteChainFirst_first_node b xs htail]
      · intro u
        exact (a.derivative_segmentFirst b u).hasDerivWithinAt
      · intro u
        first | exact ih₂ u htail | exact ih₁ u htail

end MovingSofaQuantitative
