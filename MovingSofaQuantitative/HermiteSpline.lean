module

public import MovingSofaQuantitative.Hermite

/-!
# A finite C1 Hermite chain

Uncompiled proof source. The data, rather than rounded endpoint evaluations,
are used on both sides of every joint. Right derivatives are tracked separately
from continuity; the second derivative may jump at an interpolation knot.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology

namespace MovingSofaQuantitative

structure HermiteNode where
  position : ℝ
  value : ℝ
  slope : ℝ

namespace HermiteNode

def segment (a b : HermiteNode) : ℝ → ℝ :=
  hermiteValue a.position b.position a.value b.value a.slope b.slope

def segmentFirst (a b : HermiteNode) : ℝ → ℝ :=
  hermiteFirst a.position b.position a.value b.value a.slope b.slope

def segmentSecond (a b : HermiteNode) : ℝ → ℝ :=
  hermiteSecond a.position b.position a.value b.value a.slope b.slope

def affine (a : HermiteNode) (t : ℝ) : ℝ := a.value + a.slope * (t - a.position)

@[simp] theorem segment_left (a b : HermiteNode) : a.segment b a.position = a.value :=
  hermiteValue_left _ _ _ _ _ _

@[simp] theorem segment_right (a b : HermiteNode) (hab : a.position < b.position) :
    a.segment b b.position = b.value := hermiteValue_right hab.ne _ _ _ _

@[simp] theorem segmentFirst_left (a b : HermiteNode) (hab : a.position < b.position) :
    a.segmentFirst b a.position = a.slope := hermiteFirst_left hab.ne _ _ _ _

@[simp] theorem segmentFirst_right (a b : HermiteNode) (hab : a.position < b.position) :
    a.segmentFirst b b.position = b.slope := hermiteFirst_right hab.ne _ _ _ _

theorem derivative_segment (a b : HermiteNode) (t : ℝ) :
    HasDerivAt (a.segment b) (a.segmentFirst b t) t := hermite_hasDerivAt _ _ _ _ _ _ _

theorem derivative_segmentFirst (a b : HermiteNode) (t : ℝ) :
    HasDerivAt (a.segmentFirst b) (a.segmentSecond b t) t := hermiteFirst_hasDerivAt _ _ _ _ _ _ _

theorem derivative_affine (a : HermiteNode) (t : ℝ) : HasDerivAt a.affine a.slope t := by
  convert (((hasDerivAt_id t).sub_const a.position).const_mul a.slope).const_add a.value using 1 <;> ring

end HermiteNode

/-- Strict ordering is part of the input data, not inferred by floating-point sorting. -/
def OrderedNodes (xs : List HermiteNode) : Prop :=
  xs.Pairwise (fun a b => a.position < b.position)

/-- Extrapolation past the final node is affine. It is used only to make the
ambient function well-defined and C1; the trial uses the closed knot interval. -/
def hermiteChain : List HermiteNode → ℝ → ℝ
  | [] => fun _ => 0
  | [a] => a.affine
  | a :: b :: xs => rightJoin b.position (a.segment b) (hermiteChain (b :: xs))

def hermiteChainFirst : List HermiteNode → ℝ → ℝ
  | [] => fun _ => 0
  | [a] => fun _ => a.slope
  | a :: b :: xs => rightJoin b.position (a.segmentFirst b) (hermiteChainFirst (b :: xs))

def hermiteChainSecond : List HermiteNode → ℝ → ℝ
  | [] => fun _ => 0
  | [_] => fun _ => 0
  | a :: b :: xs => rightJoin b.position (a.segmentSecond b) (hermiteChainSecond (b :: xs))

private theorem ordered_head {a b : HermiteNode} {xs : List HermiteNode}
    (h : OrderedNodes (a :: b :: xs)) : a.position < b.position := by
  exact (List.pairwise_cons.mp h).1 b (List.mem_cons_self _ _)

private theorem ordered_tail {a : HermiteNode} {xs : List HermiteNode}
    (h : OrderedNodes (a :: xs)) : OrderedNodes xs := (List.pairwise_cons.mp h).2

@[simp] theorem hermiteChain_first_node (a : HermiteNode) (xs : List HermiteNode)
    (h : OrderedNodes (a :: xs)) : hermiteChain (a :: xs) a.position = a.value := by
  cases xs with
  | nil => simp [hermiteChain, HermiteNode.affine]
  | cons b xs =>
      simp only [hermiteChain, rightJoin, if_pos (ordered_head h), HermiteNode.segment_left]

@[simp] theorem hermiteChainFirst_first_node (a : HermiteNode) (xs : List HermiteNode)
    (h : OrderedNodes (a :: xs)) : hermiteChainFirst (a :: xs) a.position = a.slope := by
  cases xs with
  | nil => rfl
  | cons b xs =>
      simp only [hermiteChainFirst, rightJoin, if_pos (ordered_head h),
        HermiteNode.segmentFirst_left a b (ordered_head h)]

/-- Adjacent Hermite pieces have exactly the same value at their joint. -/
theorem hermiteChain_continuous (xs : List HermiteNode) (h : OrderedNodes xs) :
    Continuous (hermiteChain xs) := by
  induction xs using List.twoStepInduction with
  | nil => exact continuous_const
  | singleton a => unfold hermiteChain HermiteNode.affine; fun_prop
  | cons_cons a b xs ih₁ ih₂ =>
      have hab := ordered_head h
      have htail := ordered_tail h
      apply continuous_rightJoin
      · exact continuous_iff_continuousAt.mpr fun t => (a.derivative_segment b t).continuousAt
      · exact ih₁ htail
      · rw [HermiteNode.segment_right a b hab, hermiteChain_first_node b xs htail]

/-- Adjacent first derivatives match exactly, even though their derivatives
need not match. -/
theorem hermiteChainFirst_continuous (xs : List HermiteNode) (h : OrderedNodes xs) :
    Continuous (hermiteChainFirst xs) := by
  induction xs using List.twoStepInduction with
  | nil => exact continuous_const
  | singleton a => exact continuous_const
  | cons_cons a b xs ih₁ ih₂ =>
      have hab := ordered_head h
      have htail := ordered_tail h
      apply continuous_rightJoin
      · exact continuous_iff_continuousAt.mpr fun t => (a.derivative_segmentFirst b t).continuousAt
      · exact ih₁ htail
      · rw [HermiteNode.segmentFirst_right a b hab, hermiteChainFirst_first_node b xs htail]

/-- The recorded right derivative is the derivative of the actual piecewise
function, not just of its displayed interval formulas. -/
theorem hermiteChain_rightDeriv (xs : List HermiteNode) (t : ℝ) :
    HasDerivWithinAt (hermiteChain xs) (hermiteChainFirst xs t) (Ioi t) t := by
  induction xs using List.twoStepInduction with
  | nil => exact (hasDerivAt_const t 0).hasDerivWithinAt
  | singleton a => exact (a.derivative_affine t).hasDerivWithinAt
  | cons_cons a b xs ih₁ ih₂ =>
      exact rightDeriv_rightJoin
        (fun t => (a.derivative_segment b t).hasDerivWithinAt)
        (fun t => ih₁ t) t

theorem hermiteChain_second_rightDeriv (xs : List HermiteNode) (t : ℝ) :
    HasDerivWithinAt (hermiteChainFirst xs) (hermiteChainSecond xs t) (Ioi t) t := by
  induction xs using List.twoStepInduction with
  | nil => exact (hasDerivAt_const t 0).hasDerivWithinAt
  | singleton a => exact (hasDerivAt_const t a.slope).hasDerivWithinAt
  | cons_cons a b xs ih₁ ih₂ =>
      exact rightDeriv_rightJoin
        (fun t => (a.derivative_segmentFirst b t).hasDerivWithinAt)
        (fun t => ih₁ t) t

/-- The chain agrees with its first cubic on the entire closed first interval;
at the right endpoint this uses the shared node value. -/
theorem hermiteChain_on_first {a b : HermiteNode} {xs : List HermiteNode}
    (h : OrderedNodes (a :: b :: xs)) {t : ℝ} (ht : t ∈ Icc a.position b.position) :
    hermiteChain (a :: b :: xs) t = a.segment b t := by
  rcases ht.2.lt_or_eq with htb | rfl
  · simp only [hermiteChain, rightJoin, if_pos htb]
  · simp only [hermiteChain, rightJoin, lt_self_iff_false, if_false,
      hermiteChain_first_node b xs (ordered_tail h),
      HermiteNode.segment_right a b (ordered_head h)]

theorem hermiteChainFirst_on_first {a b : HermiteNode} {xs : List HermiteNode}
    (h : OrderedNodes (a :: b :: xs)) {t : ℝ} (ht : t ∈ Icc a.position b.position) :
    hermiteChainFirst (a :: b :: xs) t = a.segmentFirst b t := by
  rcases ht.2.lt_or_eq with htb | rfl
  · simp only [hermiteChainFirst, rightJoin, if_pos htb]
  · simp only [hermiteChainFirst, rightJoin, lt_self_iff_false, if_false,
      hermiteChainFirst_first_node b xs (ordered_tail h),
      HermiteNode.segmentFirst_right a b (ordered_head h)]

end MovingSofaQuantitative
