module

public import MovingSofaQuantitative.SymmetricCapPerturbation
public import MovingSofaQuantitative.PerturbationEnergy

/-!
# Finite Hermite data define a genuine cap perturbation profile

Uncompiled proof source. This construction only needs ordering and exact
endpoint jets. A finite family of continuous polynomial pieces supplies a
uniform curvature bound, even though second derivatives jump at the knots.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

private theorem ordered_head_le {a b : HermiteNode} {xs : List HermiteNode}
    (h : OrderedNodes (a::xs)) (hb : b∈a::xs) : a.position≤b.position := by
  rcases List.mem_cons.mp hb with rfl | hb
  · exact le_rfl
  · exact ((List.pairwise_cons.mp h).1 b hb).le

/-- Values and first derivatives at every listed node are exact. -/
theorem hermiteChain_at_node {xs : List HermiteNode} (h : OrderedNodes xs)
    {a : HermiteNode} (ha : a∈xs) :
    hermiteChain xs a.position=a.value ∧ hermiteChainFirst xs a.position=a.slope := by
  revert h a ha
  induction xs using List.twoStepInduction with
  | nil => intro h a ha; cases ha
  | singleton b =>
      intro h a ha
      have he : a=b := by simpa using ha
      subst a
      simp [hermiteChain,hermiteChainFirst,HermiteNode.affine]
  | cons_cons b c xs ih₁ ih₂ =>
      intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨hermiteChain_first_node b (c::xs) h,hermiteChainFirst_first_node b (c::xs) h⟩
      · have ht : OrderedNodes (c::xs) := (List.pairwise_cons.mp h).2
        have hc := ordered_head_le ht ha
        simp only [hermiteChain,hermiteChainFirst,rightJoin,if_neg (not_lt.mpr hc)]
        first | exact ih₂ ht ha | exact ih₁ ht ha

private def chainValuePieces : List HermiteNode → List (ℝ→ℝ)
  | [] => [fun _ => 0]
  | [a] => [a.affine]
  | a::b::xs => a.segment b :: chainValuePieces (b::xs)

private def chainSecondPieces : List HermiteNode → List (ℝ→ℝ)
  | [] => [fun _ => 0]
  | [_] => [fun _ => 0]
  | a::b::xs => a.segmentSecond b :: chainSecondPieces (b::xs)

private theorem value_piece_selected (xs : List HermiteNode) (t : ℝ) :
    ∃ f∈chainValuePieces xs, hermiteChain xs t=f t := by
  induction xs using List.twoStepInduction with
  | nil => exact ⟨_,List.mem_singleton_self _,rfl⟩
  | singleton a => exact ⟨_,List.mem_singleton_self _,rfl⟩
  | cons_cons a b xs ih₁ ih₂ =>
      by_cases h : t<b.position
      · exact ⟨_,List.mem_cons_self _ _,by simp [hermiteChain,rightJoin,h]⟩
      · obtain ⟨f,hf,he⟩ := (by first | exact ih₂ | exact ih₁ :
          ∃ f∈chainValuePieces (b::xs),hermiteChain (b::xs) t=f t)
        exact ⟨f,List.mem_cons_of_mem _ hf,by simpa only [hermiteChain,rightJoin,if_neg h] using he⟩

private theorem second_piece_selected (xs : List HermiteNode) (t : ℝ) :
    (∃ f∈chainSecondPieces xs,hermiteChainSecond xs t=f t) ∧
    (∃ f∈chainSecondPieces xs,hermiteChainSecondLeft xs t=f t) := by
  induction xs using List.twoStepInduction with
  | nil => exact ⟨⟨_,List.mem_singleton_self _,rfl⟩,⟨_,List.mem_singleton_self _,rfl⟩⟩
  | singleton a => exact ⟨⟨_,List.mem_singleton_self _,rfl⟩,⟨_,List.mem_singleton_self _,rfl⟩⟩
  | cons_cons a b xs ih₁ ih₂ =>
      have htail := (by first | exact ih₂ | exact ih₁ :
        (∃ f∈chainSecondPieces (b::xs),hermiteChainSecond (b::xs) t=f t) ∧
        (∃ f∈chainSecondPieces (b::xs),hermiteChainSecondLeft (b::xs) t=f t))
      constructor
      · by_cases h : t<b.position
        · exact ⟨_,List.mem_cons_self _ _,by simp [hermiteChainSecond,rightJoin,h]⟩
        · obtain ⟨f,hf,he⟩ := htail.1
          exact ⟨f,List.mem_cons_of_mem _ hf,by simpa [hermiteChainSecond,rightJoin,h] using he⟩
      · by_cases h : t≤b.position
        · exact ⟨_,List.mem_cons_self _ _,by simp [hermiteChainSecondLeft,leftJoin,h]⟩
        · obtain ⟨f,hf,he⟩ := htail.2
          exact ⟨f,List.mem_cons_of_mem _ hf,by simpa [hermiteChainSecondLeft,leftJoin,h] using he⟩

private theorem pieces_continuous (xs : List HermiteNode) :
    (∀ f∈chainValuePieces xs,Continuous f) ∧ (∀ f∈chainSecondPieces xs,Continuous f) := by
  induction xs using List.twoStepInduction with
  | nil => simp only [chainValuePieces,chainSecondPieces,List.mem_singleton]; constructor <;> rintro f rfl <;> fun_prop
  | singleton a =>
      simp only [chainValuePieces,chainSecondPieces,List.mem_singleton]
      constructor <;> rintro f rfl
      · unfold HermiteNode.affine; fun_prop
      · fun_prop
  | cons_cons a b xs ih₁ ih₂ =>
      have ht := (by first | exact ih₂ | exact ih₁ :
        (∀ f∈chainValuePieces (b::xs),Continuous f) ∧
        (∀ f∈chainSecondPieces (b::xs),Continuous f))
      constructor
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact continuous_iff_continuousAt.mpr fun t => (a.derivative_segment b t).continuousAt
        · exact ht.1 f hf
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · unfold HermiteNode.segmentSecond hermiteSecond Cubic.second
          fun_prop
        · exact ht.2 f hf

private theorem finite_piece_bound (fs : List (ℝ→ℝ)) (hfs : ∀ f∈fs,Continuous f)
    (a b : ℝ) : ∃ M : ℝ,0≤M ∧ ∀ f∈fs,∀ t∈Icc a b,|f t|≤M := by
  induction fs with
  | nil => exact ⟨0,le_rfl,by simp⟩
  | cons f fs ih =>
      obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (hfs f (List.mem_cons_self _ _)).continuousOn
      obtain ⟨M,hM,hbound⟩ := ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
      refine ⟨|R|+M,by positivity,?_⟩
      intro g hg t ht
      rcases List.mem_cons.mp hg with rfl | hg
      · exact (hR t ht).trans ((le_abs_self R).trans (le_add_of_nonneg_right hM))
      · exact (hbound g hg t ht).trans (le_add_of_nonneg_left (abs_nonneg R))

/-- Both one-sided curvatures are bounded on a fixed compact interval. -/
theorem hermiteChain_curvature_bounded (xs : List HermiteNode) (a b : ℝ) :
    ∃ M : ℝ,0≤M ∧ ∀ t∈Icc a b,
      |hermiteChainSecond xs t+hermiteChain xs t|≤M ∧
      |hermiteChainSecondLeft xs t+hermiteChain xs t|≤M := by
  obtain ⟨V,hV,hvalue⟩ := finite_piece_bound (chainValuePieces xs) (pieces_continuous xs).1 a b
  obtain ⟨D,hD,hsecond⟩ := finite_piece_bound (chainSecondPieces xs) (pieces_continuous xs).2 a b
  refine ⟨D+V,add_nonneg hD hV,?_⟩
  intro t ht
  obtain ⟨f,hf,he⟩ := value_piece_selected xs t
  obtain ⟨⟨g,hg,hr⟩,⟨k,hk,hl⟩⟩ := second_piece_selected xs t
  rw [he,hr,hl]
  exact ⟨(abs_add_le _ _).trans (add_le_add (hsecond g hg t ht) (hvalue f hf t ht)),
    (abs_add_le _ _).trans (add_le_add (hsecond k hk t ht) (hvalue f hf t ht))⟩

/-- Exact finite data for the half profile. No geometric conclusion appears
as a field: the actual convex cap is constructed later from this data. -/
structure TrialSplineData (φ : ℝ) where
  q : ℝ
  q_nonneg : 0≤q
  head : HermiteNode
  rest : List HermiteNode
  ordered : OrderedNodes (head::rest)
  head_position : head.position=φ
  head_value : head.value= -cos φ+q*sin φ
  head_slope : head.slope=sin φ+q*cos φ
  top : HermiteNode
  top_mem : top∈head::rest
  top_position : top.position=π/2
  top_value : top.value=0

namespace TrialSplineData

variable {φ : ℝ} (D : TrialSplineData φ)

def gap (t : ℝ) := -cos t+D.q*sin t
def gapFirst (t : ℝ) := sin t+D.q*cos t
def gapSecond (t : ℝ) := cos t-D.q*sin t

def value := rightJoin φ D.gap (hermiteChain (D.head::D.rest))
def first := rightJoin φ D.gapFirst (hermiteChainFirst (D.head::D.rest))
def secondR := rightJoin φ D.gapSecond (hermiteChainSecond (D.head::D.rest))
def secondL := leftJoin φ D.gapSecond (hermiteChainSecondLeft (D.head::D.rest))

theorem gap_derivative (t : ℝ) : HasDerivAt D.gap (D.gapFirst t) t := by
  convert (hasDerivAt_cos t).neg.add ((hasDerivAt_sin t).const_mul D.q) using 1 <;> simp [gap,gapFirst]

theorem gapFirst_derivative (t : ℝ) : HasDerivAt D.gapFirst (D.gapSecond t) t := by
  convert (hasDerivAt_sin t).add ((hasDerivAt_cos t).const_mul D.q) using 1 <;> simp [gapFirst,gapSecond] <;> ring

theorem matches : D.gap φ=hermiteChain (D.head::D.rest) φ ∧
    D.gapFirst φ=hermiteChainFirst (D.head::D.rest) φ := by
  rw [←D.head_position,hermiteChain_first_node _ _ D.ordered,
    hermiteChainFirst_first_node _ _ D.ordered,D.head_position,D.head_value,D.head_slope]
  exact ⟨rfl,rfl⟩

def profile (hφ : 0<φ) : HalfCapProfile φ := by
  obtain ⟨M,hM,hcurv⟩ := hermiteChain_curvature_bounded (D.head::D.rest) φ (π/2)
  have hm := D.matches
  refine ⟨D.value,D.first,D.secondR,D.secondL,M,hM,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hasDerivAt_rightJoin D.gap_derivative
      (hermiteChain_hasDerivAt _ D.ordered) hm.1 hm.2
  · exact continuous_rightJoin
      (continuous_iff_continuousAt.mpr fun t => (D.gapFirst_derivative t).continuousAt)
      (hermiteChainFirst_continuous _ D.ordered) hm.2
  · intro t
    have h := rightDeriv_rightJoin
      (fun u => (D.gapFirst_derivative u).hasDerivWithinAt)
      (hermiteChain_second_rightDeriv (D.head::D.rest)) t
    have he : Ici t=insert t (Ioi t) := by ext u; simp only [mem_Ici,mem_insert_iff,mem_Ioi]; exact le_iff_eq_or_lt
    rw [he]
    exact h.insert
  · intro t
    have h := leftDeriv_rightJoin hm.2
      (fun u => (D.gapFirst_derivative u).hasDerivWithinAt)
      (hermiteChain_first_leftDeriv _ D.ordered) t
    have he : Iic t=insert t (Iio t) := by ext u; simp only [mem_Iic,mem_insert_iff,mem_Iio]; exact le_iff_eq_or_lt
    rw [he]
    exact h.insert
  · have ht := hermiteChain_at_node D.ordered D.top_mem
    have horder := ordered_head_le D.ordered D.top_mem
    rw [D.head_position,D.top_position] at horder
    simp only [value,rightJoin,if_neg (not_lt.mpr horder),←D.top_position,ht.1,D.top_value]
  · simpa only [first,rightJoin,if_pos hφ,gapFirst,sin_zero,cos_zero,mul_one,zero_add] using D.q_nonneg
  · intro t ht
    simp only [secondR,value,rightJoin,if_pos ht.2,gapSecond,gap]
    ring
  · intro t ht
    rcases ht.2.lt_or_eq with h | rfl
    · simp only [secondL,value,leftJoin,rightJoin,if_pos h.le,if_pos h,gapSecond,gap]; ring
    · simp only [secondL,value,leftJoin,rightJoin,if_pos le_rfl,lt_self_iff_false,if_false]
      rw [←hm.1]
      simp only [gapSecond,gap]
      ring
  · intro t ht
    simpa only [secondR,value,rightJoin,if_neg (not_lt.mpr ht.1)] using (hcurv t ht).1
  · intro t ht
    rcases ht.1.lt_or_eq with h | he
    · simpa only [secondL,value,leftJoin,rightJoin,if_neg (not_le.mpr h),if_neg (not_lt.mpr h.le)] using (hcurv t ht).2
    · subst t
      simp only [secondL,value,leftJoin,rightJoin,if_pos le_rfl,lt_self_iff_false,if_false]
      rw [←hm.1]
      simpa only [gapSecond,gap,show cos φ-D.q*sin φ+(-cos φ+D.q*sin φ)=0 by ring,abs_zero] using hM

/-- The zero endpoint of the selected family always changes both widths by -tau. -/
@[simp] theorem profile_zero (hφ : 0<φ) : (D.profile hφ).value 0= -1 := by
  simp [profile,value,rightJoin,hφ,gap]

/-- Any interior node is still an exact value/derivative node after gluing
on the zero-curvature gap. -/
theorem profile_at_node (hφ : 0<φ) {a : HermiteNode} (ha : a∈D.head::D.rest) :
    (D.profile hφ).value a.position=a.value ∧
    (D.profile hφ).first a.position=a.slope := by
  have hnode := hermiteChain_at_node D.ordered ha
  have horder := ordered_head_le D.ordered ha
  rw [D.head_position] at horder
  simpa only [profile,value,first,rightJoin,if_neg (not_lt.mpr horder)] using hnode

end TrialSplineData
end MovingSofaQuantitative
