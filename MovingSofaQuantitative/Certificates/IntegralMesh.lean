module

public import MovingSofaQuantitative.Certificates.BranchExpression
public import MovingSofaQuantitative.LocalizedSquare

/-!
# A finite upper-sum certificate for an interval integral

Uncompiled proof source. Every cell is retained, including cells crossing a
formula branch. The integrability and expression-identity hypotheses are
mathematical inputs proved for the trial; the evaluator checks only arithmetic.
No sample point or floating-point comparison enters the acceptance predicate.
-/

@[expose] public section

open Real Set MeasureTheory Finset

namespace MovingSofaQuantitative.Certificates

def meshPoint (a b : ℝ) (n j : ℕ) : ℝ := a+(b-a)*(j:ℝ)/(n:ℝ)

theorem meshPoint_mem {a b : ℝ} (hab : a≤b) {n j : ℕ} (hn : 0<n) (hj : j≤n) :
    meshPoint a b n j∈Icc a b := by
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn
  have hjr : (j:ℝ)≤n := by exact_mod_cast hj
  have hzero : 0≤(j:ℝ) := Nat.cast_nonneg j
  have hlen : 0≤b-a := sub_nonneg.mpr hab
  have hfrac : 0≤(j:ℝ)/n ∧ (j:ℝ)/n≤1 :=
    ⟨div_nonneg hzero hnr.le,(div_le_one hnr).mpr hjr⟩
  unfold meshPoint
  rw [mul_div_assoc]
  have hmul := mul_le_mul_of_nonneg_left hfrac.2 hlen
  constructor <;> nlinarith [mul_nonneg hlen hfrac.1]

theorem meshPoint_mono {a b : ℝ} (hab : a≤b) {n j k : ℕ} (hn : 0<n) (hjk : j≤k) :
    meshPoint a b n j≤meshPoint a b n k := by
  unfold meshPoint
  gcongr
  exact_mod_cast hjk

/-- Whole-cell upper bounds imply the exact finite upper sum. -/
theorem integral_le_mesh_sum {a b : ℝ} (hab : a≤b) {n : ℕ} (hn : 0<n)
    {f : ℝ→ℝ} (hi : IntervalIntegrable f volume a b) (U : Fin n→ℝ)
    (hU : ∀j:Fin n,∀t∈Icc (meshPoint a b n j) (meshPoint a b n (j+1)),f t≤U j) :
    (∫t in a..b,f t)≤∑j:Fin n,((b-a)/(n:ℝ))*U j := by
  have hsum : (∫t in a..b,f t)=
      ∑j∈Finset.range n,∫t in (meshPoint a b n j)..(meshPoint a b n (j+1)),f t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals]
    · simp only [meshPoint,Nat.cast_zero,mul_zero,zero_div,add_zero]
      rw [div_self (by exact_mod_cast hn.ne' : (n:ℝ)≠0),mul_one,add_sub_cancel_left]
    · intro j hj
      have hjn : j<n := Finset.mem_range.mp hj
      exact intervalIntegrable_subinterval hi
        (meshPoint_mem hab hn hjn.le).1
        (meshPoint_mono hab hn (Nat.le_succ j))
        (meshPoint_mem hab hn (Nat.succ_le_of_lt hjn)).2
  rw [hsum,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro j _
  have hjn := j.isLt
  have hcell := meshPoint_mono hab hn (Nat.le_succ j.val)
  have hicell := intervalIntegrable_subinterval hi
    (meshPoint_mem hab hn hjn.le).1 hcell
    (meshPoint_mem hab hn (Nat.succ_le_of_lt hjn)).2
  have h := intervalIntegral.integral_mono_on hcell hicell intervalIntegrable_const (hU j)
  have hwidth : meshPoint a b n (j.val+1)-meshPoint a b n j.val=(b-a)/(n:ℝ) := by
    unfold meshPoint
    push_cast
    ring
  simpa only [intervalIntegral.integral_const,smul_eq_mul,hwidth] using h

/-- Interval upper endpoint, safely nonnegative even for an over-wide interval. -/
def nonnegativeUpper (I : Interval) : ℚ := max 0 I.hi

/-- Sum of certified upper endpoints on a complete list of mesh cells. Failure
of any interval evaluation propagates; no failed cell is silently omitted. -/
def meshUpper (boxes : List (Box n)) (e : BranchExpr n) : Option ℚ :=
  (boxes.mapM fun box => do return nonnegativeUpper (←e.intervalValue box)).map List.sum

theorem meshUpper_sound {boxes : List (Box n)} {e : BranchExpr n} {U : ℚ}
    (h : meshUpper boxes e=some U) :
    ∃ bounds : List ℚ,bounds.length=boxes.length ∧ bounds.sum=U ∧
      ∀j:Fin boxes.length,0≤bounds[j] ∧
        ∀x,InBox (boxes[j]) x→e.realValue x≤(bounds[j]:ℝ) := by
  induction boxes generalizing U with
  | nil =>
      simp only [meshUpper,List.mapM_nil,Option.map_some,List.sum_nil,Option.some.injEq] at h
      subst U
      exact ⟨[],rfl,rfl,by intro j; exact Fin.elim0 j⟩
  | cons box boxes ih =>
      cases he : e.intervalValue box with
      | none => simp [meshUpper,he] at h
      | some I =>
          cases ht : meshUpper boxes e with
          | none => simp [meshUpper,he] at h
          | some V =>
              have hUV : nonnegativeUpper I+V=U := by
                simpa only [meshUpper,List.mapM_cons,he,Option.bind_some,
                  Option.map_some,List.sum_cons,Option.some.injEq] using h
              obtain ⟨bounds,hlen,hsum,hbounds⟩ := ih ht
              refine ⟨nonnegativeUpper I::bounds,by simp [hlen],by simpa [hsum] using hUV,?_⟩
              intro j
              refine Fin.cases ?_ (fun k => ?_) j
              · refine ⟨le_max_left _ _,?_⟩
                intro x hx
                have hv := BranchExpr.intervalValue_sound e hx he
                exact hv.2.trans (by exact_mod_cast le_max_right (0:ℚ) I.hi)
              · simpa only [List.getElem_cons_succ] using hbounds ⟨k.val,by simpa [hlen] using k.isLt⟩

/-- The upper-sum bound after all boxes have been checked. -/
theorem integral_le_checked_mesh {a b : ℝ} (hab : a≤b) {n d : ℕ} (hn : 0<n)
    (boxes : Fin n→Box d) (e : BranchExpr d) {U : ℚ}
    (hcheck : meshUpper (List.ofFn boxes) e=some U)
    {f : ℝ→ℝ} (hi : IntervalIntegrable f volume a b)
    (actual : ℝ→Fin d→ℝ)
    (hmodel : ∀t∈Icc a b,e.realValue (actual t)=f t)
    (hboxes : ∀j:Fin n,∀t∈Icc (meshPoint a b n j) (meshPoint a b n (j+1)),
      InBox (boxes j) (actual t)) :
    (∫t in a..b,f t)≤((b-a)/(n:ℝ))*(U:ℝ) := by
  obtain ⟨bounds,hlen,hsum,hbounds⟩ := meshUpper_sound hcheck
  have hlen' : bounds.length=n := by simpa using hlen
  let V : Fin n→ℝ := fun j => (bounds[⟨j.val,by simpa [hlen'] using j.isLt⟩]:ℚ)
  have hv : ∀j:Fin n,∀t∈Icc (meshPoint a b n j) (meshPoint a b n (j+1)),f t≤V j := by
    intro j t ht
    have htall : t∈Icc a b := ⟨(meshPoint_mem hab hn j.isLt.le).1.trans ht.1,
      ht.2.trans (meshPoint_mem hab hn (Nat.succ_le_of_lt j.isLt)).2⟩
    rw [←hmodel t htall]
    have hh := (hbounds ⟨j.val,by simpa using j.isLt⟩).2 (actual t)
    apply hh
    simpa using hboxes j t ht
  have h := integral_le_mesh_sum hab hn hi V hv
  have he : (∑j:Fin n,V j)=(U:ℝ) := by
    rw [←hsum,←List.sum_map_ratCast]
    simp only [V,←hlen',List.sum_ofFn]
  rw [←Finset.mul_sum,he] at h
  exact h

end MovingSofaQuantitative.Certificates
