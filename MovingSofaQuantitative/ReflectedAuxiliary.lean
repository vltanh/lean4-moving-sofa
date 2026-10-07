module

public import MovingSofaQuantitative.ActiveArcBody
public import MovingSofaQuantitative.Normalization

/-!
# Reflection of the deliberately symmetric trial family

Uncompiled proof source. Reflection is used only for the chosen lower-bound
family. No symmetry is assumed of arbitrary competitors in an upper theorem.
The two bodies are genuine compact convex sets, and every continuous paired
wall inequality is retained in the resulting WideTriple.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def verticalReflection (m : ℝ) (p : Point) : Point := (2*m-p.1,p.2)

theorem verticalReflection_continuous (m : ℝ) : Continuous (verticalReflection m) := by
  unfold verticalReflection
  fun_prop

@[simp] theorem verticalReflection_involutive (m : ℝ) (p : Point) :
    verticalReflection m (verticalReflection m p) = p := by
  ext <;> simp [verticalReflection]

theorem verticalReflection_dot (m : ℝ) (p : Point) (t : ℝ) :
    dot (verticalReflection m p) (uvec t) = dot p (uvec (π-t))+2*m*cos t := by
  simp only [verticalReflection, dot, uvec, cos_pi_sub, sin_pi_sub]
  ring

theorem verticalReflection_convex {B : Set Point} (hB : Convex ℝ B) (m : ℝ) :
    Convex ℝ (verticalReflection m '' B) := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ a b ha hb hab
  refine ⟨a • p+b • q,hB hp hq ha hb hab,?_⟩
  ext <;> simp only [verticalReflection, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · linear_combination 2*m*hab
  · ring

theorem verticalReflection_body {B : Set Point} (hB : IsConvexBody B) (m : ℝ) :
    IsConvexBody (verticalReflection m '' B) :=
  ⟨hB.1.image _,hB.2.1.image (verticalReflection_continuous m),verticalReflection_convex hB.2.2 m⟩

/-- The support formula is proved from the actual image set. -/
theorem verticalReflection_support {B : Set Point} (hB : IsConvexBody B) (m t : ℝ) :
    supp (verticalReflection m '' B) t = supp B (π-t)+2*m*cos t := by
  obtain ⟨p,hp,he⟩ := exists_dot_eq_supp hB.2.1 hB.1 (π-t)
  calc
    _ = dot (verticalReflection m p) (uvec t) := cvx_supp_eq_of_isGreatest
      (mem_image_of_mem _ hp) (by
        rintro q ⟨r,hr,rfl⟩
        rw [verticalReflection_dot,verticalReflection_dot,he]
        exact add_le_add_right (dot_le_supp hB.2.1 hr _) _)
    _ = _ := by rw [verticalReflection_dot,he]

/-- A normalized cap whose upper supports have the reflection identity is
actually preserved by reflection; lower normals need not be postulated. -/
theorem cap_verticalReflection_eq {K : Set Point} (hK : IsCap K (π/2)) {m : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) π, supp K t = supp K (π-t)+2*m*cos t) :
    verticalReflection m '' K = K := by
  have hsub : verticalReflection m '' K ⊆ K := by
    rintro p ⟨q,hq,rfl⟩
    apply (cap_mem_iff_upper hK _).mpr
    refine ⟨hK.snd_nonneg hq,?_⟩
    intro t ht
    rw [verticalReflection_dot,h t ht]
    exact add_le_add_right (dot_le_supp hK.2.1.2.1 hq _) _
  apply hsub.antisymm
  intro p hp
  exact ⟨verticalReflection m p,hsub (mem_image_of_mem _ hp),verticalReflection_involutive m p⟩

private theorem supp_period {B : Set Point} (t : ℝ) : supp B (t+2*π)=supp B t := by
  unfold supp
  simp only [uvec,cos_add_two_pi,sin_add_two_pi]

/-- The second paired wall is the reflected first paired wall, with all
translation terms cancelling. The formula is for any convex auxiliary B. -/
theorem reflected_paired_support {K B : Set Point} (hB : IsConvexBody B) {m : ℝ}
    (hsym : ∀ t ∈ Icc (0 : ℝ) π, supp K t = supp K (π-t)+2*m*cos t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (π/2)) :
    supp K (π/2+s)+supp (verticalReflection m '' B) (3*π/2+s) =
      supp K (π/2-s)+supp B (π+(π/2-s)) := by
  rw [hsym (π/2+s) ⟨by linarith [hs.1,pi_pos],by linarith [hs.2]⟩,
    verticalReflection_support hB]
  have hperiod : supp B (π-(3*π/2+s))=supp B (π+(π/2-s)) := by
    rw [← supp_period (B := B) (π-(3*π/2+s))]
    congr 1
    ring
  rw [hperiod]
  simp only [show π-(π/2+s)=π/2-s by ring,
    show 3*π/2+s=(π/2+s)+π by ring,cos_add_pi]
  ring

/-- An active arc yields an actual feasible wide triple, with no constraints
sampled and no independent assumption that its auxiliary supports are realizable. -/
def ActiveArcData.wideTriple {φ c m : ℝ} {K : Set Point} (D : ActiveArcData φ c K)
    (hsym : ∀ t ∈ Icc (0 : ℝ) π, supp K t = supp K (π-t)+2*m*cos t) : WideTriple φ := by
  let B := D.body
  let E := verticalReflection m '' B
  have hB := D.body_isConvexBody
  have hE := verticalReflection_body hB m
  have hEK : E ⊆ K := by
    rw [← cap_verticalReflection_eq D.cap hsym]
    exact image_mono D.body_subset
  refine ⟨(⟨K,D.cap.2.1⟩,⟨B,hB⟩,⟨E,hE⟩),D.cap,hB,hE,D.body_subset,hEK,
    (fun t ht => D.walls ht),D.cut,D.bottom,?_,?_,?_⟩
  · intro s hs
    rw [show 3*π/2+s=3*π/2+s by rfl]
    rw [reflected_paired_support hB hsym ⟨hs.1,by linarith [hs.2,D.order.1]⟩]
    exact D.walls ⟨by linarith [hs.2],by linarith [hs.1]⟩
  · have hh := reflected_paired_support hB hsym (s := 0) ⟨le_rfl,by linarith [pi_pos]⟩
    simpa only [add_zero,sub_zero] using hh.trans D.bottom
  · have hh := reflected_paired_support hB hsym (s := π/2-φ)
      ⟨by linarith [D.order.2.1,D.order.2.2],by linarith [D.order.1]⟩
    simpa only [show π/2-(π/2-φ)=φ by ring] using hh.trans D.cut

/-- The reflected active interval also has exactly zero paired wall slack. -/
theorem ActiveArcData.wideTriple_left_active {φ c m : ℝ} {K : Set Point}
    (D : ActiveArcData φ c K)
    (hsym : ∀ t ∈ Icc (0 : ℝ) π, supp K t = supp K (π-t)+2*m*cos t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (π/2-c)) :
    supp K (π/2+s)+supp (D.wideTriple hsym).1.2.2.1 (3*π/2+s)=1 := by
  change supp K (π/2+s)+supp (verticalReflection m '' D.body) (3*π/2+s)=1
  rw [reflected_paired_support D.body_isConvexBody hsym
    ⟨hs.1,by linarith [hs.2,D.order.1,D.order.2.1]⟩]
  exact D.active ⟨by linarith [hs.2],by linarith [hs.1]⟩

end MovingSofaQuantitative
