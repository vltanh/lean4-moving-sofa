module

public import MovingSofaQuantitative.SectorSlicing

/-!
# An actual set with the required eroded-sector area

Uncompiled proof source. The witness is the union of two open region-between
sets. Each is contained in the closed eroded sector, their horizontal intervals
are disjoint, and their computed areas add. Rigid transport handles an arbitrary
center and direction. This is an actual-set area result, not a support-only or
scalar surrogate for recovery.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def sectorTriangle (ρ h r a : ℝ) : Set Point :=
  regionBetween (fun x => -(tan h * (x - r / sin h)))
    (fun x => tan h * (x - r / sin h)) (Ioo (r / sin h) (ρ * cos a))

def sectorCircle (ρ a : ℝ) : Set Point :=
  regionBetween (fun x => -circleHeight ρ x) (circleHeight ρ) (Ioo (ρ * cos a) ρ)

def sectorWitness (ρ h r a : ℝ) : Set Point := sectorTriangle ρ h r a ∪ sectorCircle ρ a

private theorem symmetric_strip_isOpen (a b : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    IsOpen (regionBetween (fun x => -f x) f (Ioo a b)) := by
  change IsOpen {p : Point | p.1 ∈ Ioo a b ∧ -f p.1 < p.2 ∧ p.2 < f p.1}
  exact (isOpen_Ioo.preimage continuous_fst).inter
    ((isOpen_lt (hf.comp continuous_fst).neg continuous_snd).inter
      (isOpen_lt continuous_snd (hf.comp continuous_fst)))

private theorem disk_membership_of_square {p : Point} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsq : p.1 ^ 2 + p.2 ^ 2 ≤ ρ ^ 2) : norm2 p ≤ ρ := by
  have hn := norm2_sq p
  simp only [dot] at hn
  nlinarith [norm2_nonneg p]

/-- The contact line passes through the circular endpoint selected by a. -/
theorem sector_contact_equation {ρ h a r : ℝ} (hh : h ∈ Ioo 0 (π / 2))
    (hr : r = ρ * sin (h - a)) :
    tan h * (ρ * cos a - r / sin h) = ρ * sin a := by
  have hs := (sin_pos_of_pos_of_lt_pi hh.1 (by linarith [hh.2, pi_pos])).ne'
  have hc := (cos_pos_of_mem_Ioo ⟨by linarith [hh.1, pi_pos], hh.2⟩).ne'
  rw [hr, sin_sub, tan_eq_sin_div_cos]
  field_simp
  ring

/-- Both Cartesian slices lie in the two supporting half-planes and the disk. -/
theorem sectorWitness_subset {ρ h a r : ℝ} (hρ : 0 < ρ)
    (hh : h ∈ Ioo 0 (π / 2)) (ha : a ∈ Ioc 0 h)
    (hr : r = ρ * sin (h - a)) :
    sectorWitness ρ h r a ⊆ erodedSector 0 0 h r ρ := by
  have hs : 0 < sin h := sin_pos_of_pos_of_lt_pi hh.1 (by linarith [hh.2, pi_pos])
  have hc : 0 < cos h := cos_pos_of_mem_Ioo ⟨by linarith [hh.1, pi_pos], hh.2⟩
  have hsa : 0 < sin a := sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, hh.2, pi_pos])
  have hca : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith [ha.1, pi_pos], ha.2.trans_lt hh.2⟩
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact mul_nonneg hρ.le (sin_nonneg_of_mem_Icc ⟨sub_nonneg.mpr ha.2, by linarith [ha.1, hh.2, pi_pos]⟩)
  have hm : 0 < tan h := by rw [tan_eq_sin_div_cos]; positivity
  have hcontact := sector_contact_equation hh hr
  have hbase : r / sin h < ρ * cos a := by
    have hy : 0 < tan h * (ρ * cos a - r / sin h) := by rw [hcontact]; positivity
    exact sub_pos.mp ((mul_pos_iff.mp hy).resolve_right (by intro hn; exact (not_lt_of_ge hm.le) hn.1)).2
  have hp0 : 0 ≤ r / sin h := div_nonneg hr0 hs.le
  have hheight : 0 ≤ ρ * sin a := mul_nonneg hρ.le hsa.le
  have hcorner : (ρ * cos a) ^ 2 + (ρ * sin a) ^ 2 = ρ ^ 2 := by
    nlinarith [sin_sq_add_cos_sq a]
  have hline : ρ * cos a * sin h - ρ * sin a * cos h = r := by
    rw [hr, sin_sub]
    ring
  have htan : tan h * cos h = sin h := by
    rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ hc.ne']
  intro p hp
  have hp' : r ≤ p.1 * sin h + p.2 * cos h ∧
      r ≤ p.1 * sin h - p.2 * cos h ∧ norm2 p ≤ ρ := by
    rcases hp with hp | hp
    · have hx0 : 0 ≤ p.1 := hp0.trans hp.1.1.le
      have hxX : p.1 ≤ ρ * cos a := hp.1.2.le
      have hylo : -(ρ * sin a) ≤ p.2 := by
        have hl := mul_le_mul_of_nonneg_left (show p.1 - r / sin h ≤ ρ * cos a - r / sin h by linarith) hm.le
        rw [hcontact] at hl
        linarith [hp.2.1]
      have hyhi : p.2 ≤ ρ * sin a := by
        have hl := mul_le_mul_of_nonneg_left (show p.1 - r / sin h ≤ ρ * cos a - r / sin h by linarith) hm.le
        rw [hcontact] at hl
        linarith [hp.2.2]
      have hL : tan h * (p.1 - r / sin h) * cos h = p.1 * sin h - r := by
        rw [mul_right_comm, htan]
        field_simp [hs.ne']
        ring
      have hy1 := mul_le_mul_of_nonneg_right hp.2.1.le hc.le
      have hy2 := mul_le_mul_of_nonneg_right hp.2.2.le hc.le
      refine ⟨by nlinarith only [hy1, hL], by nlinarith only [hy2, hL], ?_⟩
      apply disk_membership_of_square hρ.le
      have hxsq := pow_le_pow_left₀ hx0 hxX 2
      have hysq : p.2 ^ 2 ≤ (ρ * sin a) ^ 2 := by
        nlinarith [sq_nonneg (p.2 - ρ * sin a), mul_nonneg (by linarith : 0 ≤ ρ * sin a - p.2)
          (by linarith : 0 ≤ ρ * sin a + p.2)]
      nlinarith only [hcorner, hxsq, hysq]
    · have hx : 0 ≤ p.1 := (mul_nonneg hρ.le hca.le).trans hp.1.1.le
      have hxρ : p.1 ≤ ρ := hp.1.2.le
      have hrad : 0 ≤ ρ ^ 2 - p.1 ^ 2 := by nlinarith
      have hsquare := sq_sqrt hrad
      have hroot : circleHeight ρ p.1 ≤ ρ * sin a := by
        unfold circleHeight
        have hxsq := pow_le_pow_left₀ (mul_nonneg hρ.le hca.le) hp.1.1.le 2
        nlinarith [sqrt_nonneg (ρ ^ 2 - p.1 ^ 2)]
      have hylo : -(ρ * sin a) ≤ p.2 := by linarith [hp.2.1]
      have hyhi : p.2 ≤ ρ * sin a := by linarith [hp.2.2]
      have hxsin := mul_le_mul_of_nonneg_right hp.1.1.le hs.le
      have hy1 := mul_le_mul_of_nonneg_right hylo hc.le
      have hy2 := mul_le_mul_of_nonneg_right hyhi hc.le
      refine ⟨by linarith [hline], by linarith [hline], ?_⟩
      apply disk_membership_of_square hρ.le
      have habs : |p.2| ≤ circleHeight ρ p.1 := abs_le.mpr ⟨hp.2.1.le, hp.2.2.le⟩
      have hysq := pow_le_pow_left₀ (abs_nonneg p.2) habs 2
      rw [sq_abs] at hysq
      change p.2 ^ 2 ≤ sqrt (ρ ^ 2 - p.1 ^ 2) ^ 2 at hysq
      nlinarith only [hysq, hsquare]
  change r ≤ dot (p - 0) (uvec (0 + (π / 2 - h))) ∧
    r ≤ dot (p - 0) (uvec (0 - (π / 2 - h))) ∧ euclideanDist 0 p ≤ ρ
  simpa [dot, uvec, euclideanDist, cos_pi_div_two_sub, sin_pi_div_two_sub,
    cos_neg, sin_neg, norm2_neg] using hp'

/-- The two pieces have the full surviving area, even though their dividing
vertical segment is omitted. -/
theorem area_sectorWitness {ρ h a r : ℝ} (hρ : 0 < ρ)
    (hh : h ∈ Ioo 0 (π / 2)) (ha : a ∈ Ioc 0 h)
    (hr : r = ρ * sin (h - a)) :
    area (sectorWitness ρ h r a) = ρ ^ 2 * a - (r / sin h) * (ρ * sin a) := by
  have hs : 0 < sin h := sin_pos_of_pos_of_lt_pi hh.1 (by linarith [hh.2, pi_pos])
  have hc : 0 < cos h := cos_pos_of_mem_Ioo ⟨by linarith [hh.1, pi_pos], hh.2⟩
  have hm : 0 < tan h := by rw [tan_eq_sin_div_cos]; positivity
  have hsa := sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, hh.2, pi_pos])
  have hcontact := sector_contact_equation hh hr
  have hbase : r / sin h ≤ ρ * cos a := by
    have hy : 0 ≤ tan h * (ρ * cos a - r / sin h) := by rw [hcontact]; positivity
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hm).mp hy)
  have hsub := sectorWitness_subset hρ hh ha hr
  have hdisk : sectorWitness ρ h r a ⊆ euclideanDisk ρ := by
    intro p hp
    have h := (hsub hp).2.2
    simpa [euclideanDist, norm2_neg] using h
  have hA : MeasurableSet (sectorTriangle ρ h r a) :=
    (symmetric_strip_isOpen _ _ (by fun_prop)).measurableSet
  have hB : MeasurableSet (sectorCircle ρ a) :=
    (symmetric_strip_isOpen _ _ (by unfold circleHeight; fun_prop)).measurableSet
  rw [sectorWitness, area_union_disjoint_compact_bounds
    (euclideanDisk_isConvexBody hρ.le).2.1 hA hB
    (fun _ hp => hdisk (Or.inl hp)) (fun _ hp => hdisk (Or.inr hp)) (strips_disjoint _ _),
    sectorTriangle, area_linear_strip hbase hm.le,
    sectorCircle, area_circular_segment hρ ⟨ha.1.le, ha.2.trans hh.2.le⟩]
  nlinarith [congrArg (fun z : ℝ => (ρ * cos a - r / sin h) * z) hcontact]

/-- Rotation and translation preserve the sector inequalities and Euclidean
radius. All normals are rotated together, never approximated numerically. -/
theorem erodedSector_rigid_image (p : Point) (θ h r ρ : ℝ) :
    (Rigid.mk θ p) '' erodedSector 0 0 h r ρ = erodedSector p θ h r ρ := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    change r ≤ dot (rot θ z + p - p) (uvec (θ + (π / 2 - h))) ∧
      r ≤ dot (rot θ z + p - p) (uvec (θ - (π / 2 - h))) ∧
      norm2 (p - (rot θ z + p)) ≤ ρ
    have h1 : dot (rot θ z) (uvec (θ + (π / 2 - h))) = dot z (uvec (π / 2 - h)) := by
      simp [dot, rot, uvec, cos_add, sin_add]
      linear_combination (z.1 * cos (π / 2 - h) + z.2 * sin (π / 2 - h)) * cos_sq_add_sin_sq θ
    have h2 : dot (rot θ z) (uvec (θ - (π / 2 - h))) = dot z (uvec (-(π / 2 - h))) := by
      rw [sub_eq_add_neg]
      simp [dot, rot, uvec, cos_add, sin_add]
      linear_combination (z.1 * cos (-(π / 2 - h)) + z.2 * sin (-(π / 2 - h))) * cos_sq_add_sin_sq θ
    simpa [erodedSector, euclideanDist, add_sub_cancel_right, h1, h2,
      show p - (rot θ z + p) = -(rot θ z) by abel, norm2_neg, norm2_rot] using hz
  · intro hq
    let g : Rigid := ⟨θ, p⟩
    refine ⟨g.symm q, ?_, g.apply_symm_apply q⟩
    have he : g (g.symm q) = q := g.apply_symm_apply q
    have hrot : rot θ (g.symm q) = q - p := by
      change rot θ (g.symm q) + p = q at he
      exact eq_sub_iff_add_eq.mpr he
    change r ≤ dot (g.symm q) (uvec (π / 2 - h)) ∧
      r ≤ dot (g.symm q) (uvec (-(π / 2 - h))) ∧ euclideanDist 0 (g.symm q) ≤ ρ
    have proj (a : ℝ) : dot (g.symm q) (uvec a) = dot (q - p) (uvec (θ + a)) := by
      rw [← hrot]
      simp [dot, rot, uvec, cos_add, sin_add]
      linear_combination -( (g.symm q).1 * cos a + (g.symm q).2 * sin a) * cos_sq_add_sin_sq θ
    refine ⟨?_, ?_, ?_⟩
    · rw [proj]
      exact hq.1
    · rw [proj, ← sub_eq_add_neg]
      exact hq.2.1
    · have hd := euclideanDist_rigid g 0 (g.symm q)
      simpa [g, Rigid.apply, rot, he] using hd.symm.le.trans hq.2.2

/-- Every nonempty eroded sector contains a measurable witness with exactly
the area used in the scalar budget. -/
theorem erodedSector_area_witness (p : Point) (θ : ℝ) {h r ρ : ℝ}
    (hh : h ∈ Ioo 0 (π / 2)) (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hfit : r < ρ * sin h) :
    ∃ W : Set Point, W ⊆ erodedSector p θ h r ρ ∧
      area W = ρ ^ 2 * sectorAreaFactor h (r / ρ) := by
  let u := r / ρ
  let a := h - arcsin u
  have hs : 0 < sin h := sin_pos_of_pos_of_lt_pi hh.1 (by linarith [hh.2, pi_pos])
  have hu0 : 0 ≤ u := div_nonneg hr hρ.le
  have huSin : u < sin h := (div_lt_iff₀ hρ).mpr (by simpa [mul_comm] using hfit)
  have hu1 : u < 1 := huSin.trans_le (sin_le_one h)
  have hasin : arcsin u < h := by
    rw [← arcsin_sin (by linarith [hh.1, pi_pos]) hh.2.le]
    exact strictMonoOn_arcsin ⟨by linarith, hu1.le⟩ ⟨by linarith [hs], sin_le_one h⟩ huSin
  have ha : a ∈ Ioc 0 h := ⟨sub_pos.mpr hasin, sub_le_self _ (arcsin_nonneg.mpr hu0)⟩
  have hrrel : r = ρ * sin (h - a) := by
    dsimp [a]
    rw [sub_sub_cancel, sin_arcsin (by linarith) hu1.le]
    dsimp [u]
    field_simp
  let g : Rigid := ⟨θ, p⟩
  refine ⟨g '' sectorWitness ρ h r a, ?_, ?_⟩
  · rw [← erodedSector_rigid_image p θ h r ρ]
    exact image_mono (sectorWitness_subset hρ hh ha hrrel)
  · rw [Rigid.area_image, area_sectorWitness hρ hh ha hrrel]
    have haSin : sin a = sin h * sqrt (1 - u ^ 2) - cos h * u := by
      dsimp [a]
      rw [sin_sub, cos_arcsin, sin_arcsin (by linarith) hu1.le]
    rw [haSin]
    unfold sectorAreaFactor
    dsimp [a, u]
    field_simp [hs.ne', hρ.ne']
    ring

end MovingSofaQuantitative
