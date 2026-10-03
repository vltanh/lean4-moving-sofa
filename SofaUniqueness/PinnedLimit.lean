module

public import SofaUniqueness.PinnedVariation
public import SofaUniqueness.SelectedCaps

/-!
# Pinned bounds for the specified continuum maximizer

The polygon inequalities here are w<=tau and z<=tau. They are valid before
balancedness and are not the balanced-polygon Theorem 4.1.2. The selected
polygons have vanishing signed pinned defects; upper semicontinuity of a fixed
edge length then gives the desired inequalities for their specified limit.

Positive sofa-area is stated because it supplies the compact selector. In the
shape-uniqueness application it follows from the already proved lower bound
on Gerver's area, not from any additional assumption on the starting sofa.

Uncompiled source. No admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofa

namespace SofaUniqueness

/-- The completed inner boundary, not the outer top edge, is bounded below
by the right gap before any maximality or stationarity argument is used. -/
theorem polygon_wedgeGapW_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapWInf K Θ.ω ≤ tau Θ K (π / 2) := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K t - 1) / cos t) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := π / 2) (Or.inr rfl)).2
  rw [show π / 2 + π = 3 * π / 2 by ring] at h352
  have hσ := ang_supp_zero_le_sigmaAt hK.1 hω
  have h1 := ang_wedgeGapWInf_le_supp_zero hK.1 hω
  have h2 := ang_wedgeGapWInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapW_eq] at h2
  rcases le_total ((supp K t₀ - 1) / cos t₀) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

theorem polygon_wedgeGapZ_le_tau {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) :
    wedgeGapZInf K Θ.ω ≤ tau Θ K Θ.ω := by
  obtain ⟨t₀, ht₀, hmax⟩ :=
    Θ.angles.exists_max_image (fun t => (supp K (t + π / 2) - 1) / cos (Θ.ω - t)) Θ.nonempty
  have hℓ := ang_lineLength_polyNiche_le_z (K := K) hω hmax
  have h352 := (lemma3_4_5_two hK (t := Θ.ω) (Or.inl rfl)).2
  have hσ := ang_supp_le_sigmaAt_add_pi hK.1 hω
  have h1 := ang_wedgeGapZInf_le_supp hK.1 hω
  have h2 := ang_wedgeGapZInf_le hK.1.2.1 hω (Θ.subset t₀ ht₀)
  rw [ang_wedgeGapZ_eq] at h2
  rcases le_total ((supp K (t₀ + π / 2) - 1) / cos (Θ.ω - t₀)) 0 with hW | hW
  · rw [max_eq_right hW] at hℓ
    linarith
  · rw [max_eq_left hW] at hℓ
    linarith

/-- A common coordinate box bounds the supports in every direction. -/
theorem abs_supp_le_box {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {R : ℝ}
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) (t : ℝ) :
    |supp K t| ≤ R + 1 := by
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hpt]
  have h := mpc_abs_dot_uvec_le p t
  obtain ⟨hx, hy⟩ := hbox hp
  have hx' : |p.1| ≤ R := abs_le.mpr hx
  have hy' : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  linarith

/-- Pinned inequalities for every specified cap maximizing a positive value.
The sequence in this proof converges to K itself. -/
theorem pinned_bounds_of_maximal_positive {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    {K : Set (ℝ × ℝ)} (hK : IsCap K ω) (hpositive : 0 < sofaArea ω K)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  classical
  have hω' : ω ∈ Ioc 0 (π / 2) := ⟨hω.1, hω.2.le⟩
  obtain ⟨seq⟩ := exists_selectedCapSequence hω' hK hpositive hmax
  let Ks := seq.cap
  have hcap : ∀ n, IsCap (Ks n) ω := fun n => (seq.selected n).1.1
  have hcb : ∀ n, IsConvexBody (Ks n) := fun n => (hcap n).2.1
  let η : ℕ → ℝ := fun n => hausdorffDist (Ks n) K
  have hη : ∀ n, 0 ≤ η n := fun n => ang_hausdorffDist_nonneg (hcb n) hK.2.1
  have hηlim : Tendsto η atTop (𝓝 0) := seq.tends
  let R := seq.radius + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith [seq.radius_nonneg]
  have hsupp : ∀ n s, |supp (Ks n) s| ≤ R :=
    fun n s => abs_supp_le_box (hcb n) (seq.boxed n) s
  have hclose : ∀ n s, |supp (Ks n) s - supp K s| ≤ η n :=
    fun n s => ang_abs_supp_sub_le_hausdorffDist (hcb n) hK.2.1 s
  let G := 2 * R + 2 / cos ω + 1
  have hcos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [hω.1, pi_pos], hω.2⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let err (t : ℝ) (n : ℕ) := (2 + 4 * G) * η n / sin t
  have herrlim : ∀ t, Tendsto (err t) atTop (𝓝 0) := by
    intro t
    simpa [err] using (hηlim.const_mul (2 + 4 * G)).div_const (sin t)
  have hdefect : ∀ n t, (t = ω ∨ t = π / 2) →
      |sigmaAt (Ks n) t - tau (dyadicAngleSet ω hω' (seq.index n)) (Ks n) t| ≤ err t n := by
    intro n t ht
    let S := dyadicSamples ω hω' (seq.index n)
    have htd : t ∈ (dyadicAngleSet ω hω' (seq.index n)).diamond := by
      rcases ht with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have h := abs_selected_defect_le S (seq.selected n) hω.2 (hη n) hR
      (hsupp n) (fun i => hclose n (S.normal i)) htd
    have hmass : S.totalWeight ≤ 1 := dyadic_totalWeight_le_one ω hω' (seq.index n)
    have hnumer : 2 * η n * S.totalWeight + 4 * S.totalWeight * η n * G ≤
        (2 + 4 * G) * η n := by
      have h₀ := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hη n))
      have h₁ := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hη n)) hG)
      nlinarith
    have hsint : 0 ≤ sin t := (mpc_sin_pos_of_diamond htd).le
    exact h.trans (div_le_div_of_nonneg_right hnumer hsint)
  have hgapErr : Tendsto (fun n => (1 + 1 / cos ω) * η n) atTop (𝓝 0) := by
    simpa using hηlim.const_mul (1 + 1 / cos ω)
  constructor
  · have hw : Tendsto (fun n => wedgeGapWInf (Ks n) ω) atTop (𝓝 (wedgeGapWInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun n => lemma4_1_1 hω.2 (hcap n) hK) hgapErr
    have hlim : Tendsto (fun n => wedgeGapWInf (Ks n) ω - err (π / 2) n)
        atTop (𝓝 (wedgeGapWInf K ω)) := by
      simpa using hw.sub (herrlim (π / 2))
    apply ang_le_sigmaAt_of_tendsto hcb hK.2.1 seq.tends hlim
    intro n
    have hτ : wedgeGapWInf (Ks n) ω ≤
        tau (dyadicAngleSet ω hω' (seq.index n)) (Ks n) (π / 2) :=
      polygon_wedgeGapW_le_tau (seq.selected n).1 hω.2
    have hd := (abs_le.mp (hdefect n (π / 2) (Or.inr rfl))).1
    linarith
  · have hz : Tendsto (fun n => wedgeGapZInf (Ks n) ω) atTop (𝓝 (wedgeGapZInf K ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _)
        (fun n => ang_abs_wedgeGapZInf_sub_le hω.2 (hcap n) hK) hgapErr
    have hlim : Tendsto (fun n => wedgeGapZInf (Ks n) ω - err ω n)
        atTop (𝓝 (wedgeGapZInf K ω)) := by
      simpa using hz.sub (herrlim ω)
    apply ang_le_sigmaAt_of_tendsto hcb hK.2.1 seq.tends hlim
    intro n
    have hτ : wedgeGapZInf (Ks n) ω ≤
        tau (dyadicAngleSet ω hω' (seq.index n)) (Ks n) ω :=
      polygon_wedgeGapZ_le_tau (seq.selected n).1 hω.2
    have hd := (abs_le.mp (hdefect n ω (Or.inl rfl))).1
    linarith

end SofaUniqueness
