module

public import MovingSofaOptimality.Angle.HorizontalSide
public import MovingSofaUniqueness.Selection

/-!
# Proposition 2: variations of the selected polygons

Raising one defining height of a penalized maximizer, or moving one of its two pinned strips,
bounds the defect between the edge length `σ` and the polygon quantity `τ` by the change of the
penalty (`floating_defect_le`, `pinned_defect_le`, inequalities (11) and (12) of note 20). Along the
selected sequence these defects vanish, which gives the pinned bounds (19) for the limit cap
(`pinned_bounds_of_maximal_positive`).
-/

@[expose] public section
noncomputable section

/-!
## Scalar lemmas for first variations

If `d * ε ≤ C * ε ^ 2` for all small `ε > 0`, then `d ≤ 0` (`le_zero_of_mul_le_sq`); this turns
penalized maximality into a bound on a first variation. If nonnegative weights satisfy
`∑ w i * d i = 0`, and `d i ≤ e i` with `e i ≥ 0`, then `|d k| ≤ (∑ w i * e i) / w k` whenever
`w k > 0` (`abs_defect_le_div`). With the weights `sin t`, this turns upper bounds on the defects
into the two-sided bound (12) of note 20.
-/

section

open Set
open scoped BigOperators

namespace MovingSofaUniqueness

/-- If `d * ε ≤ C * ε ^ 2` for every `ε ∈ (0, ε₀]`, then `d ≤ 0`. -/
theorem le_zero_of_mul_le_sq {d C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε ∈ Ioc (0 : ℝ) ε₀, d * ε ≤ C * ε ^ 2) : d ≤ 0 := by
  by_contra hnot
  have hd : 0 < d := lt_of_not_ge hnot
  let ε := min ε₀ (d / (2 * (|C| + 1)))
  have hC : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεd : ε ≤ d / (2 * (|C| + 1)) := min_le_right _ _
  have hm : ε * (2 * (|C| + 1)) ≤ d :=
    (le_div_iff₀ (by positivity)).mp hεd
  have hbound := h ε ⟨hε, hεle⟩
  have habs : C ≤ |C| := le_abs_self C
  have hsmall : C * ε ^ 2 < d * ε := by
    nlinarith [mul_pos hε hε]
  exact (not_lt_of_ge hbound) hsmall

/-- If `∑ w i * d i = 0`, with `w i ≥ 0` and `d i ≤ e i` where `e i ≥ 0`, then
`|w k * d k| ≤ ∑ w i * e i`. -/
theorem abs_weighted_defect_le {ι : Type*} (s : Finset ι)
    (w d e : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hd : ∀ i ∈ s, d i ≤ e i)
    (hsum : (∑ i ∈ s, w i * d i) = 0) {k : ι} (hk : k ∈ s) :
    |w k * d k| ≤ ∑ i ∈ s, w i * e i := by
  have heach := Finset.single_le_sum (s := s) (f := fun i => w i * e i)
    (fun i hi => mul_nonneg (hw i hi) (he i hi)) hk
  have hgap := Finset.single_le_sum (s := s)
    (f := fun i => w i * (e i - d i))
    (fun i hi => mul_nonneg (hw i hi) (sub_nonneg.mpr (hd i hi))) hk
  simp_rw [mul_sub] at hgap
  rw [Finset.sum_sub_distrib, hsum, sub_zero] at hgap
  have hnonneg : 0 ≤ w k * e k := mul_nonneg (hw k hk) (he k hk)
  have hupper : w k * d k ≤ w k * e k :=
    mul_le_mul_of_nonneg_left (hd k hk) (hw k hk)
  rw [abs_le]
  constructor <;> linarith

/-- The bound of `abs_weighted_defect_le`, divided by a positive weight `w k`. -/
theorem abs_defect_le_div {ι : Type*} (s : Finset ι)
    (w d e : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (he : ∀ i ∈ s, 0 ≤ e i) (hd : ∀ i ∈ s, d i ≤ e i)
    (hsum : (∑ i ∈ s, w i * d i) = 0) {k : ι} (hk : k ∈ s)
    (hwk : 0 < w k) : |d k| ≤ (∑ i ∈ s, w i * e i) / w k := by
  have h := abs_weighted_defect_le s w d e hw he hd hsum hk
  rw [abs_mul, abs_of_pos hwk] at h
  apply (le_div_iff₀ hwk).mpr
  simpa only [mul_comm] using h

end MovingSofaUniqueness

end

/-!
## Penalized maximality bounds the variation defect

Raising the assigned height `h_K(t)` of a polygon cap at a defining normal `t` by `ε > 0` changes
`A_Θ` by `(σ_K(t) - τ_K(t)) ε + O(ε²)` (Baek's Lemma 3.4.7), and the area `A_Θ` of assigned heights
is at most that of the polygon cap they define (Baek's Proposition 3.3.7,
`assigned_comparison_of_actual`). So if the move increases the penalty by at most `b ε + D ε²`,
penalized maximality gives `σ_K(t) - τ_K(t) ≤ b` (`polygon_defect_le_penalty_growth`). At a normal
with `σ_K(t) = 0` this bound holds for every `b ≥ 0`, since `τ_K(t) ≥ 0`
(`polygon_defect_le_of_zero_facet`).
-/

section

open Set Real MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The area `A_Θ` of the assigned heights `h_K`, raised by `ε` at the normal `t`. -/
def assignedAreaIncrement (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t ε : ℝ) : ℝ :=
  areaH Θ (Function.update (supp K) t (supp K t + ε))

/-- A comparison `A_Θ(C) - Pε ≤ A_Θ(K) - P₀` of penalized objectives passes to assigned heights
whose cap is a translate of `C`: their area `A_Θ` is at most `A_Θ(C)` (Baek's
Proposition 3.3.7). -/
theorem assigned_comparison_of_actual {Θ : AngleSet}
    {K C : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C)
    (height : ℝ → ℝ) (v : ℝ × ℝ)
    (hset : capH Θ height = (fun p => p + v) '' C)
    (P₀ Pε : ℝ)
    (hselect : polyArea Θ C - Pε ≤ polyArea Θ K - P₀) :
    areaH Θ height - Pε ≤ areaH Θ (supp K) - P₀ := by
  have htr : IsPolygonCapTranslate Θ (capH Θ height) := ⟨C, v, hC, hset⟩
  have hbound := proposition3_3_7 htr
  have hactual : areaT Θ (capH Θ height) = polyArea Θ C := by
    rw [hset]
    exact (theorem3_3_6 hC v).2
  have hbase : areaH Θ (supp K) = polyArea Θ K := (proposition3_3_5 hK).2
  rw [hactual] at hbound
  rw [hbase]
  linarith

/-- If, for `ε ∈ (0, ε₀]`, the assigned heights raised by `ε` at `t` have penalized objective at
most that of `K`, and the penalty grows by at most `b ε + D ε²`, then `σ_K(t) - τ_K(t) ≤ b`. -/
theorem polygon_defect_le_penalty_growth {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.diamond)
    (P : ℝ → ℝ) {ε₀ b D : ℝ} (hε₀ : 0 < ε₀)
    (hP : ∀ ε ∈ Ioc (0 : ℝ) ε₀, P ε - P 0 ≤ b * ε + D * ε ^ 2)
    (hcompare : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      assignedAreaIncrement Θ K t ε - P ε ≤ areaH Θ (supp K) - P 0) :
    sigmaAt K t - tau Θ K t ≤ b := by
  obtain ⟨r, hr, C, hC⟩ := lemma3_4_7 hK ht
  have hsmall : 0 < min r ε₀ := lt_min hr hε₀
  have hd : sigmaAt K t - tau Θ K t - b ≤ 0 :=
    le_zero_of_mul_le_sq (C := C + D) hsmall (by
      intro ε hε
      have he₁ : ε ∈ Ioc (0 : ℝ) r :=
        ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
      have he₂ : ε ∈ Ioc (0 : ℝ) ε₀ :=
        ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
      have ha := (abs_le.mp (hC ε he₁)).1
      have hp := hP ε he₂
      have hm := hcompare ε he₂
      unfold assignedAreaIncrement at hm
      nlinarith)
  linarith

/-- If `σ_K(t) = 0`, then `σ_K(t) - τ_K(t) ≤ b` for every `b ≥ 0`. -/
theorem polygon_defect_le_of_zero_facet {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    {t b : ℝ} (hσ : sigmaAt K t = 0) (hb : 0 ≤ b) :
    sigmaAt K t - tau Θ K t ≤ b := by
  have hτ : 0 ≤ tau Θ K t := tsum_nonneg (fun c => ENNReal.toReal_nonneg)
  rw [hσ]
  linarith

end MovingSofaUniqueness

end

/-!
## Floating facets: inequality (11)

The floating normals are the defining normals other than `ω` and `π/2`. Raising the height of a
polygon cap `K` at a floating normal `t` by `ε ≥ 0` gives a polygon cap `floatingCap Θ K t ε` that
contains `K`; its supports at the other defining normals are those of `K`, and at `t` its support
rises by at most `ε`. So the penalty grows by at most `atNormal t * (2 * η * ε + ε ^ 2)` when the
sampled supports of `K` are within `η` of the target (`floating_penalty_growth`), and a penalized
maximizer satisfies `σ_K(t) - τ_K(t) ≤ 2 * η * atNormal t` (`floating_defect_le`), inequality (11)
of note 20.
-/

section

open Set Real MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The cap of the assigned heights `h_K`, raised by `ε` at the normal `t`. -/
def floatingCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t ε : ℝ) : Set (ℝ × ℝ) :=
  capH Θ (Function.update (supp K) t (supp K t + ε))

/-- Raising a floating height by `ε ≥ 0` gives a polygon cap. -/
theorem floatingCap_polygon {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ} (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hε : 0 ≤ ε) : IsPolygonCap Θ (floatingCap Θ K t ε) :=
  mpc_capH_update_inner hK htω htL hε

/-- Raising a height by `0` gives back the polygon cap. -/
@[simp] theorem floatingCap_zero {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (t : ℝ) : floatingCap Θ K t 0 = K := by
  unfold floatingCap
  rw [add_zero, Function.update_eq_self]
  exact proposition3_3_4 ⟨K, 0, hK, by simp⟩

/-- A point of `K` lies below the assigned heights `h_K` raised by `ε ≥ 0` at a normal `t`. -/
theorem dot_le_update_of_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K)
    {p : ℝ × ℝ} (hp : p ∈ K) {ε : ℝ} (hε : 0 ≤ ε) (t s : ℝ) :
    dot p (uvec s) ≤ Function.update (supp K) t (supp K t + ε) s := by
  have h := dot_le_supp hK.1.2.1.2.1 hp s
  rcases eq_or_ne s t with rfl | hst
  · rw [Function.update_self]
    linarith
  · rwa [Function.update_of_ne hst]

/-- Raising a floating height enlarges the cap. -/
theorem subset_floatingCap {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ} (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hε : 0 ≤ ε) : K ⊆ floatingCap Θ K t ε := by
  intro p hp
  change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε))
  rw [nef_mem_capH_iff]
  refine ⟨fun s _ => dot_le_update_of_mem hK hp hε t s, ?_, ?_⟩
  · rw [Function.update_of_ne htω.symm, hK.1.2.2.1]
    simpa only [sub_self] using hK.1.dot_omega_nonneg hp
  · rw [Function.update_of_ne htL.symm, hK.1.2.2.2.1]
    simpa only [sub_self, dot_uvec_pi_div_two] using hK.1.snd_nonneg hp

/-- At every defining normal `s`, the support of the raised cap lies between `h_K(s)` and the raised
assigned height. -/
theorem floatingCap_support_bounds {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε s : ℝ}
    (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε) (hs : s ∈ Θ.diamond) :
    supp K s ≤ supp (floatingCap Θ K t ε) s ∧
      supp (floatingCap Θ K t ε) s ≤ Function.update (supp K) t (supp K t + ε) s := by
  have hC := floatingCap_polygon hK htω htL hε
  constructor
  · exact supp_mono (subset_floatingCap hK htω htL hε) hK.1.2.1.1 hC.1.2.1.2.1 s
  · apply supp_le_of_forall hC.1.2.1.1
    intro p hp
    change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
    rw [nef_mem_capH_iff] at hp
    exact hp.1 s hs

/-- At the defining normals other than `t`, the raised cap has the supports of `K`. -/
theorem floatingCap_support_other {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε s : ℝ}
    (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε)
    (hs : s ∈ Θ.diamond) (hst : s ≠ t) :
    supp (floatingCap Θ K t ε) s = supp K s := by
  have h := floatingCap_support_bounds hK htω htL hε hs
  rw [Function.update_of_ne hst] at h
  exact le_antisymm h.2 h.1

/-- At the raised normal `t`, the support rises by at most `ε`. -/
theorem floatingCap_support_self {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε) :
    |supp (floatingCap Θ K t ε) t - supp K t| ≤ ε := by
  have h := floatingCap_support_bounds hK htω htL hε ht
  rw [Function.update_self] at h
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith

/-- If the sampled supports of `K` are within `η` of the target, raising the height at a floating
normal `t` by `ε` increases the penalty by at most
`(2 * η * atNormal t) * ε + atNormal t * ε ^ 2`. -/
theorem floating_penalty_growth {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t η ε : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    S.penalty target (floatingCap Θ K t ε) - S.penalty target K ≤
      (2 * η * S.atNormal t) * ε + S.atNormal t * ε ^ 2 := by
  have h := S.penalty_change_one (ε := ε) hη hclose
    (fun i hi => floatingCap_support_other hK htω htL hε (S.normal_mem i) hi)
    (fun i hi => by rw [hi]; exact floatingCap_support_self hK ht htω htL hε)
  have hu := (abs_le.mp h).2
  nlinarith

/-- Inequality (11) of note 20: at a floating normal `t`, a penalized maximizer whose sampled
supports are within `η` of the target satisfies `σ_K(t) - τ_K(t) ≤ 2 * η * atNormal t`. -/
theorem floating_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K) {t η : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hη : 0 ≤ η)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    sigmaAt K t - tau Θ K t ≤ 2 * η * S.atNormal t := by
  let P : ℝ → ℝ := fun ε => S.penalty target (floatingCap Θ K t ε)
  apply polygon_defect_le_penalty_growth hK.1 ht P (ε₀ := 1)
    (D := S.atNormal t) (by norm_num)
  · intro ε hε
    dsimp only [P]
    rw [floatingCap_zero hK.1]
    exact floating_penalty_growth S hK.1 ht htω htL hη hε.1.le hclose
  · intro ε hε
    have hC := floatingCap_polygon hK.1 htω htL hε.1.le
    have hcomp := hK.2 (floatingCap Θ K t ε) hC
    have h := assigned_comparison_of_actual hK.1 hC
      (Function.update (supp K) t (supp K t + ε)) (0 : ℝ × ℝ)
      (by simp [floatingCap]) (S.penalty target K)
      (S.penalty target (floatingCap Θ K t ε)) hcomp
    simpa only [assignedAreaIncrement, P, floatingCap_zero hK.1] using h

end MovingSofaUniqueness

end

/-!
## The pinned move

Let `ω < π/2`, so that a polygon cap `K` contains the origin and the top corner `o_ω`. Raising its
height at a pinned normal `t ∈ {ω, π/2}` by `ε ∈ [0, 1]` moves both lines of the strip of that
normal, and the moved cap `K'` satisfies `(1 - ε) K + ε o_ω ⊆ K' ⊆ (1 + ε) K`
(`pinned_contract_mem`, `pinned_div_mem`). If `K'` is a translate of a polygon cap `C`, as Baek's
Lemma 3.4.8 provides when `σ_K(t) > 0`, the two strips fix the translation up to `O(ε)`
(`pinned_translation_bound`). So the supports of `C` and `K` differ by at most
`(2R + 2 / cos ω + 1) ε` when `|h_K| ≤ R` (`pinned_normalized_support_bound`).
-/

section

open Set Real MovingSofaOptimality

namespace MovingSofaUniqueness

/-- A polygon cap has support `1` at the pinned normals `ω` and `π/2`. -/
theorem pinned_support_value {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {s : ℝ} (hs : s = Θ.ω ∨ s = π / 2) : supp K s = 1 := by
  rcases hs with rfl | rfl
  · exact hK.1.2.2.1
  · exact hK.1.2.2.2.1

/-- The top corner `o_ω` has scalar product `1` with `u_ω` and with `u_{π/2}`. -/
theorem pinned_corner_dot {Θ : AngleSet} {s : ℝ}
    (hs : s = Θ.ω ∨ s = π / 2) : dot (oPt Θ.ω) (uvec s) = 1 := by
  rcases hs with rfl | rfl
  · exact oPt_dot_uvec (Ioc_subset_Icc_self Θ.hω)
  · rw [dot_uvec_pi_div_two, mpc_oPt_snd]

/-- For `ω < π/2` a polygon cap contains the origin, so its supports are nonnegative. -/
theorem pinned_support_nonneg {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) (s : ℝ) : 0 ≤ supp K s := by
  have h := dot_le_supp hK.1.2.1.2.1 (ang_cap_origin_mem hK.1 hω) s
  simpa [dot] using h

/-- For `p ∈ K` and `ε ∈ [0, 1]`, the point `(1 - ε) p + ε o_ω` lies in the cap moved by `ε` at a
pinned normal. -/
theorem pinned_contract_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ K) :
    (1 - ε) • p + ε • oPt Θ.ω ∈ floatingCap Θ K t ε := by
  have ho := hK.1.oPt_mem hω
  have hcombo : (1 - ε) • p + ε • oPt Θ.ω ∈ K :=
    hK.1.2.1.2.2 hp ho (by linarith [hε.2]) hε.1 (by ring)
  change _ ∈ capH Θ (Function.update (supp K) t (supp K t + ε))
  rw [nef_mem_capH_iff]
  refine ⟨fun s _ => dot_le_update_of_mem hK hcombo hε.1 t s, ?_, ?_⟩
  · by_cases hst : Θ.ω = t
    · subst hst
      rw [Function.update_self, pinned_support_value hK ht]
      have hp0 : 0 ≤ dot p (uvec Θ.ω) := hK.1.dot_omega_nonneg hp
      rw [dot_add_left, dot_smul_left, dot_smul_left, pinned_corner_dot ht]
      nlinarith [hε.2]
    · rw [Function.update_of_ne hst, hK.1.2.2.1]
      have h := hK.1.dot_omega_nonneg hcombo
      simpa only [sub_self] using h
  · by_cases hst : π / 2 = t
    · subst hst
      rw [Function.update_self, pinned_support_value hK ht]
      have hp0 : 0 ≤ dot p (uvec (π / 2)) := by
        rw [dot_uvec_pi_div_two]
        exact hK.1.snd_nonneg hp
      rw [dot_add_left, dot_smul_left, dot_smul_left, pinned_corner_dot ht]
      nlinarith [hε.2]
    · rw [Function.update_of_ne hst, hK.1.2.2.2.1]
      have h := hK.1.snd_nonneg hcombo
      simpa only [sub_self, dot_uvec_pi_div_two] using h

/-- The cap moved by `ε ≥ 0` at a pinned normal, scaled by `1 / (1 + ε)` about the origin, lies in
`K`. -/
theorem pinned_div_mem {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : 0 ≤ ε)
    {p : ℝ × ℝ} (hp : p ∈ floatingCap Θ K t ε) :
    (1 / (1 + ε)) • p ∈ K := by
  have hden : 0 < 1 + ε := by linarith
  change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
  rw [nef_mem_capH_iff] at hp
  rw [mpc_polycap_mem_iff hK]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hu := hp.1 s hs
    rw [dot_smul_left, one_div, inv_mul_eq_div, div_le_iff₀ hden]
    by_cases hst : s = t
    · subst s
      rw [Function.update_self, pinned_support_value hK ht] at hu
      rw [pinned_support_value hK ht]
      nlinarith
    · rw [Function.update_of_ne hst] at hu
      have hnonneg := pinned_support_nonneg hK hω s
      nlinarith
  · have hlo : 0 ≤ dot p (uvec Θ.ω) := by
      have h := hp.2.1
      by_cases hst : Θ.ω = t
      · subst hst
        rw [Function.update_self, pinned_support_value hK ht] at h
        linarith
      · rw [Function.update_of_ne hst, hK.1.2.2.1] at h
        linarith
    show 0 ≤ dot ((1 / (1 + ε)) • p) (uvec Θ.ω)
    rw [dot_smul_left]
    exact mul_nonneg (by positivity) hlo
  · have hlo : 0 ≤ dot p (uvec (π / 2)) := by
      have h := hp.2.2
      by_cases hst : π / 2 = t
      · subst hst
        rw [Function.update_self, pinned_support_value hK ht] at h
        linarith
      · rw [Function.update_of_ne hst, hK.1.2.2.2.1] at h
        linarith
    show 0 ≤ dot ((1 / (1 + ε)) • p) (uvec (π / 2))
    rw [dot_smul_left]
    exact mul_nonneg (by positivity) hlo

/-- If `|h_K| ≤ R`, moving a pinned strip by `ε ∈ [0, 1]` changes every support by at most
`2 R ε`. -/
theorem pinned_raw_support_bound {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hω : Θ.ω < π / 2) {t ε R : ℝ}
    (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R) (s : ℝ) :
    |supp (floatingCap Θ K t ε) s - supp K s| ≤ 2 * R * ε := by
  have hcpt : IsCompact (floatingCap Θ K t ε) := mpc_isCompact_capH Θ _
  obtain ⟨q, hq, hqs⟩ := exists_dot_eq_supp hK.1.2.1.2.1 hK.1.2.1.1 s
  have hmem := pinned_contract_mem hK hω ht hε hq
  have hne : (floatingCap Θ K t ε).Nonempty := ⟨_, hmem⟩
  have hupper : supp (floatingCap Θ K t ε) s ≤ (1 + ε) * supp K s := by
    apply supp_le_of_forall hne
    intro p hp
    have h := dot_le_supp hK.1.2.1.2.1 (pinned_div_mem hK hω ht hε.1 hp) s
    rw [dot_smul_left, one_div, inv_mul_eq_div, div_le_iff₀ (by linarith [hε.1] : 0 < 1 + ε)] at h
    nlinarith
  have hlower := dot_le_supp hcpt hmem s
  rw [dot_add_left, dot_smul_left, dot_smul_left, hqs] at hlower
  have ho := hK.1.oPt_mem hω
  have hodot : -R ≤ dot (oPt Θ.ω) (uvec s) := by
    have h := dot_le_supp hK.1.2.1.2.1 ho (s + π)
    rw [dot_uvec_add_pi] at h
    have hb := (abs_le.mp (hsupp (s + π))).2
    linarith
  have hKs := abs_le.mp (hsupp s)
  rw [abs_le]
  constructor <;> nlinarith [hε.1]

/-- If the translate by `v` of a polygon cap lies in the strip `a ≤ dot p (uvec s) ≤ a + 1` at a
pinned normal `s`, then `dot v (uvec s) = a`. -/
theorem translated_strip_support {Θ : AngleSet} {C : Set (ℝ × ℝ)}
    (hC : IsPolygonCap Θ C) (v : ℝ × ℝ) {s a : ℝ}
    (hs : s = Θ.ω ∨ s = π / 2)
    (hlo : ∀ p ∈ (fun q => q + v) '' C, a ≤ dot p (uvec s))
    (hhi : ∀ p ∈ (fun q => q + v) '' C, dot p (uvec s) ≤ a + 1) :
    dot v (uvec s) = a := by
  have hc := hC.1.2.1
  have htop : supp C s = 1 := pinned_support_value hC hs
  have hbot : supp C (s + π) = 0 := by
    rcases hs with rfl | rfl
    · exact hC.1.2.2.2.2.1
    · rw [show π / 2 + π = 3 * π / 2 by ring]
      exact hC.1.2.2.2.2.2.1
  obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hc.2.1 hc.1 s
  obtain ⟨q, hq, hqs⟩ := exists_dot_eq_supp hc.2.1 hc.1 (s + π)
  rw [htop] at hps
  rw [hbot, dot_uvec_add_pi] at hqs
  have hu := hhi (p + v) ⟨p, hp, rfl⟩
  have hl := hlo (q + v) ⟨q, hq, rfl⟩
  rw [dot_add_left, hps] at hu
  rw [dot_add_left] at hl
  linarith

/-- If the cap moved by `ε` at a pinned normal is the translate by `v` of a polygon cap, then
`|dot v (uvec s)| ≤ (2 / cos ω + 1) ε` for every `s`. -/
theorem pinned_translation_bound {Θ : AngleSet} {K C : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C) (hω : Θ.ω < π / 2)
    {t ε : ℝ} (ht : t = Θ.ω ∨ t = π / 2) (hε : 0 ≤ ε)
    (v : ℝ × ℝ) (hset : floatingCap Θ K t ε = (fun p => p + v) '' C) (s : ℝ) :
    |dot v (uvec s)| ≤ (2 / cos Θ.ω + 1) * ε := by
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hsin : 0 ≤ sin Θ.ω := sin_nonneg_of_nonneg_of_le_pi Θ.hω.1.le
    (by linarith [hω, pi_pos])
  let a : ℝ → ℝ := fun r => Function.update (supp K) t (supp K t + ε) r - 1
  have ha : ∀ r, (r = Θ.ω ∨ r = π / 2) → a r ∈ Icc (0 : ℝ) ε := by
    intro r hr
    dsimp [a]
    by_cases hrt : r = t
    · subst r
      rw [Function.update_self, pinned_support_value hK ht]
      constructor <;> linarith
    · rw [Function.update_of_ne hrt, pinned_support_value hK hr]
      constructor <;> linarith
  have hv : ∀ r, (r = Θ.ω ∨ r = π / 2) → dot v (uvec r) = a r := by
    intro r hr
    apply translated_strip_support hC v hr
    · intro p hp
      rw [← hset] at hp
      change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
      rw [nef_mem_capH_iff] at hp
      rcases hr with rfl | rfl
      · exact hp.2.1
      · exact hp.2.2
    · intro p hp
      rw [← hset] at hp
      change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
      rw [nef_mem_capH_iff] at hp
      have h := hp.1 r (Or.inr hr)
      dsimp [a]
      linarith
  have hy := ha (π / 2) (Or.inr rfl)
  have hx := ha Θ.ω (Or.inl rfl)
  rw [← hv (π / 2) (Or.inr rfl), dot_uvec_pi_div_two] at hy
  rw [← hv Θ.ω (Or.inl rfl)] at hx
  have hyabs : |v.2| ≤ ε := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hxy : |v.1| ≤ 2 * ε / cos Θ.ω := by
    rw [le_div_iff₀ hcos]
    simp only [dot, uvec] at hx
    have hs := sin_le_one Θ.ω
    have hprod : v.2 * sin Θ.ω ≤ ε := by nlinarith [hy.1, hy.2]
    rw [← abs_of_pos hcos, ← abs_mul, abs_le]
    constructor <;> nlinarith [hx.1, hx.2, hy.1]
  have hdot := abs_dot_uvec_le v s
  have hbound : |v.1| + |v.2| ≤ (2 / cos Θ.ω + 1) * ε := by
    have heq : 2 * ε / cos Θ.ω + ε = (2 / cos Θ.ω + 1) * ε := by ring
    rw [← heq]
    exact add_le_add hxy hyabs
  exact hdot.trans hbound

/-- If the cap moved by `ε` at a pinned normal is a translate of the polygon cap `C`, the supports
of `C` and `K` differ by at most `(2R + 2 / cos ω + 1) ε`. -/
theorem pinned_normalized_support_bound {Θ : AngleSet} {K C : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (hC : IsPolygonCap Θ C) (hω : Θ.ω < π / 2)
    {t ε R : ℝ} (ht : t = Θ.ω ∨ t = π / 2) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R)
    (v : ℝ × ℝ) (hset : floatingCap Θ K t ε = (fun p => p + v) '' C) (s : ℝ) :
    |supp C s - supp K s| ≤ (2 * R + 2 / cos Θ.ω + 1) * ε := by
  have hraw := pinned_raw_support_bound hK hω ht hε hR hsupp s
  have hv := pinned_translation_bound hK hC hω ht hε.1 v hset s
  have heq : supp (floatingCap Θ K t ε) s = supp C s + dot v (uvec s) := by
    rw [hset]
    exact supp_translate C v s hC.1.2.1.2.1 hC.1.2.1.1
  rw [heq] at hraw
  have htri := abs_sub (supp C s + dot v (uvec s) - supp K s) (dot v (uvec s))
  have halg : supp C s + dot v (uvec s) - supp K s - dot v (uvec s) =
      supp C s - supp K s := by ring
  rw [halg] at htri
  nlinarith

end MovingSofaUniqueness

end

/-!
## Pinned facets: inequality (12)

At a pinned normal `t`, a penalized maximizer `K` with `|h_K| ≤ R`, whose sampled supports are
within `η` of the target, satisfies `σ_K(t) - τ_K(t) ≤ 2 W η (2R + 2 / cos ω + 1)`, where `W` is the
total sample weight (`pinned_defect_le`). Every polygon cap satisfies
`∑_{t ∈ Θ^◇} sin t (σ_K(t) - τ_K(t)) = 0` (`polygon_weighted_defect_zero`), the identity (13) of
note 20. With the floating bounds (11), this bounds every defect from both sides
(`abs_selected_defect_le`), which is inequality (12).
-/

section

open Set Real MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- At a pinned normal `t`, a penalized maximizer with `|h_K| ≤ R`, whose sampled supports are
within `η` of the target, satisfies `σ_K(t) - τ_K(t) ≤ 2 W η (2R + 2 / cos ω + 1)`, where `W` is the
total sample weight. -/
theorem pinned_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K)
    (hω : Θ.ω < π / 2) {t η R : ℝ} (ht : t = Θ.ω ∨ t = π / 2)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    sigmaAt K t - tau Θ K t ≤
      2 * S.totalWeight * η * (2 * R + 2 / cos Θ.ω + 1) := by
  let G := 2 * R + 2 / cos Θ.ω + 1
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have htd : t ∈ Θ.diamond := Or.inr ht
  by_cases hσ : 0 < sigmaAt K t
  · -- For `σ_K(t) > 0`, Baek's Lemma 3.4.8 makes the moved caps translates of polygon caps
    -- `C ε` for small `ε`, whose supports are within `G ε` of those of `K`.
    obtain ⟨r, hr, hfeasible⟩ := lemma3_4_8 hK.1 htd hσ
    let r' := min r 1
    have hr' : 0 < r' := lt_min hr zero_lt_one
    have hC : ∀ e : Ioc (0 : ℝ) r', ∃ C v, IsPolygonCap Θ C ∧
        floatingCap Θ K t e.1 = (fun p => p + v) '' C := by
      intro e
      exact hfeasible e.1 ⟨e.2.1, e.2.2.trans (min_le_left _ _)⟩
    choose C v hCp hset using hC
    let chosen : ℝ → Set (ℝ × ℝ) := fun ε =>
      if he : ε ∈ Ioc (0 : ℝ) r' then C ⟨ε, he⟩ else K
    let P : ℝ → ℝ := fun ε => S.penalty target (chosen ε)
    have hchosen0 : chosen 0 = K := by simp [chosen]
    apply polygon_defect_le_penalty_growth hK.1 htd P hr'
      (D := S.totalWeight * G ^ 2)
    · intro ε he
      have hε : ε ∈ Icc (0 : ℝ) 1 :=
        ⟨he.1.le, he.2.trans (min_le_right _ _)⟩
      have hgrowth := S.penalty_change_uniform hη hclose
        (fun i => pinned_normalized_support_bound hK.1 (hCp ⟨ε, he⟩)
          hω ht hε hR hsupp (v ⟨ε, he⟩) (hset ⟨ε, he⟩) (S.normal i))
      dsimp only [P]
      rw [hchosen0, show chosen ε = C ⟨ε, he⟩ from dite_eq_left he]
      have h := (abs_le.mp hgrowth).2
      dsimp [G] at h ⊢
      nlinarith
    · intro ε he
      have hcompare := hK.2 (C ⟨ε, he⟩) (hCp ⟨ε, he⟩)
      have h := assigned_comparison_of_actual hK.1 (hCp ⟨ε, he⟩)
        (Function.update (supp K) t (supp K t + ε)) (v ⟨ε, he⟩)
        (hset ⟨ε, he⟩) (S.penalty target K) (S.penalty target (C ⟨ε, he⟩)) hcompare
      dsimp only [P]
      rw [hchosen0, show chosen ε = C ⟨ε, he⟩ from dite_eq_left he]
      exact h
  · have hz : sigmaAt K t = 0 := le_antisymm (le_of_not_gt hσ) ENNReal.toReal_nonneg
    apply polygon_defect_le_of_zero_facet hz
    change 0 ≤ 2 * S.totalWeight * η * G
    have hw := S.totalWeight_nonneg
    positivity

/-- The identity (13) of note 20: `∑_{t ∈ Θ^◇} sin t (σ_K(t) - τ_K(t)) = 0` for every polygon
cap. -/
theorem polygon_weighted_defect_zero {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) :
    (∑ t ∈ mpcDiamond Θ, sin t * (sigmaAt K t - tau Θ K t)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_comm (sin _)]
  rw [mpc_sum_sigma_sin hK, mpc_sum_tau_sin hK, sub_self]

/-- The upper bound on the defect at `t`: the floating bound `2 * η * atNormal t`, plus the pinned
bound at `ω` and `π/2`. -/
def selectorDefectBound {Θ : AngleSet} (S : SupportSamples Θ) (G η t : ℝ) : ℝ := by
  exact 2 * η * S.atNormal t +
    if t = Θ.ω ∨ t = π / 2 then 2 * S.totalWeight * η * G else 0

theorem selectorDefectBound_nonneg {Θ : AngleSet} (S : SupportSamples Θ)
    {G η : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) (t : ℝ) :
    0 ≤ selectorDefectBound S G η t := by
  have hw := S.atNormal_nonneg t
  have hW := S.totalWeight_nonneg
  unfold selectorDefectBound
  split_ifs <;> positivity

/-- Summed over `Θ^◇`, the bounds are at most `2 * η * W + 4 * W * η * G`, where `W` is the total
sample weight. -/
theorem selectorDefectBound_sum_le {Θ : AngleSet} (S : SupportSamples Θ)
    {G η : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) :
    (∑ t ∈ mpcDiamond Θ, selectorDefectBound S G η t) ≤
      2 * η * S.totalWeight + 4 * S.totalWeight * η * G := by
  let b := 2 * S.totalWeight * η * G
  have hb : 0 ≤ b := by
    have hW := S.totalWeight_nonneg
    dsimp [b]
    positivity
  -- At most two defining normals are pinned.
  have hpin : (∑ t ∈ mpcDiamond Θ, if t = Θ.ω ∨ t = π / 2 then b else 0) ≤ 2 * b := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((mpcDiamond Θ).filter (fun t => t = Θ.ω ∨ t = π / 2)).card ≤ 2 :=
      (Finset.card_le_card (s := _) (t := {Θ.ω, π / 2}) fun t ht => by
        simpa using (Finset.mem_filter.mp ht).2).trans Finset.card_le_two
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb
  unfold selectorDefectBound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, S.sum_atNormal]
  dsimp [b] at hpin
  linarith

/-- Inequality (12) of note 20: for a penalized maximizer with `|h_K| ≤ R`, whose sampled supports
are within `η` of the target, `|σ_K(t) - τ_K(t)| ≤ (2 η W + 4 W η (2R + 2 / cos ω + 1)) / sin t` at
every defining normal `t`, where `W` is the total sample weight. -/
theorem abs_selected_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K)
    (hω : Θ.ω < π / 2) {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hsupp : ∀ s, |supp K s| ≤ R)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    {t : ℝ} (ht : t ∈ Θ.diamond) :
    |sigmaAt K t - tau Θ K t| ≤
      (2 * η * S.totalWeight +
        4 * S.totalWeight * η * (2 * R + 2 / cos Θ.ω + 1)) / sin t := by
  let G := 2 * R + 2 / cos Θ.ω + 1
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have herror : ∀ s ∈ mpcDiamond Θ,
      sigmaAt K s - tau Θ K s ≤ selectorDefectBound S G η s := by
    intro s hs
    have hsd := mpc_mem_mpcDiamond.mp hs
    by_cases hpin : s = Θ.ω ∨ s = π / 2
    · have h := pinned_defect_le S hK hω hpin hη hR hsupp hclose
      have hnonneg : 0 ≤ 2 * η * S.atNormal s := by
        have hw := S.atNormal_nonneg s
        positivity
      simp only [selectorDefectBound, ite_eq_left hpin]
      exact h.trans (le_add_of_nonneg_left hnonneg)
    · have hnot := not_or.mp hpin
      simpa only [selectorDefectBound, ite_eq_right hpin, add_zero] using
        floating_defect_le S hK hsd hnot.1 hnot.2 hη hclose
  have h := abs_defect_le_div (mpcDiamond Θ) sin
    (fun s => sigmaAt K s - tau Θ K s) (selectorDefectBound S G η)
    (fun s hs => (mpc_sin_pos_of_diamond (mpc_mem_mpcDiamond.mp hs)).le)
    (fun s _ => selectorDefectBound_nonneg S hG hη s) herror
    (polygon_weighted_defect_zero hK.1) (mpc_mem_mpcDiamond.mpr ht)
    (mpc_sin_pos_of_diamond ht)
  have hsum : (∑ s ∈ mpcDiamond Θ, sin s * selectorDefectBound S G η s) ≤
      2 * η * S.totalWeight + 4 * S.totalWeight * η * G := by
    calc
      _ ≤ ∑ s ∈ mpcDiamond Θ, selectorDefectBound S G η s := by
        apply Finset.sum_le_sum
        intro s hs
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (sin_le_one s)
          (selectorDefectBound_nonneg S hG hη s)
      _ ≤ _ := selectorDefectBound_sum_le S hG hη
  exact h.trans (div_le_div_of_nonneg_right hsum (mpc_sin_pos_of_diamond ht).le)

end MovingSofaUniqueness

end

/-!
## The pinned bounds (19)

For a polygon cap with `ω < π/2`, Baek's Lemma 3.4.5 on the sides of the niche along the two strips
gives `w_K° ≤ τ_K(π/2)` and `z_K° ≤ τ_K(ω)` for the wedge gap infima (`ang_wedgeGapWInf_le_tau`,
`ang_wedgeGapZInf_le_tau`). Along the polygon caps selected for a cap `K` that maximizes `A_ω` with
positive value, the pinned defects tend to zero, the gap infima converge (Baek's Lemma 4.1.1), and
the edge length `σ` at a fixed normal is upper semicontinuous. Hence `w_K° ≤ σ_K(π/2)` and
`z_K° ≤ σ_K(ω)` (`pinned_bounds_of_maximal_positive`), the pinned bounds (19) of note 20.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The pinned bounds (19) of note 20: for `ω ∈ (0, π/2)`, a cap maximizing `A_ω` with positive
value satisfies `w_K° ≤ σ_K(π/2)` and `z_K° ≤ σ_K(ω)`. -/
theorem pinned_bounds_of_maximal_positive {ω : ℝ} (hω : ω ∈ Ioo 0 (π / 2))
    {K : Set (ℝ × ℝ)} (hK : IsCap K ω) (hpositive : 0 < sofaArea ω K)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K) :
    wedgeGapWInf K ω ≤ sigmaAt K (π / 2) ∧ wedgeGapZInf K ω ≤ sigmaAt K ω := by
  -- Step 1: the selected polygon caps `Ks n` (Proposition 1) converge to `K`; their supports are
  -- bounded by `R` and within `η n` of those of `K`, where `η n → 0`.
  have hω' : ω ∈ Ioc 0 (π / 2) := ⟨hω.1, hω.2.le⟩
  obtain ⟨seq⟩ := exists_selectedCapSequence hω' hK hpositive hmax
  let Ks := seq.cap
  have hcap : ∀ n, IsCap (Ks n) ω := fun n => (seq.selected n).1.1
  have hcb : ∀ n, IsConvexBody (Ks n) := fun n => (hcap n).2.1
  let η : ℕ → ℝ := fun n => hausdorffDist (Ks n) K
  have hη : ∀ n, 0 ≤ η n := fun n => hausdorffDist_nonneg _ _
  have hηlim : Tendsto η atTop (𝓝 0) := seq.tends
  let R := seq.radius + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith [seq.radius_nonneg]
  have hsupp : ∀ n s, |supp (Ks n) s| ≤ R :=
    fun n s => abs_supp_le_box (hcb n) (seq.boxed n) s
  have hclose : ∀ n s, |supp (Ks n) s - supp K s| ≤ η n :=
    fun n s => abs_supp_sub_le_hausdorffDist (hcb n) hK.2.1 s
  -- Step 2: by inequality (12), their defects `|σ - τ|` at the pinned normals are at most
  -- `err t n`, which tends to zero.
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
    have htd : t ∈ (dyadicAngleSet ω hω' (seq.index n)).diamond := Or.inr ht
    have h := abs_selected_defect_le S (seq.selected n) hω.2 (hη n) hR
      (hsupp n) (fun i => hclose n (S.normal i)) htd
    have hmass : S.totalWeight ≤ 1 := dyadic_totalWeight_le_one ω hω' (seq.index n)
    have hnumer : 2 * η n * S.totalWeight + 4 * S.totalWeight * η n * G ≤
        (2 + 4 * G) * η n := by
      have h := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by linarith) (hη n) : 0 ≤ (2 + 4 * G) * η n)
      linarith
    have hsint : 0 ≤ sin t := (mpc_sin_pos_of_diamond htd).le
    exact h.trans (div_le_div_of_nonneg_right hnumer hsint)
  -- Step 3: the wedge gap infima of `Ks n` converge to those of `K` (Baek's Lemma 4.1.1) and are
  -- at most `τ`, hence at most `σ` plus an error tending to zero; and the limit of such bounds is
  -- at most `σ_K`.
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
      ang_wedgeGapWInf_le_tau (seq.selected n).1 hω.2
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
      ang_wedgeGapZInf_le_tau (seq.selected n).1 hω.2
    have hd := (abs_le.mp (hdefect n ω (Or.inl rfl))).1
    linarith

end MovingSofaUniqueness

end
