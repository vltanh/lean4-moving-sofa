module

public import MovingSofaOptimality.Balanced.MaxPolygonCapExists

/-!
# The polyline of a polygon cap (§3.4)

Definitions 3.4.2–3.4.4, Theorem 3.4.4 and Lemma 3.4.5: the boundary of `F_ω \ 𝒩_Θ(K)` is a
polyline between two half-lines (Theorem 3.4.4, `thm:polyline`), and the sides of the niche on the
walls have the lengths `τ_K` of the polyline (Lemma 3.4.5, `lem:polyline-length`). This is the third
of the four modules of §3.4 (see `MaximumPolygonCap`).

**Statement fix.** In Theorem 3.4.4 the edge lengths are written `∃ ℓ > (0 : ℝ)`; the original
`∃ ℓ > 0` was elaborated with `ℓ : ℕ`, which makes the statement false
(`mpc_theorem3_4_4_nat_false`, at the end of `MaximumPolygonCap`).

**Organization.**
* Definitions 3.4.2–3.4.3 and Theorem 3.4.4: the boundary of `F_ω \ 𝒩_Θ(K)` is the graph of `mpcG`
  (`mpc_frontier_eq`), and the vertices of the polyline are the sorted crossings of the walls
  (`mpc_polyline_data`, `mpc_polyline_vertices`).
* Definition 3.4.4 (`tau`) and Lemma 3.4.5: the lengths are computed in the abscissa
  (`mpc_lineLength_eq`, `mpc_tau_eq_lineLength`); on an inner wall, the frontier of the niche and
  the polyline agree up to finitely many crossings (`mpc_inner_wall`, `mpc_wallB_vec`,
  `mpc_wallD_vec`), and a bottom side `l(t, 0)` splits into the part on the frontier of the niche
  and the part on the polyline (`mpc_volume_bottom`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-! ## The polyline (Definitions 3.4.2–3.4.3, Theorem 3.4.4)

The boundary of `F_ω \ 𝒩_Θ(K)` is the graph of `mpcG` (`mpc_frontier_eq`). Left of `C_K⁺(ω)` and
right of `A_K⁻(0)` it is the half-lines `l⃗_K` and `r⃗_K`; in between it is the polyline `𝐩_K`,
whose vertices are the breakpoints of `mpcG`: the crossings of the walls `l(s, h_K(s) - 1)`,
`s ∈ Θ^◇` (`mpc_polyline_data`). -/

/-- An `x`-monotone polyline through `p_1, …, p_n` (Definition 3.4.2, `def:polyline`). -/
def IsXMonotonePolyline (P : Set (ℝ × ℝ)) : Prop :=
  ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), StrictMono (fun i => (p i).1) ∧
    P = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ)

/-- The open half-line `l⃗_K` from `C_K⁺(ω)` in the direction `v_ω`, without its endpoint. -/
def rayLeft (K : Set (ℝ × ℝ)) (ω : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s : ℝ, 0 < s ∧ p = cPlus K ω + s • vvec ω}

/-- The open half-line `r⃗_K` from `A_K⁻(0)` in the direction `u_0`, without its endpoint. -/
def rayRight (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | ∃ s : ℝ, 0 < s ∧ p = aMinus K 0 + s • uvec 0}

/-- The polyline `𝐩_K` of a polygon cap (Definition 3.4.3, `def:polyline-of-cap`): the boundary of
`F_ω \ 𝒩_Θ(K)` without the two open half-lines. -/
def polyline (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  frontier (fan Θ.ω \ polyNiche Θ K) \ (rayLeft K Θ.ω ∪ rayRight K)

section Polyline

open Filter Topology

/-! ### The half-lines `l⃗_K`, `r⃗_K` and the polyline as parts of a graph -/

section Rays

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- Left of `C_K⁺(ω)`, `mpcG` is the side `l(ω, 0)` of the fan. -/
lemma mpc_G_left (hK : IsPolygonCap Θ K) {x : ℝ} (hx : x ≤ (cPlus K Θ.ω).1) :
    mpcG Θ K x = mpcL K Θ.ω x := by
  obtain ⟨h1, h2⟩ := mpc_left_of_C hK hx
  rw [mpcG, max_eq_left h1.le, h2]

/-- Right of `A_K⁻(0)`, `mpcG` is the axis `y = 0`. -/
lemma mpc_G_right (hK : IsPolygonCap Θ K) {x : ℝ} (hx : (aMinus K 0).1 ≤ x) :
    mpcG Θ K x = 0 := by
  obtain ⟨h1, h2⟩ := mpc_right_of_A hK hx
  rw [mpcG, max_eq_left h1.le, h2]

/-- The boundary of `F_ω \ 𝒩_Θ(K)` is the graph of `mpcG`. -/
lemma mpc_frontier_eq (hK : IsPolygonCap Θ K) :
    frontier (fan Θ.ω \ polyNiche Θ K) = {p | p.2 = mpcG Θ K p.1} := by
  rw [mpc_fan_diff_eq hK]
  exact mpc_frontier_epigraph (mpc_continuous_mpcG Θ K)

/-- The half-line `l⃗_K` is the part of the graph of `mpcG` left of `C_K⁺(ω)`. -/
lemma mpc_rayLeft_eq (hK : IsPolygonCap Θ K) :
    rayLeft K Θ.ω = {p | p.1 < (cPlus K Θ.ω).1 ∧ p.2 = mpcG Θ K p.1} := by
  have hω0 := mpc_omega_pos Θ
  have hsω : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [mpc_omega_le Θ, pi_pos])
  obtain ⟨hC1, hC2⟩ := mpc_cPlus_coords hK
  set c := supp K (Θ.ω + π / 2)
  ext p
  simp only [rayLeft, mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hp1 : (cPlus K Θ.ω + s • vvec Θ.ω).1 = -((c + s) * sin Θ.ω) := by
      simp only [Prod.fst_add, Prod.smul_fst, vvec_fst, smul_eq_mul, hC1]; ring
    refine ⟨by rw [hp1, hC1]; nlinarith, ?_⟩
    rw [mpc_G_left hK (by rw [hp1, hC1]; nlinarith), mpc_mpcL_omega hK, hp1]
    simp only [Prod.snd_add, Prod.smul_snd, vvec_snd, smul_eq_mul, hC2]
    field_simp
  · rintro ⟨h1, h2⟩
    rw [mpc_G_left hK h1.le, mpc_mpcL_omega hK] at h2
    refine ⟨-p.1 / sin Θ.ω - c, ?_, ?_⟩
    · rw [hC1] at h1
      rw [sub_pos, lt_div_iff₀ hsω]
      linarith
    · ext
      · simp only [Prod.fst_add, Prod.smul_fst, vvec_fst, smul_eq_mul, hC1]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, vvec_snd, smul_eq_mul, hC2, h2]
        field_simp
        ring

/-- The half-line `r⃗_K` is the part of the graph of `mpcG` right of `A_K⁻(0)`. -/
lemma mpc_rayRight_eq (hK : IsPolygonCap Θ K) :
    rayRight K = {p | (aMinus K 0).1 < p.1 ∧ p.2 = mpcG Θ K p.1} := by
  obtain ⟨hA1, hA2⟩ := mpc_aMinus_coords hK
  ext p
  simp only [rayRight, mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hp1 : (aMinus K 0 + s • uvec 0).1 = (aMinus K 0).1 + s := by
      simp [uvec_zero]
    refine ⟨by rw [hp1]; linarith, ?_⟩
    rw [mpc_G_right hK (by rw [hp1]; linarith)]
    simp [uvec_zero, hA2]
  · rintro ⟨h1, h2⟩
    rw [mpc_G_right hK h1.le] at h2
    refine ⟨p.1 - (aMinus K 0).1, by linarith, ?_⟩
    ext
    · simp [uvec_zero]
    · simp [uvec_zero, hA2, h2]

/-- The polyline `𝐩_K` is the graph of `mpcG` between `C_K⁺(ω)` and `A_K⁻(0)`. -/
lemma mpc_polyline_eq (hK : IsPolygonCap Θ K) :
    polyline Θ K = {p | (cPlus K Θ.ω).1 ≤ p.1 ∧ p.1 ≤ (aMinus K 0).1 ∧ p.2 = mpcG Θ K p.1} := by
  rw [polyline, mpc_frontier_eq hK, mpc_rayLeft_eq hK, mpc_rayRight_eq hK]
  ext p
  simp only [Set.mem_sdiff, mem_union, mem_ofPred_eq, not_or, not_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by by_contra h; push Not at h; exact absurd h1 (h2 h),
      by by_contra h; push Not at h; exact absurd h1 (h3 h), h1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3, fun h => absurd h (not_lt.2 h1), fun h => absurd h (not_lt.2 h2)⟩

end Rays

/-! ### Piecewise linear functions -/

/-- A continuous function without zeros on `(a, b)` has a constant sign on `[a, b]`. -/
lemma mpc_sign_const {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h0 : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 ≤ f x) ∨ (∀ x ∈ Icc a b, f x ≤ 0) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le, exists_prop] at hcon
  obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hcon
  -- `f` changes sign between `x` and `y`, so it vanishes strictly between them
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc (a := x) (b := y) hf.continuousOn
    (mem_uIcc.2 (Or.inl ⟨hfx.le, hfy.le⟩))
  have hcx : c ≠ x := fun h => by rw [h] at hfc; linarith
  have hcy : c ≠ y := fun h => by rw [h] at hfc; linarith
  rcases mem_uIcc.1 hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h0 c ⟨by linarith [hx.1, lt_of_le_of_ne h1 (Ne.symm hcx)],
      by linarith [hy.2, lt_of_le_of_ne h2 hcy]⟩ hfc
  · exact h0 c ⟨by linarith [hy.1, lt_of_le_of_ne h1 (Ne.symm hcy)],
      by linarith [hx.2, lt_of_le_of_ne h2 hcx]⟩ hfc

/-- The segment between two points of the graph of a line is the graph over the interval. -/
lemma mpc_segment_graph (s c a b : ℝ) (hab : a ≤ b) :
    segment ℝ (a, mpcLineY s c a) (b, mpcLineY s c b) =
      {p | a ≤ p.1 ∧ p.1 ≤ b ∧ p.2 = mpcLineY s c p.1} := by
  rw [segment_eq_image']
  ext p
  simp only [mem_image, mem_Icc, mem_ofPred_eq]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul, mpcLineY]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    ring
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      ext
      · simp; linarith
      · simp [h3, le_antisymm h1 h2]
    · refine ⟨(p.1 - a) / (b - a), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
      have hba : b - a ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, h3, mpcLineY]
        field_simp
        ring

/-- The intervals between consecutive points of an increasing sequence cover its range. -/
lemma mpc_iUnion_Icc {n : ℕ} {xs : Fin (n + 1) → ℝ} (hxs : StrictMono xs) (hn : 0 < n) :
    ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) = Icc (xs 0) (xs (Fin.last n)) := by
  apply subset_antisymm
  · refine iUnion_subset fun i => Icc_subset_Icc (hxs.monotone (Fin.zero_le _))
      (hxs.monotone (Fin.le_last _))
  · intro y ⟨hy0, hy1⟩
    -- the first index `k` with `y ≤ xs k`
    have hex : ∃ k : ℕ, ∃ hk : k < n + 1, y ≤ xs ⟨k, hk⟩ := ⟨n, Nat.lt_succ_self n, hy1⟩
    classical
    let k := Nat.find hex
    obtain ⟨hk, hyk⟩ := Nat.find_spec hex
    rw [mem_iUnion]
    by_cases hk0 : k = 0
    · refine ⟨⟨0, hn⟩, ?_, ?_⟩
      · have : (Fin.castSucc (⟨0, hn⟩ : Fin n)) = 0 := rfl
        rw [this]; exact hy0
      · have e : xs ⟨k, hk⟩ ≤ xs (Fin.succ ⟨0, hn⟩) := by
          apply hxs.monotone
          show k ≤ 1
          omega
        exact hyk.trans e
    · have hk1 : k - 1 < n := by omega
      refine ⟨⟨k - 1, hk1⟩, ?_, ?_⟩
      · have hlt := Nat.find_min hex (show k - 1 < k by omega)
        push Not at hlt
        exact (hlt (by omega)).le
      · have : (Fin.succ (⟨k - 1, hk1⟩ : Fin n)) = ⟨k, hk⟩ := by
          ext; simp; omega
        rw [this]; exact hyk

/-! ### The breakpoints and vertices of the polyline -/

/-- The abscissa where the lines `l(s, c)` and `l(s', c')` meet. -/
noncomputable def mpcCrossX (s c s' c' : ℝ) : ℝ := (c * sin s' - c' * sin s) / sin (s' - s)

/-- The candidate breakpoints of the polyline: the ends and the crossings of the inner walls. -/
noncomputable def mpcBreaks (Θ : AngleSet) (K : Set (ℝ × ℝ)) : Finset ℝ :=
  (((mpcDiamond Θ ×ˢ mpcDiamond Θ).image
      (fun q => mpcCrossX q.1 (supp K q.1 - 1) q.2 (supp K q.2 - 1))) ∪
    {(cPlus K Θ.ω).1, (aMinus K 0).1}).filter
    (fun x => (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1)

section Vertices

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

lemma mpc_breaks_bounds {x : ℝ} (hx : x ∈ mpcBreaks Θ K) :
    (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 :=
  (Finset.mem_filter.1 hx).2

lemma mpc_C_mem_breaks (hK : IsPolygonCap Θ K) : (cPlus K Θ.ω).1 ∈ mpcBreaks Θ K :=
  Finset.mem_filter.2 ⟨Finset.mem_union_right _ (by simp), le_rfl, (mpc_C_lt_A hK).le⟩

lemma mpc_A_mem_breaks (hK : IsPolygonCap Θ K) : (aMinus K 0).1 ∈ mpcBreaks Θ K :=
  Finset.mem_filter.2 ⟨Finset.mem_union_right _ (by simp), (mpc_C_lt_A hK).le, le_rfl⟩

/-- A crossing of two inner walls between the ends is a breakpoint. -/
lemma mpc_cross_mem_breaks {s s' : ℝ} (hs : s ∈ Θ.diamond) (hs' : s' ∈ Θ.diamond)
    (h : s ≠ s') {x : ℝ} (hx : (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1)
    (heq : mpcL K s x = mpcL K s' x) : x ∈ mpcBreaks Θ K := by
  have hx' := mpc_lineY_eq_imp (mpc_sin_pos_of_diamond hs).ne'
    (mpc_sin_pos_of_diamond hs').ne' (mpc_diamond_sin_sub_ne hs hs' h) heq
  refine Finset.mem_filter.2 ⟨Finset.mem_union_left _ (Finset.mem_image.2 ⟨(s, s'), ?_, ?_⟩), hx⟩
  · exact Finset.mem_product.2 ⟨mpc_mem_mpcDiamond.2 hs, mpc_mem_mpcDiamond.2 hs'⟩
  · exact hx'.symm

/-- On an interval without breakpoints, the inner walls are ordered. -/
lemma mpc_walls_ordered {a b : ℝ} (ha : (cPlus K Θ.ω).1 ≤ a)
    (hb : b ≤ (aMinus K 0).1) (hgap : ∀ y ∈ mpcBreaks Θ K, ¬ (a < y ∧ y < b))
    {s s' : ℝ} (hs : s ∈ Θ.diamond) (hs' : s' ∈ Θ.diamond) :
    (∀ x ∈ Icc a b, mpcL K s x ≤ mpcL K s' x) ∨ (∀ x ∈ Icc a b, mpcL K s' x ≤ mpcL K s x) := by
  by_cases h : s = s'
  · subst h; exact Or.inl fun _ _ => le_rfl
  have hne : ∀ x ∈ Ioo a b, (mpcL K s' - mpcL K s) x ≠ 0 := fun x hx h0 =>
    hgap x (mpc_cross_mem_breaks hs hs' h ⟨by linarith [hx.1], by linarith [hx.2]⟩
      (sub_eq_zero.1 h0).symm) hx
  rcases mpc_sign_const ((mpc_continuous_mpcL K s').sub (mpc_continuous_mpcL K s)) hne
    with h1 | h1
  · left; intro x hx; have := h1 x hx; simp only [Pi.sub_apply] at this; linarith
  · right; intro x hx; have := h1 x hx; simp only [Pi.sub_apply] at this; linarith

/-- On an interval without breakpoints, the lower boundary of `F_ω \ 𝒩_Θ(K)` is a single wall. -/
lemma mpc_piece {a b : ℝ} (ha : (cPlus K Θ.ω).1 ≤ a)
    (hb : b ≤ (aMinus K 0).1) (hgap : ∀ y ∈ mpcBreaks Θ K, ¬ (a < y ∧ y < b)) :
    ∃ s ∈ Θ.diamond, ∀ x ∈ Icc a b, mpcG Θ K x = mpcL K s x := by
  let P : (ℝ → ℝ) → Prop := fun f => ∃ s ∈ Θ.diamond, ∀ x ∈ Icc a b, f x = mpcL K s x
  have hmax : ∀ f g, P f → P g → P (fun x => max (f x) (g x)) := by
    rintro f g ⟨s, hs, hf⟩ ⟨s', hs', hg⟩
    rcases mpc_walls_ordered ha hb hgap hs hs' with h | h
    · exact ⟨s', hs', fun x hx => by dsimp only; rw [hf x hx, hg x hx, max_eq_right (h x hx)]⟩
    · exact ⟨s, hs, fun x hx => by dsimp only; rw [hf x hx, hg x hx, max_eq_left (h x hx)]⟩
  have hmin : ∀ f g, P f → P g → P (fun x => min (f x) (g x)) := by
    rintro f g ⟨s, hs, hf⟩ ⟨s', hs', hg⟩
    rcases mpc_walls_ordered ha hb hgap hs hs' with h | h
    · exact ⟨s, hs, fun x hx => by dsimp only; rw [hf x hx, hg x hx, min_eq_left (h x hx)]⟩
    · exact ⟨s', hs', fun x hx => by dsimp only; rw [hf x hx, hg x hx, min_eq_right (h x hx)]⟩
  have hL : ∀ s ∈ Θ.diamond, P (mpcL K s) := fun s hs => ⟨s, hs, fun _ _ => rfl⟩
  have hlow : P (mpcLow Θ K) :=
    hmax _ _ (hL _ (Or.inr (Or.inl rfl))) (hL _ (Or.inr (Or.inr rfl)))
  have htop : P (mpcTop Θ K) := by
    rw [mpc_mpcTop_eq]
    apply Finset.sup'_induction (p := P)
    · intro f hf g hg; exact hmax f g hf hg
    · intro t ht
      exact hmin _ _ (hL _ (Or.inl (Or.inl ht))) (hL _ (Or.inl (Or.inr ⟨t, ht, rfl⟩)))
  exact hmax _ _ hlow htop

/-- The vertices of the polyline: an increasing enumeration of the breakpoints, with the wall
`mpcL K (s i)` followed on the `i`-th piece. -/
lemma mpc_polyline_data (hK : IsPolygonCap Θ K) :
    ∃ (n : ℕ) (xs : Fin (n + 1) → ℝ) (sp : Fin n → ℝ), 0 < n ∧ StrictMono xs ∧
      xs 0 = (cPlus K Θ.ω).1 ∧ xs (Fin.last n) = (aMinus K 0).1 ∧
      (∀ i, sp i ∈ Θ.diamond) ∧
      (∀ i, ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K (sp i) x) := by
  set B := mpcBreaks Θ K
  have hC := mpc_C_mem_breaks hK
  have hA := mpc_A_mem_breaks hK
  have hCA := mpc_C_lt_A hK
  have hcard : 1 < B.card := Finset.one_lt_card.2 ⟨_, hC, _, hA, hCA.ne⟩
  set n := B.card - 1 with hn
  have hcard' : B.card = n + 1 := by omega
  set xs := B.orderEmbOfFin hcard' with hxs
  have hmono : StrictMono xs := xs.strictMono
  have hmem : ∀ i, xs i ∈ B := fun i => Finset.orderEmbOfFin_mem B hcard' i
  have hsurj : ∀ y ∈ B, ∃ i, xs i = y := fun y hy => by
    rw [← Set.mem_range, hxs, Finset.range_orderEmbOfFin]; exact hy
  have h0 : xs 0 = (cPlus K Θ.ω).1 := by
    have e := Finset.orderEmbOfFin_zero hcard' (Nat.succ_pos n)
    have : (0 : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := rfl
    rw [this, e]
    exact le_antisymm (B.min'_le _ hC) (B.le_min' _ _ fun y hy => (mpc_breaks_bounds hy).1)
  have hlast : xs (Fin.last n) = (aMinus K 0).1 := by
    have e := Finset.orderEmbOfFin_last hcard' (Nat.succ_pos n)
    have : Fin.last n = ⟨n + 1 - 1, Nat.sub_lt (Nat.succ_pos n) (Nat.succ_pos 0)⟩ := by
      ext; simp
    rw [this, e]
    exact le_antisymm (B.max'_le _ _ fun y hy => (mpc_breaks_bounds hy).2) (B.le_max' _ hA)
  have hpiece : ∀ i : Fin n, ∃ s ∈ Θ.diamond,
      ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K s x := by
    intro i
    apply mpc_piece (mpc_breaks_bounds (hmem _)).1
      (mpc_breaks_bounds (hmem _)).2
    intro y hy ⟨h1, h2⟩
    obtain ⟨j, rfl⟩ := hsurj y hy
    have e1 := hmono.lt_iff_lt.1 h1
    have e2 := hmono.lt_iff_lt.1 h2
    rw [Fin.lt_def] at e1 e2
    simp at e1 e2
    omega
  choose sp hsp hspG using hpiece
  exact ⟨n, xs, sp, by omega, hmono, h0, hlast, hsp, hspG⟩

end Vertices


/-- The pieces of the polyline are segments. -/
lemma mpc_segment_piece {Θ : AngleSet} {K : Set (ℝ × ℝ)} {a b s : ℝ} (hab : a ≤ b)
    (hG : ∀ x ∈ Icc a b, mpcG Θ K x = mpcL K s x) :
    segment ℝ (a, mpcG Θ K a) (b, mpcG Θ K b) = {q | a ≤ q.1 ∧ q.1 ≤ b ∧ q.2 = mpcG Θ K q.1} := by
  rw [hG a ⟨le_rfl, hab⟩, hG b ⟨hab, le_rfl⟩, mpcL, mpcL, mpc_segment_graph _ _ _ _ hab]
  ext q
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [hG q.1 ⟨h1, h2⟩, mpcL]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h3, hG q.1 ⟨h1, h2⟩, mpcL]⟩

/-- The vertices `P_i = (x_i, G(x_i))` of the polyline, from the data of `mpc_polyline_data`:
`P_0 = C_K⁺(ω)`, `P_n = A_K⁻(0)`, `𝐩_K` is the union of the segments `[P_i, P_{i+1}]`, and
`P_i - P_{i+1} = ℓ_i v_{s_i}` with `ℓ_i = (x_{i+1} - x_i) / sin s_i`. -/
lemma mpc_polyline_vertices {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {n : ℕ}
    {xs : Fin (n + 1) → ℝ} {sp : Fin n → ℝ} (hn : 0 < n) (hmono : StrictMono xs)
    (h0 : xs 0 = (cPlus K Θ.ω).1) (hlast : xs (Fin.last n) = (aMinus K 0).1)
    (hsp : ∀ i, sp i ∈ Θ.diamond)
    (hspG : ∀ i, ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K (sp i) x) :
    (xs 0, mpcG Θ K (xs 0)) = cPlus K Θ.ω ∧
      (xs (Fin.last n), mpcG Θ K (xs (Fin.last n))) = aMinus K 0 ∧
      polyline Θ K = ⋃ i : Fin n, segment ℝ (xs i.castSucc, mpcG Θ K (xs i.castSucc))
        (xs i.succ, mpcG Θ K (xs i.succ)) ∧
      ∀ i : Fin n, (xs i.castSucc, mpcG Θ K (xs i.castSucc)) - (xs i.succ, mpcG Θ K (xs i.succ)) =
        ((xs i.succ - xs i.castSucc) / sin (sp i)) • vvec (sp i) := by
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · have hsω : 0 < sin Θ.ω := mpc_sin_pos_of_diamond (Θ := Θ) (Or.inr (Or.inl rfl))
    obtain ⟨hC1, hC2⟩ := mpc_cPlus_coords hK
    rw [h0, mpc_G_left hK le_rfl, mpc_mpcL_omega hK]
    ext
    · rfl
    · simp only
      rw [hC1, hC2]
      field_simp
  · rw [hlast, mpc_G_right hK le_rfl]
    ext
    · rfl
    · exact (mpc_aMinus_coords hK).2.symm
  · -- the pieces cover `[C_K⁺(ω)_x, A_K⁻(0)_x]`, and each piece is a segment
    have hseg : ∀ i : Fin n, segment ℝ (xs i.castSucc, mpcG Θ K (xs i.castSucc))
        (xs i.succ, mpcG Θ K (xs i.succ)) =
        {q | xs i.castSucc ≤ q.1 ∧ q.1 ≤ xs i.succ ∧ q.2 = mpcG Θ K q.1} := fun i =>
      mpc_segment_piece (hmono (Fin.castSucc_lt_succ (i := i))).le (hspG i)
    have hcov := mpc_iUnion_Icc hmono hn
    rw [h0, hlast] at hcov
    rw [mpc_polyline_eq hK]
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, hseg]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov.symm ▸ ⟨h1, h2⟩ :
        p.1 ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ))
      exact ⟨i, hi.1, hi.2, h3⟩
    · rintro ⟨i, h1, h2, h3⟩
      have : p.1 ∈ Icc (cPlus K Θ.ω).1 (aMinus K 0).1 := hcov ▸ mem_iUnion.2 ⟨i, h1, h2⟩
      exact ⟨this.1, this.2, h3⟩
  · have hi := hmono (Fin.castSucc_lt_succ (i := i))
    have hs := mpc_sin_pos_of_diamond (hsp i)
    rw [hspG i _ ⟨le_rfl, hi.le⟩, hspG i _ ⟨hi.le, le_rfl⟩]
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, vvec_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_sub, Prod.smul_snd, vvec_snd, smul_eq_mul, mpcL, mpcLineY]
      field_simp
      ring

end Polyline

/-- **Theorem 3.4.4** (`thm:polyline`). For a polygon cap `K`, the boundary of `F_ω \ 𝒩_Θ(K)` is the
disjoint union, from left to right, of `l⃗_K`, an `x`-monotone polyline `𝐩_K` from `C_K⁺(ω)` to
`A_K⁻(0)` whose segments have normal angles in `Θ^◇`, and `r⃗_K`.

The edge lengths `ℓ` are real numbers: the original statement wrote `∃ ℓ > 0`, which Lean
elaborated with `ℓ : ℕ` (the only constraint on `ℓ` being the scalar action `ℓ • vvec s`); that
version is false
(`mpc_theorem3_4_4_nat_false`: the polyline of `𝓒_Θ(1)` for `Θ = {π/4}`, `ω = π/2` is one
horizontal segment of length `2√2`, which is no sum of natural lengths). -/
theorem theorem3_4_4 {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) :
    frontier (fan Θ.ω \ polyNiche Θ K) = rayLeft K Θ.ω ∪ polyline Θ K ∪ rayRight K ∧
      Disjoint (rayLeft K Θ.ω) (polyline Θ K ∪ rayRight K) ∧ Disjoint (polyline Θ K) (rayRight K) ∧
      ∃ (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ), p 0 = cPlus K Θ.ω ∧ p (Fin.last n) = aMinus K 0 ∧
        StrictMono (fun i => (p i).1) ∧
        polyline Θ K = ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ∧
        ∀ i : Fin n, ∃ s ∈ Θ.diamond, ∃ ℓ > (0 : ℝ), p i.castSucc - p i.succ = ℓ • vvec s := by
  have hCA := mpc_C_lt_A hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mpc_frontier_eq hK, mpc_rayLeft_eq hK, mpc_polyline_eq hK, mpc_rayRight_eq hK]
    ext p
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · intro h
      by_cases h1 : p.1 < (cPlus K Θ.ω).1
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · by_cases h2 : (aMinus K 0).1 < p.1
        · exact Or.inr ⟨h2, h⟩
        · push Not at h1 h2
          exact Or.inl (Or.inr ⟨h1, h2, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, _, h⟩) | ⟨_, h⟩) <;> exact h
  · rw [mpc_rayLeft_eq hK, mpc_polyline_eq hK, mpc_rayRight_eq hK, Set.disjoint_left]
    rintro p ⟨h1, _⟩ (⟨h2, _, _⟩ | ⟨h2, _⟩) <;> linarith
  · rw [mpc_polyline_eq hK, mpc_rayRight_eq hK, Set.disjoint_left]
    rintro p ⟨_, h1, _⟩ ⟨h2, _⟩
    linarith
  · obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK
    obtain ⟨hP0, hPn, hunion, hedge⟩ := mpc_polyline_vertices hK hn hmono h0 hlast hsp hspG
    refine ⟨n, fun i => (xs i, mpcG Θ K (xs i)), hP0, hPn, hmono, hunion, fun i =>
      ⟨sp i, hsp i, _, div_pos ?_ (mpc_sin_pos_of_diamond (hsp i)), hedge i⟩⟩
    linarith [hmono (Fin.castSucc_lt_succ (i := i))]

/-! ## The lengths of the polyline (Definition 3.4.4) and of the sides of the niche (Lemma 3.4.5)

`τ_K(t)` is the length of the polyline on the wall `l(t, h_K(t) - 1)` (`mpc_tau_eq_lineLength`).
On an inner wall, the frontier of the niche agrees with the polyline up to finitely many crossings
(Lemma 3.4.5 (1)); on a bottom side `l(t, 0)`, the side `σ_K(t + π)` splits into the part on the
frontier of the niche and the part on the polyline (Lemma 3.4.5 (2)). -/

/-- `τ_K(t)`, the total length of the edges of the polyline `𝐩_K` with normal angle `t`
(Definition 3.4.4, `def:polyline-length`): the sum over the parallel lines `l(t, c)` of the length
of the part of `𝐩_K` on them. Only finitely many terms are nonzero. -/
noncomputable def tau (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  ∑' c : ℝ, lineLength t c (polyline Θ K)

/-! ### Computing `τ_K(t)` in the abscissa -/

section Tau

open Filter Topology MeasureTheory

/-- Telescoping over `Fin`. -/
lemma mpc_sum_telescope {M : Type*} [AddCommGroup M] {n : ℕ} (g : Fin (n + 1) → M) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => g i.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    abel

/-- The length of `X ∩ l(s, c)` computed in the abscissa. -/
lemma mpc_lineLength_eq {s : ℝ} (hs : 0 < sin s) (c : ℝ) (X : Set (ℝ × ℝ)) :
    lineLength s c X = (volume {x : ℝ | (x, mpcLineY s c x) ∈ X}).toReal / sin s := by
  set S := {x : ℝ | (x, mpcLineY s c x) ∈ X}
  have hpre : {σ : ℝ | c • uvec s + σ • vvec s ∈ X} =
      (fun σ => -sin s * σ) ⁻¹' ((fun y => c * cos s + y) ⁻¹' S) := by
    ext σ
    simp only [mem_ofPred_eq, mem_preimage, S]
    have e : c • uvec s + σ • vvec s = (c * cos s + -sin s * σ,
        mpcLineY s c (c * cos s + -sin s * σ)) := by
      ext
      · simp [uvec, vvec]; ring
      · simp only [Prod.snd_add, Prod.smul_snd, uvec_snd, vvec_snd, smul_eq_mul, mpcLineY]
        field_simp
        linear_combination c * sin_sq_add_cos_sq s
    rw [e]
  rw [lineLength, hpre, Real.volume_preimage_mul_left (neg_ne_zero.2 hs.ne'),
    measure_preimage_add, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    abs_neg, abs_of_pos hs]
  ring


/-- Intervals between consecutive points of an increasing sequence are almost disjoint. -/
lemma mpc_measure_union_Icc {n : ℕ} {xs : Fin (n + 1) → ℝ} (hxs : StrictMono xs)
    (S : Finset (Fin n)) :
    volume (⋃ i ∈ S, Icc (xs i.castSucc) (xs i.succ)) =
      ∑ i ∈ S, ENNReal.ofReal (xs i.succ - xs i.castSucc) := by
  rw [measure_biUnion_finset₀]
  · simp only [Real.volume_Icc]
  · intro i _ j _ hij
    have key : ∀ i j : Fin n, i < j →
        AEDisjoint volume (Icc (xs i.castSucc) (xs i.succ)) (Icc (xs j.castSucc) (xs j.succ)) := by
      intro i j hlt
      apply measure_mono_null (t := {xs i.succ}) _ (measure_singleton _)
      rintro x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
      have : xs i.succ ≤ xs j.castSucc := by
        apply hxs.monotone
        rw [Fin.le_def]; simp; exact hlt
      exact le_antisymm h2 (this.trans h3)
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  · intro i _; exact measurableSet_Icc.nullMeasurableSet

/-- Two sets of reals that agree up to finite sets have the same measure. -/
lemma mpc_volume_eq_of_finite_diff {S T F G : Set ℝ} (hF : F.Finite) (hG : G.Finite)
    (h1 : S ⊆ T ∪ F) (h2 : T ⊆ S ∪ G) : volume S = volume T := by
  apply le_antisymm
  · calc volume S ≤ volume (T ∪ F) := measure_mono h1
      _ ≤ volume T + volume F := measure_union_le _ _
      _ = volume T := by rw [hF.measure_zero, add_zero]
  · calc volume T ≤ volume (S ∪ G) := measure_mono h2
      _ ≤ volume S + volume G := measure_union_le _ _
      _ = volume S := by rw [hG.measure_zero, add_zero]

section TauComp

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- `τ_K(t)` is the length of the polyline on the wall `l(t, h_K(t) - 1)`: the other parallel lines
meet the polyline in finitely many points (crossings with the other walls). -/
lemma mpc_tau_eq_lineLength (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.diamond) :
    tau Θ K t = lineLength t (supp K t - 1) (polyline Θ K) := by
  obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK
  have hst := mpc_sin_pos_of_diamond ht
  have hcov := mpc_iUnion_Icc hmono hn
  rw [h0, hlast] at hcov
  have hpoly := mpc_polyline_eq hK
  rw [tau]
  apply tsum_eq_single
  intro c hc
  rw [mpc_lineLength_eq hst]
  have : volume {x : ℝ | (x, mpcLineY t c x) ∈ polyline Θ K} = 0 := by
    apply measure_mono_null _ ((Finset.univ.image
      (fun i => mpcCrossX t c (sp i) (supp K (sp i) - 1)) : Finset ℝ).finite_toSet.measure_zero _)
    intro x hx
    rw [mem_ofPred_eq, hpoly] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    have : x ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ) := by rw [hcov]; exact ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    simp only at h3
    rw [hspG i x hi, mpcL] at h3
    by_cases hit : sp i = t
    · rw [hit] at h3
      exact absurd (mpc_lineY_inj hst.ne' h3) hc
    · have := mpc_lineY_eq_imp hst.ne' (mpc_sin_pos_of_diamond (hsp i)).ne'
        (mpc_diamond_sin_sub_ne ht (hsp i) (Ne.symm hit)) h3
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, this.symm⟩)
  rw [this, ENNReal.toReal_zero, zero_div]

/-- `τ_K(t)` in terms of the polyline data: the total horizontal extent of the pieces on the wall
with normal angle `t`, divided by `sin t`. -/
lemma mpc_tau_eq (hK : IsPolygonCap Θ K) {n : ℕ} {xs : Fin (n + 1) → ℝ} {sp : Fin n → ℝ}
    (hn : 0 < n) (hmono : StrictMono xs) (h0 : xs 0 = (cPlus K Θ.ω).1)
    (hlast : xs (Fin.last n) = (aMinus K 0).1) (hsp : ∀ i, sp i ∈ Θ.diamond)
    (hspG : ∀ i, ∀ x ∈ Icc (xs i.castSucc) (xs i.succ), mpcG Θ K x = mpcL K (sp i) x)
    {t : ℝ} (ht : t ∈ Θ.diamond) :
    tau Θ K t = (∑ i ∈ Finset.univ.filter (fun i => sp i = t),
      (xs i.succ - xs i.castSucc)) / sin t := by
  have hst := mpc_sin_pos_of_diamond ht
  have hcov := mpc_iUnion_Icc hmono hn
  rw [h0, hlast] at hcov
  have hpoly := mpc_polyline_eq hK
  rw [mpc_tau_eq_lineLength hK ht, mpc_lineLength_eq hst]
  congr 1
  set U := ⋃ i ∈ Finset.univ.filter (fun i => sp i = t), Icc (xs i.castSucc) (xs i.succ)
  -- the polyline meets the wall in the pieces following it, and in crossings with other walls
  set F : Finset ℝ :=
    Finset.univ.image (fun i => mpcCrossX t (supp K t - 1) (sp i) (supp K (sp i) - 1))
  have hsub : {x : ℝ | (x, mpcLineY t (supp K t - 1) x) ∈ polyline Θ K} ⊆ U ∪ (F : Set ℝ) := by
    intro x hx
    rw [mem_ofPred_eq, hpoly] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov.symm ▸ ⟨h1, h2⟩ :
      x ∈ ⋃ i : Fin n, Icc (xs i.castSucc) (xs i.succ))
    by_cases hit : sp i = t
    · exact Or.inl (mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hit⟩, hi⟩)
    · right
      simp only at h3
      rw [hspG i x hi, mpcL] at h3
      have := mpc_lineY_eq_imp hst.ne' (mpc_sin_pos_of_diamond (hsp i)).ne'
        (mpc_diamond_sin_sub_ne ht (hsp i) (Ne.symm hit)) h3
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, this.symm⟩)
  have hUS : U ⊆ {x : ℝ | (x, mpcLineY t (supp K t - 1) x) ∈ polyline Θ K} := by
    intro x hx
    obtain ⟨i, hi, hx'⟩ := mem_iUnion₂.1 hx
    rw [mem_ofPred_eq, hpoly]
    have hb0 : xs 0 ≤ xs i.castSucc := hmono.monotone (Fin.zero_le _)
    have hb1 : xs i.succ ≤ xs (Fin.last n) := hmono.monotone (Fin.le_last _)
    rw [h0] at hb0
    rw [hlast] at hb1
    refine ⟨hb0.trans hx'.1, hx'.2.trans hb1, ?_⟩
    simp only
    rw [hspG i x hx', (Finset.mem_filter.1 hi).2, mpcL]
  rw [mpc_volume_eq_of_finite_diff F.finite_toSet finite_empty hsub (fun x hx => Or.inl (hUS hx)),
    mpc_measure_union_Icc hmono, ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun i _ =>
    ENNReal.toReal_ofReal (by linarith [hmono (Fin.castSucc_lt_succ (i := i))])

end TauComp

/-- The dot product is additive over finite sums. -/
lemma mpc_dot_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ × ℝ) (v : ℝ × ℝ) :
    dot (∑ i ∈ S, f i) v = ∑ i ∈ S, dot (f i) v := by
  simp only [dot, Prod.fst_sum, Prod.snd_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- Partial telescoping over `Fin`. -/
lemma mpc_sum_telescope_from {M : Type*} [AddCommGroup M] {n : ℕ} (g : Fin (n + 1) → M)
    (k : Fin (n + 1)) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.castSucc), (g i.castSucc - g i.succ) =
      g k - g (Fin.last n) := by
  have htel := mpc_sum_telescope (fun j => g (max j k))
  rw [max_eq_left (Fin.le_last k), max_eq_right (Fin.zero_le k)] at htel
  rw [Finset.sum_filter, ← neg_sub (g (Fin.last n)), ← htel, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [max_eq_left (h.trans (Fin.castSucc_lt_succ (i := i)).le), max_eq_left h]
    abel
  · push Not at h
    have h' : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 h
    rw [max_eq_right h', max_eq_right h.le]
    abel

section Balance

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- `∑_{t ∈ Θ^◇} τ_K(t) sin t = A_K⁻(0)_x - C_K⁺(ω)_x`. -/
lemma mpc_sum_tau_sin (hK : IsPolygonCap Θ K) :
    ∑ t ∈ mpcDiamond Θ, tau Θ K t * sin t = (aMinus K 0).1 - (cPlus K Θ.ω).1 := by
  obtain ⟨n, xs, sp, hn, hmono, h0, hlast, hsp, hspG⟩ := mpc_polyline_data hK
  have e : ∀ t ∈ mpcDiamond Θ, tau Θ K t * sin t =
      ∑ i ∈ Finset.univ.filter (fun i => sp i = t), (xs i.succ - xs i.castSucc) := by
    intro t ht
    have ht' := mpc_mem_mpcDiamond.1 ht
    rw [mpc_tau_eq hK hn hmono h0 hlast hsp hspG ht',
      div_mul_cancel₀ _ (mpc_sin_pos_of_diamond ht').ne']
  rw [Finset.sum_congr rfl e, Finset.sum_fiberwise_of_maps_to
    (fun i _ => mpc_mem_mpcDiamond.2 (hsp i)), mpc_sum_telescope, h0, hlast]

end Balance

end Tau

/-! ### The frontier of the polygon niche on the walls -/

section NicheWalls

open Filter Topology MeasureTheory


/-- Membership in the half-line `b⃗_K(t)` of the wall `b_K(t) = l(t, h_K(t) - 1)`. -/
lemma mpc_mem_wallBVec (S : Set (ℝ × ℝ)) (t : ℝ) (P : ℝ × ℝ) :
    P ∈ wallBVec S t ↔ dot P (uvec t) = supp S t - 1 ∧
      dot P (uvec (t + π / 2)) ≤ supp S (t + π / 2) - 1 := by
  rw [uvec_add_pi_div_two]
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    have hq : q = (0, q.2) := by ext; exact hq1; rfl
    rw [hq]
    simp only [hallwayMap, rot, dot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    constructor
    · linear_combination (supp S t - 1) * sin_sq_add_cos_sq t
    · have e : (cos t * 0 - sin t * q.2 + (supp S t - 1) * cos t + (supp S (t + π / 2) - 1) *
          -sin t) * -sin t + (sin t * 0 + cos t * q.2 + (supp S t - 1) * sin t +
          (supp S (t + π / 2) - 1) * cos t) * cos t = q.2 + (supp S (t + π / 2) - 1) := by
        linear_combination (q.2 + (supp S (t + π / 2) - 1)) * sin_sq_add_cos_sq t
      rw [e]; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨(0, dot P (vvec t) - (supp S (t + π / 2) - 1)), ⟨rfl, by simp only; linarith⟩, ?_⟩
    have hP := eq_dot_uvec_smul_add P t
    rw [h1] at hP
    conv_rhs => rw [hP]
    ext <;> simp only [hallwayMap, rot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

/-- Membership in the half-line `d⃗_K(t)` of the wall `d_K(t) = l(t + π/2, h_K(t + π/2) - 1)`. -/
lemma mpc_mem_wallDVec (S : Set (ℝ × ℝ)) (t : ℝ) (P : ℝ × ℝ) :
    P ∈ wallDVec S t ↔ dot P (uvec (t + π / 2)) = supp S (t + π / 2) - 1 ∧
      dot P (uvec t) ≤ supp S t - 1 := by
  rw [uvec_add_pi_div_two]
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    have hq : q = (q.1, 0) := by ext; rfl; exact hq1
    rw [hq]
    simp only [hallwayMap, rot, dot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    constructor
    · linear_combination (supp S (t + π / 2) - 1) * sin_sq_add_cos_sq t
    · have e : (cos t * q.1 - sin t * 0 + (supp S t - 1) * cos t + (supp S (t + π / 2) - 1) *
          -sin t) * cos t + (sin t * q.1 + cos t * 0 + (supp S t - 1) * sin t +
          (supp S (t + π / 2) - 1) * cos t) * sin t = q.1 + (supp S t - 1) := by
        linear_combination (q.1 + (supp S t - 1)) * sin_sq_add_cos_sq t
      rw [e]; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨(dot P (uvec t) - (supp S t - 1), 0), ⟨rfl, by simp only; linarith⟩, ?_⟩
    have hP := eq_dot_uvec_smul_add P t
    rw [h1] at hP
    conv_rhs => rw [hP]
    ext <;> simp only [hallwayMap, rot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

section NicheFrontier

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The closure of the niche lies between `mpcLow` and `mpcTop`. -/
lemma mpc_closure_polyNiche (hK : IsPolygonCap Θ K) :
    closure (polyNiche Θ K) ⊆ {p | mpcLow Θ K p.1 ≤ p.2 ∧ p.2 ≤ mpcTop Θ K p.1} := by
  rw [mpc_polyNiche_eq hK]
  apply closure_minimal
  · rintro p ⟨h1, h2⟩; exact ⟨h1, h2.le⟩
  · exact (isClosed_le ((mpc_continuous_mpcLow Θ K).comp continuous_fst) continuous_snd).inter
      (isClosed_le continuous_snd ((mpc_continuous_mpcTop Θ K).comp continuous_fst))

/-- The region strictly between `mpcLow` and `mpcTop` is interior to the niche. -/
lemma mpc_interior_polyNiche (hK : IsPolygonCap Θ K) :
    {p : ℝ × ℝ | mpcLow Θ K p.1 < p.2 ∧ p.2 < mpcTop Θ K p.1} ⊆ interior (polyNiche Θ K) := by
  apply interior_maximal
  · rw [mpc_polyNiche_eq hK]; rintro p ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
  · exact (isOpen_lt ((mpc_continuous_mpcLow Θ K).comp continuous_fst) continuous_snd).inter
      (isOpen_lt continuous_snd ((mpc_continuous_mpcTop Θ K).comp continuous_fst))

/-- A frontier point of the niche lies between `mpcLow` and `mpcTop`, on one of them. -/
lemma mpc_frontier_polyNiche (hK : IsPolygonCap Θ K) {p : ℝ × ℝ}
    (hp : p ∈ frontier (polyNiche Θ K)) :
    mpcLow Θ K p.1 ≤ p.2 ∧ p.2 ≤ mpcTop Θ K p.1 ∧
      (p.2 = mpcLow Θ K p.1 ∨ p.2 = mpcTop Θ K p.1) := by
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨a, b⟩ := mpc_closure_polyNiche hK h1
  refine ⟨a, b, ?_⟩
  by_contra h
  push Not at h
  exact h2 (mpc_interior_polyNiche hK ⟨lt_of_le_of_ne a (Ne.symm h.1), lt_of_le_of_ne b h.2⟩)

/-- Where `mpcLow < mpcTop`, the point of the graph of `mpcTop` is a frontier point of the niche. -/
lemma mpc_top_mem_frontier (hK : IsPolygonCap Θ K) {x : ℝ}
    (hx : mpcLow Θ K x < mpcTop Θ K x) : (x, mpcTop Θ K x) ∈ frontier (polyNiche Θ K) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := min (ε / 2) ((mpcTop Θ K x - mpcLow Θ K x) / 2)
    have hδ : 0 < δ := lt_min (half_pos hε) (by linarith)
    refine ⟨(x, mpcTop Θ K x - δ), ?_, ?_⟩
    · rw [mpc_polyNiche_eq hK]
      refine ⟨?_, by simp only; linarith⟩
      have := min_le_right (ε / 2) ((mpcTop Θ K x - mpcLow Θ K x) / 2)
      simp only
      linarith
    · rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [show mpcTop Θ K x - (mpcTop Θ K x - δ) = δ by ring, abs_of_pos hδ]
      exact max_lt hε (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  · have := interior_subset h
    rw [mpc_polyNiche_eq hK] at this
    exact lt_irrefl _ this.2

/-- A point of the niche on the graph of `mpcLow` is a frontier point of the niche. -/
lemma mpc_low_mem_frontier (hK : IsPolygonCap Θ K) {p : ℝ × ℝ} (hp : p ∈ polyNiche Θ K)
    (hlow : p.2 = mpcLow Θ K p.1) : p ∈ frontier (polyNiche Θ K) := by
  refine mpc_mem_frontier_of_below (subset_closure hp) fun δ hδ hmem => ?_
  rw [mpc_polyNiche_eq hK] at hmem
  have := hmem.1
  simp only at this
  linarith

end NicheFrontier

/-- The crossings of the wall `l(s, h_K(s) - 1)` with the other walls. -/
noncomputable def mpcWallCross (Θ : AngleSet) (K : Set (ℝ × ℝ)) (s : ℝ) : Finset ℝ :=
  (mpcDiamond Θ).image (fun r => mpcCrossX s (supp K s - 1) r (supp K r - 1))

section Walls

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- A meeting point of the wall `l(s, h_K(s) - 1)` with another wall is a crossing. -/
lemma mpc_mem_wallCross {s r x : ℝ} (hs : s ∈ Θ.diamond) (hr : r ∈ Θ.diamond) (hrs : r ≠ s)
    (h : mpcL K s x = mpcL K r x) : x ∈ (mpcWallCross Θ K s : Set ℝ) := by
  have := mpc_lineY_eq_imp (mpc_sin_pos_of_diamond hs).ne' (mpc_sin_pos_of_diamond hr).ne'
    (mpc_diamond_sin_sub_ne hs hr (Ne.symm hrs)) h
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨r, mpc_mem_mpcDiamond.2 hr, this.symm⟩)

/-- An angle of `Θ ∪ (Θ + π/2)` lies in `Θ^◇` and differs from `ω` and `π/2`. -/
lemma mpc_inner_ne {s : ℝ} (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2) :
    s ∈ Θ.diamond ∧ s ≠ Θ.ω ∧ s ≠ π / 2 := by
  have hω := mpc_omega_le Θ
  rcases hs with h | ⟨t, ht, rfl⟩
  · have := mpc_angles_bounds h
    exact ⟨Or.inl (Or.inl h), by linarith, by linarith⟩
  · have := mpc_angles_bounds ht
    exact ⟨Or.inl (Or.inr ⟨t, ht, rfl⟩), by linarith, by linarith⟩

/-- A point of an inner wall at which the wall equals the lower boundary of the fan is a
crossing. -/
lemma mpc_low_cross {s x : ℝ} (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2)
    (h : mpcL K s x = mpcLow Θ K x) : x ∈ (mpcWallCross Θ K s : Set ℝ) := by
  obtain ⟨hsd, h1, h2⟩ := mpc_inner_ne hs
  rw [mpcLow] at h
  rcases max_choice (mpcL K Θ.ω x) (mpcL K (π / 2) x) with h' | h' <;> rw [h'] at h
  · exact mpc_mem_wallCross hsd (Or.inr (Or.inl rfl)) (Ne.symm h1) h
  · exact mpc_mem_wallCross hsd (Or.inr (Or.inr rfl)) (Ne.symm h2) h

/-- On an inner wall, the frontier of the polygon niche and the polyline agree up to the
crossings. -/
lemma mpc_inner_wall (hK : IsPolygonCap Θ K) {s : ℝ}
    (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2) :
    {x | (x, mpcL K s x) ∈ frontier (polyNiche Θ K)} ⊆
        {x | (x, mpcL K s x) ∈ polyline Θ K} ∪ (mpcWallCross Θ K s : Set ℝ) ∧
      {x | (x, mpcL K s x) ∈ polyline Θ K} ⊆
        {x | (x, mpcL K s x) ∈ frontier (polyNiche Θ K)} ∪ (mpcWallCross Θ K s : Set ℝ) := by
  rw [mpc_polyline_eq hK]
  constructor
  · intro x hx
    obtain ⟨h1, h2, h3 | h3⟩ := mpc_frontier_polyNiche hK hx
    · exact Or.inr (mpc_low_cross hs h3)
    · left
      simp only [mem_ofPred_eq] at h1 h2 h3 ⊢
      have hG : mpcG Θ K x = mpcL K s x := by rw [mpcG, max_eq_right (h3 ▸ h1), h3]
      exact ⟨(mpc_between hK (h1.trans h2)).1, (mpc_between hK (h1.trans h2)).2, hG.symm⟩
  · rintro x ⟨h1, h2, h3⟩
    simp only at h3
    by_cases hlt : mpcLow Θ K x < mpcTop Θ K x
    · left
      have hG : mpcG Θ K x = mpcTop Θ K x := max_eq_right hlt.le
      show (x, mpcL K s x) ∈ frontier (polyNiche Θ K)
      rw [h3, hG]
      exact mpc_top_mem_frontier hK hlt
    · right
      push Not at hlt
      have hG : mpcG Θ K x = mpcLow Θ K x := max_eq_left hlt
      exact mpc_low_cross hs (h3.trans hG)

/-- At a frontier point of the niche on an inner wall `l(s, h_K(s) - 1)` other than a crossing,
`mpcTop` is attained by the pair of walls `(r, r + π/2)`, `r ∈ Θ`, containing `s`. -/
lemma mpc_top_pair (hK : IsPolygonCap Θ K) {s x : ℝ}
    (hs : s ∈ Θ.angles ∨ ∃ t ∈ Θ.angles, s = t + π / 2)
    (hx : (x, mpcL K s x) ∈ frontier (polyNiche Θ K)) (hc : x ∉ (mpcWallCross Θ K s : Set ℝ)) :
    ∃ r ∈ Θ.angles, (s = r ∨ s = r + π / 2) ∧
      mpcL K s x = min (mpcL K r x) (mpcL K (r + π / 2) x) := by
  obtain ⟨hsd, -, -⟩ := mpc_inner_ne hs
  obtain ⟨-, -, h3 | h3⟩ := mpc_frontier_polyNiche hK hx
  · exact absurd (mpc_low_cross hs h3) hc
  simp only at h3
  obtain ⟨r, hr, hrtop⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
    (fun r => min (mpcL K r x) (mpcL K (r + π / 2) x))
  rw [mpcTop, hrtop] at h3
  refine ⟨r, hr, ?_, h3⟩
  by_contra hne
  push Not at hne
  rcases min_choice (mpcL K r x) (mpcL K (r + π / 2) x) with h' | h' <;> rw [h'] at h3
  · exact hc (mpc_mem_wallCross hsd (Or.inl (Or.inl hr)) (Ne.symm hne.1) h3)
  · exact hc (mpc_mem_wallCross hsd (Or.inl (Or.inr ⟨r, hr, rfl⟩)) (Ne.symm hne.2) h3)

/-- On the wall `b_K(t)`, the frontier of the niche lies on the half-line `b⃗_K(t)` up to
crossings. -/
lemma mpc_wallB_vec (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.angles) :
    {x | (x, mpcL K t x) ∈ frontier (polyNiche Θ K)} ⊆
      {x | (x, mpcL K t x) ∈ frontier (polyNiche Θ K) ∩ wallBVec K t} ∪
        (mpcWallCross Θ K t : Set ℝ) := by
  intro x hx
  by_cases hc : x ∈ (mpcWallCross Θ K t : Set ℝ)
  · exact Or.inr hc
  refine Or.inl ⟨hx, ?_⟩
  obtain ⟨r, hr, hrt, hmin⟩ := mpc_top_pair hK (Or.inl ht) hx hc
  obtain rfl : t = r := hrt.resolve_right fun h => by
    linarith [(mpc_angles_bounds ht).2, (mpc_angles_bounds hr).1, mpc_omega_le Θ]
  rw [mpc_mem_wallBVec, mpc_dot_le_iff (mpc_sin_pos_of_diamond (Or.inl (Or.inr ⟨t, ht, rfl⟩)))]
  refine ⟨mpc_dot_lineY _ _ _ (mpc_sin_pos_of_diamond (Or.inl (Or.inl ht))).ne', ?_⟩
  exact hmin.trans_le (min_le_right _ _)

/-- On the wall `d_K(t)`, the frontier of the niche lies on the half-line `d⃗_K(t)` up to
crossings. -/
lemma mpc_wallD_vec (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ Θ.angles) :
    {x | (x, mpcL K (t + π / 2) x) ∈ frontier (polyNiche Θ K)} ⊆
      {x | (x, mpcL K (t + π / 2) x) ∈ frontier (polyNiche Θ K) ∩ wallDVec K t} ∪
        (mpcWallCross Θ K (t + π / 2) : Set ℝ) := by
  intro x hx
  by_cases hc : x ∈ (mpcWallCross Θ K (t + π / 2) : Set ℝ)
  · exact Or.inr hc
  refine Or.inl ⟨hx, ?_⟩
  obtain ⟨r, hr, hrt, hmin⟩ := mpc_top_pair hK (Or.inr ⟨t, ht, rfl⟩) hx hc
  obtain rfl : t = r := by
    rcases hrt with h | h
    · linarith [(mpc_angles_bounds ht).1, (mpc_angles_bounds hr).2, mpc_omega_le Θ]
    · linarith
  rw [mpc_mem_wallDVec, mpc_dot_le_iff (mpc_sin_pos_of_diamond (Or.inl (Or.inl ht)))]
  refine ⟨mpc_dot_lineY _ _ _ (mpc_sin_pos_of_diamond (Or.inl (Or.inr ⟨t, ht, rfl⟩))).ne', ?_⟩
  exact hmin.trans_le (min_le_left _ _)

end Walls

section Bottom

variable {Θ : AngleSet} {K : Set (ℝ × ℝ)}

/-- The part of a bottom side of the fan between `C_K⁺(ω)` and `A_K⁻(0)` has horizontal extent
`σ_K(t + π) sin t`. -/
lemma mpc_volume_bottom (hK : IsPolygonCap Θ K) {t : ℝ} (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    volume {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧ mpcL K t x = mpcLow Θ K x} =
      ENNReal.ofReal (sigmaAt K (t + π) * sin t) := by
  have hω0 := mpc_omega_pos Θ
  have hsω : 0 < sin Θ.ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [mpc_omega_le Θ, pi_pos])
  obtain ⟨hC1, -⟩ := mpc_cPlus_coords hK
  obtain ⟨hA1, -⟩ := mpc_aMinus_coords hK
  have hLω := mpc_mpcL_omega hK
  have hLπ := mpc_mpcL_pi_div_two hK
  rcases lt_or_eq_of_le (mpc_omega_le Θ) with hlt | heq
  · obtain ⟨hs1, h0, hs2, h1⟩ := mpc_sigma_bottom_lt hK hlt
    have hcω : 0 < cos Θ.ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
    -- the side `l(ω, 0)` of the fan is above the axis left of `0` and below it right of `0`
    have hsign : ∀ x, mpcL K Θ.ω x ≤ 0 ↔ 0 ≤ x := fun x => by
      rw [hLω, div_le_iff₀ hsω, zero_mul, neg_nonpos]
      exact ⟨fun h => by nlinarith, fun h => by nlinarith⟩
    have hsign' : ∀ x, 0 ≤ mpcL K Θ.ω x ↔ x ≤ 0 := fun x => by
      rw [hLω, le_div_iff₀ hsω, zero_mul, neg_nonneg]
      exact ⟨fun h => by nlinarith, fun h => by nlinarith⟩
    rcases ht with rfl | rfl
    · have hset : {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧
          mpcL K Θ.ω x = mpcLow Θ K x} = Icc (cPlus K Θ.ω).1 0 := by
        ext x
        simp only [mem_ofPred_eq, mem_Icc, mpcLow, hLπ, eq_comm (a := mpcL K Θ.ω x),
          max_eq_left_iff, hsign']
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, by linarith [h.2], h.2⟩⟩
      rw [hset, Real.volume_Icc, hC1, hs2]
      congr 1
      ring
    · have hset : {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧
          mpcL K (π / 2) x = mpcLow Θ K x} = Icc 0 (aMinus K 0).1 := by
        ext x
        simp only [mem_ofPred_eq, mem_Icc, mpcLow, hLπ, eq_comm (a := (0 : ℝ)), max_eq_right_iff,
          hsign]
        refine ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨?_, h.2, h.1⟩⟩
        rw [hC1]
        nlinarith
      rw [hset, Real.volume_Icc, hA1, show π / 2 + π = 3 * π / 2 by ring, hs1, sin_pi_div_two,
        mul_one, sub_zero]
  · have htπ : t = π / 2 := by rcases ht with rfl | rfl; exacts [heq, rfl]
    subst htπ
    have hset : {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧
        mpcL K (π / 2) x = mpcLow Θ K x} = Icc (cPlus K Θ.ω).1 (aMinus K 0).1 := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc, mpcLow, hLπ, heq, max_self, and_true]
    rw [hset, Real.volume_Icc, show π / 2 + π = 3 * π / 2 by ring, mpc_sigma_bottom_eq hK heq,
      sin_pi_div_two, mul_one, (mpc_cPlus_eq hK).2.2.2.2, hA1, sub_eq_add_neg]

end Bottom

end NicheWalls

/-- **Lemma 3.4.5** (`lem:polyline-length`) (1). For `t ∈ Θ`, the sides of `𝒩_Θ(K)` on `b_K(t)`
(all on the half-line `b⃗_K(t)`) have total length `τ_K(t)`, and those on `d_K(t)` (all on
`d⃗_K(t)`) have total length `τ_K(t + π/2)`. -/
theorem lemma3_4_5_one {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ Θ.angles) :
    lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t ∧
      lineLength t (supp K t - 1) (frontier (polyNiche Θ K) ∩ wallBVec K t) = tau Θ K t ∧
      lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K)) =
        tau Θ K (t + π / 2) ∧
      lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K) ∩ wallDVec K t) =
        tau Θ K (t + π / 2) := by
  have htd : t ∈ Θ.diamond := Or.inl (Or.inl ht)
  have hsd2 : t + π / 2 ∈ Θ.diamond := Or.inl (Or.inr ⟨t, ht, rfl⟩)
  have hfin := fun s => (mpcWallCross Θ K s).finite_toSet
  obtain ⟨hA1, hA2⟩ := mpc_inner_wall hK (Or.inl ht)
  obtain ⟨hB1, hB2⟩ := mpc_inner_wall hK (s := t + π / 2) (Or.inr ⟨t, ht, rfl⟩)
  have e1 : lineLength t (supp K t - 1) (frontier (polyNiche Θ K)) = tau Θ K t := by
    rw [mpc_tau_eq_lineLength hK htd, mpc_lineLength_eq (mpc_sin_pos_of_diamond htd),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond htd)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (hfin t) (hfin t) hA1 hA2
  have e2 : lineLength (t + π / 2) (supp K (t + π / 2) - 1) (frontier (polyNiche Θ K)) =
      tau Θ K (t + π / 2) := by
    rw [mpc_tau_eq_lineLength hK hsd2, mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (hfin _) (hfin _) hB1 hB2
  refine ⟨e1, ?_, e2, ?_⟩
  · rw [← e1, mpc_lineLength_eq (mpc_sin_pos_of_diamond htd),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond htd)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (G := (mpcWallCross Θ K t : Set ℝ)) finite_empty (hfin t)
      (fun x hx => Or.inl hx.1) (mpc_wallB_vec hK ht)
  · rw [← e2, mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2),
      mpc_lineLength_eq (mpc_sin_pos_of_diamond hsd2)]
    congr 2
    exact mpc_volume_eq_of_finite_diff (G := (mpcWallCross Θ K (t + π / 2) : Set ℝ))
      finite_empty (hfin _) (fun x hx => Or.inl hx.1) (mpc_wallD_vec hK ht)

open MeasureTheory in
/-- **Lemma 3.4.5** (2). For `t ∈ {ω, π/2}`, the sides of `𝒩_Θ(K)` on `l(t, 0)` have total length
`σ_K(t + π) - τ_K(t)`. -/
theorem lemma3_4_5_two {Θ : AngleSet} {K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t : ℝ}
    (ht : t ∈ ({Θ.ω, π / 2} : Set ℝ)) :
    lineLength t 0 (frontier (polyNiche Θ K)) = sigmaAt K (t + π) - tau Θ K t ∧
      lineLength t 0 (polyNiche Θ K) = sigmaAt K (t + π) - tau Θ K t := by
  have htd : t ∈ Θ.diamond := nef_pair_mem_diamond ht
  have hst := mpc_sin_pos_of_diamond htd
  have hc0 : (0 : ℝ) = supp K t - 1 := by rw [(mpc_supp_bot hK.1 ht).1]; ring
  have hLlow : ∀ x, mpcL K t x ≤ mpcLow Θ K x := by
    rcases ht with rfl | rfl
    · exact fun x => le_max_left _ _
    · exact fun x => le_max_right _ _
  -- In the abscissa: `Z` is the part of the bottom side `l(t, 0) = l(t, h_K(t) - 1)` of `F_ω`
  -- between `C_K⁺(ω)` and `A_K⁻(0)`; it splits into the part `Y` in the niche and the part `X` on
  -- the polyline, and `SF` is the part on the frontier of the niche.
  set Y := {x | (x, mpcL K t x) ∈ polyNiche Θ K}
  set SF := {x | (x, mpcL K t x) ∈ frontier (polyNiche Θ K)}
  set X := {x | (x, mpcL K t x) ∈ polyline Θ K}
  set Z := {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧ mpcL K t x = mpcLow Θ K x}
  have hpoly := mpc_polyline_eq hK
  -- Step 1: `Z` is the disjoint union of `Y` and the closed set `X`.
  have hYZ : Y ⊆ Z := by
    intro x hx
    simp only [Y, mem_ofPred_eq] at hx
    rw [mpc_polyNiche_eq hK] at hx
    obtain ⟨h1, h2⟩ := hx
    exact ⟨(mpc_between hK (h1.trans h2.le)).1, (mpc_between hK (h1.trans h2.le)).2,
      le_antisymm (hLlow x) h1⟩
  have hXZ : X ⊆ Z := by
    intro x hx
    simp only [X, mem_ofPred_eq] at hx
    rw [hpoly] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    simp only at h3
    exact ⟨h1, h2, le_antisymm (hLlow x) (h3 ▸ le_max_left _ _)⟩
  have hZYX : Z ⊆ Y ∪ X := by
    rintro x ⟨h1, h2, h3⟩
    by_cases hlt : mpcL K t x < mpcTop Θ K x
    · left
      show (x, mpcL K t x) ∈ polyNiche Θ K
      rw [mpc_polyNiche_eq hK]
      exact ⟨h3.symm.le, hlt⟩
    · right
      push Not at hlt
      show (x, mpcL K t x) ∈ polyline Θ K
      rw [hpoly]
      refine ⟨h1, h2, ?_⟩
      simp only
      rw [mpcG, max_eq_left (h3 ▸ hlt), h3]
  have hdisj : Disjoint Y X := by
    rw [Set.disjoint_left]
    intro x hY hX
    simp only [Y, X, mem_ofPred_eq] at hY hX
    rw [mpc_polyNiche_eq hK] at hY
    rw [hpoly] at hX
    have := hY.2
    have h3 := hX.2.2
    simp only at this h3
    rw [h3] at this
    exact absurd (le_max_right _ _) (not_le.2 this)
  have hXc : IsClosed X := by
    have : X = {x | (cPlus K Θ.ω).1 ≤ x ∧ x ≤ (aMinus K 0).1 ∧ mpcL K t x = mpcG Θ K x} := by
      ext x; simp only [X, mem_ofPred_eq, hpoly]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_eq (mpc_continuous_mpcL K t) (mpc_continuous_mpcG Θ K)))
  -- Step 2: `|Y| = σ_K(t + π) sin t - |X|`, where `|X| = τ_K(t) sin t`.
  have hvolZ := mpc_volume_bottom hK ht
  have hZfin : volume Z ≠ ⊤ := by rw [hvolZ]; exact ENNReal.ofReal_ne_top
  have hsum : volume Z = volume Y + volume X := by
    rw [subset_antisymm hZYX (union_subset hYZ hXZ)]
    exact measure_union hdisj hXc.measurableSet
  have hreal : (volume Y).toReal = sigmaAt K (t + π) * sin t - (volume X).toReal := by
    have := congrArg ENNReal.toReal hsum
    have hnn : 0 ≤ sigmaAt K (t + π) * sin t := mul_nonneg ENNReal.toReal_nonneg hst.le
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top hZfin (measure_mono hYZ))
      (ne_top_of_le_ne_top hZfin (measure_mono hXZ)), hvolZ, ENNReal.toReal_ofReal hnn] at this
    linarith
  have htau : tau Θ K t = (volume X).toReal / sin t := by
    rw [mpc_tau_eq_lineLength hK htd, mpc_lineLength_eq hst]
    rfl
  -- Step 3: the frontier of the niche on `l(t, 0)` is `Y`, up to the crossings with the walls.
  have hSF : SF ⊆ Y ∪ (mpcWallCross Θ K t : Set ℝ) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := mpc_frontier_polyNiche hK hx
    simp only at h1 h2 h3
    rcases lt_or_eq_of_le h2 with hlt | heq
    · left
      show (x, mpcL K t x) ∈ polyNiche Θ K
      rw [mpc_polyNiche_eq hK]
      exact ⟨h1, hlt⟩
    · right
      obtain ⟨r, hr, hrtop⟩ := Finset.exists_mem_eq_sup' Θ.nonempty
        (fun r => min (mpcL K r x) (mpcL K (r + π / 2) x))
      rw [mpcTop, hrtop] at heq
      rcases min_choice (mpcL K r x) (mpcL K (r + π / 2) x) with h' | h' <;> rw [h'] at heq
      · exact mpc_mem_wallCross htd (Or.inl (Or.inl hr)) (nef_ne_of_mem_angles (Or.inl hr) ht) heq
      · exact mpc_mem_wallCross htd (Or.inl (Or.inr ⟨r, hr, rfl⟩))
          (nef_ne_of_mem_angles (Or.inr ⟨r, hr, rfl⟩) ht) heq
  have hYSF : Y ⊆ SF := by
    intro x hx
    have h1 : (x, mpcL K t x) ∈ polyNiche Θ K := hx
    rw [mpc_polyNiche_eq hK] at h1
    exact mpc_low_mem_frontier hK hx (le_antisymm (hLlow x) h1.1)
  have hvolSF : volume SF = volume Y :=
    mpc_volume_eq_of_finite_diff (mpcWallCross Θ K t).finite_toSet finite_empty hSF
      (fun x hx => Or.inl (hYSF hx))
  rw [hc0, mpc_lineLength_eq hst, mpc_lineLength_eq hst]
  change (volume SF).toReal / sin t = _ ∧ (volume Y).toReal / sin t = _
  rw [hvolSF, hreal, htau]
  constructor <;> field_simp

end MovingSofaOptimality
