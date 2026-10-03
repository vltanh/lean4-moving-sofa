module

public import MovingSofaOptimality.Monotone.CapContainsNiche

/-!
# Simple Nef polygons (§3.1)

Definitions 3.1.1–3.1.4, Proposition 3.1.1 (`pro:monotone-boolean-function`) and Theorem 3.1.2
(`thm:simple-nef-polygon`). Definition 3.1.5 (the `O`-notation with subscripts) is rendered by
explicit constants: a statement `f = O_{X,i}(g)` becomes `∃ C, |f| ≤ C g` with `C` chosen after `X`
and `i`.
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

/-- An `n`-ary boolean function (Definition 3.1.1, `def:boolean-function`). -/
abbrev BoolFun (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- A monotone boolean function (Definition 3.1.2, `def:monotone-boolean-function`). -/
def BoolFun.IsMonotone {n : ℕ} (E : BoolFun n) : Prop :=
  ∀ P Q : Fin n → Bool, (∀ i, P i = true → Q i = true) → E P = true → E Q = true

/-- Boolean expressions built from variables with conjunctions and disjunctions only. -/
inductive PosBoolExpr (n : ℕ) where
  | var (i : Fin n)
  | and (a b : PosBoolExpr n)
  | or (a b : PosBoolExpr n)

/-- The boolean function of a positive boolean expression. -/
def PosBoolExpr.eval {n : ℕ} : PosBoolExpr n → BoolFun n
  | .var i => fun P => P i
  | .and a b => fun P => a.eval P && b.eval P
  | .or a b => fun P => a.eval P || b.eval P

/-- **Proposition 3.1.1** (`pro:monotone-boolean-function`). A boolean function obtained from the
variables by conjunctions and disjunctions is monotone. -/
theorem proposition3_1_1 {n : ℕ} (e : PosBoolExpr n) : e.eval.IsMonotone := by
  induction e with
  | var i => intro P Q hPQ h; exact hPQ i h
  | and a b iha ihb =>
    intro P Q hPQ h
    simp only [PosBoolExpr.eval, Bool.and_eq_true] at h ⊢
    exact ⟨iha P Q hPQ h.1, ihb P Q hPQ h.2⟩
  | or a b iha ihb =>
    intro P Q hPQ h
    simp only [PosBoolExpr.eval, Bool.or_eq_true] at h ⊢
    exact h.imp (iha P Q hPQ) (ihb P Q hPQ)

open Classical in
/-- The Nef polygon `𝓔(H_1, …, H_n) = {p : 𝓔(p ∈ H_1, …, p ∈ H_n)}` (Definition 3.1.3,
`def:nef-polygon`). -/
noncomputable def nefPolygon {n : ℕ} (E : BoolFun n) (H : Fin n → Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | E (fun i => decide (p ∈ H i)) = true}

/-- A defining half-plane of a simple Nef polygon: the closed half-plane `H₋(t, h)` or the open
half-plane `H₋°(t, h)`. -/
structure HalfPlaneData where
  t : ℝ
  h : ℝ
  isOpen : Bool

/-- The half-plane described by a `HalfPlaneData`. -/
def HalfPlaneData.toSet (d : HalfPlaneData) : Set (ℝ × ℝ) :=
  if d.isOpen then halfMinusOpen d.t d.h else halfMinus d.t d.h

/-- The boundary line `l(t, h)` of a defining half-plane. -/
def HalfPlaneData.boundary (d : HalfPlaneData) : Set (ℝ × ℝ) := line d.t d.h

/-- The half-plane pushed by `δ` in the direction of its normal: `H₋(t, h + δ)` or
`H₋°(t, h + δ)`. -/
def HalfPlaneData.shift (d : HalfPlaneData) (δ : ℝ) : HalfPlaneData := { d with h := d.h + δ }

/-- `X` is a simple Nef polygon with defining half-planes `H_1, …, H_n` (Definition 3.1.4,
`def:simple-nef-polygon`): `X = 𝓔(H_1, …, H_n)` for a monotone boolean function `𝓔`, and the
half-planes have pairwise different boundary lines. -/
def IsSimpleNefPolygon {n : ℕ} (X : Set (ℝ × ℝ)) (E : BoolFun n) (H : Fin n → HalfPlaneData) :
    Prop :=
  E.IsMonotone ∧ Pairwise (fun i j => (H i).boundary ≠ (H j).boundary) ∧
    X = nefPolygon E (fun i => (H i).toSet)

/-! ### Auxiliary material for Theorem 3.1.2

For `δ ≥ 0` the half-plane grows, `X ⊆ X'_δ`, and `X'_δ \ X` is the part of the fixed set
`Y = {p : 𝓔(…, true, …) ∧ ¬𝓔(…, false, …)}` (the `i`-th argument replaced by `true`, resp. `false`)
in the strip between `l_i` and the pushed line; `δ ≤ 0` is symmetric. By Cavalieri's principle in
the frame `(u_{t_i}, v_{t_i})` (rotations preserve the area), the area of that part is the integral
over the strip of the length `g(s)` of the slice of `Y` along `l(t_i, s)`. The slices vary
Lipschitz-continuously for `s` near `h_i`, because the other boundary lines are different from
`l_i`; and `g(h_i) = 𝓗¹(∂X ∩ l_i)`, because a point of `l_i` on no other boundary line is a boundary
point of `X` exactly when it lies in `Y`. This replaces the paper's decomposition into the regions
`R_k` cut out by the other boundary lines. -/

section NefAux

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Fubini in a rotated frame -/

/-- Cavalieri's principle in the frame `(u_t, v_t)`: the area of a measurable set is the integral
over `s` of the length of its slice along the line `l(t, s)`, parametrized by
`r ↦ s u_t + r v_t`. -/
lemma nef_volume_eq_lintegral (t : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    volume A = ∫⁻ s, volume {r : ℝ | rot t (s, r) ∈ A} := by
  rw [← volume_preimage_rot t A, Measure.volume_eq_prod,
    Measure.prod_apply ((continuous_rot t).measurable hA)]
  rfl

/-! ### Membership vectors -/

open Classical in
/-- The membership vector `(p ∈ S_1, …, p ∈ S_n)`. -/
private noncomputable def nefVec {n : ℕ} (S : Fin n → Set (ℝ × ℝ)) (p : ℝ × ℝ) : Fin n → Bool :=
  fun j => decide (p ∈ S j)

private lemma nef_mem_nefPolygon {n : ℕ} {E : BoolFun n} {S : Fin n → Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ nefPolygon E S ↔ E (nefVec S p) = true := Iff.rfl

private lemma nef_vec_apply {n : ℕ} (S : Fin n → Set (ℝ × ℝ)) (p : ℝ × ℝ) (j : Fin n) :
    nefVec S p j = true ↔ p ∈ S j := by
  simp [nefVec]

private lemma nef_vec_update {n : ℕ} (S : Fin n → Set (ℝ × ℝ)) (i : Fin n) (T : Set (ℝ × ℝ))
    (p : ℝ × ℝ) :
    nefVec (Function.update S i T) p =
      Function.update (nefVec S p) i (nefVec (fun _ => T) p i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [nefVec]
  · simp [nefVec, Function.update_of_ne hj]

/-- The set `Y = {p : 𝓔(…, true, …) ∧ ¬𝓔(…, false, …)}` of points where membership in the Nef
polygon is decided by the `i`-th half-plane. -/
private def nefY {n : ℕ} (E : BoolFun n) (S : Fin n → Set (ℝ × ℝ)) (i : Fin n) : Set (ℝ × ℝ) :=
  {p | E (Function.update (nefVec S p) i true) = true ∧
    E (Function.update (nefVec S p) i false) = false}

private lemma nef_mono_update {n : ℕ} {E : BoolFun n} (hE : E.IsMonotone) (P : Fin n → Bool)
    (i : Fin n) (h : E (Function.update P i false) = true) :
    E (Function.update P i true) = true := by
  refine hE _ _ (fun j hj => ?_) h
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne hji] at hj ⊢; exact hj

/-- Pushing the `i`-th set outwards adds exactly the part of `Y` in the added region. -/
private lemma nef_update_eq_union {n : ℕ} {E : BoolFun n} (hE : E.IsMonotone)
    (S : Fin n → Set (ℝ × ℝ)) (i : Fin n) {T : Set (ℝ × ℝ)} (hT : S i ⊆ T) :
    nefPolygon E (Function.update S i T) = nefPolygon E S ∪ (nefY E S i ∩ (T \ S i)) := by
  ext p
  simp only [mem_union, nef_mem_nefPolygon, nefY, mem_inter_iff, Set.mem_sdiff, mem_ofPred_eq]
  rw [nef_vec_update]
  have hX : E (nefVec S p) = E (Function.update (nefVec S p) i (nefVec S p i)) := by
    rw [Function.update_eq_self]
  rw [hX]
  by_cases hpS : p ∈ S i
  · have hpT := hT hpS
    have e1 : nefVec (fun _ => T) p i = true := (nef_vec_apply _ _ _).2 hpT
    have e2 : nefVec S p i = true := (nef_vec_apply _ _ _).2 hpS
    rw [e1, e2]; tauto
  · have e2 : nefVec S p i = false := by
      simpa [nefVec] using hpS
    rw [e2]
    by_cases hpT : p ∈ T
    · have e1 : nefVec (fun _ => T) p i = true := (nef_vec_apply _ _ _).2 hpT
      rw [e1]
      constructor
      · intro h
        by_cases hf : E (Function.update (nefVec S p) i false) = true
        · exact Or.inl hf
        · exact Or.inr ⟨⟨h, by simpa using hf⟩, hpT, hpS⟩
      · rintro (h | ⟨⟨h, -⟩, -⟩)
        · exact nef_mono_update hE _ i h
        · exact h
    · have e1 : nefVec (fun _ => T) p i = false := by simpa [nefVec] using hpT
      rw [e1]; tauto

private lemma nef_disjoint_Y {n : ℕ} {E : BoolFun n} (S : Fin n → Set (ℝ × ℝ)) (i : Fin n)
    (T : Set (ℝ × ℝ)) : Disjoint (nefPolygon E S) (nefY E S i ∩ (T \ S i)) := by
  rw [Set.disjoint_left]
  rintro p hp ⟨⟨-, hF⟩, -, hpS⟩
  have hX : E (nefVec S p) = E (Function.update (nefVec S p) i (nefVec S p i)) := by
    rw [Function.update_eq_self]
  rw [nef_mem_nefPolygon, hX] at hp
  have e2 : nefVec S p i = false := by simpa [nefVec] using hpS
  rw [e2] at hp
  simp [hp] at hF

/-- `Y` does not depend on the `i`-th set. -/
private lemma nef_nefY_update {n : ℕ} (E : BoolFun n) (S : Fin n → Set (ℝ × ℝ)) (i : Fin n)
    (T : Set (ℝ × ℝ)) : nefY E (Function.update S i T) i = nefY E S i := by
  ext p; simp only [nefY, mem_ofPred_eq, nef_vec_update, Function.update_idem]

/-- Pushing the `i`-th set inwards removes exactly the part of `Y` in the removed region. -/
private lemma nef_eq_update_union {n : ℕ} {E : BoolFun n} (hE : E.IsMonotone)
    (S : Fin n → Set (ℝ × ℝ)) (i : Fin n) {T : Set (ℝ × ℝ)} (hT : T ⊆ S i) :
    nefPolygon E S = nefPolygon E (Function.update S i T) ∪ (nefY E S i ∩ (S i \ T)) := by
  have h1 : Function.update (Function.update S i T) i (S i) = S := by simp
  have := nef_update_eq_union hE (Function.update S i T) i (T := S i) (by simpa using hT)
  rw [h1, nef_nefY_update] at this
  simpa using this

private lemma nef_disjoint_Y' {n : ℕ} {E : BoolFun n} (S : Fin n → Set (ℝ × ℝ)) (i : Fin n)
    (T : Set (ℝ × ℝ)) :
    Disjoint (nefPolygon E (Function.update S i T)) (nefY E S i ∩ (S i \ T)) := by
  have := nef_disjoint_Y (E := E) (Function.update S i T) i (S i)
  rw [nef_nefY_update] at this
  simpa using this

/-! ### Measurability -/

private lemma nef_measurable_nefVec {n : ℕ} {S : Fin n → Set (ℝ × ℝ)}
    (hS : ∀ j, MeasurableSet (S j)) :
    Measurable (nefVec S) := by
  refine Measurable.of_eval fun j => measurable_to_bool ?_
  have : (fun p => nefVec S p j) ⁻¹' {true} = S j := by
    ext p; simp [nefVec]
  rw [this]; exact hS j

private lemma nef_measurableSet_preimage_nefVec {n : ℕ} {S : Fin n → Set (ℝ × ℝ)}
    (hS : ∀ j, MeasurableSet (S j)) (B : Set (Fin n → Bool)) : MeasurableSet (nefVec S ⁻¹' B) :=
  nef_measurable_nefVec hS (Set.toFinite B).measurableSet

private lemma nef_measurableSet_nefY {n : ℕ} (E : BoolFun n) {S : Fin n → Set (ℝ × ℝ)}
    (hS : ∀ j, MeasurableSet (S j)) (i : Fin n) : MeasurableSet (nefY E S i) :=
  nef_measurableSet_preimage_nefVec hS
    {P | E (Function.update P i true) = true ∧ E (Function.update P i false) = false}

/-! ### Half-planes -/

private lemma nef_dot_rot_pair (t t' s r : ℝ) :
    dot (rot t (s, r)) (uvec t') = s * dot (uvec t) (uvec t') + r * dot (vvec t) (uvec t') := by
  rw [rot_pair, dot_add_left, dot_smul_left, dot_smul_left]

private lemma nef_mem_toSet_of_isOpen {d : HalfPlaneData} (hd : d.isOpen = true) (p : ℝ × ℝ) :
    p ∈ d.toSet ↔ dot p (uvec d.t) < d.h := by
  simp [HalfPlaneData.toSet, hd, halfMinusOpen]

private lemma nef_mem_toSet_of_not_isOpen {d : HalfPlaneData} (hd : d.isOpen = false)
    (p : ℝ × ℝ) : p ∈ d.toSet ↔ dot p (uvec d.t) ≤ d.h := by
  simp [HalfPlaneData.toSet, hd, halfMinus]

private lemma nef_mem_toSet_of_lt (d : HalfPlaneData) {p : ℝ × ℝ} (h : dot p (uvec d.t) < d.h) :
    p ∈ d.toSet := by
  cases hd : d.isOpen
  · exact (nef_mem_toSet_of_not_isOpen hd p).2 h.le
  · exact (nef_mem_toSet_of_isOpen hd p).2 h

private lemma nef_not_mem_toSet_of_lt (d : HalfPlaneData) {p : ℝ × ℝ}
    (h : d.h < dot p (uvec d.t)) : p ∉ d.toSet := by
  cases hd : d.isOpen
  · rw [nef_mem_toSet_of_not_isOpen hd p]; exact not_le.2 h
  · rw [nef_mem_toSet_of_isOpen hd p]; exact not_lt.2 h.le

private lemma nef_measurableSet_toSet (d : HalfPlaneData) : MeasurableSet d.toSet := by
  unfold HalfPlaneData.toSet
  split
  · exact (isOpen_halfMinusOpen _ _).measurableSet
  · exact (isClosed_halfMinus _ _).measurableSet

/-- Away from its boundary line, membership in a half-plane is locally constant. -/
private lemma nef_eventually_mem_toSet_iff (d : HalfPlaneData) {p : ℝ × ℝ}
    (hp : dot p (uvec d.t) ≠ d.h) : ∀ᶠ q in 𝓝 p, (q ∈ d.toSet ↔ p ∈ d.toSet) := by
  have hc : Continuous fun q : ℝ × ℝ => dot q (uvec d.t) := continuous_dot _
  rcases lt_or_gt_of_ne hp with h | h
  · filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with q hq
    exact iff_of_true (nef_mem_toSet_of_lt d hq) (nef_mem_toSet_of_lt d h)
  · filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with q hq
    exact iff_of_false (nef_not_mem_toSet_of_lt d hq) (nef_not_mem_toSet_of_lt d h)

/-- Points of the boundary line are accumulated by points inside and outside the half-plane. -/
private lemma nef_frequently_toSet (d : HalfPlaneData) {p : ℝ × ℝ}
    (hp : dot p (uvec d.t) = d.h) : (∃ᶠ q in 𝓝 p, q ∈ d.toSet) ∧ (∃ᶠ q in 𝓝 p, q ∉ d.toSet) := by
  have hf : Continuous fun ε : ℝ => p + ε • uvec d.t := by fun_prop
  have hdot : ∀ ε : ℝ, dot (p + ε • uvec d.t) (uvec d.t) = d.h + ε := by
    intro ε; rw [dot_add_left, dot_smul_left, dot_uvec_self, hp, mul_one]
  constructor
  · have ht : Tendsto (fun ε : ℝ => p + ε • uvec d.t) (𝓝[<] 0) (𝓝 p) := by
      have := (hf.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio 0))
      simpa using this
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact nef_mem_toSet_of_lt d (by rw [hdot]; linarith [show ε < 0 from hε])
  · have ht : Tendsto (fun ε : ℝ => p + ε • uvec d.t) (𝓝[>] 0) (𝓝 p) := by
      have := (hf.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact nef_not_mem_toSet_of_lt d (by rw [hdot]; linarith [show 0 < ε from hε])

/-- Membership in the frontier only depends on the germ of the set. -/
private lemma nef_mem_frontier_congr {A B : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (h : ∀ᶠ q in 𝓝 p, (q ∈ A ↔ q ∈ B)) : p ∈ frontier A ↔ p ∈ frontier B := by
  simp only [frontier, Set.mem_sdiff, mem_closure_iff_frequently, mem_interior_iff_mem_nhds]
  have h1 : (∃ᶠ q in 𝓝 p, q ∈ A) ↔ ∃ᶠ q in 𝓝 p, q ∈ B := frequently_congr h
  have h2 : A ∈ 𝓝 p ↔ B ∈ 𝓝 p := eventually_congr h
  rw [h1, h2]

/-- The local structure of a Nef polygon at a point of the `i`-th boundary line lying on no other
boundary line: it is a boundary point if and only if it lies in `Y`. -/
private lemma nef_mem_frontier_iff_mem_nefY {n : ℕ} {E : BoolFun n} (hE : E.IsMonotone)
    (H : Fin n → HalfPlaneData) (i : Fin n) {p : ℝ × ℝ} (hpi : dot p (uvec (H i).t) = (H i).h)
    (hpj : ∀ j, j ≠ i → dot p (uvec (H j).t) ≠ (H j).h) :
    p ∈ frontier (nefPolygon E (fun j => (H j).toSet)) ↔
      p ∈ nefY E (fun j => (H j).toSet) i := by
  set S : Fin n → Set (ℝ × ℝ) := fun j => (H j).toSet with hS
  have hloc : ∀ᶠ q in 𝓝 p, ∀ j, j ≠ i → (q ∈ S j ↔ p ∈ S j) := by
    rw [eventually_all]
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall fun q h => absurd hj h
    · filter_upwards [nef_eventually_mem_toSet_iff (H j) (hpj j hj)] with q hq _ using hq
  have hvec : ∀ᶠ q in 𝓝 p, nefVec S q = Function.update (nefVec S p) i (nefVec S q i) := by
    filter_upwards [hloc] with q hq
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      simp only [nefVec]
      exact decide_eq_decide.2 (hq j hj)
  by_cases hY : p ∈ nefY E S i
  · obtain ⟨hT, hF⟩ := id hY
    have hloc' : ∀ᶠ q in 𝓝 p, (q ∈ nefPolygon E S ↔ q ∈ S i) := by
      filter_upwards [hvec] with q hq
      rw [nef_mem_nefPolygon, hq]
      by_cases hqi : q ∈ S i
      · have : nefVec S q i = true := (nef_vec_apply _ _ _).2 hqi
        rw [this]; exact iff_of_true hT hqi
      · have : nefVec S q i = false := by simpa [nefVec] using hqi
        rw [this, hF]; exact iff_of_false (by simp) hqi
    rw [nef_mem_frontier_congr hloc']
    refine iff_of_true ?_ hY
    obtain ⟨h1, h2⟩ := nef_frequently_toSet (H i) hpi
    refine ⟨mem_closure_iff_frequently.2 h1, fun hin => ?_⟩
    rw [mem_interior_iff_mem_nhds] at hin
    exact h2 (Filter.mem_of_superset hin fun q hq hq' => hq' hq)
  · have hTF : E (Function.update (nefVec S p) i true) =
        E (Function.update (nefVec S p) i false) := by
      simp only [nefY, mem_ofPred_eq, not_and] at hY
      cases hT : E (Function.update (nefVec S p) i true) <;>
        cases hF : E (Function.update (nefVec S p) i false)
      · rfl
      · have := nef_mono_update hE _ i hF
        rw [hT] at this; exact absurd this (by simp)
      · exact absurd hF (hY hT)
      · rfl
    have hloc' : ∀ᶠ q in 𝓝 p, (q ∈ nefPolygon E S ↔
        q ∈ {_q : ℝ × ℝ | E (Function.update (nefVec S p) i true) = true}) := by
      filter_upwards [hvec] with q hq
      rw [nef_mem_nefPolygon, hq]
      show _ ↔ E (Function.update (nefVec S p) i true) = true
      cases nefVec S q i
      · rw [hTF]
      · rfl
    rw [nef_mem_frontier_congr hloc']
    simp only [hY, iff_false]
    by_cases he : E (Function.update (nefVec S p) i true) = true <;> simp [he]

/-! ### Slices of the half-planes along the lines `l(t, s)` -/

private lemma nef_sq_add_sq (t t' : ℝ) :
    dot (vvec t) (uvec t') ^ 2 + dot (uvec t) (uvec t') ^ 2 = 1 := by
  rw [dot_vvec_uvec', dot_uvec_uvec, show t' - t = -(t - t') by ring, sin_neg, neg_sq]
  exact sin_sq_add_cos_sq _

/-- If `l(t', c)` is parallel to `l(t, h)` and different from it, then `c ≠ h (u_t · u_{t'})`. -/
private lemma nef_parallel_ne {t t' h c : ℝ} (ha : dot (vvec t) (uvec t') = 0)
    (hne : line t' c ≠ line t h) : c ≠ h * dot (uvec t) (uvec t') := by
  intro hc
  apply hne
  have hb : dot (uvec t) (uvec t') ≠ 0 := by
    intro hb; have := nef_sq_add_sq t t'; rw [ha, hb] at this; norm_num at this
  ext p
  have hp : dot p (uvec t') = dot p (uvec t) * dot (uvec t) (uvec t') := by
    conv_lhs => rw [eq_dot_uvec_smul_add p t]
    rw [dot_add_left, dot_smul_left, dot_smul_left, ha, mul_zero, add_zero]
  simp only [line, mem_ofPred_eq, hp, hc]
  constructor
  · intro h'; exact mul_right_cancel₀ hb h'
  · intro h'; rw [h']

/-- For a line parallel to and different from `l(t, h)`, membership of `rot t (s, r)` in the
corresponding half-plane does not depend on `r`, nor on `s` near `h`. -/
private lemma nef_eventually_parallel {t h : ℝ} (d : HalfPlaneData)
    (ha : dot (vvec t) (uvec d.t) = 0) (hne : d.boundary ≠ line t h) :
    ∀ᶠ s in 𝓝 h, ∀ r, (rot t (s, r) ∈ d.toSet ↔ rot t (h, r) ∈ d.toSet) := by
  have hc := nef_parallel_ne ha hne
  set b := dot (uvec t) (uvec d.t)
  have hdot : ∀ s r, dot (rot t (s, r)) (uvec d.t) = s * b := by
    intro s r; rw [nef_dot_rot_pair, ha, mul_zero, add_zero]
  have hcont : Continuous fun s : ℝ => s * b := by fun_prop
  rcases lt_or_gt_of_ne hc with h' | h'
  · -- `d.h < h * b`: the points are outside
    filter_upwards [continuousAt_const.eventually_lt hcont.continuousAt h'] with s hs r
    exact iff_of_false (nef_not_mem_toSet_of_lt d (by rw [hdot]; exact hs))
      (nef_not_mem_toSet_of_lt d (by rw [hdot]; exact h'))
  · filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const h'] with s hs r
    exact iff_of_true (nef_mem_toSet_of_lt d (by rw [hdot]; exact hs))
      (nef_mem_toSet_of_lt d (by rw [hdot]; exact h'))

private lemma nef_abs_le_of_not_iff (d : HalfPlaneData) {p q : ℝ × ℝ}
    (h : ¬(p ∈ d.toSet ↔ q ∈ d.toSet)) :
    |dot p (uvec d.t) - d.h| ≤ |dot p (uvec d.t) - dot q (uvec d.t)| := by
  cases hd : d.isOpen
  · rw [nef_mem_toSet_of_not_isOpen hd, nef_mem_toSet_of_not_isOpen hd] at h
    by_cases hp : dot p (uvec d.t) ≤ d.h
    · have hq : ¬ dot q (uvec d.t) ≤ d.h := fun hq => h (iff_of_true hp hq)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    · have hq : dot q (uvec d.t) ≤ d.h := by
        by_contra hq; exact h (iff_of_false hp hq)
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  · rw [nef_mem_toSet_of_isOpen hd, nef_mem_toSet_of_isOpen hd] at h
    by_cases hp : dot p (uvec d.t) < d.h
    · have hq : ¬ dot q (uvec d.t) < d.h := fun hq => h (iff_of_true hp hq)
      rw [abs_of_neg (by linarith), abs_of_nonpos (by linarith)]; linarith
    · have hq : dot q (uvec d.t) < d.h := by
        by_contra hq; exact h (iff_of_false hp hq)
      rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]; linarith

/-- For a line not parallel to `l(t, ·)`, the parameters `r` at which membership of `rot t (s, r)`
and `rot t (s', r)` in the half-plane differ lie in a ball of radius `O(|s - s'|)`. -/
private lemma nef_not_iff_subset_ball {t : ℝ} (d : HalfPlaneData)
    (ha : dot (vvec t) (uvec d.t) ≠ 0) (s s' : ℝ) :
    {r : ℝ | ¬(rot t (s, r) ∈ d.toSet ↔ rot t (s', r) ∈ d.toSet)} ⊆
      Metric.closedBall ((d.h - s * dot (uvec t) (uvec d.t)) / dot (vvec t) (uvec d.t))
        (|dot (uvec t) (uvec d.t) / dot (vvec t) (uvec d.t)| * |s - s'|) := by
  intro r hr
  set a := dot (vvec t) (uvec d.t)
  set b := dot (uvec t) (uvec d.t)
  have h1 := nef_abs_le_of_not_iff d hr
  rw [nef_dot_rot_pair, nef_dot_rot_pair] at h1
  have h2 : |s * b + r * a - d.h| ≤ |b| * |s - s'| := by
    calc |s * b + r * a - d.h| ≤ |s * b + r * a - (s' * b + r * a)| := h1
      _ = |b| * |s - s'| := by rw [show s * b + r * a - (s' * b + r * a) = b * (s - s') by ring,
          abs_mul]
  rw [Metric.mem_closedBall, Real.dist_eq]
  rw [abs_div, div_mul_eq_mul_div, le_div_iff₀ (abs_pos.2 ha), ← abs_mul]
  calc |(r - (d.h - s * b) / a) * a| = |s * b + r * a - d.h| := by
        congr 1; field_simp; ring
    _ ≤ |b| * |s - s'| := h2

/-- The slices of `Y` along the lines `l(t_i, s)` vary Lipschitz-continuously (in measure) for `s`
near `h_i`. -/
private lemma nef_slice_lipschitz {n : ℕ} (E : BoolFun n) (H : Fin n → HalfPlaneData) (i : Fin n)
    (hH : Pairwise (fun i j => (H i).boundary ≠ (H j).boundary)) :
    ∃ ρ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |s - (H i).h| < ρ →
      volume {r | rot (H i).t (s, r) ∈ nefY E (fun j => (H j).toSet) i} ≤
          volume {r | rot (H i).t ((H i).h, r) ∈ nefY E (fun j => (H j).toSet) i} +
            ENNReal.ofReal (M * |s - (H i).h|) ∧
      volume {r | rot (H i).t ((H i).h, r) ∈ nefY E (fun j => (H j).toSet) i} ≤
          volume {r | rot (H i).t (s, r) ∈ nefY E (fun j => (H j).toSet) i} +
            ENNReal.ofReal (M * |s - (H i).h|) := by
  set t := (H i).t with ht
  set h := (H i).h with hh
  set S : Fin n → Set (ℝ × ℝ) := fun j => (H j).toSet with hS
  set a : Fin n → ℝ := fun j => dot (vvec t) (uvec (H j).t) with ha
  set b : Fin n → ℝ := fun j => dot (uvec t) (uvec (H j).t) with hb
  set M : ℝ := ∑ j, 2 * |b j / a j| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => by positivity
  -- near `h`, the lines parallel to `l(t, h)` do not separate `rot t (s, r)` from `rot t (h, r)`
  have hpar : ∀ᶠ s in 𝓝 h, ∀ j, j ≠ i → a j = 0 →
      ∀ r, (rot t (s, r) ∈ S j ↔ rot t (h, r) ∈ S j) := by
    rw [eventually_all]
    intro j
    by_cases hj : j ≠ i ∧ a j = 0
    · filter_upwards [nef_eventually_parallel (H j) hj.2 (hH hj.1)] with s hs _ _ using hs
    · exact Eventually.of_forall fun s h1 h2 => absurd ⟨h1, h2⟩ hj
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1 hpar
  refine ⟨ρ, hρ, M, hM0, fun s hs => ?_⟩
  have hsρ := hρ' (y := s) (by rwa [Real.dist_eq])
  set D : Fin n → Set ℝ := fun j => {r | ¬(rot t (s, r) ∈ S j ↔ rot t (h, r) ∈ S j)} with hD
  set Y := nefY E S i with hY
  -- the symmetric difference of the slices lies in the union of the `D j`, `j ≠ i`
  have hsub : ∀ r, ¬(rot t (s, r) ∈ Y ↔ rot t (h, r) ∈ Y) →
      r ∈ ⋃ j ∈ Finset.univ.erase i, D j := by
    intro r hr
    by_contra hcon
    simp only [mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true, hD, mem_ofPred_eq,
      not_exists, not_not] at hcon
    apply hr
    have hvec : ∀ c : Bool, Function.update (nefVec S (rot t (s, r))) i c =
        Function.update (nefVec S (rot t (h, r))) i c := by
      intro c
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        simp only [nefVec]
        exact decide_eq_decide.2 (hcon j hj)
    simp only [hY, nefY, mem_ofPred_eq, hvec]
  -- for a line `l_j` not parallel to `l(t, h)`, `D j` lies in an interval of length
  -- `2 |b_j / a_j| |s - h|`
  have hDj : ∀ j ∈ Finset.univ.erase i,
      volume (D j) ≤ ENNReal.ofReal (2 * |b j / a j| * |s - h|) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    by_cases haj : a j = 0
    · have : D j = ∅ := by
        ext r; simp only [hD, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
        exact hsρ j hji haj r
      rw [this, measure_empty]; exact zero_le
    · calc volume (D j) ≤ volume (Metric.closedBall (((H j).h - s * b j) / a j)
            (|b j / a j| * |s - h|)) := measure_mono (nef_not_iff_subset_ball (H j) haj s h)
        _ = ENNReal.ofReal (2 * |b j / a j| * |s - h|) := by
          rw [Real.volume_closedBall]; ring_nf
  have hU : volume (⋃ j ∈ Finset.univ.erase i, D j) ≤ ENNReal.ofReal (M * |s - h|) := by
    calc volume (⋃ j ∈ Finset.univ.erase i, D j)
        ≤ ∑ j ∈ Finset.univ.erase i, volume (D j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (2 * |b j / a j| * |s - h|) :=
          Finset.sum_le_sum hDj
      _ = ENNReal.ofReal (∑ j ∈ Finset.univ.erase i, 2 * |b j / a j| * |s - h|) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm
      _ ≤ ENNReal.ofReal (M * |s - h|) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hM, Finset.sum_mul]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun j _ _ => by positivity
  -- each slice lies in the other one together with `⋃ D j`
  have hle : ∀ A B : Set ℝ, (∀ r ∈ A, r ∉ B → r ∈ ⋃ j ∈ Finset.univ.erase i, D j) →
      volume A ≤ volume B + ENNReal.ofReal (M * |s - h|) := fun A B hAB =>
    (measure_mono fun r hr => (em (r ∈ B)).imp_right (hAB r hr)).trans
      ((measure_union_le _ _).trans (by gcongr))
  exact ⟨hle _ _ fun r hr hr' => hsub r fun hiff => hr' (hiff.1 hr),
    hle _ _ fun r hr hr' => hsub r fun hiff => hr' (hiff.2 hr)⟩

/-- A line `l(t_j, c_j)` different from `l(t, h)` meets it in at most one point. -/
private lemma nef_subsingleton_line_inter {t h : ℝ} (d : HalfPlaneData)
    (hne : d.boundary ≠ line t h) :
    {r : ℝ | dot (rot t (h, r)) (uvec d.t) = d.h}.Subsingleton := by
  intro r₁ hr₁ r₂ hr₂
  simp only [mem_ofPred_eq, nef_dot_rot_pair] at hr₁ hr₂
  by_cases ha : dot (vvec t) (uvec d.t) = 0
  · exact absurd (by rw [ha, mul_zero, add_zero] at hr₁; exact hr₁.symm)
      (nef_parallel_ne ha hne)
  · have : (r₁ - r₂) * dot (vvec t) (uvec d.t) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact absurd h' ha

/-- The slice of the boundary of a simple Nef polygon along the `i`-th line agrees with the slice of
`Y`, up to finitely many points. -/
private lemma nef_volume_frontier_slice {n : ℕ} {E : BoolFun n} (hE : E.IsMonotone)
    (H : Fin n → HalfPlaneData) (i : Fin n)
    (hH : Pairwise (fun i j => (H i).boundary ≠ (H j).boundary)) :
    volume {r : ℝ | (H i).h • uvec (H i).t + r • vvec (H i).t ∈
        frontier (nefPolygon E (fun j => (H j).toSet))} =
      volume {r | rot (H i).t ((H i).h, r) ∈ nefY E (fun j => (H j).toSet) i} := by
  set t := (H i).t with ht
  set h := (H i).h with hh
  set Z : Set ℝ := ⋃ j ∈ Finset.univ.erase i, {r : ℝ | dot (rot t (h, r)) (uvec (H j).t) = (H j).h}
    with hZ
  have hZ0 : volume Z = 0 := by
    refine (measure_biUnion_null_iff (Finset.univ.erase i).countable_toSet).2 fun j hj => ?_
    exact (nef_subsingleton_line_inter (H j) (hH (Finset.ne_of_mem_erase hj))).measure_zero _
  have hkey : ∀ r, r ∉ Z → ((H i).h • uvec (H i).t + r • vvec (H i).t ∈
      frontier (nefPolygon E (fun j => (H j).toSet)) ↔
        rot t (h, r) ∈ nefY E (fun j => (H j).toSet) i) := by
    intro r hr
    rw [← rot_pair]
    refine nef_mem_frontier_iff_mem_nefY hE H i (dot_rot_uvec_eq_fst _ _) fun j hj => ?_
    intro hcon
    apply hr
    simp only [hZ, mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true, mem_ofPred_eq]
    exact ⟨j, hj, hcon⟩
  refine measure_congr (ae_eq_set.2 ⟨measure_mono_null (fun r hr => ?_) hZ0,
    measure_mono_null (fun r hr => ?_) hZ0⟩)
  · by_contra hrZ
    exact hr.2 ((hkey r hrZ).1 hr.1)
  · by_contra hrZ
    exact hr.2 ((hkey r hrZ).2 hr.1)

/-- The slice of a bounded set along a line has finite length. -/
private lemma nef_volume_slice_lt_top {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B) (t c : ℝ) :
    volume {r : ℝ | c • uvec t + r • vvec t ∈ B} < ⊤ := by
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  refine lt_of_le_of_lt (measure_mono fun r hr => ?_)
    (measure_Icc_lt_top (a := -(2 * R)) (b := 2 * R))
  have hq := hR hr
  rw [mem_closedBall_zero_iff] at hq
  set q := c • uvec t + r • vvec t
  have hr' : dot q (vvec t) = r := by
    simp only [q, dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self]; ring
  have h1 : |q.1| ≤ R := (Real.norm_eq_abs q.1 ▸ norm_fst_le q).trans hq
  have h2 : |q.2| ≤ R := (Real.norm_eq_abs q.2 ▸ norm_snd_le q).trans hq
  have hs := abs_le.1 (abs_sin_le_one t)
  have hc := abs_le.1 (abs_cos_le_one t)
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [← hr']
  simp only [dot, vvec]
  constructor <;> nlinarith

/-- Cavalieri's principle in the frame `(u_t, v_t)`, for the part of `Y` in a strip. -/
private lemma nef_volume_inter_strip (t : ℝ) {Y : Set (ℝ × ℝ)} (hY : MeasurableSet Y) {I : Set ℝ}
    (hI : MeasurableSet I) :
    volume (Y ∩ {p | dot p (uvec t) ∈ I}) = ∫⁻ s in I, volume {r | rot t (s, r) ∈ Y} := by
  have hm : MeasurableSet (Y ∩ {p | dot p (uvec t) ∈ I}) :=
    hY.inter (measurableSet_preimage (continuous_dot _).measurable hI)
  rw [nef_volume_eq_lintegral t hm, ← lintegral_indicator hI]
  congr 1; funext s
  by_cases hs : s ∈ I
  · rw [indicator_of_mem hs]; congr 1; ext r
    simp only [mem_inter_iff, mem_ofPred_eq, dot_rot_uvec_eq_fst, hs, and_true]
  · rw [indicator_of_notMem hs]
    convert measure_empty (μ := (volume : Measure ℝ))
    ext r
    simp only [mem_inter_iff, mem_ofPred_eq, dot_rot_uvec_eq_fst, hs, and_false,
      mem_empty_iff_false]

/-- Pushing a half-plane from the offset `h` to the offset `h' ≥ h` (same normal angle `t`, same
openness) enlarges it by a strip `{p : p · u_t ∈ I}` of width `h' - h`. -/
private lemma nef_toSet_diff {d d' : HalfPlaneData} {t : ℝ} (ht : d.t = t) (ht' : d'.t = t)
    (ho : d'.isOpen = d.isOpen) (hh : d.h ≤ d'.h) :
    d.toSet ⊆ d'.toSet ∧ ∃ I : Set ℝ, MeasurableSet I ∧ volume I = ENNReal.ofReal (d'.h - d.h) ∧
      I ⊆ Icc d.h d'.h ∧ d'.toSet \ d.toSet = {p | dot p (uvec t) ∈ I} := by
  subst ht
  cases hd : d.isOpen
  · have hd' := ho.trans hd
    refine ⟨fun p hp => ?_, Ioc d.h d'.h, measurableSet_Ioc, Real.volume_Ioc, Ioc_subset_Icc_self,
      ?_⟩
    · rw [nef_mem_toSet_of_not_isOpen hd] at hp
      rw [nef_mem_toSet_of_not_isOpen hd', ht']
      linarith
    · ext p
      rw [Set.mem_sdiff, nef_mem_toSet_of_not_isOpen hd', nef_mem_toSet_of_not_isOpen hd, ht',
        mem_ofPred_eq, mem_Ioc, not_le]
      tauto
  · have hd' := ho.trans hd
    refine ⟨fun p hp => ?_, Ico d.h d'.h, measurableSet_Ico, Real.volume_Ico, Ico_subset_Icc_self,
      ?_⟩
    · rw [nef_mem_toSet_of_isOpen hd] at hp
      rw [nef_mem_toSet_of_isOpen hd', ht']
      linarith
    · ext p
      rw [Set.mem_sdiff, nef_mem_toSet_of_isOpen hd', nef_mem_toSet_of_isOpen hd, ht',
        mem_ofPred_eq, mem_Ico, not_lt]
      tauto

/-- If `g` is within `M d` of `g₀` on a set `I` of length `d`, then `∫_I g = g₀ d + O(M d²)`. -/
private lemma nef_lintegral_estimate {g : ℝ → ℝ≥0∞} {g₀ : ℝ≥0∞} (hg₀ : g₀ ≠ ⊤) {I : Set ℝ}
    (hI : MeasurableSet I) {d M : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M) (hvol : volume I = ENNReal.ofReal d)
    (hup : ∀ s ∈ I, g s ≤ g₀ + ENNReal.ofReal (M * d))
    (hlow : ∀ s ∈ I, g₀ ≤ g s + ENNReal.ofReal (M * d)) :
    (∫⁻ s in I, g s) ≠ ⊤ ∧ |(∫⁻ s in I, g s).toReal - g₀.toReal * d| ≤ M * d ^ 2 := by
  have hU : (∫⁻ s in I, g s) ≤ (g₀ + ENNReal.ofReal (M * d)) * ENNReal.ofReal d := by
    calc (∫⁻ s in I, g s) ≤ ∫⁻ _ in I, (g₀ + ENNReal.ofReal (M * d)) :=
          setLIntegral_mono measurable_const hup
      _ = _ := by rw [setLIntegral_const, hvol]
  have hL : g₀ * ENNReal.ofReal d ≤
      (∫⁻ s in I, g s) + ENNReal.ofReal (M * d) * ENNReal.ofReal d := by
    calc g₀ * ENNReal.ofReal d = ∫⁻ _ in I, g₀ := by rw [setLIntegral_const, hvol]
      _ ≤ ∫⁻ s in I, (g s + ENNReal.ofReal (M * d)) := setLIntegral_mono' hI hlow
      _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const, hvol]
  have hfin : (g₀ + ENNReal.ofReal (M * d)) * ENNReal.ofReal d ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hg₀, ENNReal.ofReal_ne_top⟩) ENNReal.ofReal_ne_top
  have hV : (∫⁻ s in I, g s) ≠ ⊤ := ne_top_of_le_ne_top hfin hU
  refine ⟨hV, ?_⟩
  have hU' := ENNReal.toReal_mono hfin hU
  have hL' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hV, ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩) hL
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hg₀ ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hd, ENNReal.toReal_ofReal (mul_nonneg hM hd)] at hU'
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hV (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top), ENNReal.toReal_mul, ENNReal.toReal_ofReal hd,
    ENNReal.toReal_ofReal (mul_nonneg hM hd)] at hL'
  rw [abs_le]
  constructor <;> nlinarith

/-- If `X₂` is `X₁` together with the part of `Y` in a strip `{p : p · u_t ∈ I}` of width `d`,
and the lengths `g(s)` of the slices of `Y` along the lines `l(t, s)`, `s ∈ I`, are within `M d`
of `g₀`, then `|X₂| - |X₁| = g₀ d + O(M d²)`. -/
private lemma nef_area_add_strip {X₁ X₂ Y : Set (ℝ × ℝ)} {t d M : ℝ} {g₀ : ℝ≥0∞} {I : Set ℝ}
    (hX₁ : volume X₁ ≠ ⊤) (hY : MeasurableSet Y) (hI : MeasurableSet I) (hd : 0 ≤ d)
    (hM : 0 ≤ M) (hvol : volume I = ENNReal.ofReal d) (hg₀ : g₀ ≠ ⊤)
    (hup : ∀ s ∈ I, volume {r | rot t (s, r) ∈ Y} ≤ g₀ + ENNReal.ofReal (M * d))
    (hlow : ∀ s ∈ I, g₀ ≤ volume {r | rot t (s, r) ∈ Y} + ENNReal.ofReal (M * d))
    (hX₂ : X₂ = X₁ ∪ (Y ∩ {p | dot p (uvec t) ∈ I}))
    (hdisj : Disjoint X₁ (Y ∩ {p | dot p (uvec t) ∈ I})) :
    |area X₂ - area X₁ - g₀.toReal * d| ≤ M * d ^ 2 := by
  have hm : MeasurableSet (Y ∩ {p | dot p (uvec t) ∈ I}) :=
    hY.inter (measurableSet_preimage (continuous_dot _).measurable hI)
  obtain ⟨hfin, hest⟩ := nef_lintegral_estimate hg₀ hI hd hM hvol hup hlow
  rw [area, area, hX₂, measure_union hdisj hm, nef_volume_inter_strip t hY hI,
    ENNReal.toReal_add hX₁ hfin, add_sub_cancel_left]
  exact hest

/-- **Theorem 3.1.2** (`thm:simple-nef-polygon`). Pushing the `i`-th defining half-plane of a
bounded simple Nef polygon `X` by `δ` changes its area by `𝓗¹(∂X ∩ l_i) δ + O_{X,i}(δ²)`. The
paper's statement leaves the boundedness of `X` (finiteness of its area) implicit. -/
theorem theorem3_1_2 {n : ℕ} {X : Set (ℝ × ℝ)} {E : BoolFun n} {H : Fin n → HalfPlaneData}
    (hX : IsSimpleNefPolygon X E H) (hb : Bornology.IsBounded X) (i : Fin n) :
    ∃ ε > 0, ∃ C : ℝ, ∀ δ : ℝ, |δ| ≤ ε →
      |area (nefPolygon E (Function.update (fun j => (H j).toSet) i ((H i).shift δ).toSet)) -
          area X - lineLength (H i).t (H i).h (frontier X) * δ| ≤ C * δ ^ 2 := by
  obtain ⟨hE, hH, rfl⟩ := hX
  have hSm : ∀ j, MeasurableSet ((fun j => (H j).toSet) j) := fun j => nef_measurableSet_toSet (H j)
  have hYm : MeasurableSet (nefY E (fun j => (H j).toSet) i) := nef_measurableSet_nefY E hSm i
  have hXfin : volume (nefPolygon E (fun j => (H j).toSet)) ≠ ⊤ := hb.measure_lt_top.ne
  -- the length `g(s)` of the slice of `Y` along `l(t_i, s)`; `g(h_i) = 𝓗¹(∂X ∩ l_i)` is finite
  have hfr := nef_volume_frontier_slice hE H i hH
  set Y := nefY E (fun j => (H j).toSet) i with hY
  set g : ℝ → ℝ≥0∞ := fun s => volume {r | rot (H i).t (s, r) ∈ Y} with hg
  have hg0 : g (H i).h ≠ ⊤ := by
    have := (nef_volume_slice_lt_top (hb.closure.subset frontier_subset_closure) (H i).t
      (H i).h).ne
    rwa [hfr] at this
  have hL : lineLength (H i).t (H i).h (frontier (nefPolygon E (fun j => (H j).toSet))) =
      (g (H i).h).toReal := by
    rw [lineLength, hfr]
  -- `g` is Lipschitz near `h_i`
  obtain ⟨ρ, hρ, M, hM, hlip⟩ := nef_slice_lipschitz E H i hH
  refine ⟨ρ / 2, by positivity, M, fun δ hδ => ?_⟩
  rw [hL]
  have hbound : ∀ s, |s - (H i).h| ≤ |δ| →
      g s ≤ g (H i).h + ENNReal.ofReal (M * |δ|) ∧ g (H i).h ≤ g s + ENNReal.ofReal (M * |δ|) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hlip s (lt_of_le_of_lt hs (by linarith))
    have hmono : ENNReal.ofReal (M * |s - (H i).h|) ≤ ENNReal.ofReal (M * |δ|) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs hM)
    exact ⟨h1.trans (by gcongr), h2.trans (by gcongr)⟩
  rcases le_or_gt 0 δ with hδ0 | hδ0
  · -- `δ ≥ 0`: the polygon gains the part of `Y` in a strip of width `δ`
    obtain ⟨hTsub, I, hIm, hIvol, hIsub, hIeq⟩ :=
      nef_toSet_diff (d := H i) (d' := (H i).shift δ) (t := (H i).t) rfl rfl rfl
        (by simp [HalfPlaneData.shift, hδ0])
    simp only [HalfPlaneData.shift, add_sub_cancel_left] at hIvol hIsub
    rw [abs_of_nonneg hδ0] at hbound
    have hI : ∀ s ∈ I, |s - (H i).h| ≤ δ := fun s hs =>
      abs_sub_le_iff.2 ⟨by linarith [(hIsub hs).2], by linarith [(hIsub hs).1]⟩
    refine nef_area_add_strip hXfin hYm hIm hδ0 hM hIvol hg0 (fun s hs => (hbound s (hI s hs)).1)
      (fun s hs => (hbound s (hI s hs)).2) ?_ ?_
    · rw [nef_update_eq_union hE (fun j => (H j).toSet) i hTsub, hIeq]
    · rw [← hIeq]; exact nef_disjoint_Y _ i _
  · -- `δ < 0`: the polygon loses the part of `Y` in a strip of width `-δ`
    obtain ⟨hTsub, I, hIm, hIvol, hIsub, hIeq⟩ :=
      nef_toSet_diff (d := (H i).shift δ) (d' := H i) (t := (H i).t) rfl rfl rfl
        (by simp [HalfPlaneData.shift, hδ0.le])
    simp only [HalfPlaneData.shift, sub_add_cancel_left] at hIvol hIsub
    rw [abs_of_neg hδ0] at hbound
    have hI : ∀ s ∈ I, |s - (H i).h| ≤ -δ := fun s hs =>
      abs_sub_le_iff.2 ⟨by linarith [(hIsub hs).2], by linarith [(hIsub hs).1]⟩
    have heq := nef_eq_update_union hE (fun j => (H j).toSet) i hTsub
    have hX'fin : volume (nefPolygon E (Function.update (fun j => (H j).toSet) i
        ((H i).shift δ).toSet)) ≠ ⊤ :=
      ne_top_of_le_ne_top hXfin (measure_mono (heq ▸ subset_union_left))
    have := nef_area_add_strip (X₂ := nefPolygon E fun j => (H j).toSet) hX'fin hYm hIm
      (neg_nonneg.2 hδ0.le) hM hIvol hg0
      (fun s hs => (hbound s (hI s hs)).1) (fun s hs => (hbound s (hI s hs)).2)
      (by rw [heq, hIeq]) (by rw [← hIeq]; exact nef_disjoint_Y' _ i _)
    rw [← abs_neg, ← neg_sq]
    convert this using 2
    ring

end NefAux

end MovingSofaOptimality
