module

public import MovingSofaOptimality.Main

/-!
# Rigid maps, and the recovery of a set from its area

A `Rigid` map of `ℝ × ℝ` is a rotation about the origin followed by a translation; it preserves
volume. A closed set contained in a regular closed set `G` of finite measure, with the same measure,
is `G` itself (`Rigid.recover`): this is the last step of the uniqueness theorem. A moving sofa lies
in a horizontal strip of height one, so a rigid image of it has width at most one in the image of
the vertical direction (`snd_sub_le_one_of_isMovingSofa`, `dot_sub_vvec_le_one_of_mem_image`); this
shows that no rotation is needed (`cor:translate` of the manuscript `docs/paper`).
-/

@[expose] public section
noncomputable section

/-!
## A closed subset of full measure

Let `μ` be a measure that is positive on nonempty open sets. A closed set `s` with
`μ (t \ s) = 0` contains the interior of `t`, hence the closure of that interior; so if `s ⊆ t` and
`t` is regular closed, then `s = t` (`eq_of_subset_of_null_sdiff`). When `μ t` is finite, equal
measures give `μ (t \ s) = 0` (`eq_of_subset_of_measure_eq`). This is the last step of the proof of
the theorem in note 20.
-/

section

open Set MeasureTheory

namespace MovingSofaUniqueness

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable {μ : Measure X} [Measure.IsOpenPosMeasure μ]
variable {s t : Set X}

/-- A closed set `s` with `μ (t \ s) = 0` contains the interior of `t`: otherwise the nonempty
open set `interior t \ s` would have measure zero. -/
theorem interior_subset_of_null_sdiff (hs : IsClosed s) (hnull : μ (t \ s) = 0) :
    interior t ⊆ s := by
  intro x hx
  by_contra hxs
  have hopen : IsOpen (interior t \ s) := isOpen_interior.inter hs.isOpen_compl
  exact hopen.measure_ne_zero μ ⟨x, hx, hxs⟩
    (measure_mono_null (Set.sdiff_subset_sdiff_left interior_subset) hnull)

/-- A closed subset `s` of a regular closed set `t` with `μ (t \ s) = 0` is `t`. -/
theorem eq_of_subset_of_null_sdiff (hs : IsClosed s) (hst : s ⊆ t)
    (ht : closure (interior t) = t) (hnull : μ (t \ s) = 0) : s = t := by
  refine Set.Subset.antisymm hst ?_
  rw [← ht]
  exact closure_minimal (interior_subset_of_null_sdiff hs hnull) hs

/-- A closed subset `s` of a regular closed set `t` with `μ s = μ t < ∞` is `t`. -/
theorem eq_of_subset_of_measure_eq [OpensMeasurableSpace X]
    (hs : IsClosed s) (hst : s ⊆ t) (ht : closure (interior t) = t)
    (htfin : μ t ≠ ⊤) (hvol : μ s = μ t) : s = t := by
  refine eq_of_subset_of_null_sdiff (μ := μ) hs hst ht ?_
  rw [measure_sdiff hst hs.measurableSet.nullMeasurableSet (hvol ▸ htfin), hvol, tsub_self]

end MovingSofaUniqueness

end

/-!
## Rigid maps of the plane

The norm of `ℝ × ℝ` is the sup norm, so a rigid map is represented by its angle and its shift: a
`Rigid` map is the rotation `rot angle` about the origin followed by the translation by `shift`.
Rigid maps compose (`Rigid.trans`), have inverses (`Rigid.symm`) and preserve Lebesgue measure
(`Rigid.volume_image`). `Rigid.recover` concludes `g '' s = G` from `g '' s ⊆ G` and
`volume s = volume G`, for a closed set `s` and a regular closed set `G` of finite measure.
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The plane `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ

/-- An orientation-preserving rigid map of the plane: the rotation by `angle` about the origin,
followed by the translation by `shift`. -/
structure Rigid where
  angle : ℝ
  shift : Plane

/-- The rigid map `p ↦ rot angle p + shift`. -/
def Rigid.apply (g : Rigid) (p : Plane) : Plane :=
  rot g.angle p + g.shift

instance : CoeFun Rigid (fun _ => Plane → Plane) := ⟨Rigid.apply⟩

/-- The translation by `v`. -/
def Rigid.translate (v : Plane) : Rigid := ⟨0, v⟩
/-- The rotation by `a` about the origin. -/
def Rigid.rotate (a : ℝ) : Rigid := ⟨a, 0⟩

/-- The rigid map that applies `g`, then `h`, in the order of `Equiv.trans`. -/
def Rigid.trans (g h : Rigid) : Rigid :=
  ⟨h.angle + g.angle, rot h.angle g.shift + h.shift⟩

/-- The inverse of a rigid map. -/
def Rigid.symm (g : Rigid) : Rigid :=
  ⟨-g.angle, -rot (-g.angle) g.shift⟩

@[simp] theorem Rigid.translate_apply (v p : Plane) : Rigid.translate v p = p + v := by
  simp [Rigid.translate, Rigid.apply]

@[simp] theorem Rigid.rotate_apply (a : ℝ) (p : Plane) : Rigid.rotate a p = rot a p := by
  simp [Rigid.rotate, Rigid.apply]

@[simp] theorem Rigid.trans_apply (g h : Rigid) (p : Plane) : (g.trans h) p = h (g p) := by
  simp only [Rigid.trans, Rigid.apply, rot_add, rot_add_vec]
  abel

@[simp] theorem Rigid.symm_apply_apply (g : Rigid) (p : Plane) : g.symm (g p) = p := by
  simp [Rigid.symm, Rigid.apply, rot_add_vec, rot_neg_rot]

@[simp] theorem Rigid.apply_symm_apply (g : Rigid) (p : Plane) : g (g.symm p) = p := by
  have hneg : rot g.angle (-rot (-g.angle) g.shift) = -g.shift := by
    rw [← neg_one_smul ℝ, rot_smul, rot_rot_neg, neg_one_smul]
  simp only [Rigid.symm, Rigid.apply, rot_add_vec, rot_rot_neg, hneg]
  abel

theorem Rigid.continuous (g : Rigid) : Continuous g :=
  (continuous_rot g.angle).add continuous_const

@[simp] theorem Rigid.trans_image (g h : Rigid) (s : Set Plane) :
    (g.trans h) '' s = h '' (g '' s) := by
  rw [Set.image_image]
  simp

/-- The translation by `v` is the map `p ↦ p + v`. -/
theorem Rigid.coe_translate (v : Plane) : (Rigid.translate v : Plane → Plane) = fun p => p + v :=
  funext (Rigid.translate_apply v)

/-- The rotation by `a` is the map `rot a`. -/
theorem Rigid.coe_rotate (a : ℝ) : (Rigid.rotate a : Plane → Plane) = rot a :=
  funext (Rigid.rotate_apply a)

/-- `p` lies in the translate of `s` by `v` if and only if `p - v` lies in `s`. -/
theorem Rigid.mem_translate_image {v p : Plane} {s : Set Plane} :
    p ∈ Rigid.translate v '' s ↔ p - v ∈ s := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨p - v, hp, by simp⟩

/-- A rigid map with angle zero is the translation by its shift. -/
theorem Rigid.eq_translate_of_angle_eq_zero {g : Rigid} (h : g.angle = 0) :
    g = Rigid.translate g.shift := by
  obtain ⟨a, v⟩ := g
  dsimp only at h
  subst h
  rfl

/-- A rigid map maps closed sets to closed sets: its image is the preimage under its inverse. -/
theorem Rigid.isClosed_image (g : Rigid) {s : Set Plane} (hs : IsClosed s) :
    IsClosed (g '' s) := by
  rw [Set.image_eq_preimage_of_inverse g.symm_apply_apply g.apply_symm_apply]
  exact hs.preimage g.symm.continuous

/-- A rigid map preserves Lebesgue measure: rotations have determinant one, and translations
preserve the measure. -/
@[simp] theorem Rigid.volume_image (g : Rigid) (s : Set Plane) :
    volume (g '' s) = volume s := by
  have he : g '' s = (fun p => p + g.shift) '' (rot g.angle '' s) := by
    rw [Set.image_image]
    rfl
  rw [he, Set.image_add_right, volume_preimage_add, volume_image_rot]

@[simp] theorem Rigid.area_image (g : Rigid) (s : Set Plane) : area (g '' s) = area s := by
  rw [area, area, g.volume_image]

/-- If `g '' s ⊆ G` for a closed set `s` and a regular closed set `G` of finite volume, and
`volume s = volume G`, then `g '' s = G`. -/
theorem Rigid.recover (g : Rigid) {s G : Set Plane} (hs : IsClosed s)
    (hsub : g '' s ⊆ G) (hreg : closure (interior G) = G)
    (hfin : volume G ≠ ⊤) (hvol : volume s = volume G) : g '' s = G :=
  eq_of_subset_of_measure_eq (g.isClosed_image hs) hsub hreg hfin (by simpa using hvol)

/-! ## A moving sofa lies in a horizontal strip of height one -/

/-- A moving sofa lies in a horizontal strip of height one: its translate at the start of its
movement lies in the horizontal side `H_L = (-∞, 1] × [0, 1]` of the hallway. -/
theorem snd_sub_le_one_of_isMovingSofa {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) {p q : Plane} (hp : p ∈ S) (hq : q ∈ S) :
    p.2 - q.2 ≤ 1 := by
  obtain ⟨ω, -, -, θ, c, hm⟩ := hS
  have hp' := hm.start p hp
  have hq' := hm.start q hq
  rw [hm.angle_zero, rot_zero] at hp' hq'
  obtain ⟨-, -, hp1⟩ := hp'
  obtain ⟨-, hq0, -⟩ := hq'
  simp only [Prod.snd_add] at hp1 hq0
  linarith

/-- If a rigid map `g` of angle `θ` takes a moving sofa `S` onto a set containing `x` and `y`, then
`(x - y) · v_θ ≤ 1`: the image of `S` has width at most one in the direction
`v_θ = u_{θ + π/2}`, the image of the vertical direction under `R_θ`. -/
theorem dot_sub_vvec_le_one_of_mem_image {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (g : Rigid) {x y : Plane} (hx : x ∈ g '' S)
    (hy : y ∈ g '' S) : dot (x - y) (vvec g.angle) ≤ 1 := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  have he : g p - g q = rot g.angle (p - q) := by
    change rot g.angle p + g.shift - (rot g.angle q + g.shift) = rot g.angle (p - q)
    ext <;> simp only [rot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [he, dot_rot_vvec_eq_snd, Prod.snd_sub]
  exact snd_sub_le_one_of_isMovingSofa hS hp hq

end MovingSofaUniqueness

end

/-!
## Caps with horizontally translated supports

A right-angle cap is the set of points `p` with `0 ≤ p.2` and `dot p (uvec t) ≤ h_K(t)` for
`t ∈ [0, π]` (`mem_right_cap_iff`), and its niche is also described by its supports
(`mem_right_niche_iff`). So if `h_K(t) - h_G(t) = a cos t` on `[0, π]`, translation by `(a, 0)` maps
`G` onto `K` (`cap_eq_translate_of_upper_support`) and the niche of `G` onto that of `K`, and `K`
minus its niche is the translate of `G` minus its niche (`sofa_eq_translate_of_upper_support`):
equation (21) of note 20, and `lem:translate` of the manuscript `docs/paper`. Conversely, a horizontal
translate of a right-angle cap is a right-angle cap (`isCap_translate_horizontal`) whose niche is the
translated niche (`niche_translate_horizontal`), so it has the same sofa area
(`sofaArea_translate_horizontal`) and its sofa is the translated sofa (`cap_minus_niche_translate`).
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- A point lies in a right-angle cap if and only if it lies above the floor and below the
supporting lines at the normals in `[0, π]`. -/
theorem mem_right_cap_iff {K : Set Plane} (hK : IsCap K (π / 2)) (p : Plane) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  constructor
  · intro hp
    exact ⟨(inj_cap_strip hK hp).1,
      fun t _ => dot_le_supp hK.2.1.2.1 hp t⟩
  · rintro ⟨hfloor, hupper⟩
    obtain ⟨hω, hbody, hωtop, htop, hωfloor, hbottom, hplanes⟩ := hK
    rw [nef_eq_setOf_supp hbody hplanes]
    intro t ht
    simp only [jSet, mem_union, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with (ht | ht) | ht | ht
    · exact hupper t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
    · exact hupper t ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    · have he : t = 3 * π / 2 := by linarith
      rw [he, hbottom, uvec_three_pi_div_two]
      simpa [dot] using hfloor
    · rw [ht, hbottom, uvec_three_pi_div_two]
      simpa [dot] using hfloor

/-- A point lies in the niche of a right-angle cap if and only if it lies above the floor and in
the open inner quadrant of some `t ∈ (0, π/2)`. -/
theorem mem_right_niche_iff (K : Set Plane) (p : Plane) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2),
      dot p (uvec t) < supp K t - 1 ∧
      dot p (vvec t) < supp K (t + π / 2) - 1 := by
  have hf : p ∈ fan (π / 2) ↔ 0 ≤ p.2 := by
    simp [fan, halfPlus, uvec_pi_div_two, dot]
  change (p ∈ fan (π / 2) ∧ p ∈ ⋃ t ∈ Ioo (0 : ℝ) (π / 2), qMinus K t) ↔ _
  rw [hf]
  simp only [mem_iUnion, exists_prop, ms_mem_qMinus_iff]

private theorem dot_sub_horizontal_u (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (uvec t) = dot p (uvec t) - a * cos t := by
  simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

private theorem dot_sub_horizontal_v (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (vvec t) = dot p (vvec t) + a * sin t := by
  simp only [dot, vvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

/-- If `h_K(t) - h_G(t) = a cos t` on `[0, π]`, then `p ∈ K` if and only if `p - (a, 0) ∈ G`. -/
theorem mem_cap_sub_horizontal_iff {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ K ↔ p - (a, 0) ∈ G := by
  rw [mem_right_cap_iff hK, mem_right_cap_iff hG]
  simp only [Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨hp, hu⟩
    refine ⟨hp, fun t ht => ?_⟩
    rw [dot_sub_horizontal_u]
    linarith [hu t ht, hsupp t ht]
  · rintro ⟨hp, hu⟩
    refine ⟨hp, fun t ht => ?_⟩
    have hi := hu t ht
    rw [dot_sub_horizontal_u] at hi
    linarith [hsupp t ht]

/-- Under the same support identity, `p` lies in the niche of `K` if and only if `p - (a, 0)` lies
in the niche of `G`. -/
theorem mem_niche_sub_horizontal_iff {K G : Set Plane} (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ niche K (π / 2) ↔ p - (a, 0) ∈ niche G (π / 2) := by
  rw [mem_right_niche_iff, mem_right_niche_iff]
  simp only [Prod.snd_sub, sub_zero]
  have hbounds : ∀ t ∈ Ioo (0 : ℝ) (π / 2),
      supp K t - supp G t = a * cos t ∧
        supp K (t + π / 2) - supp G (t + π / 2) = -a * sin t := by
    intro t ht
    refine ⟨hsupp t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩, ?_⟩
    have h := hsupp (t + π / 2)
      ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    simpa [cos_add_pi_div_two, mul_neg, neg_mul] using h
  constructor
  · rintro ⟨hp, t, ht, hu, hv⟩
    refine ⟨hp, t, ht, ?_, ?_⟩
    · rw [dot_sub_horizontal_u]
      linarith [(hbounds t ht).1]
    · rw [dot_sub_horizontal_v]
      linarith [(hbounds t ht).2]
  · rintro ⟨hp, t, ht, hu, hv⟩
    rw [dot_sub_horizontal_u] at hu
    rw [dot_sub_horizontal_v] at hv
    exact ⟨hp, t, ht, by linarith [(hbounds t ht).1],
      by linarith [(hbounds t ht).2]⟩

/-- Equation (21) of note 20: if `h_K(t) - h_G(t) = a cos t` on `[0, π]`, then `K` minus its niche
is the translate by `(a, 0)` of `G` minus its niche. -/
theorem sofa_eq_translate_of_upper_support {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t) :
    K \ niche K (π / 2) = Rigid.translate (a, 0) '' (G \ niche G (π / 2)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p - (a, 0), ⟨(mem_cap_sub_horizontal_iff hK hG a hsupp p).mp hp.1,
      fun hn => hp.2 ((mem_niche_sub_horizontal_iff a hsupp p).mpr hn)⟩, ?_⟩
    simp
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(mem_cap_sub_horizontal_iff hK hG a hsupp _).mpr (by simpa using hq.1), ?_⟩
    intro hn
    have hqN := (mem_niche_sub_horizontal_iff a hsupp _).mp hn
    exact hq.2 (by simpa using hqN)

/-- `lem:translate` of the manuscript `docs/paper`, for the caps: if
`h_K(t) - h_G(t) = a cos t` on `[0, π]` for two right-angle caps, then `K = G + (a, 0)`. With
`mem_niche_sub_horizontal_iff` and `sofa_eq_translate_of_upper_support`, this is part (a) of the lemma. -/
theorem cap_eq_translate_of_upper_support {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t) :
    K = Rigid.translate (a, 0) '' G := by
  ext p
  rw [Rigid.mem_translate_image]
  exact mem_cap_sub_horizontal_iff hK hG a hsupp p

/-- Translating a convex body by `(a, 0)` adds `a cos t` to its support function:
`h_{G + (a, 0)}(t) - h_G(t) = a cos t`. -/
theorem supp_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a t : ℝ) :
    supp (Rigid.translate (a, 0) '' G) t - supp G t = a * cos t := by
  rw [Rigid.coe_translate, supp_translate G _ t hG.2.1 hG.1]
  simp only [dot, uvec]
  ring

/-- A horizontal translate `G + (a, 0)` of a right-angle cap `G` is a right-angle cap: the
translation keeps the support values at the normals `π/2` and `3π/2`, where `cos t = 0`, and the
normal angles of the half-planes. -/
theorem isCap_translate_horizontal {G : Set Plane} (hG : IsCap G (π / 2)) (a : ℝ) :
    IsCap (Rigid.translate (a, 0) '' G) (π / 2) := by
  obtain ⟨hω, hbody, htop, htop', hfloor, hfloor', hplanes⟩ := hG
  have hs : ∀ t, cos t = 0 → supp (Rigid.translate (a, 0) '' G) t = supp G t := by
    intro t ht
    have h := supp_translate_horizontal hbody a t
    rwa [ht, mul_zero, sub_eq_zero] at h
  have hc₁ : cos (π / 2) = 0 := cos_pi_div_two
  have hc₂ : cos (π / 2 + π) = 0 := by rw [cos_add_pi, hc₁, neg_zero]
  have hc₃ : cos (3 * π / 2) = 0 := by rw [show 3 * π / 2 = π / 2 + π by ring, hc₂]
  refine ⟨hω, ?_, (hs _ hc₁).trans htop, (hs _ hc₁).trans htop', (hs _ hc₂).trans hfloor,
    (hs _ hc₃).trans hfloor', ?_⟩
  · rw [Rigid.coe_translate]
    exact nef_isConvexBody_translate hbody _
  · rw [Rigid.coe_translate]
    exact nef_isHalfPlaneInter_translate hplanes _

/-- The niche of `G + (a, 0)` is the niche of `G` translated by `(a, 0)`. -/
theorem niche_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    niche (Rigid.translate (a, 0) '' G) (π / 2) = Rigid.translate (a, 0) '' niche G (π / 2) := by
  ext p
  rw [Rigid.mem_translate_image]
  exact mem_niche_sub_horizontal_iff a (fun t _ => supp_translate_horizontal hG a t) p

/-- A horizontal translation preserves the sofa area: `𝒜_{π/2}(G + (a, 0)) = 𝒜_{π/2}(G)`, since
it translates the niche and preserves areas. -/
theorem sofaArea_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    sofaArea (π / 2) (Rigid.translate (a, 0) '' G) = sofaArea (π / 2) G := by
  unfold sofaArea
  rw [niche_translate_horizontal hG, Rigid.area_image, Rigid.area_image]

/-- The sofa of a horizontal translate of a convex body is the translate of its sofa. -/
theorem cap_minus_niche_translate {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    (Rigid.translate (a, 0) '' G) \ niche (Rigid.translate (a, 0) '' G) (π / 2) =
      Rigid.translate (a, 0) '' (G \ niche G (π / 2)) := by
  rw [niche_translate_horizontal hG a]
  have hinj : Function.Injective (Rigid.translate (a, 0)) := by
    intro p q heq
    have h : p + (a, 0) = q + (a, 0) := by
      simpa only [Rigid.translate_apply] using heq
    exact add_right_cancel h
  exact (image_sdiff hinj _ _).symm

end MovingSofaUniqueness

end
