module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import MovingSofaBridge.Motion
public import MovingSofaUniqueness.RegularClosed
public import MovingSofaStability.CapEstimate
public import MovingSofaStability.Margins

/-!
# Punctured sofas: the exponent one half is optimal

Removing an open disk of small radius `r` from the interior of Gerver's sofa `G` leaves a moving
sofa that has lost the area `π r²` and lies at distance exactly `r` from the rigid copies of `G`
(`punctured_gerver_family`). So no bound `C εᵃ` with `a > 1/2` on the distance from a moving sofa
of deficit `ε` to the rigid copies of `G` holds (`no_hausdorff_exponent_gt_half`,
`rigid_distance_not_higher_order`).
-/

@[expose] public section
noncomputable section

open Real Set Metric MeasureTheory Filter Topology
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-!
## Removing a disk

Let `S` be a closed connected set that contains the closed Euclidean disk of center `p` and radius
`r > 0`. Removing the open disk leaves a closed set, connected as the circle is connected
(`puncture_connected`), `r`-close to `S` (`puncture_euclideanClose`), of area `|S| - π r²` if `S` is
compact (`puncture_area_loss`), and moved by every movement of `S` (`puncture_movingWithAngle`).
-/

/-- Removing from a closed preconnected set `S` an open set `U` with `closure U ⊆ S` and connected
frontier leaves a connected set: if closed sets `A ⊇ frontier U` and `B` separate `S \ U`, then
`(S \ U ∩ A) ∪ closure U` and `S \ U ∩ B` separate `S`. -/
theorem connected_sdiff_of_connected_frontier {X : Type*} [TopologicalSpace X] {S U : Set X}
    (hS : IsClosed S) (hconn : IsPreconnected S) (hU : IsOpen U) (hcl : closure U ⊆ S)
    (hF : IsConnected (frontier U)) : IsConnected (S \ U) := by
  rw [hU.frontier_eq] at hF
  have hFY : closure U \ U ⊆ S \ U := sdiff_subset_sdiff_left hcl
  refine ⟨hF.nonempty.mono hFY, isPreconnected_iff_subset_of_disjoint_closed.2
    fun A B hA hB hcover hdisj => ?_⟩
  -- the connected set `closure U \ U` lies in `A` or in `B`, say in `A`
  wlog hFA : closure U \ U ⊆ A generalizing A B
  · have hFB := (isPreconnected_iff_subset_of_disjoint_closed.1 hF.isPreconnected A B hA hB
      (hFY.trans hcover) (subset_empty_iff.1 fun x hx => hdisj.subset ⟨hFY hx.1, hx.2⟩))
    exact (this B A hB hA (by rwa [union_comm]) (by rwa [inter_comm B A])
      (hFB.resolve_left hFA)).symm
  have hY : IsClosed (S \ U) := hS.sdiff hU
  refine (isPreconnected_iff_subset_of_disjoint_closed.1 hconn ((S \ U ∩ A) ∪ closure U)
      (S \ U ∩ B) ((hY.inter hA).union isClosed_closure) (hY.inter hB) ?_ ?_).imp
    (fun h x hx => (h hx.1).elim (·.2) fun hxU => hFA ⟨hxU, hx.2⟩) fun h x hx => (h hx.1).2
  · intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl (Or.inr (subset_closure hxU))
    · exact (hcover ⟨hx, hxU⟩).imp (fun hA => Or.inl ⟨⟨hx, hxU⟩, hA⟩) fun hB => ⟨⟨hx, hxU⟩, hB⟩
  · refine subset_empty_iff.1 fun x ⟨_, hxA, hxY, hxB⟩ => hdisj.subset ⟨hxY, ?_, hxB⟩
    exact hxA.elim (·.2) fun hxU => hFA ⟨hxU, hxY.2⟩

/-- The coordinates of `MovingSofaBridge` as a homeomorphism from the Euclidean plane. -/
def diskCoordinates : EuclideanSpace ℝ (Fin 2) ≃ₜ Point where
  toFun := MovingSofaBridge.coordinates
  invFun := MovingSofaBridge.point
  left_inv := MovingSofaBridge.point_coordinates
  right_inv := MovingSofaBridge.coordinates_point
  continuous_toFun := MovingSofaBridge.coordinates_continuous
  continuous_invFun := MovingSofaBridge.point_continuous

/-- An open Euclidean disk; `euclideanBall` is the closed one. -/
def openEuclideanBall (p : Point) (r : ℝ) : Set Point :=
  {q | euclideanDist p q < r}

/-- The set `S` with the open Euclidean disk of center `p` and radius `r` removed. -/
def puncture (S : Set Point) (p : Point) (r : ℝ) : Set Point :=
  S \ openEuclideanBall p r

/-- The coordinates turn the distance of the Euclidean plane into `euclideanDist`. -/
theorem dist_diskCoordinates_symm (p q : Point) :
    dist (diskCoordinates.symm q) (diskCoordinates.symm p) = euclideanDist p q := by
  change dist (MovingSofaBridge.point q) (MovingSofaBridge.point p) = _
  rw [euclideanDist_comm]
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, euclideanDist, norm2, dot,
    MovingSofaBridge.point, Real.dist_eq, sq]

/-- The open Euclidean disk is the preimage of a ball of the Euclidean plane. -/
theorem openEuclideanBall_eq (p : Point) (r : ℝ) :
    openEuclideanBall p r = diskCoordinates.symm ⁻¹' ball (diskCoordinates.symm p) r := by
  ext q
  show euclideanDist p q < r ↔ _
  rw [mem_preimage, mem_ball, dist_diskCoordinates_symm]

/-- The open Euclidean disk is open. -/
theorem isOpen_openEuclideanBall (p : Point) (r : ℝ) : IsOpen (openEuclideanBall p r) := by
  rw [openEuclideanBall_eq]
  exact isOpen_ball.preimage diskCoordinates.symm.continuous

/-- The open Euclidean disk of radius `r` has area `π r²`. -/
theorem area_openEuclideanBall (p : Point) {r : ℝ} (hr : 0 ≤ r) :
    area (openEuclideanBall p r) = π * r ^ 2 := by
  rw [openEuclideanBall_eq, Homeomorph.preimage_symm]
  change (volume (MovingSofaBridge.coordinates '' _)).toReal = _
  rw [MovingSofaBridge.volume_coordinates_image, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal pi_pos.le, mul_comm]

/-- The puncture of a closed connected set that contains the closed disk is connected, as the
circle, the frontier of the open disk, is connected. -/
theorem puncture_connected {S : Set Point} (hS : IsClosed S) (hconn : IsConnected S)
    {p : Point} {r : ℝ} (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    IsConnected (puncture S p r) := by
  refine connected_sdiff_of_connected_frontier hS hconn.isPreconnected
    (isOpen_openEuclideanBall p r) ?_ ?_
  · rw [openEuclideanBall_eq, ← Homeomorph.preimage_closure, closure_ball _ hr.ne']
    exact fun q hq => hball ((dist_diskCoordinates_symm p q).symm.trans_le hq)
  · rw [openEuclideanBall_eq, ← Homeomorph.preimage_frontier, frontier_ball _ hr.ne',
      Homeomorph.isConnected_preimage]
    exact isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ hr.le

/-- The puncture of a compact set has lost the area `π r²` of the disk. -/
theorem puncture_area_loss {S : Set Point} (hS : IsCompact S)
    {p : Point} {r : ℝ} (hr : 0 ≤ r) (hball : euclideanBall p r ⊆ S) :
    area S - area (puncture S p r) = π * r ^ 2 := by
  have h := area_inter_add_sdiff (isOpen_openEuclideanBall p r).measurableSet
    hS.isBounded.measure_lt_top.ne
  have hsub : openEuclideanBall p r ⊆ S := fun q (hq : euclideanDist p q < r) => hball hq.le
  rw [inter_eq_right.2 hsub, area_openEuclideanBall p hr] at h
  rw [puncture]
  linarith

/-- A set and its puncture are `r`-close: a point `x` of the open disk lies within `r` of the
point of the circle on the ray from `p` through `x`. -/
theorem puncture_euclideanClose {S : Set Point} {p : Point} {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    EuclideanClose r (puncture S p r) S := by
  refine ⟨fun x hx => ⟨x, hx.1, (euclideanDist_self x).trans_le hr.le⟩, fun x hx => ?_⟩
  by_cases hin : x ∈ openEuclideanBall p r
  swap
  · exact ⟨x, ⟨hx, hin⟩, (euclideanDist_self x).trans_le hr.le⟩
  suffices ∃ q, euclideanDist p q = r ∧ euclideanDist x q ≤ r by
    obtain ⟨q, hq, hd⟩ := this
    exact ⟨q, ⟨hball hq.le, hq.not_lt⟩, hd⟩
  rcases eq_or_ne x p with rfl | hxp
  · have h : euclideanDist x (x + (r, 0)) = r := by
      simp [euclideanDist, norm2, dot, sqrt_mul_self hr.le]
    exact ⟨x + (r, 0), h, h.le⟩
  set n := euclideanDist p x
  have hn : 0 < n := (euclideanDist_nonneg p x).lt_of_ne (by simpa [n, eq_comm] using hxp)
  have hxpn : norm2 (x - p) = n := euclideanDist_comm x p
  refine ⟨p + (r / n) • (x - p), ?_, ?_⟩
  · change norm2 (p - (p + (r / n) • (x - p))) = r
    rw [sub_add_cancel_left, norm2_neg, norm2_smul, hxpn, abs_of_pos (by positivity),
      div_mul_cancel₀ _ hn.ne']
  · change norm2 (x - (p + (r / n) • (x - p))) ≤ r
    rw [show x - (p + (r / n) • (x - p)) = (1 - r / n) • (x - p) by module, norm2_smul, hxpn,
      abs_of_nonpos (sub_nonpos.2 ((one_le_div hn).2 (show n < r from hin).le)), neg_sub,
      sub_mul, div_mul_cancel₀ _ hn.ne']
    linarith

/-- A movement of `S` moves the closed connected subset `puncture S p r`. -/
theorem puncture_movingWithAngle {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω) {p : Point} {r : ℝ} (hr : 0 < r)
    (hball : euclideanBall p r ⊆ S) : IsMovingSofaWithAngle (puncture S p r) ω := by
  obtain ⟨hSc, hSconn, θ, c, hm⟩ := hS
  exact ⟨hSc.sdiff (isOpen_openEuclideanBall p r), puncture_connected hSc hSconn hr hball, θ, c,
    { hm with
      start := fun q hq => hm.start q hq.1
      inside := fun t ht q hq => hm.inside t ht q hq.1
      finish := fun q hq => hm.finish q hq.1 }⟩

/-!
## Rigid copies keep interior points

An interior point of a compact set `X` lies in every rigid copy of `X` close enough to `X`
(`rigid_copies_retain_interior`), by compactness of the coefficients of the rigid maps.
-/

/-- The coefficients `((cos θ, sin θ), v)` of the rigid map `x ↦ R_θ x + v`. -/
def rotationShift (g : Rigid) : Point × Point := ((cos g.angle, sin g.angle), g.shift)

/-- The inverse `x ↦ R_{-θ} (x - v)` of a rigid map, as a function of its coefficients
`z = ((cos θ, sin θ), v)`. -/
def coefficientInverse (z : Point × Point) (p : Point) : Point :=
  (z.1.1 * (p.1 - z.2.1) + z.1.2 * (p.2 - z.2.2),
    -z.1.2 * (p.1 - z.2.1) + z.1.1 * (p.2 - z.2.2))

/-- At the coefficients of a rigid map `g`, `coefficientInverse` is the inverse of `g`. -/
@[simp] theorem coefficientInverse_rotationShift (g : Rigid) (p : Point) :
    coefficientInverse (rotationShift g) p = g.symm p := by
  ext <;> simp only [coefficientInverse, rotationShift, Rigid.symm, Rigid.apply,
    rot, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, cos_neg, sin_neg] <;> ring

/-- An interior point `p` of a compact set `X` lies in every rigid copy `g(X)` that is `δ`-close
to `X` with `δ < η`, for some `η > 0`. Otherwise rigid maps `gₙ x = R_{θₙ} x + vₙ` with `δₙ → 0`
and `p ∉ gₙ(X)` have a subsequence with `(cos θₙ, sin θₙ, vₙ) → (cos θ, sin θ, v)`; the limit
`g x = R_θ x + v` has `g⁻¹(X) ⊆ X`, so `X` is a neighborhood of `g⁻¹ p`, and `p ∈ gₙ(X)` for
large `n`. -/
theorem rigid_copies_retain_interior {X : Set Point} (hX : IsCompact X)
    {p : Point} (hp : p ∈ interior X) :
    ∃ η : ℝ, 0 < η ∧ ∀ g : Rigid, ∀ δ : ℝ,
      δ < η → EuclideanClose δ X (g '' X) → p ∈ g '' X := by
  by_contra! hnot
  choose g δ hsmall hclose hout using fun n : ℕ => hnot (1 / ((n : ℝ) + 1)) (by positivity)
  -- the shifts are bounded: `vₙ = (gₙ p - q) + q - R_{θₙ} p` with `q ∈ X` within `δₙ ≤ 1` of `gₙ p`
  obtain ⟨R, hR⟩ := hX.isBounded.exists_norm_le
  have hpX := interior_subset hp
  have hshift (n : ℕ) : ‖(g n).shift‖ ≤ 3 * R + 1 := by
    obtain ⟨q, hq, hd⟩ := (hclose n).2 (g n p) (mem_image_of_mem _ hpX)
    have h₁ : ‖g n p - q‖ ≤ 1 := (product_norm_le_norm2 _).trans (hd.trans
      ((hsmall n).le.trans (div_le_one_of_le₀ (by simp) (by positivity))))
    have h₂ : ‖rot (g n).angle p‖ ≤ 2 * R := (product_norm_le_norm2 _).trans (by
      rw [norm2_rot]
      exact (norm2_le_two_product_norm p).trans (by linarith [hR p hpX]))
    calc ‖(g n).shift‖ = ‖(g n p - q) + q - rot (g n).angle p‖ := by
          rw [Rigid.apply]
          abel_nf
      _ ≤ ‖g n p - q‖ + ‖q‖ + ‖rot (g n).angle p‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 3 * R + 1 := by linarith [hR q hq]
  have hB : IsCompact ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ closedBall (0 : Point) (3 * R + 1)) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  obtain ⟨⟨⟨c, s⟩, v⟩, -, σ, hσ, hz⟩ := hB.tendsto_subseq (x := fun n => rotationShift (g n))
    fun n => ⟨⟨⟨neg_one_le_cos _, cos_le_one _⟩, neg_one_le_sin _, sin_le_one _⟩,
      mem_closedBall_zero_iff.2 (hshift n)⟩
  -- the limit is the coefficient vector of a rigid map `F`
  have hunit : c ^ 2 + s ^ 2 = 1 :=
    (isClosed_eq (f := fun z : Point × Point => z.1.1 ^ 2 + z.1.2 ^ 2) (by fun_prop)
      continuous_const).mem_of_tendsto hz (Eventually.of_forall fun n => cos_sq_add_sin_sq _)
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).1 (show ‖(⟨c, s⟩ : ℂ)‖ = 1 by
    rw [Complex.norm_def, Complex.normSq_mk, ← sq, ← sq, hunit, sqrt_one])
  obtain ⟨rfl, rfl⟩ : cos θ = c ∧ sin θ = s :=
    ⟨by simpa using congrArg Complex.re hθ, by simpa using congrArg Complex.im hθ⟩
  let F : Rigid := ⟨θ, v⟩
  have hlim (x : Point) : Tendsto (fun n => (g (σ n)).symm x) atTop (𝓝 (F.symm x)) := by
    have hc : Continuous fun z => coefficientInverse z x := by
      unfold coefficientInverse
      fun_prop
    simpa only [Function.comp_def, coefficientInverse_rotationShift] using
      (hc.tendsto (rotationShift F)).comp hz
  -- `F⁻¹ x` is the limit of points of `X` within `δₙ` of `gₙ⁻¹ x`, so `F⁻¹(X) ⊆ X`
  have hFX (x : Point) (hx : x ∈ X) : F.symm x ∈ X := by
    have hnear (n : ℕ) : ∃ q ∈ X, euclideanDist ((g n).symm x) q ≤ δ n := by
      obtain ⟨_, ⟨q, hq, rfl⟩, hd⟩ := (hclose n).1 x hx
      exact ⟨q, hq, by rwa [← euclideanDist_rigid (g n), Rigid.apply_symm_apply]⟩
    choose q hqX hqd using hnear
    refine hX.isClosed.mem_of_tendsto ((hlim x).congr_dist (squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop)))
      (Eventually.of_forall fun n => hqX (σ n))
    exact (dist_eq_norm _ _).trans_le
      ((product_norm_le_norm2 _).trans ((hqd (σ n)).trans (hsmall (σ n)).le))
  -- so `X` is a neighborhood of `F⁻¹ p`, and `gₙ⁻¹ p ∈ X` for large `n`
  have hnhds : X ∈ 𝓝 (F.symm p) :=
    mem_of_superset ((isOpen_interior.preimage F.continuous).mem_nhds (by simpa using hp))
      fun y hy => by simpa using hFX _ (interior_subset hy)
  obtain ⟨n, hn⟩ := ((hlim p).eventually hnhds).exists
  exact hout (σ n) ⟨_, hn, Rigid.apply_symm_apply _ p⟩

/-!
## Punctured Gerver sofas

Removing a disk of small radius `r` around an interior point of Gerver's sofa costs the area `π r²`
and moves the sofa away from all rigid copies of Gerver's sofa by exactly `r`
(`punctured_gerver_family`). As `C (π r²)ᵃ < r` for small `r` when `a > 1/2`
(`exists_puncture_scale`), no exponent above one half bounds the distance by a power of the
deficit.
-/

/-- The distance from `S` to the rigid copies of `T`: the infimum of the radii `d ≥ 0` for which
`S` and `g(T)` are `d`-close for some orientation-preserving rigid map `g`. -/
def rigidHausdorffDistance (S T : Set Point) : ℝ :=
  sInf {d : ℝ | 0 ≤ d ∧ ∃ g : Rigid, EuclideanClose d S (g '' T)}

/-- For an interior point `p` of Gerver's sofa `G` and every small `r > 0`, the puncture `G_r` of
`G` at the open disk of center `p` and radius `r` is a moving sofa of deficit `π r²`; it is
`r`-close to `G`, and `d`-close to no rigid copy of `G` with `d < r`, so its distance to the rigid
copies of `G` is `r`. -/
theorem punctured_gerver_family {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ p : Point, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      IsMovingSofa (puncture (gerverSofa P) p r) ∧
      sofaDeficit P (puncture (gerverSofa P) p r) = π * r ^ 2 ∧
      EuclideanClose r (puncture (gerverSofa P) p r) (gerverSofa P) ∧
      (∀ g : Rigid, ∀ d : ℝ,
        EuclideanClose d (puncture (gerverSofa P) p r) (g '' gerverSofa P) → r ≤ d) ∧
      rigidHausdorffDistance (puncture (gerverSofa P) p r) (gerverSofa P) = r := by
  have hG := (GerverParams.gm_movingSofa_std hP hbox).1
  have hGc : IsCompact (gerverSofa P) := isCompact_of_isMovingSofa ⟨π / 2, hG⟩
  -- `G` is the closure of its interior, so it has an interior point `p`
  obtain ⟨p, hp⟩ : (interior (gerverSofa P)).Nonempty := by
    rw [← closure_nonempty_iff, gerver_regularClosed hP hbox]
    exact hG.2.1.nonempty
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
  obtain ⟨η, hη, hret⟩ := rigid_copies_retain_interior hGc hp
  refine ⟨p, min (R / 2) (η / 3), lt_min (by positivity) (by positivity), fun r hr hrsmall => ?_⟩
  have hrR : r < R / 2 := hrsmall.trans_le (min_le_left _ _)
  have hrη : r < η / 3 := hrsmall.trans_le (min_le_right _ _)
  have hball : euclideanBall p r ⊆ gerverSofa P := fun q (hq : euclideanDist p q ≤ r) =>
    hRball <| mem_ball.2 <| calc
      dist q p = ‖p - q‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ euclideanDist p q := product_norm_le_norm2 _
      _ < R := by linarith
  have hclose := puncture_euclideanClose hr hball
  -- if `G_r` and `g(G)` are `d`-close with `d < r`, then `G` and `g(G)` are `(r + d)`-close, so
  -- `p ∈ g(G)`, and `p` lies within `d < r` of a point of `G_r`, which is false
  have hmin (g : Rigid) (d : ℝ)
      (hd : EuclideanClose d (puncture (gerverSofa P) p r) (g '' gerverSofa P)) : r ≤ d := by
    by_contra! hdr
    obtain ⟨q, hq, hpq⟩ := hd.2 p (hret g (r + d) (by linarith) (hclose.symm.trans hd))
    exact hq.2 (hpq.trans_lt hdr)
  -- the identity attains `r`
  have hid : ∃ g : Rigid, EuclideanClose r (puncture (gerverSofa P) p r) (g '' gerverSofa P) :=
    ⟨Rigid.translate 0, by simpa only [Rigid.coe_translate, add_zero, image_id'] using hclose⟩
  refine ⟨⟨π / 2, puncture_movingWithAngle hG hr hball⟩, puncture_area_loss hGc hr.le hball,
    hclose, hmin, le_antisymm (csInf_le ⟨0, fun d hd => hd.1⟩ ⟨hr.le, hid⟩) ?_⟩
  exact le_csInf ⟨r, hr.le, hid⟩ fun d ⟨_, g, hg⟩ => hmin g d hg

/-- For `a > 1/2`, arbitrarily small radii `r > 0` have `π r² < ε₀` and `C (π r²)ᵃ < r`, as
`C (π r²)ᵃ = C πᵃ r^(2a - 1) · r` and `r^(2a - 1) → 0`. -/
theorem exists_puncture_scale {a C ε₀ r₀ : ℝ} (ha : 1 / 2 < a)
    (hε₀ : 0 < ε₀) (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ π * r ^ 2 < ε₀ ∧ C * (π * r ^ 2) ^ a < r := by
  have hq : 0 < 2 * a - 1 := by linarith
  have h₁ : ∀ᶠ r in 𝓝 (0 : ℝ), π * r ^ 2 < ε₀ :=
    ((continuous_const.mul (continuous_pow 2)).tendsto' 0 0 (by simp)).eventually_lt_const hε₀
  have h₂ : ∀ᶠ r in 𝓝 (0 : ℝ), C * π ^ a * r ^ (2 * a - 1) < 1 :=
    ((continuous_const.mul (continuous_rpow_const hq.le)).tendsto' 0 0
      (by simp [zero_rpow hq.ne'])).eventually_lt_const one_pos
  have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < r₀ ∧ π * r ^ 2 < ε₀ ∧
      C * π ^ a * r ^ (2 * a - 1) < 1 :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds ((eventually_lt_nhds hr₀).and (h₁.and h₂)))
  obtain ⟨r, hr, hrr₀, harea, hsmall⟩ := h.exists
  refine ⟨r, hr, hrr₀, harea, ?_⟩
  calc C * (π * r ^ 2) ^ a = C * π ^ a * r ^ (2 * a - 1) * r := by
        rw [mul_rpow pi_pos.le (sq_nonneg r), ← rpow_natCast, ← rpow_mul hr.le,
          rpow_sub_one hr.ne', Nat.cast_ofNat]
        field_simp
    _ < 1 * r := mul_lt_mul_of_pos_right hsmall hr
    _ = r := one_mul r

/-- **No exponent above one half.** For `a > 1/2`, every constant `C` and every `ε₀ > 0`, some
moving sofa `S` of deficit `ε ∈ (0, ε₀)` is `C εᵃ`-close to no rigid copy of Gerver's sofa. -/
theorem no_hausdorff_exponent_gt_half {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {a : ℝ} (ha : 1 / 2 < a)
    (C : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ S : Set Point, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      ∀ g : Rigid, ¬EuclideanClose (C * (sofaDeficit P S) ^ a) S (g '' gerverSofa P) := by
  obtain ⟨p, r₀, hr₀, hfamily⟩ := punctured_gerver_family hP hbox
  obtain ⟨r, hr, hrsmall, harea, hpower⟩ := exists_puncture_scale (C := C) ha hε₀ hr₀
  obtain ⟨hmove, hdef, -, hminimal, -⟩ := hfamily r hr hrsmall
  refine ⟨_, hmove, by rw [hdef]; positivity, by rwa [hdef], fun g hclose => ?_⟩
  rw [hdef] at hclose
  exact (hminimal g _ hclose).not_gt hpower

/-- **No exponent above one half**, for the distance to the rigid copies: for `a > 1/2`, every
constant `C` and every `ε₀ > 0`, some moving sofa `S` of deficit `ε ∈ (0, ε₀)` has distance more
than `C εᵃ` from the rigid copies of Gerver's sofa. -/
theorem rigid_distance_not_higher_order {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {a : ℝ} (ha : 1 / 2 < a)
    (C : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ S : Set Point, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      C * (sofaDeficit P S) ^ a < rigidHausdorffDistance S (gerverSofa P) := by
  obtain ⟨p, r₀, hr₀, hfamily⟩ := punctured_gerver_family hP hbox
  obtain ⟨r, hr, hrsmall, harea, hpower⟩ := exists_puncture_scale (C := C) ha hε₀ hr₀
  obtain ⟨hmove, hdef, -, -, hdist⟩ := hfamily r hr hrsmall
  exact ⟨_, hmove, by rw [hdef]; positivity, by rwa [hdef], by rwa [hdef, hdist]⟩

end MovingSofaStability
