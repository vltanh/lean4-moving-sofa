module

public import MovingSofaBridge.Defs
public import MovingSofaExtremal.CertificateDefs
public import MovingSofaStability.CapEstimate

/-!
# The certificate's statements, proved

This module proves the two statements of `Challenge.lean`, the Challenge at the root, about the
certificate, with the definitions of `MovingSofaBridge.Defs` and
`MovingSofaExtremal.CertificateDefs`: `Certificate.coercive_certificate`, from
`MovingSofaStability.coercive_certificate`, and `Certificate.gerver_triple` (Gerver's triple meets
the certificate's hypothesis and attains its bound), from `MovingSofaStability.wideGerverTriple` and
`MovingSofaStability.wideGerver_value`.

The bridge lemmas say that each definition of `MovingSofaExtremal.CertificateDefs` is the library's
definition of the same name (for `gerverCap`, the library's `GerverParams.cap`): by definition,
except the surface area measure `sigma` and the curve area `convexCurveArea` that uses it, which
agree with the library's on convex bodies, and Baek's upper bound `upperQ`, which agrees with the
library's when its two tails are convex bodies. `Solution`, the solution at the root, imports this
module, which imports neither `baek.Solution` nor `MovingSofaUniqueness.Main`;
`scripts/AuditCoerciveRoute.lean` checks that the proofs use neither Baek's Theorem 1.1.1 nor the
first proof of uniqueness.
-/

@[expose] public section

open Real Set MeasureTheory

namespace Certificate

/-! ### Baek's definitions are the library's -/

/-- The library's version of a parameter tuple. -/
def toLib (P : Baek.GerverParams) : MovingSofaOptimality.GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂,
    P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

theorem toLib_isSolution (P : Baek.GerverParams) : (toLib P).IsSolution ↔ P.IsSolution := Iff.rfl

theorem toLib_inBox (P : Baek.GerverParams) : (toLib P).InBox ↔ P.InBox := Iff.rfl

theorem gerverSofa_eq_lib (P : Baek.GerverParams) :
    Baek.gerverSofa P = MovingSofaOptimality.gerverSofa (toLib P) := rfl

/-- The Euclidean distance in the Challenge's vocabulary is the library's. -/
theorem euclideanDist_eq_lib (p q : ℝ × ℝ) :
    Baek.euclideanDist p q = MovingSofaStability.euclideanDist p q := by
  simp only [Baek.euclideanDist, MovingSofaStability.euclideanDist, MovingSofaOptimality.norm2,
    MovingSofaOptimality.dot, Prod.fst_sub, Prod.snd_sub]
  congr 1
  ring

/-- Closeness in the Challenge's vocabulary is the library's. -/
theorem euclideanClose_iff_lib (r : ℝ) (S T : Set (ℝ × ℝ)) :
    Baek.EuclideanClose r S T ↔ MovingSofaStability.EuclideanClose r S T := by
  simp only [Baek.EuclideanClose, MovingSofaStability.EuclideanClose,
    MovingSofaStability.DirectedClose, euclideanDist_eq_lib]

/-! ### The certificate's definitions are the library's -/

theorem cross_eq_lib : cross = MovingSofaOptimality.cross := rfl

theorem line_eq_lib : line = MovingSofaOptimality.line := rfl

theorem halfMinus_eq_lib : halfMinus = MovingSofaOptimality.halfMinus := rfl

theorem isConvexBody_eq_lib : IsConvexBody = MovingSofaOptimality.IsConvexBody := rfl

theorem supp_eq_lib : supp = MovingSofaOptimality.supp := rfl

theorem suppLine_eq_lib : suppLine = MovingSofaOptimality.suppLine := rfl

theorem edge_eq_lib : edge = MovingSofaOptimality.edge := rfl

theorem vplus_eq_lib : vplus = MovingSofaOptimality.vplus := rfl

theorem vminus_eq_lib : vminus = MovingSofaOptimality.vminus := rfl

theorem sigmaFun_eq_lib : sigmaFun = MovingSofaOptimality.sigmaFun := rfl

/-- On convex bodies, the surface area measure is the library's: the distribution function is
monotone and right-continuous, so both are the measure of the same Stieltjes function. -/
theorem sigma_eq_lib {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    sigma K = MovingSofaOptimality.sigma K := by
  have hK' : MovingSofaOptimality.IsConvexBody K := hK
  have h : Monotone (sigmaFun K) ∧ ∀ x, ContinuousWithinAt (sigmaFun K) (Ici x) x :=
    ⟨MovingSofaOptimality.monotone_sigmaFun hK',
      MovingSofaOptimality.continuousWithinAt_sigmaFun hK'⟩
  rw [sigma, dite_eq_left h, MovingSofaOptimality.sigma, MovingSofaOptimality.sigmaStieltjes,
    dite_eq_left hK']
  rfl

theorem isHalfPlaneInter_eq_lib : IsHalfPlaneInter = MovingSofaOptimality.IsHalfPlaneInter := rfl

theorem jSet_eq_lib : jSet = MovingSofaOptimality.jSet := rfl

theorem isCap_eq_lib : IsCap = MovingSofaOptimality.IsCap := rfl

theorem hStrip_eq_lib : hStrip = MovingSofaOptimality.hStrip := rfl

theorem vStrip_eq_lib : vStrip = MovingSofaOptimality.vStrip := rfl

theorem vStripRot_eq_lib : vStripRot = MovingSofaOptimality.vStripRot := rfl

theorem para_eq_lib : para = MovingSofaOptimality.para := rfl

theorem hallwayMap_eq_lib : hallwayMap = MovingSofaOptimality.hallwayMap := rfl

theorem qPlusL_eq_lib : qPlusL = MovingSofaOptimality.qPlusL := rfl

theorem qPlus_eq_lib : qPlus = MovingSofaOptimality.qPlus := rfl

theorem capOf_eq_lib : capOf = MovingSofaOptimality.capOf := rfl

theorem innerCorner_eq_lib : innerCorner = MovingSofaOptimality.innerCorner := rfl

/-- On convex bodies, the curve area of an arc of the boundary is the library's. -/
theorem convexCurveArea_eq_lib {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    convexCurveArea K a b = MovingSofaOptimality.convexCurveArea K a b := by
  rw [convexCurveArea, sigma_eq_lib hK]
  rfl

theorem clampFun_eq_lib {α : Type*} : @clampFun α = @MovingSofaOptimality.clampFun α := rfl

theorem lsMeasure_eq_lib {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] :
    @lsMeasure E _ _ = @MovingSofaOptimality.lsMeasure E _ _ := rfl

theorem crossCLM_eq_lib : crossCLM = MovingSofaOptimality.crossCLM := rfl

theorem curveBilin_eq_lib : curveBilin = MovingSofaOptimality.curveBilin := rfl

theorem curveArea_eq_lib : curveArea = MovingSofaOptimality.curveArea := rfl

theorem segArea_eq_lib : segArea = MovingSofaOptimality.segArea := rfl

theorem xB_eq_lib : xB = MovingSofaOptimality.xB := rfl

theorem yD_eq_lib : yD = MovingSofaOptimality.yD := rfl

theorem xRight_eq_lib : xRight = MovingSofaOptimality.xRight := rfl

theorem xLeft_eq_lib : xLeft = MovingSofaOptimality.xLeft := rfl

/-- When the tails `B` and `D` are convex bodies, Baek's upper bound is the library's. -/
theorem upperQ_eq_lib {φ : ℝ} {K B D : Set (ℝ × ℝ)} (hB : IsConvexBody B)
    (hD : IsConvexBody D) : upperQ φ K B D = MovingSofaOptimality.upperQ φ K B D := by
  rw [upperQ, convexCurveArea_eq_lib hB, convexCurveArea_eq_lib hD]
  rfl

theorem inWideL_eq_lib : InWideL = MovingSofaStability.InWideL := rfl

theorem gerverCap_eq_lib (P : Baek.GerverParams) : gerverCap P = (toLib P).cap := rfl

theorem capReferenceShift_eq_lib :
    capReferenceShift = MovingSofaStability.capReferenceShift := rfl

theorem shiftedReferenceCap_eq_lib :
    shiftedReferenceCap = MovingSofaStability.shiftedReferenceCap := rfl

end Certificate

/-! ### The certificate -/

/-- **The coercive certificate** (Theorem 11.1 of the manuscript). For every triple `(K, B, D)` of
the enlarged domain `T̄`, Baek's upper bound satisfies `𝒬(K, B, D) ≤ |G|`, and the cap `K` and the
translate `K_G + (s_K, 0)` of Gerver's cap with the leftmost abscissa of `K` are
`2 sec φ √(|G| - 𝒬(K, B, D))`-close. -/
theorem Certificate.coercive_certificate (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) (K B D : Set (ℝ × ℝ)) (h : Certificate.InWideL P.φ K B D) :
    Certificate.upperQ P.φ K B D ≤ (volume (Baek.gerverSofa P)).toReal ∧
      Baek.EuclideanClose
        ((2 / cos P.φ) * √((volume (Baek.gerverSofa P)).toReal - Certificate.upperQ P.φ K B D))
        K (Certificate.shiftedReferenceCap (Certificate.gerverCap P) K) := by
  have hw : MovingSofaStability.InWideL (Certificate.toLib P).φ K B D := h
  rw [Certificate.upperQ_eq_lib hw.2.1 hw.2.2.1, Certificate.euclideanClose_iff_lib,
    Certificate.gerverCap_eq_lib, Certificate.shiftedReferenceCap_eq_lib]
  exact MovingSofaStability.coercive_certificate ((Certificate.toLib_isSolution P).2 hP)
    ((Certificate.toLib_inBox P).2 hPb) ⟨(⟨K, hw.1.2.1⟩, ⟨B, hw.2.1⟩, ⟨D, hw.2.2.1⟩), hw⟩

/-- **Gerver's triple.** Gerver's cap `K_G`, with the two tails of Gerver's triple, lies in the
enlarged domain `T̄` and attains `𝒬 = |G|`: the hypothesis of the certificate can be met, and its
bound `𝒬 ≤ |G|` is attained. -/
theorem Certificate.gerver_triple (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ B D : Set (ℝ × ℝ), Certificate.InWideL P.φ (Certificate.gerverCap P) B D ∧
      Certificate.upperQ P.φ (Certificate.gerverCap P) B D =
        (volume (Baek.gerverSofa P)).toReal := by
  have hP' := (Certificate.toLib_isSolution P).2 hP
  have hPb' := (Certificate.toLib_inBox P).2 hPb
  let x := MovingSofaStability.wideGerverTriple hP' hPb'
  have hx : Certificate.InWideL P.φ (Certificate.gerverCap P) x.1.2.1.1 x.1.2.2.1 := x.2
  refine ⟨x.1.2.1.1, x.1.2.2.1, hx, ?_⟩
  rw [Certificate.upperQ_eq_lib hx.2.1 hx.2.2.1]
  exact MovingSofaStability.wideGerver_value hP' hPb'
