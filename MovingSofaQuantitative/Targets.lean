module

public import MovingSofaQuantitative.CapQuotient
public import MovingSofaStability.Sharpness

/-!
# Exact statement contract for the quantitative appendix

These declarations are DEFINITIONS OF PROPOSITIONS, not proofs or axioms.
They specify the types that completed theorem declarations must inhabit.
No target may be marked checked merely because its proposition elaborates.
The statement audit must compare each future proof's type against these values.

All geometric conclusions use the original actual set or an actual convex cap.
The three translation conventions have separate definitions. The final cutoff
is rational 1 / 10^600, not a floating-point literal or a rounded dyadic zero.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative.Targets

/-- The common exact cutoff required by the final appendix proposition. -/
def epsilonStar : ℝ := 1 / (10 : ℝ) ^ (600 : ℕ)

/-- The two actual-set conclusions at the fixed midpoint/top normalization. -/
def SofaConclusions (P : GerverParams) (S : Set Point) : Prop :=
  EuclideanClose ((23 / 10) * sqrt (sofaDeficit P S))
    (midpointNormalizedSofa P S) (gerverSofa P) ∧
  symmetricDifferenceArea (midpointNormalizedSofa P S) (gerverSofa P) ≤
    50 * sqrt (sofaDeficit P S)

/-- The assertion is about every admissible reduced motion, not a selected one. -/
def AngleConclusions (P : GerverParams) (S : Set Point) : Prop :=
  ∀ ω : ℝ, IsMovingSofaWithAngle S ω →
    ω ∈ Icc (arccos (5 / 11 : ℝ)) (π / 2) →
    0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ (31 / 10) * sofaDeficit P S

/-- G.1: actual cap residual energy, after midpoint alignment. -/
def CenteredEnergy : Prop :=
  ∀ φ : ℝ, φ ∈ Ioo 0 (π / 4) → ∀ K₀ K₁ : ConvexBodySet,
    IsCap K₀.1 (π / 2) → IsCap K₁.1 (π / 2) →
    EuclideanClose ((1 / cos φ) * sqrt (capResidualEnergy φ K₀ K₁))
      K₁.1 (centeredReference K₀.1 K₁.1)

/-- G.1: full-Q consequence on the integrated enlarged triple domain. -/
def CenteredCap : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ x : WideTriple P.φ,
    EuclideanClose ((1 / cos P.φ) * sqrt (qDeficit P x))
      x.1.1.1 (centeredReference P.cap x.1.1.1)

/-- G.1: the Ki consequence uses its own area deficit, not a solver objective. -/
def CenteredKi : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ K : Set Point, IsKi K →
    EuclideanClose ((1 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (centeredReference P.cap K)

def CenteredNumeric : Prop :=
  ∀ φ : ℝ, φ ∈ Icc (0.039 : ℝ) 0.04 →
    1 / cos φ ≤ 1250 / 1249 ∧ (1250 / 1249 : ℝ) < 1001 / 1000

/-- Main theorem / G.2: coefficients are fixed, the entry threshold may be existential. -/
def ExplicitLocalStability : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ S : Set Point, IsMovingSofa S →
      sofaDeficit P S < ε₀ → SofaConclusions P S ∧ AngleConclusions P S

/-- G.3: punctures constrain every universal coefficient, even with arbitrary rigid alignment. -/
def SofaCoefficientLower : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ C ε₀ : ℝ, 0 < ε₀ →
    (∀ S : Set Point, IsMovingSofa S → 0 < sofaDeficit P S → sofaDeficit P S < ε₀ →
      ∃ g : Rigid, EuclideanClose (C * sqrt (sofaDeficit P S)) S (g '' gerverSofa P)) →
    1 / sqrt π ≤ C

/-- G.3: sharpness is realized by ACTUAL caps arbitrarily close to Gerver.
This does not assert sharpness for qDeficit or sofaDeficit. -/
def CenteredResidualSharpness : Prop :=
  ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
    ∀ C η : ℝ, C < 1 / cos P.φ → 0 < η →
      ∃ K : ConvexBodySet, IsCap K.1 (π / 2) ∧ EuclideanClose η K.1 P.cap ∧
        0 < capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 K ∧
        C * sqrt (capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 K) <
          capTranslationDistance P.cap K.1

/-- G.4: the zero-first-variation face, with all feasibility constraints retained. -/
def CriticalFaceUpper : Prop :=
  ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
    ∀ x : WideTriple P.φ, wideDualSlack hP hbox x = 0 →
      capTranslationDistance P.cap x.1.1.1 ≤ (93 / 100) * sqrt (qDeficit P x)

/-- G.4: the finite-deficit estimate, with a real exponent 2/3. -/
def FullQFinite : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ x : WideTriple P.φ,
    0 < qDeficit P x → qDeficit P x ≤ 1 / 512 →
      capTranslationDistance P.cap x.1.1.1 ≤
        (93 / 100) * sqrt (qDeficit P x) + 8 * (qDeficit P x) ^ (2 / 3 : ℝ)

def FullQ094 : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ x : WideTriple P.φ,
    0 ≤ qDeficit P x → qDeficit P x ≤ 1 / (10 : ℝ) ^ (18 : ℕ) →
      capTranslationDistance P.cap x.1.1.1 ≤ (94 / 100) * sqrt (qDeficit P x)

/-- A uniform margin is deliberately included. Arbitrarily small examples with
ratio merely >461/500 would not on their own imply strictness of the infimum. -/
def FeasibleCriticalLower : Prop :=
  ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
    ∃ L : ℝ, (461 / 500 : ℝ) < L ∧ ∀ η : ℝ, 0 < η →
      ∃ x : WideTriple P.φ, wideDualSlack hP hbox x = 0 ∧
        0 < qDeficit P x ∧ qDeficit P x < η ∧
        L * sqrt (qDeficit P x) ≤ capTranslationDistance P.cap x.1.1.1

def IntrinsicInterval : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox →
    (461 / 500 : ℝ) < intrinsicQCoefficient P ∧ intrinsicQCoefficient P ≤ 93 / 100

/-- The weak global estimate is an entry theorem, not the sharp local conclusion. -/
def EffectiveEntry : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ S : Set Point,
    IsMovingSofa S → 0 ≤ sofaDeficit P S →
    sofaDeficit P S ≤ 1 / (10 : ℝ) ^ (144 : ℕ) →
    EuclideanClose (3000000 * (sofaDeficit P S) ^ (1 / 12 : ℝ))
      (midpointNormalizedSofa P S) (gerverSofa P)

def EffectiveAngleEntry : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ (S : Set Point) (ω : ℝ),
    IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11 : ℝ)) (π / 2) →
    0 < sofaDeficit P S → sofaDeficit P S ≤ 1 / (10 : ℝ) ^ (30 : ℕ) →
    0 ≤ π / 2 - ω ∧ π / 2 - ω < 500 * (sofaDeficit P S) ^ (1 / 6 : ℝ)

/-- MANDATORY final appendix proposition. There is no already-local hypothesis,
no existential radius, and no replacement of S by an auxiliary maximizing sofa. -/
def ExplicitCutoff : Prop :=
  ∀ (P : GerverParams), P.IsSolution → P.InBox → ∀ S : Set Point,
    IsMovingSofa S → 0 ≤ sofaDeficit P S → sofaDeficit P S ≤ epsilonStar →
    SofaConclusions P S ∧ AngleConclusions P S

end MovingSofaQuantitative.Targets
