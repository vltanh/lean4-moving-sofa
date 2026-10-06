module

public import MovingSofaExtremal.Geometry
public import MovingSofaExtremal.HorizontalTranslation
public import MovingSofaExtremal.CoerciveRigidity
public import MovingSofaExtremal.Optimality
public import MovingSofaExtremal.Uniqueness

/-!
# The coercive extremal route

Intended proof-source entry points:

* MovingSofaExtremal.right_angle_maximizer_certificate
* MovingSofaExtremal.right_angle_maximizer_eq_gerver
* MovingSofaExtremal.gerver_sofa_optimal
* MovingSofaExtremal.image_eq_gerver_of_volume_eq
* MovingSofaExtremal.gerver_sofa_optimal_and_unique

The quantitative input is the lower cap-distance layer. GlobalStability and
QualitativeEntry are deliberately absent, preventing use of the original
uniqueness theorem through the global stability argument.

The faithful Baek library, the original uniqueness proof, and the historical
MaximizerRoute remain unchanged. SolutionCoercive separately transports the
new conclusions through the unchanged bridge to the Challenge's statements.

All additions are uncompiled proof source. No Lean or CI has been run, and no
audit success or kernel verification is claimed.
-/
