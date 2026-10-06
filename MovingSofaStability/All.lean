module

public import MovingSofaStability.Basic
public import MovingSofaStability.WideDomain
public import MovingSofaStability.Deficit
public import MovingSofaStability.CapEstimate
public import MovingSofaStability.Margins
public import MovingSofaStability.LocalGeometry
public import MovingSofaStability.LocalBound
public import MovingSofaStability.Terminal
public import MovingSofaStability.Recovery
public import MovingSofaStability.Global
public import MovingSofaStability.Sharpness

/-!
# The stability of Gerver's sofa

The modules follow the steps of the proof (`docs/stability.md`): the statements (`Basic`); Baek's
upper bound on the enlarged domain of triples and its deficit (`WideDomain`, `Deficit`); the cap
estimate and the coercive certificate (`CapEstimate`); the margins of Gerver's sofa (`Margins`); the
upper bound near Gerver's cap (`LocalGeometry`, `LocalBound`); the cost of a missing final angle
(`Terminal`); from the cap back to the sofa (`Recovery`); compactness, uniqueness and the stability
theorems (`Global`); and the punctured sofas, which show that the exponent one half is optimal
(`Sharpness`).
-/
