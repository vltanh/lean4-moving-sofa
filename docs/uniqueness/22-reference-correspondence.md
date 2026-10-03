# 22. The exact formal-conjectures reference and the paper construction

Date: 2026-10-02. Status: mathematical argument and uncompiled Lean source.

## Result and verification boundary

The new bridge states, for every paper parameter witness P with `P.IsSolution`
and `P.InBox`,

```lean
SofaUniqueness.Bridge.coordinates '' MovingSofa.gerversSofa
  = MovingSofa.gerverSofa P
```

Here the lower-case `gerversSofa` is the literal integral-defined reference
from the inspected formal-conjectures file, not an arbitrary maximizer chosen
by the local proof. Its constants still come from the same full four-equation
existence-and-uniqueness specification. The other `gerverSofa P` is the actual
five-phase construction used in the paper formalization.

The coordinate map is `(p 0, p 1)`. It is a volume-preserving homeomorphism,
not an isometry for the ordinary product norm. The equality above is equality
of sets, not equality almost everywhere or only equality of volume.

Every new step has an explicit Lean proof body. This is NOT a claim that those
bodies elaborate or have been independently checked. No Lean, Lake, CI,
Comparator or independent checker was run. Possible source, API, tactic,
mathematical and version-porting errors remain subject to review. The code and
comparison configuration are not Palomar certification.

## 1. The reference equations are handled on their full domain

Write L = pi/2, delta = theta-phi, and use c=cos(phi), s=sin(phi),
u=cos(theta), v=sin(theta). The upstream domain is

```text
0 <= phi <= theta <= pi/4,    A >= 0, B >= 0.
```

The first and third equations eliminate B, and the fourth reconstructs it:

```text
D = 3c-u > 0,
N = delta*u + 3s-v-u+1,
k = 1+delta/2,
l = L-phi-theta+delta/2+delta^2/4,
A = N/D,    B = k*A+l.
```

These are exact identities in `ReferenceEquations.lean`. In particular the
paper theorem asserting uniqueness only in a small box is not substituted
for the upstream full-domain theorem.

### Analytic localization

The boundary equations exclude phi=0 and phi=theta. The fourth equation gives
B>=A. Combining the first and third equations then gives

```text
3 sin(phi)^2 - cos(phi) sin(phi)
  <= (theta-phi) (cos(phi)-sin(phi)).
```

If phi>=1/2, use theta-phi<=3/10, sin(phi)>=23/48, cos(phi)<=1 to contradict
this inequality. Thus every root has phi<1/2.

For the stronger bound, define

```text
J = c-k*s,
Z = s*(1+l)+(1-c)/2,
Q = N*J-D*Z.
```

The reference third equation is Q=0 after the reconstruction. Its exact
partial derivatives are proved in `ReferenceDifferential.lean`. To show
Q_phi<0, replace l by m=delta/2+delta^2/4 in that derivative. The replacement
increases the derivative on phi<=1/2 because

```text
(-D*c+3*s^2)*(L-phi-theta) <= 0.
```

The resulting derivative q has diagonal value

```text
q(phi,phi)=(s-c)*(1-c+2*s) <= 0,
```

and its theta derivative, multiplied by four, is

```text
-6*delta*(c^2-s^2) + 6*s*(s-c) - 2*c^2 + 4*c*(u-c) - 2*c
  + c*v*(delta^2-2) + 2*s*v*(delta-1) < 0.
```

Each displayed summand is nonpositive on the triangle, and `-2*c` is strictly
negative. This proves the sign analytically.

On the line phi=1/20, the other partial derivative Q_theta is positive;
`ReferencePhiLocalization.lean` proves this with elementary rational bounds,
splitting theta at 1/2. At its upper endpoint theta=pi/4 the bounds

```text
N <= 257/1000, D >= 2286/1000,
0 <= J <= 932/1000, Z >= 111/1000
```

give Q<0. Monotonicity in theta and then phi excludes every root with
phi>=1/20. Hence every full-domain root satisfies

```text
0 < phi < 1/20,    phi < theta <= pi/4.
```

This uses one displayed scalar boundary estimate and signed derivatives,
not a subdivision grid or a recursively evaluated exclusion certificate.

### A separating residual proves uniqueness

After substituting reconstructed A and B, put

```text
C = 1-A-delta,
F = A*c-(B+1)*s+(c-1)/2,
G = -3*C*v+(A-1)*s+(1-2*B)*c+3*u,
H = G+(9/10)*F.
```

F is the third equation and G the second. On the entire localized triangle,
not merely at the roots, `ReferenceSmallBounds.lean` proves

```text
0<=A<=4/25, 7/10<=B<=2, 199/100<=D<=23/10, C>0.
```

For example the numerator bound uses

```text
b(t)=(t-1)cos(t)-sin(t)+1,
b'(t)=(1-t)sin(t)<=t(1-t),
b(t)<=t^2/2-t^3/3<=3/20  for 0<=t<=4/5.
```

The exact derivatives and rational bounds in `ReferenceResiduals.lean` and
`ReferenceDerivativeSigns.lean` give

```text
F_phi <= -2/3,    0 <= F_theta/C <= 1/2,
G_phi <= 3/5,     G_theta/C <= -2/3.
```

Thus F decreases strictly with phi and increases weakly with theta, whereas
H decreases weakly with phi and strictly with theta.

Suppose two zeros had theta<theta'. Then F(phi,theta')>=0. Strict decrease
in phi forces phi<=phi', since F(phi',theta')=0. But strict decrease of H in
theta gives H(phi,theta')<0, and weak decrease in phi gives
H(phi',theta')<=H(phi,theta')<0, a contradiction. Swapping the zeros shows
theta=theta', and strict phi monotonicity gives phi=phi'. Reconstruction gives
equality of A and B. This is `Reference.spec_unique`.

## 2. Existence and the explicit parameter correspondence

For a reference tuple (A,B,phi,theta), define

```text
a1 = ((A+1/2)sin(phi)+(B+1)cos(phi))/2,
b1 = (phi-1-A)/2,
b2 = B-1/2-b1*phi+phi^2/4,
kappa1 = (1-a1,1/4),
kappa2 = kappa1 + R_phi(-B/2,1/4),
kappa3 = kappa2 + R_theta(1/2,(1-A-(theta-phi))/2).
```

The other coefficients and translations are explicit in `Data.toPaper`.
The third and fourth reference equations give derivative matching at phi
and theta. Continuity fixes the translations. Reflection gives the other two
junctions. Before imposing any equation, the first contact error is exactly

```text
x2(phi)-contactB(x4,L-theta) = (-eq2/2,-eq1/2).
```

This proves the two contact conditions directly, without using sofa uniqueness.

Conversely, for a paper solution P, define

```text
A = P.phi-1-2*P.b1,
B = 1/2-P.phi^2/4+P.b1*P.phi+P.b2.
```

The derivative and value junctions reconstruct every coefficient and
translation of P. The contact-error identity then yields the first two
reference equations. The existing paper parameter enclosures establish A,B>=0.
Thus the already constructed paper witness gives existence for the exact
upstream specification. Combining this existence with the independent global
uniqueness argument proves

```lean
Reference.spec_existsUnique :
  ∃! q : ℝ × ℝ × ℝ × ℝ, Spec q.1 q.2.1 q.2.2.1 q.2.2.2
```

Only after proving global uniqueness do we identify an arbitrary reference
solution with the paper witness and deduce that it lies in the paper's box.
There is no circular use of boxed uniqueness to establish global uniqueness.

## 3. Integral boundary coordinates from the actual contact curve

The reference radius r has the paper contact C's curvature density. The
reference chooses left-hand values at the four breakpoints; the convenient
paper right derivative chooses right-hand values. `ReferenceRadius.lean`
proves equality almost everywhere and integrability before invoking FTC.
It does not assume pointwise equality at the breakpoints.

Since C'(t)=-r(t)u_t on the appropriate one-sided formulation,

```text
integral_a^b r(t)cos(t)dt = C(a)_x-C(b)_x,
integral_a^b r(t)sin(t)dt = C(a)_y-C(b)_y.
```

The final contact is `(2*kappa3_x-1,0)`. It follows that the literal reference
integrals X,Y satisfy

```text
C(t) = (2*kappa3_x-X(t),Y(t)),
A(t) = (X(L-t),Y(L-t)).
```

The initial contact gives Y(0)=1, while the second reference equation gives

```text
kappa3_x = 1-4*a1/3,
2*kappa3_x = 4*X(0)-2.
```

These supply the normalizations actually present in upstream's path formula.

## 4. The two path conventions and the exact sets

The contact projection identities are

```text
A(t).u_t = x(t).u_t+1,
C(t).v_t = x(t).v_t+1.
```

Substituting the integral contact coordinates into upstream's literal branch
formulas proves

```text
p(t) = (x(t).u_t,x(t).v_t),
R_t p(t) = x(t).
```

This is the required relationship: upstream translates BEFORE rotating, while
the paper translation x(t) is applied AFTER rotating. The assertion p(t)=x(t)
would be wrong. Also p(0)=0 is proved, so the initial horizontal hallway is not
silently shifted. The final vertical hallway is carried through separately.

`Bridge/ReferenceRotation.lean` checks the sign of the actual canonical
orientation used by `EuclideanGeometry.o.rotation`: the standard oriented
orthonormal basis has area one, its quarter turn sends e0 to e1 and e1 to -e0,
and the rotation therefore has the paper's counterclockwise matrix.
Constructing some other isometry would not have established this fact about
the specified reference.

Transferring each hallway intersection gives the main equality
`coordinates_gerversSofa_eq_paper`. Neither its proof nor its parameter/path
prerequisites import the new sofa shape-uniqueness theorem.

## 5. The exact endpoint is now a corollary over proved reference facts

`MovingSofaUniquenessFC/ReferenceFacts.lean` derives the literal reference's motion
and optimal volume from the correspondence and the existing paper optimality
result. `MovingSofaUniquenessFC/Final.lean` then contains

```lean
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  exact Canonical.volume_eq_constant_iff_congruent hs
    isMovingSofa_gerversSofa sofaConstant_eq_volume_gerversSofa
```

Both reference facts now have local source proofs; the generic theorem's
premises are not left uninstantiated or filled by catalog placeholders.
The competitor's assumptions and the meaning of congruence are unchanged.

## Dependency and submission boundaries

`ReferenceDefs` retains the inspected upstream mathematical definitions and
full parameter domain. `Model` is shared by publication and submission;
ordinary Lean bridges connect it to the paper presentation. No source
relocation, generated insertion fragment, external script or rejected external
reference package is required.

`comparator.reference-uniqueness.json` is configured for the exact target AND
the full parameter theorem, plus the reference definitions, with only
`propext`, `Quot.sound`, and `Classical.choice` permitted and an independent
checker enabled. It has NOT been executed. It does not by itself enforce the
additional source-level tactic restrictions or prove an axiom closure.

The independent Challenge files retain their statement placeholders but are
not imported by the solution. The new source examples are likewise unexecuted.
Lean 4.35.0-rc3 versus the inspected upstream 4.33.1 remains an untested porting
boundary. Publication, upstream acceptance and Palomar validation are not
claimed on the strength of uncompiled source alone.
