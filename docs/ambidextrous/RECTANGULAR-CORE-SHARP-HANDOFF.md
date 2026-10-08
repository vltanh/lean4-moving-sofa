# Rectangular-core sharp-optimality research handoff

**Purpose:** Act directly on the proposed “expand Gerver to a width-two
hallway, intersect the two turning halves, and remove a filled central
rectangle” strategy. Mathematical proofs only; no Lean formalization,
no finite-angle global area search, and no claim that Romik optimality
has been proved.

## Exact results established

**A. Reversible widened-turn geometry.**
[RAD1](reversible-anisotropic-doubled-corridor.md)
proves the necessary *and sufficient* support-depth system for
vertical Minkowski filling \(B=A+[0,1]e_y\):
at a conventional turning angle \(\theta\), the doubled parent must
satisfy arm-normal width bounds **\(1+\sin\theta\) and
\(1+\cos\theta\)**. This is a genuinely reversible *angle-dependent*
constraint system, not one rigid width-two hallway.
Ordinary width-two feasibility alone cannot be inverted.

**B. Full convex-core area formula.**
[RCE1](rectangular-core-exact-two-turn-area.md)
takes **arbitrary independent convex cores** \(V_i\) of width T,
height 1/2 and full bottom segment, and adds the literal rectangle
\([0,T]\times[0,1/2]\).
Assuming the two complete turning niches stay below height 1/2,
the resulting paired survivor is a genuine compact connected
full-two-turn sofa, with exact ordinary area

\[
\boxed{
|E|=T+|V_1|+|V_2|
-\int_0^{2T}
\big[(n_1+A_2-1)_++(n_2+A_1-1)_+\big]\,dx.
}
\tag{RC-H.1}
\]

The filler supplies precisely the positive term T; the two
*effective* actual forbidden niche losses are the two positive
parts. This is not the same as subtracting two free-standing
Gerver niche areas; clipping against the opposite parent matters.
The **unproved global filled-core theorem** is that the integral
in RC-H.1 always exceeds \(T+|V_1|+|V_2|-M\).
This statement is a real, falsifiable ordinary-area target, but
it is not proved here and is not claimed equivalent to unrestricted
Romik optimality unless every competitive sofa can be admitted to
the core class, which is separately unproved.

**C. Hand sharp inequality for actual independent triangular cores.**
[TCG1](triangular-core-expanded-gerver-sharp-hand-bound.md)
proves, over a whole rational three-parameter box,
\[
11/10\le T\le6/5,\quad2/5\le a,b\le4/5,
\]
the sharp target for both complete turning parents:
\[
|E_{a,b,T}|\le
3T/2-2(T+1/2-\sqrt2)^2<41/25<M.
\]
The lower and upper \(45^\circ\) hallways contribute two
**disjoint physically removed triangles**, with no weighted
functional calibration involved.
[TCA1](triangular-core-fullturn-admission.md)
proves full continuum-angle niche ceilings and valid connected
two-turn motions, not just two feasible snapshots.

**D. Cubic tip-clipping law for independently curved parents.**
[CCC1](curved-core-cubic-clipping-hand-bound.md) proves from
the support-curvature ODE, without a contact-pattern assumption,
that for two length-T top faces displaced by d≤η, whose open
curvatures satisfy \(0\le\rho\le1-\eta\) and whose niches remain
inside those faces, the entire positive two-cap clipping
correction satisfies
\[
\boxed{0\le G\le 2d^3/(3\eta).}
\tag{RC-H.2}
\]
The essential fact is a **quadratic niche tip-height bound**
\(n(a+x)\le x^2/\eta\), integrated over each unmatched
top-face interval of length d.
The sharp area bound follows *conditionally* if the
sum of the genuine signed one-turn deficits is ≥RC-H.2.
This conditional premise has **not** been proved for arbitrary
caps.

**E. Hand strict sharp theorem for two independent actual curved
Romik-core shears.**
[SCR1](sheared-romik-core-sharp-local-theorem.md)
uses the literal Romik reference core \(V_*\), independent
horizontal shears of its upper point by \(\delta_1,\delta_2\),
and fills each with the same rectangle.
For \(|\delta_i|\le1/2000\) it proves
\[
\boxed{|E_{\delta_1,\delta_2}|
\le M-\frac3{250}(\delta_1^2+\delta_2^2).}
\tag{RC-H.3}
\]
The full parent niches stay below the midline and inside their
shifted faces; the resulting sofa has both true complete
continuous turns. The *existing* written AF1/SD1/SR1 functional
identity/coercivity chain gives a quadratic weighted deficit;
CCC1 pays the cubic clipping loss.
These historical dependencies are self-reviewed but not independently
refereed or Lean-verified. Thus RC-H.3 is not independently certified
outside its explicit mathematical premises.

## A new exact obstruction: averaging the curved cores is not free

[EAC1](expanded-core-averaging-clipping-counterexample.md)
uses *two identical* full-filler triangular cores
of width \(T=7/6\) with top apex x-coordinate
\(a=16/15\). An elementary three-regime
support calculation proves the entire complete-turn
niche lies below \(y=1/2\), so the symmetric
intersection is a **genuine connected two-turn sofa**.

Yet a positive part of the turning niche lies **outside the
cap's flat top-face interval**. Its exact clipping satisfies

\[
\boxed{
|E(U,U)|-2\Psi(U)
\ge\frac{15}{47}
\left(\frac{47}{30}-\sqrt2\right)^2>0.}
\tag{RC-H.4}
\]

Therefore the proposed scalar Jensen replacement
\[
|E(U,V)|\le2\Psi((U+V)/2)
\]
is **false on the general filled-core domain even when U=V**.
Averaging two parents and invoking the one-turn weighted
value theorem is not a legitimate universal proof. The
counterexample does **not** beat M; it refutes the bridge.

## October 8 follow-up: admission correction and an infinite-dimensional sharp theorem

**Critical geometric correction: horizontal-core admission is automatic.**
[UHCD1](universal-horizontal-core-decomposition.md)
proves by horizontal slicing that **every** compact
downward convex cap U with upper face length \(T\ge0\)
has a unique canonical decomposition

\[
\boxed{U=C(U)+[0,T]e_x,\qquad
|U|=|C(U)|+T,}
\]

where the core C(U) has a singleton top face.
If U has a complete bottom rectangle of height h, it
even decomposes as
\[
U=V(U,h)+([0,T]\times[0,h]).
\]
The previous HF2 proof did not need maximizing-specific
arguments for the decomposition: those arguments were
needed to force \(h=1/2\) and \(T=W/2\).
The presence of a horizontal rectangular summand
is therefore **not** a global admission obstacle.
For full-turn ordinary-area comparisons, UHCD.6 gives
the exact effective-niche identity for two point-top
cores of *arbitrary and unequal top-face lengths*,
without assuming a common midline.
The old global obstacle is that this effective-niche
inequality has not been proved at the sharp constant.

**Exact filler-to-forbidden-triangle tradeoff.**
[FAP1](rectangular-filling-exact-angle-penalty.md)
shows that filling a curved core by
\([0,T]\times[0,h]\) raises the inner forbidden corner
at every conventional turn angle t by the exact vector
\((T\cos^2t,T\sin t\cos t+h)\), and the
area of its single-angle forbidden triangle is
\[
\tfrac12\sin t\cos t\,
\bigl(B_{\rm core}(t)+T+h/(\sin t\cos t)\bigr)_+^2.
\]
This is a real geometric turning cost of the center
filler, not two independent Gerver areas. But
overlap between different angle triangles makes
their **union** the real remaining optimization.

**New full-turn near-reference sharp theorem.**
[UFC1](general-unequal-face-cubic-clipping.md)
extends the analytic cubic clipping estimate to unequal
top-face lengths: for curvature gap \(\eta\), the
pairwise clipping is at most
\[
\boxed{G\le\bigl(|a_U-a_V|^3+
|b_U-b_V|^3\bigr)/(3\eta)}
\]
when the endpoint discrepancies are at most \(\eta\)
and the niches stay below half-height.

The new [ASS1](actual-sofa-smooth-sharp-neighborhood.md)
then proves an **ordinary-area sharp inequality for
actual connected full-turn sofas** whose hull has the
reference horizontal projection \([-m,m]\), vertical
span one, and whose two canonical cap supports differ
from Romik's by at most \(10^{-3}\) in open-quarter
\(L^\infty\) **second derivative** norm:
\[
\boxed{|S|\le M-\frac{100}{3}
\sum_{j\in\{U,V\}}
(|a_j+m/2|^3+|b_j-m/2|^3)\le M.}
\]
There is **no** artificial midline-rectangle assumption
on S, no imposed symmetry, no matched top-face position
or length, and no assumption that the two caps have
a fixed contact chart. Equal-area rigidity follows from
the existing fixed-width strict concavity.
[S2C1](smooth-two-cap-sharp-neighborhood.md)
gives the synthetic actual-body construction and
explicit nonzero independent perturbations of both
top-face endpoints, demonstrating the neighborhood
is not vacuous.

**Exact reason this still does NOT close the conjecture.**
The hypothesis of ASS1 is **much stronger** than
Hausdorff closeness: it rules out arbitrarily thin
new facets, moving curvature jumps with order-one
density contrast, and arbitrary width variation.
No theorem forces a global area maximizer into
this regularity neighborhood or shows all
competitive partial-turn motions can be completed.
The fixed-width AF/SD/SR mathematical dependencies
also remain self-reviewed rather than independently
refereed. Consequently the new sharp local theorem
is a strict and meaningful enlargement of the
previous finite-mode results, but is **not**
a global optimality or uniqueness proof.

**Revised priority:** prove global/near-reference
geometric admission to a norm compatible with the
trace-energy/clipping absorption (or prove that
absorption directly without second-derivative
smallness), rather than continuing to rederive
Minkowski rectangle decompositions or sample
distant finite-angle upper bounds.

## Precisely what would close the idea

Prove the **effective niche lower bound in RC-H.1** for every
filled-core pair satisfying genuinely complete turning geometry,
or prove a valid area-nondecreasing map reducing every
competitive full/partial-turn sofa into a smaller filled-core
class for which that bound is established.

Do not:
- replace the effective niche losses by full niches (RC-H.4);
- infer a symmetric maximizer merely from reflected feasibility;
- treat a static uniform width-two corridor as reversible (RAD1);
- treat a near-reference two-shear theorem as uniform
  local stability against arbitrary singular support deformations;
- claim full-turn optimality proves arbitrary partial-turn
  optimality without an additional motion argument.

The unrestricted ambidextrous sharp value \(M\) remains **open**.
The present work provides a correct filled-core formulation,
a strict hand proof on two explicit nontrivial subclasses,
an analytic cubic interaction estimate, and an exact negative
control blocking a false averaging shortcut. No CI or
independent mathematical review is claimed.
