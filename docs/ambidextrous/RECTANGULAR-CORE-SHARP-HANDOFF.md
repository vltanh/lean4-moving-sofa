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
