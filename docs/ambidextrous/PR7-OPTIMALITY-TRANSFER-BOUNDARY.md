# PR #7's variational method versus Romik optimality: precise transfer and stop conditions

**Research status, October 8, 2026.**
This is a direct attempt to prove the **unrestricted**
ambidextrous area bound
\[
|S|\le M=1+4Y^2+\arctan Y,\quad4Y^3+3Y-1=0
\]
using the one-corner methods in
[PR #7](https://github.com/vltanh/lean4-moving-sofa/pull/7).
**The global proof was not obtained.**
The useful transfers, one decisive structural obstruction
and a smaller but global turn-angle theorem are recorded
with their exact scopes. No Lean formalization or
computer-assisted area bound was attempted in this pass.

## 1. PR #7's forward contact ODE and Romik really share the same interior frequency

PR #7's
[FORWARD_CONTACT_MODEL.md]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/FORWARD_CONTACT_MODEL.md)
derives a central contact-mode characteristic factor
\[
(\lambda^2+1)
[4\sin^2\beta\,\lambda^2+
4\sin^2\beta-3].
\]
At the physical right-angle bend \(\beta=\pi/2\)
this becomes, **exactly**,
\[
\boxed{(\lambda^2+1)(4\lambda^2+1).}
\tag{PTB.1}
\]
There is a frequency-1 mode from the Euclidean
translation/gauge part and a genuinely changing
contact mode of frequency **one half**.

Romik's exact middle one-turn cap support
from [RH.2](romik-horizontal-misalignment-sharp-bound.md)
is
\[
f_*(t)=R_0\cos(t/2+\pi/8)+\tfrac12\sin t,\quad
g_*(t)=R_0\sin(t/2+\pi/8)+\tfrac12\cos t.
\]
Its nontrivial homogeneous part likewise has
frequency one half. Thus the PR #7 *forward*
contact ODE is a genuine analytic relative
of the Gerver/Romik construction, not an
unrelated numerical family.

**But the boundary conditions differ.**
For Gerver, the one-turn area objective is
\(\mathcal A(U)\). For the relevant Romik
one-turn half, the objective is
\[
\Psi(U)=\mathcal A(U)-W(U)/2.
\]
At fixed horizontal width, their interior
first variations coincide. The width term
changes the free horizontal-endpoint
transversality by exactly \(1/2\);
in the explicit candidate this moves the
initial supporting height from Gerver's
zero-edge condition to the Romik
half-height contact. These facts are
already identified in PR #3's
[OT2b](one-turn-reduction.md) and
[WV2](one-turn-weighted-value.md).
Consequently merely solving the *same*
second-order interior ODE does **not**
prove the two-handed optimum.

## 2. The central PR #7 *area majorant* does not transfer as written

PR #7's successful reverse-bend upper
bound first proves a **one-crossing
geometric fact**: the canonical inner
corner moves through the actual vertical
strip in one increasing-height crossing.
It can therefore subtract an area
\(\int x(y)\,dy\) to the left of a
*single* forbidden graph, and then
maximize a strictly concave quadratic.

The ordinary 90-degree one-turn inner
wall normals have **opposite horizontal
signs**:
\[
u_t=(\cos t,\sin t),\quad
v_t=(-\sin t,\cos t).
\]
At height y below an inner corner
\(C=(x_C,h_C)\), the forbidden region
is the **bounded interval**
\[
x_C-(h_C-y)\cot t<x<
x_C+(h_C-y)\tan t,
\]
not a ray extending left of one wall.

More decisively, the
[direct proof DC1](pr7-double-crossing-area-transfer.md)
shows Romik's **actual reference** inner
corner height starts at zero, rises
strictly to
\[
R_0+\tfrac12-\sqrt2>0
\quad\text{at }t=\pi/4,
\]
and then strictly returns to zero.
Every height between zero and that
maximum is reached **twice** by the
actual reference hallway orientations.
Thus there is no single PR #7-type
crossing graph even at the
proposed optimum.

## 3. A correct PR #7-style two-front area formula is now proved

[DC2–DC6](pr7-double-crossing-area-transfer.md)
establish the exact replacement:
if each one-turn corner's height
superlevel angle sets are connected,
then **at every positive horizontal
height the entire one-turn forbidden
niche is a single interval**,
whose left and right endpoints are
the infimum and supremum of explicit
continuous-angle wall expressions.

For two caps U,V with complete
niches below half-height, let
\(C=U\cap\rho V\). The area of the
two-turn survivor is exactly

\[
\begin{aligned}
|E|=|C|
&-\int_0^{1/2}|N(U)_y\cap C_y|\,dy\\
&-\int_0^{1/2}|N(V)_y\cap C_{1-y}|\,dy.
\end{aligned}
\tag{PTB.2}
\]

Each intersection length is the
positive part of
**min(right boundary) minus max(left boundary)**,
given explicitly in DC.6.
This is a fully *ordinary-area*
identity, not a signed quadratic
that ignores disconnected niche
components or clipped forbidden regions.

The reference candidate satisfies
the two-front hypotheses, but a
global maximizing competitor is
not yet known to do so. Even
within that domain, no theorem
bounds the two effective loss
integrals below by \(|C|-M\).

**This is the exact point where the
PR #7 transfer stops.** PR #7's
spectral/coercive quadratic method
does not itself prove the inequality
for these *two coupled, clipped*
loss integrals.

## 4. A genuine ancillary global transfer from the companion fixed-angle program

The
[PR #7 cross-PR audit]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/CROSS_PR_TRANSFER_AUDIT.md)
highlights the same-corridor
[PR #4 fixed-net-angle theory]
(https://github.com/vltanh/lean4-moving-sofa/pull/4)
as a more appropriate partner for
the 90-degree geometry.

[FA65](fixed-angle-65-degree-necessary-turn.md)
combines PR #4's
**universal relaxed one-turn bound**
\(m(\omega)\le1+\omega^2/2\)
with the arbitrary-motion proper-angle
reduction already written in PR #3.
It gives a new global necessary condition
for any putative sofa of area at least M:

\[
\boxed{
\alpha_->227/200,\qquad
\alpha_+>227/200
\quad\text{radians} \ (\sim65.03^\circ).
}
\tag{PTB.3}
\]

The rational comparison is exact:
\[
1+(227/200)^2/2=131529/80000
<616648051/375000000<M.
\]
This improves the earlier
individual 60.227-degree terminal-angle
exclusion. It **does not** force full
quarter turns or settle the sharp area.

The source PR #4 majorization is a
self-reviewed mathematical proof draft,
not an independently checked kernel
theorem; FA65's acceptance therefore
depends on that source.

## 5. The decisive unsolved global inequality

For actual full-turn hull caps U,V with
nonempty canonical-envelope fibers,
the exact ordinary-area formula
already written in PR #3 is
\[
\boxed{|E|=\Psi(U)+\Psi(V)+G(U,V),\quad G\ge0.}
\]
The full signed cap maximum
\(\Psi(X)\le M/2\) is also an
existing written result. Therefore
a sufficient globally sharp comparison
is
\[
\boxed{
G(U,V)\le
[M/2-\Psi(U)]+[M/2-\Psi(V)].
}
\tag{PTB.4}
\]

**The PR #7 proof does not show PTB.4.**
It solves a different single-crossing
area majorant for an obtuse *physical
hallway bend*. Importing its strict
quadratic maximum without simultaneously
proving the two-front *ordinary-area*
majorization is logically invalid.

Actual positive clipping is not just
a bookkeeping possibility:
[SC3](repair-shadow-clipping-obstruction.md)
and
[PII2](pair-versus-identical-romik-obstruction.md)
construct fully feasible
near-reference families with positive
interaction G. No global argument can
silently replace G by zero.

At present the most relevant
**remaining actual counterexample
class** among complete-two-turn sofas
is the positive *opposite-end top/bottom
face* class, by the earlier
[PD3](full-turn-positive-face-density.md)
reduction. The two-front formula could
be a viable proof language for that
class **only after** proving the
ordinary-area calibration PTB.4 (or
an equivalent interval-loss inequality).
Merely enumerating more Gerver-like
or PR #7-derived trial shapes will not
supply that universal comparison.

## 6. Honest conclusion

This pass **did not prove unrestricted
Romik optimality**. It obtained:
- the exact common half-frequency
  behind PR #7's forward ODE and Romik's
  interior curve;
- a hand proof that PR #7's critical
  single-crossing hypothesis fails
  **already at Romik**;
- a valid two-front *ordinary-area*
  formulation replacing that geometry;
- a cross-PR improvement of each
  necessary partial turn to over
  65 degrees, conditional on PR #4.

What remains is genuinely harder:
an ordinary-area majorant for two
arbitrary interacting 90-degree turns,
including **hidden and clipped**
inner-wall regions and possibly
non-unimodal switching trajectories.
Neither PR #7's reverse-bend optimum
nor its spectral gap closes this.

**No Lean code, CI, global numeric
certificate or unrestricted
optimality theorem is claimed.**
The source research chains remain
self-reviewed and need independent
mathematical examination.
