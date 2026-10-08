# An exact \(P_J\) value theorem from baseline support barriers

The current sharp-value difficulty is **not** the smoothly
perturbed middle arcs of a reference cap that still has its whole
middle-half top face and its niche inside that same interval.
For every such cap, the exact spatial partition functional
**equals** the previously solved signed one-turn functional.
This note makes the conclusion independent of an assumed
curvature density or candidate contact topology. It is a
useful solved-domain gate, not unrestricted optimality.

Let \(U\) be any normalized compact convex downward-closed
height-one cap with horizontal projection \(I=[l,r]\), width
\(W=r-l\), and full positive niche roof \(n_U\). Set

\[
a=l+W/4,\qquad b=r-W/4,\qquad J=[a,b].
\]

Write \(f(t)=h_U(\cos t,\sin t)\) and
\(g(t)=h_U(-\sin t,\cos t)\), \(0<t<\pi/2\).
Denote the cap upper roof by \(A_U(x)\), and the weighted
one-turn functional by \(\Psi(U)=|U|-|N(U)|-W/2\).

**Theorem PJ-ZS1 (zero-slack admission).** Suppose

1. \(A_U(x)=1\) for every \(x\in J\), i.e. \(J\) is contained
   in the cap's top face; and
2. the two genuine full-angle support inequalities hold:
   \[
   \boxed{f(t)-1\le b\cos t,\qquad
   g(t)-1\le -a\sin t\quad(0<t<\pi/2).}
   \tag{PJ-ZS.1}
   \]

Then the positive full niche is confined to \(J\), and

\[
\boxed{P_J(U)=\Psi(U)\le M/2.}
\tag{PJ-ZS.2}
\]

The conclusion requires no curvature domination, smoothness,
symmetry, reference proximity, or contact ordering, just the
two displayed actual support inequalities and the face
condition. The final inequality uses the existing written
weighted-cap value theorem WV2, whose independent mathematical
review remains outstanding. The equality \(P_J=\Psi\) is
elementary and independent of WV2.

**Proof.** For \(x\ge b\), the first forbidden
wall has height

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t}
\le\frac{(b-x)\cos t}{\sin t}\le0.
\]

For \(x\le a\), the second forbidden wall has height

\[
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}
\le\frac{(x-a)\sin t}{\cos t}\le0.
\]

Every inner forbidden quadrant has roof
\(\min(R_t,L_t)\), hence no point of positive height
occurs outside \((a,b)\) at any turn angle. Thus \(n_U=0\)
a.e. on \(I\setminus J\). Together with the top-face
hypothesis \(A_U=1\) on \(J\), the exact SPB.5 identity

\[
P_J(U)-\Psi(U)
=\int_J(1-A_U)+\int_{I\setminus J}n_U
\]

has two zero terms. WV2 then gives PJ-ZS.2. QED.

**How this affects the \(P_J\) roadmap.** The existing
[PJ-MID](spatial-half-partition-middle-arc-variation.md)
and [PJ-COUP](spatial-half-partition-coupled-middle-variation.md)
smooth, compactly supported perturbations preserve the top
face and, whenever their curvature densities remain in
\([0,1]\), satisfy the baseline support barriers by the
same argument as SR/SW. Their *value inequality* is therefore
already supplied by PJ-ZS1/WV2. The quadratic formulas can
still contribute quantitative strictness, but they do not
remove the genuinely open admission difficulty.

A future sharp-value proof must handle caps in which at
least one of the two **exact zero-slack conditions**
fails: a cap roof loses height inside \(J\), or the positive
niche leaks into its exterior. The correction is the explicit
nonnegative sum in SPB.5 and cannot be suppressed by a
global concavity premise (CN proves that premise false).

Neither PJ-ZS1 nor WV2 proves that *every* competitive
two-turn cap satisfies PJ-ZS.1, that every area optimizer
has the centered top face, or that partial turning motions
can be completed at zero area cost. No unrestricted sharp
optimality or uniqueness theorem is claimed.
