# A 65-degree individual-turn gate from the neighboring fixed-angle program

**Theorem FA65 (new cross-PR angle exclusion).**
Assume the universal fixed-net-angle inequality proved in the
written [PR #4 beyond-one-radian relaxation theorem]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/fixed-rotation-angle-paper-20261005/docs/fixed-angle/beyond-one-radian.tex):

\[
\boxed{m(\omega)\le1+\omega^2/2
\quad(0\le\omega\le\pi/2),}
\tag{FA65.1}
\]
where m(ω) is the unrestricted one-handed sofa optimum
for an actual unit-width **right-angle** hallway with prescribed
net rotation ω. For ω>1 the source's inequality is strict.
These are **mathematical draft results** with a
nontrivial all-maximizer geometric-majorization dependency,
not an independently reviewed or Lean-certified theorem.

Then **every compact connected ambidextrous sofa**
with common incoming strip, arbitrary partial/backtracking
motions, and area at least Romik's candidate
\[
M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\ Y>0,
\]
must have **both** effective conventional turn angles
satisfying the exact new bound
\[
\boxed{
\alpha_- >\frac{227}{200},\qquad
\alpha_+ >\frac{227}{200}.
}
\tag{FA65.2}
\]
The threshold is approximately 65.03 degrees,
compared with the 60.227-degree individual-turn
gate from the earlier terminal-angle certificate TE1.
In particular a hypothetical sofa beating M
cannot use a conventional partial turn shorter
than 227/200 radians in either hand.

**Proof.** The proper-angle reach reduction in
[GH](midpoint-bound-general-motions.md)
and [JT](joint-terminal-strips-one-sixth-transfer.md)
applies because M>\sqrt2. It associates to each
handed motion an *actual prescribed-net-angle*
right-hallway passage with amount
\(\alpha_\pm\in(\pi/4,\pi/2]\).
If the original motion reaches a full quarter,
that complete quarter (with its outgoing unit strip)
may be selected; otherwise the original proper
partial terminal passage provides the actual
outgoing unit strip at its effective endpoint.
No monotonicity of the original path is assumed.

Apply FA65.1 independently to both passages:
\[
|S|\le m(\alpha_\pm)
\le1+\alpha_\pm^2/2.
\]
If either \(\alpha_\pm\le227/200\),
then
\[
|S|\le1+\frac12\left(\frac{227}{200}\right)^2
=\frac{131529}{80000}
=1.6441125.
\tag{FA65.3}
\]

This is strictly below **the exact candidate area** M.
To prove the comparison with only rational arithmetic,
put x=149/500=0.298. The polynomial
\(4z^3+3z-1\) is strictly increasing for z>0,
and direct substitution gives
\[
4x^3+3x-1=-4551/31250000<0.
\]
Consequently \(Y>x\). Since
\(z\mapsto1+4z^2+\arctan z\) is strictly increasing,
and \(\arctan x>x-x^3/3\) for 0<x<1,
\[
\boxed{
M>1+4x^2+x-x^3/3
=\frac{616648051}{375000000}
>\frac{131529}{80000}.
}
\tag{FA65.4}
\]
The last strict difference is
\(211727/750000000>0\).
This contradicts \(|S|\ge M\).
Thus both α satisfy FA65.2. QED.

## Scope and practical meaning

This is a true **global geometric filtering theorem**,
conditional on the cross-PR fixed-angle sharp
relaxation and the earlier GH/JT angle normalization.
It excludes a larger class of incomplete original
motions **without** a finite-angle area search,
without importing the near-180° bend optimum,
and without assuming full quarter turns.

It **does not** prove that either motion must turn
all the way through \(\pi/2\).
The remaining partial interval
\(227/200<\alpha_\pm<\pi/2\)
is still substantial.
Nor does it bound the positive two-cap clipping
correction \(G(U,V)\), and so it does not prove
\(|S|\le M\). The PR #7 reverse-bend result
concerns a different *physical hallway angle*
and cannot replace the PR #4 fixed-net-angle
bound used here.

The PR #7 cross-project
[CROSS_PR_TRANSFER_AUDIT.md]
(https://github.com/vltanh/lean4-moving-sofa/blob/research/arbitrary-hallway-angles-20261005/experiments/hallway_angles/CROSS_PR_TRANSFER_AUDIT.md)
already identifies PR #4's same-shape angle completion
and area-majorization methods as transfer candidates.
The present argument records an **actual direct
numeric-free implication** of its one-turn bound
for the two-handed problem, not a global closure.

No Lean formalization, CI, or sampled angle numerical
certificate is used by the new arithmetic/logic.
The source PR #4's independent review status
is not upgraded.
