# A strict *global* horizontal-width gap for competitive full turns

**Corollary SWG1.** Let \(M\) be Romik's exact
feasible candidate area. There exists a **universal
constant \(\delta>0\)** such that every compact
connected sofa \(S\) capable of both complete
conventional quarter turns from one common
incoming unit-width strip satisfies

\[
\boxed{|S|\ge M\quad\Longrightarrow\quad
\operatorname{width}_x(S)\le2\sqrt2-\delta.}
\tag{SWG.1}
\]

This is a genuinely global exclusion of an **entire
positive-width neighborhood of the maximum
horizontal span**, derived from the exact
maximal-width area theorem
[EXW1](extreme-width-anchored-area.md)
and an established compactness argument.
It is **nonquantitative**: no numerical value
of \(\delta\) has been certified here.
It neither identifies the exact area optimum
nor proves a sharp statement for partial turns.

## Proof via compactness, without an unproved stability assumption

Suppose no \(\delta>0\) existed. Then for
every integer \(n\ge1\) there would be an
actual compact connected full-turn sofa
\(S_n\) with \(|S_n|\ge M\) and

\[
2\sqrt2-\frac1n <
W_n:=\operatorname{width}_x S_n
\le2\sqrt2.
\]

The upper bound is [TSW1](three-point-switching-fiber-width.md).
Translate each \(S_n\) so its leftmost and
bottommost coordinates are zero. Its actual
incoming vertical span is \(\le1\), hence

\[
S_n\subseteq[0,2\sqrt2]\times[0,1].
\]

The hyperspace of nonempty compact subsets
of this fixed rectangle is compact under
Hausdorff distance (Blaschke selection).
Pass to a Hausdorff-convergent subsequence
\(S_{n_k}\to S_\infty\).
The limit is nonempty, compact and
**connected**: a positive-distance
separation of the limit would separate
every sufficiently close approximating
compact connected set.

The support functions of \(S_{n_k}\)
converge uniformly to that of \(S_\infty\).
Every member of each \(S_{n_k}\) satisfies
the canonical lower and upper hallway
support-depth disjunction at **every**
angle \(0\le t\le\pi/2\). For any
\(p\in S_\infty\), choose \(p_k\in
S_{n_k}\) tending to p. Passing to
the limit in each closed disjunction
shows that p satisfies the corresponding
canonical full-angle constraints for
\(S_\infty\). The common incoming strip,
the endpoint frames, and continuous
support-tightened corner placements also
pass to the limit. Thus \(S_\infty\)
is a **genuinely full-turn feasible**
connected sofa, not merely a sampled
orientation witness. This is precisely
the closure reasoning used in
[FR1](full-turn-compact-finite-reduction.md).

Horizontal extrema converge under
Hausdorff distance, so

\[
\operatorname{width}_xS_\infty
=\lim W_{n_k}=2\sqrt2.
\]

Planar Lebesgue area is **upper
semicontinuous** on compact subsets
of a fixed bounded rectangle under
Hausdorff convergence: the approximants
eventually lie in every fixed
neighborhood of the limit, and the
areas of shrinking neighborhoods tend
to the limit's area. Hence

\[
|S_\infty|\ge\limsup_k|S_{n_k}|\ge M.
\]

But [EXW1](extreme-width-anchored-area.md)
applies to every full-turn body of
width exactly \(2\sqrt2\) and yields

\[
|S_\infty|\le
\frac{170619797734244653516561}
{104857600000000000000000}
<\frac{41}{25}<M,
\]

a contradiction. Therefore a
universal \(\delta>0\) exists. QED.

## What this changes

Earlier TSW gave a **closed** feasible
width interval \(W\le2\sqrt2\).
EXW establishes a strict area deficit
at its far endpoint, with an exact
short rational certificate.
SWG now removes a **whole open**
outer-width class from every potential
counterexample to Romik's sharp area
bound, without needing a reference-hull
neighborhood or an assumed contact
pattern.

The proof does not give an **explicit**
\(\delta\). An effective follow-up would
quantify near-equality in the TSW
safe-wall switches, certify the resulting
small support-offset uncertainty, and
robustly replay EXW's six-angle
anchored slice certificate. Compactness
guarantees that some such width
neighborhood is excludable, but the
present argument does not supply its
size or computational cost.

No Lean formalization, CI or independent
refereeing is claimed. The unrestricted
full-turn area bound \(A_F\le M\) and
the partial-turn sharp bound remain open.
