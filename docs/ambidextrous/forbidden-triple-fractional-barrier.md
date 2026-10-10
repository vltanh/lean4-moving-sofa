# A universal fractional barrier to ordinary-area certificates using *only* forbidden triples

**Exact negative result FT-FRAC1.** Fix any incoming horizontal
unit strip \(0\le y\le1\) and any horizontal-width interval
with a representative \(W\ge5/2\). Partition the full possible
rectangle \(B_W=[0,W]\times[0,1]\) into finitely many measurable
positive-area spatial cells \(C_i\) of areas \(a_i\), with
\(\sum_i a_i=W\). Consider the *bare occupancy LP*
with variables \(0\le z_i\le1\), constraints

\[
z_i+z_j+z_k\le2
\tag{FT-FRAC.1}
\]

for every certified **distinct-cell** forbidden triple, drawn from
*any number of conventional lower/upper hallway orientations*,
and objective \(\sum_i a_i z_i\).
Then the LP optimum is necessarily at least

\[
\boxed{\frac{2W}{3}\ \ge\ \frac53\ >\ M.}
\tag{FT-FRAC.2}
\]

This holds for an arbitrarily fine grid, all real hallway angles,
and the union of both handed turning families. Therefore **no
certificate consisting only of independently weighted
forbidden-triple inequalities and the bounds \(0\le z_i\le1\)**
can establish the sharp Romik area bound on the entire
horizontal-width range \(W\ge5/2\). A more elaborate integer
or component-aware procedure might still work; this lemma does
not rule out forbidden-triple reasoning itself.

## Proof: the constant two-thirds occupation vector

Set \(z_i=2/3\) for **every** cell, irrespective of its position.
For every inequality FT-FRAC.1, its left side equals \(2\);
hence this vector satisfies *every possible such inequality*,
including constraints discovered adaptively at later stages.
It also obeys \(0\le z_i\le1\). The objective is exactly
\(\sum_i (2/3)a_i=(2/3)W\). This proves the first comparison.

For the last strict comparison use the exact Romik candidate
constant \(M=1+4Y^2+\arctan Y\),
\(4Y^3+3Y-1=0\), \(Y>0\).
The cubic is strictly increasing and positive at \(3/10\),
so \(Y<3/10\); since \(\arctan Y<Y\),

\[
M<1+4(3/10)^2+3/10=83/50<5/3.
\]

The last difference is \(5/3-83/50=1/150>0\).
This proves FT-FRAC.2 without numerical optimization. QED.

## No hidden repeated-point pair cuts

The exact forbidden-triple lemma CF1 permits \(q=r\), in
which case one might wish to add a **stronger**
occupancy-pair inequality \(z_p+z_q\le1\).
But no such repeated-point forbidden pair exists
in the height-one incoming strip for **a proper
conventional quarter-turn frame**.

Indeed for a lower-handed frame
\(u=(c,s),v=(-s,c)\), \(c,s\ge0\), and two points
\(p,q\) in the strip, write \(d=q-p\).
If \(d_x\ge0\), then
\(d\cdot v=-s d_x+c d_y\le c\le1\).
If \(d_x\le0\), then
\(d\cdot u=c d_x+s d_y\le s\le1\).
Thus it is impossible for *both*
\(d\cdot u>1\) and \(d\cdot v>1\).
Reflect vertically for upper-handed frames.
Consequently the special two-point version of
CF1 does not defeat the constant \(2/3\) vector
in the present strip normalization.

The theorem concerns the *basic* fractional
LP. It does not prove that the actual geometric
problem has area \(5/3\); indeed any infeasible
fractional vector may be realized by **no set at all**.
An LP certificate augmented with forced anchors,
component/connectivity constraints, valid
higher-order occupancy inequalities or exact
per-box polygon-area enclosures is a
mathematically different relaxation and is
not ruled out by FT-FRAC1.

## Direct relevance to the branch's proof strategy

The [CF2](configuration-area-certificate.md) rational
dual construction is valid and useful for *some*
area bounds, but in its bare form it proves a bound
for **all** occupancy vectors satisfying only
FT-FRAC.1 and \([0,1]\) caps.
The explicit feasible fractional point prevents its
upper bound from dropping below \(5/3\) at \(W=5/2\).
Therefore a proposal to **close Romik optimality by
finer and finer spatial grids with only CF2 triple
inequalities** is blocked on a nontrivial width
interval even if the grid becomes infinite.

This is a rigorously established *methodological*
obstruction, not an obstruction to optimality of
Romik's actual sofa. It does not assert that the
scalar \(P_J\) inequality is true or false,
and it does not require any candidate contact
pattern, curvature assumption, or Lean formalization.

**Next gate:** find a valid strengthening whose
convex relaxation cuts off \(z_i\equiv2/3\).
A concrete option is a higher-order *rank*
inequality: if a collection \(T\) of \(m>3\)
cells has **no realizable triple** among its
occupied cells, then \(\sum_{i\in T}z_i\le2\).
That inference is sound only when *every*
triple is independently certified forbidden and
must be checked exactly. Another possibility is
anchored/global component constraints or exact
spatial polygon-area envelopes.

No CI, optimizer or Lean build is a premise.
