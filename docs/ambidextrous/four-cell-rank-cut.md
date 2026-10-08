# A genuine four-cell rank-two inequality defeating the \(2/3\) fractional point

**Theorem FCR1 (exact higher-order spatial conflict).** Normalize the
incoming strip to \(0\le y\le1\). Every compact sofa admitting both
**complete conventional** quarter-turn hallway families obeys the
following occupancy constraint for four **positive-area squares**:

\[
\begin{aligned}
C_0&=[0,1/12]\times[0,1/12],\\
C_1&=[3/4,5/6]\times[11/12,1],\\
C_2&=[19/12,5/3]\times[0,1/12],\\
C_3&=[29/12,5/2]\times[11/12,1].
\end{aligned}\tag{FCR.1}
\]

Set \(z_i=1\) if the actual sofa intersects \(C_i\), and
\(z_i=0\) otherwise. Then

\[
\boxed{z_0+z_1+z_2+z_3\le2.}\tag{FCR.2}
\]

If the horizontal projection is shorter than \(5/2\), some cells
may not be met, but the same implication remains valid. This
inequality also transfers to any common horizontal translation
of all four cells lying inside the normalized strip.

Crucially, this is **stronger than the four triple inequalities**
in their fractional relaxation: \(z_i=2/3\) satisfies each
three-cell inequality with equality, but violates FCR.2
because \(\sum_i z_i=8/3>2\). Thus it supplies a concrete
constraint missing from the basic CF2 occupancy LP, whose
universal fractional barrier is proved in
[FT-FRAC](forbidden-triple-fractional-barrier.md).

## The four independently forbidden triples

For cosine \(c>0\), sine \(s>0\) and handedness
\(h=+1\) (lower) or \(h=-1\) (upper/reflected),
the hallway normal pair is
\(u=(c,hs)\), \(v=(-s,hc)\).
For each three-cell subset, the table supplies
three distinct cell indices \(p,q,r\) and a
**real visited conventional hallway frame** at which
every point choice from the respective cells gives

\[
(q-p)\cdot u>1,\qquad (r-p)\cdot v>1.
\tag{FCR.3}
\]

All entries are exact. The two margin columns are
the minima of the left-hand sides minus one
over the **entire rectangular cells**.

| Triple | \(p,q,r\) | \((c,s);h\) | \(u\) margin | \(v\) margin |
|---|---|---|---:|---:|
| \(0,1,2\) | \(1,2,0\) | \(21/29,20/29;-1\) | \(41/348\) | \(11/174\) |
| \(0,1,3\) | \(1,3,0\) | \(12/13,5/13;-1\) | \(67/156\) | \(1/39\) |
| \(0,2,3\) | \(2,3,0\) | \(5/13,12/13;+1\) | \(3/52\) | \(55/156\) |
| \(1,2,3\) | \(2,3,1\) | \(21/29,20/29;+1\) | \(41/348\) | \(7/58\) |

The exact minimum of a linear dot-product difference
\( (q-p)\cdot n\) for two axis-aligned rectangles is
obtained independently on each coordinate: when
\(n_x\ge0\) use \(q_x^- -p_x^+\), otherwise
\(q_x^+-p_x^-\); apply the analogous rule for
\(n_y\). This gives the displayed positive rational
margins, with minimum \(1/39\).

Because the normal pairs are orthonormal and each
orientation is visited in the relevant complete
turn, CF1's exact forbidden-triple lemma shows
that **none** of the four three-cell subsets can
all be occupied. Therefore at most two of the
four cells can be occupied. This proves FCR.2.

## Executed finite checker

The short standard-library-only
[exact checker](computer-assisted/check_four_cell_rank.py)
evaluates all eight strict rectangle inequalities
with rational arithmetic, checks all four triples
and the positive margin \(1/39\), and rejects any
failed condition. The locally executed source has
SHA-256:

    0968608450ad0c8f68461cb5a926e2262cfd8021595e2eb39c7f26bc9b1cc03a

and Git blob:

    482405a2956ee5f59c2f350fdc61402fe6156be5

The fetched committed file's Git blob matches the
source that passed locally. The checker is
a verifier of *finite rectangle geometry*;
the short final inference uses CF1.

## Effect on the attempted global area program

On the exact 30-by-12 partition of the
\(5/2\times1\) rectangle, all 18 Pythagorean
angles in each handed turn produce 37,188
distinct-cell forbidden triples and 574
four-cell complete subhypergraphs (four
three-cell conflicts per quadruple).
Eight of those cliques can be chosen
vertex-disjoint. These counts come from
a bounded exploratory exhaustive search,
not a certified optimizer, and the valid
individual inequalities can be checked
independently as above.

**The global relaxation is still too weak.**
A floating-point HiGHS LP on this partition
has area optimum \(2.0347222\ldots\)
both before and after adding all 574
rank-two clique inequalities. A binary
MILP gives \(2.0277777\ldots\).
These are **diagnostics, not verified upper
certificates**; they show that even a sound
strengthening need not improve the objective
until new classes of interacting configurations
are incorporated. Neither LP outcome approaches
the published external \(1.765\) upper benchmark.

The current positive theorem is FCR.2, not a
global bound \(M\), nor a proof that an
arbitrary partial turn visits all four
specific rational frames. No Lean or CI
was run. More substantial progress requires
global component/occupancy coherence,
stronger higher-rank cuts, or a different
area-exclusion architecture.
