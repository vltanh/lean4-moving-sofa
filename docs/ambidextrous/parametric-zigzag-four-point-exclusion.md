# A width-uniform forbidden zigzag, valid across the competitive full-turn domain

**Theorem ZZ1 (four-point zigzag exclusion).**
Let \(S\subset\mathbb R\times[0,1]\) be
any compact sofa able to complete both conventional
right-angle hallway turns in a common incoming
horizontal orientation. Fix any \(W>15/8\)
and any horizontal translation \(x_0\).
Among the four alternating points

\[
\boxed{
(x_0,0),\
(x_0+W/3,1),\
(x_0+2W/3,0),\
(x_0+W,1),
}\tag{ZZ.1}
\]

**at most two can belong to S**.

This is an exact **global structural theorem**
on actual point configurations, without convexity,
curvature, reference proximity, symmetry, smoothness,
or an assumed maximizing shape. It is stronger than
the case \(W=5/2\) in
[FCR](four-cell-rank-cut.md).
The sharp optimal area \(M\) is **not proved**.

## 1. Four elementary rational-frame certificates

Write the four points as \(P_0,\dots,P_3\)
in the order in ZZ.1. A feasible sofa
cannot contain a triple \(p,q,r\)
whose point differences simultaneously
have \((q-p)\cdot u>1\) and
\((r-p)\cdot v>1\) for any genuinely
visited hallway normal pair \((u,v)\);
this is the elementary CF1 forbidden-triple
criterion.

For each three-point subset, choose
the following complete-turn rational
frame and order. The two final columns
give the **exact dot products** before
subtracting one.

| Triple | \(p,q,r\) | \(u,v\) | \((q-p)\cdot u\) | \((r-p)\cdot v\) |
|---|---|---|---|---|
| \(0,1,2\) | \(1,2,0\) | \(u=(21,-20)/29,\ v=(-20,-21)/29\) | \((7W+20)/29\) | \((20W/3+21)/29\) |
| \(0,1,3\) | \(1,3,0\) | \(u=(4,-3)/5,\ v=(-3,-4)/5\) | \(8W/15\) | \((W+4)/5\) |
| \(0,2,3\) | \(2,3,0\) | \(u=(3,4)/5,\ v=(-4,3)/5\) | \((W+4)/5\) | \(8W/15\) |
| \(1,2,3\) | \(2,3,1\) | \(u=(21,20)/29,\ v=(-20,21)/29\) | \((7W+20)/29\) | \((20W/3+21)/29\) |

Every normal pair is orthonormal, with its
proper handedness. The first two rows use
the *upper* reflected conventional turn,
the last two rows the *lower* turn.
All four frames are genuinely visited when
both turns are complete.

Every one of the eight dot products is
**strictly larger than one** for \(W>15/8\);
the only largest threshold comes from
\(8W/15>1\). Consequently none of the
four possible triples can belong to S.
That establishes ZZ1. QED.

The point theorem is translation-invariant
and applies to any prospective four
points of that alternating form. It does
not require that their four x-coordinates
span the *entire* horizontal projection of S.

## 2. A robust positive-area version at all competitive widths

Put \(\alpha_i=i/3\) for \(i=0,1,2,3\),
and let \(e>0\). Form four squares

\[
\begin{aligned}
C_0(W,e)&=[0,e]\times[0,e],\\
C_1(W,e)&=[W/3-e,W/3]\times[1-e,1],\\
C_2(W,e)&=[2W/3-e,2W/3]\times[0,e],\\
C_3(W,e)&=[W-e,W]\times[1-e,1].
\end{aligned}\tag{ZZ.2}
\]

**Theorem ZZ2 (uniform thickened zigzag).**
Whenever S admits both complete turns,
the binary occupancy indicators of these
four positive-area squares satisfy

\[
\boxed{z_0+z_1+z_2+z_3\le2}
\tag{ZZ.3}
\]

under **either** of the following regimes:

- **For every \(W\ge2\)**, take
  \(e=1/64\). Every required ordered
  rectangle-dot-product difference
  exceeds one by at least \(31/960\).
- **For every \(W\ge23/10\)**, take
  \(e=1/12\). All four squares are still
  disjoint and the minimum exact
  margin is \(1/58\).

The second regime includes horizontal
widths near Romik's \(2.334\ldots\);
these are not merely distant wide-sofa
examples.

**Proof of ZZ2.** The minimum of
\((q-p)\cdot u\) over points p,q
in two axis-aligned squares is obtained
by independently selecting the appropriate
extreme coordinate according to each
sign of u. The same holds for v.
For every one of the eight dot-product
tests in the ZZ1 table, that minimum
is **affine in W**, with a *strictly
positive exact rational coefficient*.

Hence it suffices to evaluate all eight
minimum margins at the threshold
\(W=2\) (when \(e=1/64\)) or
\(W=23/10\) (when \(e=1/12\)).
The direct Fraction-based evaluator
[check_parametric_zigzag_rank.py](computer-assisted/check_parametric_zigzag_rank.py)
independently reconstructs each
affine coefficient, asserts its strict
positivity, proves that the four
squares are disjoint, and verifies
every endpoint margin.

It reports respectively
\(31/960\) and \(1/58\) as the
least strict margin. Because the slopes
are positive, all eight inequalities
remain strict at *every larger real W*
without numerical sampling or an
unverified interval extrapolation.
Each of the four triples is impossible
for its chosen hallway frame.
Thus at most two squares are occupied,
proving ZZ.3. QED.

The executed checker source SHA-256 is

    f09acdd281c78fff138905b576f300d728f660ebcaa52911067aea1d56c6f8f9

and its verified committed Git blob is

    0f981847c17f2c37a7c8d40dfff15c64d413c970

with the fetched blob identical to the
locally executed exact source.
No Lean, CI or global optimizer is
part of the result.

## 3. What this does and does not change

The result is now **width-uniform across
every known competitive full-turn width**:
the branch's analytic AW theorem already
excludes area \(\ge M\) when \(W\le2\).
It provides a sound *higher-order* constraint
for spatial partition methods, based only
on actual hallway feasibility and
positive-area occupied regions.

However the total area of four small
squares is not large enough to imply a
competitive global upper bound.
The exploratory \(30\times12\) LP audit
in [FCR](four-cell-rank-cut.md)
shows that adding even hundreds of
rank-two cuts did not improve the
coarse-grid optimum. ZZ1/ZZ2 therefore
do **not** prove the sharp sofa conjecture,
identify an optimizing shape, or
eliminate the general opposite-face class.

**Next acceptance gate:** show how the
zigzag obstruction interacts with
actual large-area density at *many*
translations/scales so that an exact
ordinary-area bound improves on the
external \(353/200=1.765\) result.
Absent such an aggregation, pursuing
additional isolated forbidden patterns
is not sufficient progress.
