# Direction 3: an exact finite-angle exclusion over a whole placement box

**First-attempt result.** This certifies one positive-size region of hallway-placement space, not a sampled set of shapes. Eight supporting offsets vary independently through rational intervals. Every body in that region has area at most 709/480<8/5<M. A larger proposed box fails this particular exclusion and is recorded as a non-result. This is a seed certificate, not a complete parameter covering or an improved unrestricted bound.

The method is a robust, spatially allocated forbidden-union bound of Direction 2. It uses rational unit normals and exact ordinary area. Existing Notes 44--46 and the occupancy work remain prior finite-angle results; no claim is made that finite-angle upper bounds or interval branching are new methods. Labels D3 are local.

## 1. Universal parameter-box enclosure

Fix a bounded outer set B^+ containing every candidate in a specified parameter region. At each selected hallway frame, let its two unit-normal outer offsets be z_i,z_j; the forbidden quadrant has thresholds z_i-1,z_j-1. Suppose the parameter region supplies lower bounds z_i>=z_i^-.

Define the robust quadrant Q^- using the lower thresholds z_i^--1,z_j^--1. Then Q^- is contained in the true forbidden quadrant at **every** parameter in the region. Consequently

$$\boxed{S\subseteq B^+\setminus\bigcup Q^-,\qquad
|S|\le|B^+\setminus\bigcup Q^-|.}$$

Any additional outer constraints or unsampled hallway angles only reduce the admissible body. Connectivity is unnecessary for this upper bound: counting the total remaining envelope, including disconnected pieces, is safe here. This is distinct from claiming that the relaxed envelope is itself a valid continuous-motion sofa.

For rational B^+, rational unit normals and rational lower offsets, the displayed upper bound is an exactly computable rational area. Inclusion-exclusion of clipped polygons is one algorithm. Ordering all wall-line intersection abscissae and integrating the selected affine upper/lower fiber lengths is an independent one. No quadrature or angular sampling error enters either finite computation.

## 2. An explicit eight-dimensional box

Let B_0=[0,12/5] times [0,1] and B^+=[0,49/20] times [0,1]. Choose the two lower-turn orthonormal pairs

$$(3/5,4/5),\ (-4/5,3/5),\qquad
(4/5,3/5),\ (-3/5,4/5),$$

and their reflections across the horizontal axis for two upper-turn positions. The order of the two normals in a frame does not affect the L-hallway. These are four orientations that a full-turn body necessarily visits.

For each of the eight normals n_i, let z_i^0=h_{B_0}(n_i), and suppose its hallway outer offset satisfies

$$\boxed{|z_i-z_i^0|\le1/20\qquad(i=1,\ldots,8).}$$

No equality with the support of B_0 is imposed; all eight coordinates may vary independently. Actual canonical supports are allowed, but the upper theorem also covers nontight raw placements. The only additional requirement is S subset B^+.

**Theorem D3.1.** Every measurable S in B^+ meeting these four hallway placements satisfies

$$\boxed{|S|\le709/480<8/5<M.}$$

Thus every compatible full-turn body in this parameter box is strictly subcritical. This does not say that every possible competitor belongs to the box.

## 3. Hand calculation of the entire robust envelope

Use z_i^-=z_i^0-1/20. For the two lower robust quadrants the wall inequalities are

$$(3/5)x+(4/5)y<119/100,\qquad(-4/5)x+(3/5)y<-9/20,$$

and

$$(4/5)x+(3/5)y<147/100,\qquad(-3/5)x+(4/5)y<-1/4.$$

Their union below the upper strip line has nonnegative roof

$$n(x)=\max\left(0,
\min(119/80-3x/4,\ 4x/3-3/4),
\min(49/20-4x/3,\ 3x/4-5/16)\right).$$

The two upper robust quadrants are exact reflections under y -> 1-y. Hence the remaining fiber length is (1-2n(x))_+.

The function n is symmetric about x=6/5. On the left surviving part it has the explicit pieces

$$n(x)=\begin{cases}
0,&0\le x\le5/12,\\
3x/4-5/16,&5/12\le x\le3/4,\\
4x/3-3/4,&3/4\le x\le15/16.
\end{cases}$$

These follow by ordering the two increasing wall lines; their crossing is at x=3/4, and their companion descending lines are higher on this range. Between 15/16 and 117/80, at least one of the two lower tent roofs is at least 1/2. Indeed the first has height at least 1/2 on [15/16,79/60], the second on [13/12,117/80], and these intervals overlap. Thus no positive fiber length survives throughout that central interval.

The left lobe area is therefore

$$\int_0^{15/16}(1-2n)_+dx
=5/12+1/4+3/64=137/192.$$

Reflection gives an identical right lobe inside [0,12/5]. The extra interval [12/5,49/20] has length 1/20 and n=0, so its possible contribution is 1/20. The full robust upper envelope has exact area

$$2(137/192)+1/20=\boxed{709/480}.$$

The gap to 8/5 is 59/480>0. This proves the entire offset-box assertion; it is not a test at its midpoint. Strict/open wall boundaries have planar area zero.

## 4. Failure control and actual computational check

Repeating the same robust construction with radius 1/10 and outer box width 12/5+1/10 gives exact upper area 117/70>8/5. The larger box is **not excluded by this certificate**. That is not evidence of a feasible body of this area, and not a counterexample to optimality: it only identifies a limit of this coarse enclosing region.

The rational checker evaluates both boxes by polygon clipping/inclusion-exclusion and independently by vertical line-order integration, obtaining the same fractions. The smaller result has the hand derivation above, so a proof of this particular branch does not depend on trusting the script.

## 5. Global role and remaining gate

The result demonstrates an actual area exclusion over a nonzero parameter region without assuming cap regularity, symmetry, balancedness, or full continuous feasibility of the relaxed set. It is not a new global bound and does not yet localize near-maximal bodies close to the reference. Other placement boxes, variable width/translation charts and a sharp residual region remain uncovered.

A concrete continuation would use the critical-face reduction of Direction 1 where the robust box is inconclusive, and overlap-safe spatial certificates from Direction 2. It must retain a complete list of covered and residual parameter regions. Merely running the test on many boxes and reporting successful cases would not constitute a proof.

The Kallus--Romik finite-position program (arXiv:1706.06630) is the primary methodological precedent. The new calculation here is deliberately small and fully displayed. No external claimed ambidextrous bound is used. No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was run.
