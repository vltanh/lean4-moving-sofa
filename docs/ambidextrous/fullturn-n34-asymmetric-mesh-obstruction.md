# Exact asymmetric n=34 finite-hallway obstruction to the proposed global 1.65 certificate

**Theorem AW34 (finite-placement only).** The finite relaxation using both handed hallway families at the rational angles
\[
t_j=2\arctan(j/34),\qquad j=1,\dots,33,
\]
and an additional **exact \(45^\circ\)** frame in each handed family, admits a compact, **connected** set of area
\[
\boxed{|E|\ge\frac{4125119548180921069}{2500000000000000000}
=1.6500478192723684\ldots>\frac{33}{20}.}
\tag{AW34.1}
\]
Consequently \(A_{34}>33/20\). A complete branch-and-bound search with **only these orientations**, however expensive, cannot prove \(A_{34}\le33/20\). This is a finite-position competitor; **no continuous turning motion between the sampled positions is asserted**.

This sharpens [the n=32 symmetric reference-offset obstruction](fullturn-n32-rational-mesh-obstruction.md). Unlike that example, the n=34 witness uses *independent* placements for the two hands and is asymmetric. Reference placements at n=34 give an area below 1.65, but they are **not the maximizers over all placements**.

## 1. Exact input and hallway interpretation

The [frozen rational input](computer-assisted/finite-mesh-n34-witness.json) consists of 136 integers divided by \(Q=10^{12}\). They specify two translation offsets for each of the 34 lower and 34 upper hallway frames, in the order
\[
(f^-_1,\ldots,f^-_{34};g^-_1,\ldots,g^-_{34};
 f^+_1,\ldots,f^+_{34};g^+_1,\ldots,g^+_{34}).
\]
For \(1\le j\le33\), the orthonormal lower-frame normals are
\[
n_j=\left(\frac{34^2-j^2}{34^2+j^2},
           \frac{68j}{34^2+j^2}\right),\qquad
n_j^\perp=(-n_{j,y},n_{j,x}).
\]
The last entry of every 34-element block uses the *exact*, irrational \(45^\circ\) frame \((1,1)/\sqrt2,\,(-1,1)/\sqrt2\). The upper family is the vertical reflection of individually placed lower-type frames, but its translation offsets are **independent**.

For each frame with offsets \(f,g\), the actual closed unit L-hallway is the set of points p satisfying
\[
p\cdot n\le f,\quad p\cdot n^\perp\le g,\quad
(p\cdot n\ge f-1\ \lor\ p\cdot n^\perp\ge g-1).
\tag{AW34.2}
\]
The offsets defining the hallway do **not** need to equal the support function of the eventual intersection. Thus all 136 input numbers unambiguously specify legitimate finite hallway placements without an unproved support-tightness condition.

Intersect all 68 hallways with the incoming strip and the explicit rectangle
\[
B=[-13/10,13/10]\times[0,1].
\]

## 2. Full real-fiber lower bound and connectivity

For any fixed x, each lower-handed frame imposes two affine outer roof bounds and excludes the quadrant below the minimum of two affine inner roof bounds. Intersecting all lower frames gives a closed lower survivor interval \([n_-(x),a_-(x)]\), and reflecting the upper family gives \([1-a_+(x),1-n_+(x)]\). The exact common fiber is
\[
\left[\max(n_-(x),1-a_+(x)),
      \ \min(a_-(x),1-n_+(x))\right],
\tag{AW34.3}
\]
or empty. No concavity of the body or continuous hallway motion is assumed.

The [independent rational checker](computer-assisted/certified_n34_asymmetric_witness.py) partitions B's horizontal interval into **1,000,000 closed rational cells**, each of width \(13/5{,}000{,}000\). On each entire cell it computes:

- a directed **lower** bound on each outer roof via the monotonicity of the two affine walls;
- a directed **upper** bound on each forbidden niche roof via the minimum of the respective affine upper bounds;
- the consequent directed **lower** bound on the vertical fiber length.

The rational 34-step angle normals are exact. For the exact \(45^\circ\) frame, integer square roots enclose \(Q\sqrt2\) between consecutive integers; the checker propagates these **outward** to every wall expression, rather than replacing \(45^\circ\) by a nearby rational angle. The area summation uses integer arithmetic, not midpoint quadrature.

A cell is retained for a **connected** area certificate only when its upper and lower interval bounds guarantee that **every x in the whole cell** has \((x,1/2)\) in its fiber. The largest such contiguous run has
\[
902937\text{ cells},\qquad
x\in\left[-\frac{5833633}{5000000},\frac{1476137}{1250000}\right].
\]
Every fiber throughout this interval is an interval containing the same horizontal segment, so the set it defines is compact and connected.

The exact **lower** fiber-length integers over these retained cells sum to
\[
\boxed{\sum_{\rm run}L_i=634633776643218626.}
\]
Consequently its area is at least
\[
\frac{634633776643218626\cdot2600000}{10^{24}}
=\frac{4125119548180921069}{2500000000000000000}
=\frac{33}{20}
+\boxed{\frac{119548180921069}{2500000000000000000}}.
\tag{AW34.4}
\]
This is a **strict rational certificate** for a connected *finite-position* body.

## 3. Independent whole-cell regressions and limitations

The same 136 frozen exact rational support offsets were checked with three x-partitions:

| Whole x-cells | Rigorous lower bound for one connected component |
|---:|---:|
| 200,000 | 1.650027045892284 |
| 1,000,000 | **1.6500478192723684** |
| 2,000,000 | 1.6500504160399994 |

The increasing lower bounds are consistent but are not the mathematical premise: the exact one-million-cell integer sum in (AW34.4) suffices. The original discovery search had 16 completed independent-hands optimizations in approximately 20 seconds. Its floating-point objective has **no role** in checking (AW34.4); the checker only reads the frozen 136 rational integers.

This shows a crucial certificate-design barrier: **even when the reference support configuration passes an n=34 local test, the complete global finite-position optimum is greater than 1.65**. We must search denser meshes (or add valid virtual/continuum constraints) and cover **all** asymmetric translated hallways. A successful local optimizer below 1.65 says nothing about that covering.

This does not prove that n=40,48,64 or any other mesh succeeds. The global premise \(A_F\le33/20\), Romik's exact optimality, and the unrestricted partial-turn \(1/6\) gain remain **unproved**. Neither large CI nor Lean compilation nor an optimizer-derived upper bound is claimed.
