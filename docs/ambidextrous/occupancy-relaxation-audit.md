# A necessary correction to the optimality-only occupancy plan

This audits the proposed computer-assisted route before a large search. It does not change CF2. It identifies a structural floor for the unconditioned LP and the extra geometric information needed to overcome it. Labels OR are local; baseline `924ee7fef66b4cb1b9d5d9ba356a41d6adb250c7`.

## 1. The fractional barrier

Partition a region Omega into finitely many cells of areas a_i>=0. Consider exactly

$$
0\le z_i\le1,\qquad z_i+z_j+z_k\le2
$$

for any collection of triples of distinct cells, maximizing sum_i a_i z_i.

**Proposition OR1.** The LP optimum is at least `(2/3)|Omega|`, because the constant assignment z_i=2/3 satisfies every triple, at every angular and spatial resolution.

For equal cells the same barrier follows directly from CF2. Put L=sum_e lambda_e and c_i=sum_{e containing i}lambda_e. Then sum_i c_i=3L, and the valid scalar inequality

$$
\frac23c+(1-c)_+\ge\frac23\qquad(c\ge0)
$$

gives

$$
2L+\sum_i(1-c_i)_+\ge2N/3.
$$

For c<=1 the left scalar expression is 1-c/3; for c>=1 it is 2c/3. This also corrects an unnecessary, incorrectly written scalar sub-inequality in the first draft; the constant feasible vector and the conclusion were unaffected.

On [0,4] times [0,1], the barrier is 8/3. Even with the actual width-W rectangle it is 2W/3, above the target when W>=3M/2. This is not a feasible sofa of that area: it is a defect of the fractional relaxation. Additional angles or finer cells alone cannot remove it.

## 2. Repeated witnesses and the important terminal distinction

In general CF1 permits q=r. Two cells whose point differences exceed one in both frame coordinates cannot both meet the body, giving a pair cut z_i+z_j<=1.

However, such a two-point hallway conflict is impossible for two points in the incoming unit-height strip and the conventional angle sectors. For a displacement (dx,dy) with |dy|<=1 and dx>=0, its second coordinate in either frame `(c,s),(-s,c)` or `(c,-s),(-s,-c)` is at most one. For dx<0 its first coordinate is at most one. Here c,s>=0. Hence it cannot exceed one in both coordinates. Thus repeated-witness hallway cuts do not cure OR1 in this normalized global problem.

**Terminal-strip constraints are different.** At a terminal normal n, the whole body lies in a strip of width one. If every difference between points in cells P,Q has scalar product with n greater than one, P and Q are incompatible. Only one normal is tested. These pair cuts are valid and can be nontrivial in the incoming strip.

Even an arbitrary collection of pair and triple cuts leaves z_i=1/2 feasible when there are no forced cells or geometric exclusions. Its optimum is therefore at least |Omega|/2. On an area-four box this is still two. Mandatory occupied witness regions, empty regions, stronger configuration cuts, or branching are needed as well.

## 3. Mandatory extreme witnesses

Normalize the horizontal projection to [0,W]. Compactness supplies points (0,y_l) and (W,y_r) with both heights in [0,1]. For a width box [W_0,W_1], the body therefore meets both witness rectangles

$$
\{0\}\times[0,1],\qquad [W_0,W_1]\times[0,1].
$$

They can be represented by two zero-area variables fixed to one. A forbidden triple involving one witness then becomes a pair constraint on ordinary occupation variables; with two witnesses it can force a cell to be empty. Witnesses may be refined by branches on their heights or locations, provided the branches cover all possibilities.

This is a geometric premise supplied by compactness and normalization, not rounding a fractional LP solution. Terminal-strip pair cuts and these forced witnesses are the first strengthened model being tested.

## 4. Exact branching and the local boundary

A split on an ordinary cell's true meet indicator covers all bodies: either it is zero or one. Both children must be retained unless independently infeasible or upper-bounded. A tree with unresolved leaves is not a global certificate.

Alternatively branch directly on support/placement boxes and compute interval upper bounds on ordinary finite-position envelope area. Both strategies are related to the finite-position approach of Kallus and Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630; no novelty claim is made for branching or LP dual certificates.

A residual set also cannot be declared a local candidate neighborhood without a geometric implication to the topology and exact hypotheses of the local theorem. Uniform support closeness does control derivative traces on compact arcs where the reference support is continuously differentiable, but not across its exposed-face jumps, and it does not impose a curvature cap. Finite sampled support closeness additionally needs interpolation/error control. The existing restricted area theorems are not automatically an unrestricted local theorem.

## 5. Decision and proof boundary

Retain CF2 where it is effective, but do not launch the distinct-triple-only LP on the entire search region expecting refinement to close the proof. Test forced extreme witnesses and terminal-strip cuts, with every numerical dual converted to a separately checked rational upper bound. If those remain weak, use integral or support-box branching rather than reporting a floating-point optimization result as closure.

This correction concerns the computational method. It proves neither the optimal value nor the geometric admission required by the existing auxiliary calibrations. No CI or Lean/Lake compilation is used.
