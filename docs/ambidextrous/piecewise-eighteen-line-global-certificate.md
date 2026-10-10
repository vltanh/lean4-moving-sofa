# Exact 18-line area integration for a global four-hallway branch certificate

**Scope.** This derives the mathematical correctness of a faster exact area oracle for the existing O'Keefe four-\((3,4,5)\)-hallway eight-offset certificate, in CP's canonical-support reduced parameter box. The analytic result is not a new sofa-area upper bound until a **complete** box tree has been replayed. It is a feasible *global* proof-search technique: no reference shape, symmetry, smoothness, or selected numerical placement is assumed. Labels PL are local.

## 1. Every box-enlarged fiber is an interval controlled by 18 affine lines

Fix the incoming \(B=[0,5]\times[0,1]\). At each of the four hallway frames \(j\), with angle normals \((c_j,s_j)\), \((-s_j,c_j)\) and appropriate vertical reflection on the upper hand, let the offset pair range independently over \([a_j^-,a_j^+]\times[b_j^-,b_j^+]\).

The union of all placed hallways in this offset rectangle is exactly
\[
\widehat X_j=
\{cx+sy\le a_j^++1,\ -sx+cy\le b_j^++1,\
 (cx+sy\ge a_j^-\ \lor\ -sx+cy\ge b_j^-)\},
\tag{PL.1}
\]
with the reflected coordinate forms for upper-handed hallways. Their common intersection \(C(E)=B\cap\bigcap_j\widehat X_j\) contains the intersection at **every single** parameter vector in E.

Reflecting the upper two frames by \(y'=1-y\), define for each hand \(t\in\{-,+\}\):
\[
A_t(x)=\min\!\left(1,\min_{j\in t}
 \frac{a_j^++1-c_jx}{s_j},
 \frac{b_j^++1+s_jx}{c_j}\right),
\]
\[
N_t(x)=\max\!\left(0,\max_{j\in t}
 \min\left\{\frac{a_j^--c_jx}{s_j},
            \frac{b_j^-+s_jx}{c_j}\right\}\right).
\]
Every vertical fiber of \(C(E)\) is a closed interval (possibly empty) whose exact height is
\[
\boxed{\ell_E(x)=\left[
\min(A_-(x),1-N_+(x))
-\max(N_-(x),1-A_+(x))\right]_+.}
\tag{PL.2}
\]
There are **16 affine wall-height functions** (two outer and two inner per frame), plus the fixed lines \(y=0,y=1\). Each branch of PL.2 is identically zero or an affine difference of two of these **18** lines. Therefore a branch can change only where a pair of these 18 lines intersects.

## 2. Exact rational knot integration, with no hidden switch interval

Let every offset endpoint be a **rational** number; branch-and-bound dyadic boxes have this property. All four chosen normals have rational \(c_j,s_j\in\{3/5,4/5\}\). Hence each wall-height line has exact rational coefficients. The area
\[
|C(E)|=\int_0^5\ell_E(x)\,dx
\]
is a finite sum of trapezoids over exact rational intersections of the 18 lines. Even degenerate coincident walls or point contacts do not affect the statement; parallel/identical pairs simply contribute no proper crossing.

For fast bounded-integer evaluation, choose \(Q=2^{32}\), round each upper offset endpoint **upward** to an integer multiple of \(1/Q\), and each lower endpoint **downward**. These changes only enlarge \(C(E)\). Since the 3–4–5 slopes are \(\pm4/3,\pm3/4\), each of the 18 resulting lines can be written in uniform integer form
\[
12Y=A_iX+B_i,\qquad X=Qx,\ Y=Qy,
\tag{PL.3}
\]
where \(A_i\in\{0,\pm16,\pm9\}\) and \(B_i\in\mathbb Z\).

Every nonparallel pair intersects at
\[
X_{ij}=\frac{B_j-B_i}{A_i-A_j}.
\]
For each intersection in \((0,5Q)\), insert **both**
\(\lfloor X_{ij}\rfloor,\lceil X_{ij}\rceil\), together with \(0,5Q\), and sort/merge. Then every interval between **consecutive integer knots of width at least two** contains **no crossing** of any pair of wall-height lines. All their orderings are constant. Accordingly \(\ell_E\) is *exactly affine* (or identically zero) on each such interval. A crossing in a nonintegral position is confined to a one-unit interval.

At any integer knot X, compute a directed **upper integer fiber height** \(H(X)\ge Q\,\ell_E(X/Q)\) using ceilings of the outer-wall expressions and floors of the inner-wall expressions, with the final min/max/positive-part operations performed in their safe monotone order. The arithmetic uses only integers.

If consecutive knots have width \(w\ge2\), the **whole** area contribution is at most the trapezoid
\[
\frac{w[H(X_l)+H(X_r)]}{2Q^2}.
\tag{PL.4}
\]
On a width-one knot cell, the fiber height is Lipschitz because every wall-height line has slope of absolute value at most \(4/3\), and the min/max operators preserve the maximum Lipschitz constant. Therefore \(\ell_E\) has Lipschitz constant at most \(8/3\). Its area over such a cell is at most
\[
\frac{\max(H(X_l),H(X_r))+3}{Q^2}.
\tag{PL.5}
\]
The extra **three** integer height units dominate \((8/3)\times1\) exactly. This protects against an active-wall switch *within* the one-unit cell without any numerical tolerance.

Summing PL.4–PL.5 proves a completely **rigorous upper bound** on the box-enlarged *total* area. Since the inner/outer rounding and every subsequent height rounding are conservative, this calculation remains valid for **every real hallway placement inside the original offset box**. No polygon-contact component graph is required when this total-area upper bound passes.

## 3. Reusable global certificate soundness

CP1 proves that for **each connected component** in the unrestricted four-hallway relaxation, one may translate its attained left and bottom extrema to zero and tighten all hallway outer supports. This preserves its area, and its eight canonical support offsets lie in the rational CP root box. Thus a complete dyadic partition of that root whose every leaf either

1. violates an explicitly proved necessary convex-support inequality, or
2. has an upper total-area bound \(\le T\) from PL.4–PL.5,

proves the **global connected-component area bound** \(G\le T\).

Completeness is indispensable: a prefix of a tree with an unvisited stack, an undecided depth-cap leaf, or a floating-point area comparison proves no global threshold. A leaf check must use the box endpoints reconstructed from the root and the split path, not trust claimed bounds attached to the leaf.

All 18-line comparisons, intersection floors/ceilings, upper-height evaluations and the threshold test can be performed in signed 128-bit integers at the fixed scale \(Q=2^{32}\), because the root offsets lie in bounded rational intervals and all slopes have small integer coefficients. An implementation must still check the bounds on maximum dyadic depth and intermediate magnitude; this note does not claim an independently verified machine implementation until replay.

## 4. Actual bounded performance and limits

In a local **15-second** comparison at target \(T=7/4=1.75\), the earlier conservative whole-cell oracle processed approximately **69,287** nodes and the new 18-line oracle approximately **415,442** nodes (same eight-dimensional root, support feasibility pruning and DFS splitting). This is a measured **sixfold search-throughput improvement**, not a sixfold reduction in the eventual tree's size. A separate full-tree run is still in progress as a bounded, resumable **discovery search**. It is not complete and must not be represented as a global theorem.

The original target \(A_F\le33/20=1.65\) is **not** implied by even a completed four-angle \(7/4\) certificate. The known connected four-angle witness is above \(M\approx1.645\); the separate exact MW and AW34 witnesses show that even the 32- and 34-step higher-angle meshes admit connected finite-position examples above 1.65. To prove the full-turn premise one needs still denser angles or genuinely new valid continuum constraints, and complete covering of the higher-dimensional offset domain.

No long-running search prefix, numerical witness, or source-code test substitutes for the mathematical area theorem PL or a complete certificate.
