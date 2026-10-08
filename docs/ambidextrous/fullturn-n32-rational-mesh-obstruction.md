# Exact counterexample to certifying 1.65 with the n=32 finite hallway mesh

**Status.** This is a rigorously checkable *negative result* for the proposed **finite-angle global certificate**. It proves that the n=32 rational half-angle mesh, **even augmented by the exact \(\pi/4\) frames on both turns**, has a connected finite-hallway survivor of area **strictly greater than** \(33/20=1.65\). Therefore its global finite optimum \(A_{32}>33/20\). No branch-and-bound for *that fixed angle set* can certify \(A_{32}\le33/20\), regardless of search time. This is **not a continuously moving full-turn sofa** and does not contradict Romik's proposed optimality. Labels MW are local.

The proof combines the exact centered Romik support formulas and algebraic-root isolation already committed in [NL](one-sixth-fullturn-near-reference-certificate.md) with an **opposite-direction**, entire-cell **lower** area Riemann sum. The connection to existing results is direct: NL's local witness need not be optimized to generate a global lower obstruction; a finite-intersection witness only requires explicitly chosen placement offsets. The extra \(45^\circ\) angle is included to match the exact finite mesh of [FR](full-turn-compact-finite-reduction.md), not an angle omitted for convenience.

## 1. Fixed angles and actual ordinary hallway placements

Set \(n=32\). For \(j=1,\ldots,31\) take the rational *unit* frame normals
\[
(c_j,s_j)=\left(\frac{n^2-j^2}{n^2+j^2},\frac{2nj}{n^2+j^2}\right),
\quad(-s_j,c_j),
\]
and their vertically reflected upper-turn counterparts. Also take the exact \(45^\circ\) orthonormal pair \(((1,1)/\sqrt2,(-1,1)/\sqrt2)\), again in both handed families. The incoming horizontal strip is \(0\le y\le1\).

Every unit \(L\)-hallway is the union of two arms with support-coordinate constraints
\[
cx+sy\le f,\quad -sx+cy\le g,\quad
(cx+sy\ge f-1\ \text{or}\ -sx+cy\ge g-1).
\tag{MW.1}
\]
Every \(f,g\) below is a specific rational number, selected once for its frame. It need **not** be the actual support of the finite intersection; that is harmless when constructing a feasible finite placement.

Write \(Q=10^{12}\). For each rational frame, first enclose the exact centered Romik support \(f_*,g_*\) using NL's directed integer intervals
\[
f_j^-/Q\le f_*(t_j)\le f_j^+/Q,\quad
g_j^-/Q\le g_*(t_j)\le g_j^+/Q.
\]
Choose the **rational** hallway support thresholds
\[
F_j/Q,\ G_j/Q,\quad
F_j=\lfloor(f_j^-+f_j^+)/2\rfloor,\quad
G_j=\lfloor(g_j^-+g_j^+)/2\rfloor.
\tag{MW.2}
\]
Their values are exact once n is specified. All reference algebraic isolation in the underlying library uses exact polynomial signs, directed rational division and integer square roots.

At \(45^\circ\), choose the same rational offset \(F/Q\) for both normals, where
\[
s_-=\left\lfloor Q/\sqrt2\right\rfloor,\quad
R_-=1302051691595,\ R_+=1302051691636,
\quad
F=\left\lfloor
\frac{\bigl(\lfloor(R_-+R_+)/2\rfloor+Q/2\bigr)s_-}{Q}
\right\rfloor.
\tag{MW.3}
\]
This rational is close to \((R+1/2)/\sqrt2\), but **closeness is not part of feasibility**: any explicit rational f,g defines a unit hallway. Reflections of the lower hallway placements through \(y=1/2\) define the upper-handed placements. The resulting finite body is symmetric under \(y\mapsto1-y\); no symmetry restriction is imposed on \(A_{32}\), which can only be larger.

We also intersect with the fixed rational rectangle
\[
B=\left[-\frac{1167049}{10^6},\frac{1167049}{10^6}\right]\times[0,1].
\tag{MW.4}
\]
All choices are rational except the *directions* of the exact 45° frames, whose needed comparisons are bounded by integer square roots.

## 2. Exact fiber description, area and connectedness

For the 31 rational frame placements, let
\[
U(x)=\min\left(1,\inf_j\frac{F_j/Q-c_jx}{s_j},
                         \inf_j\frac{G_j/Q+s_jx}{c_j}\right)
\]
be the outer upper roof and
\[
N(x)=\max\left(0,\sup_j\min\left[
       \frac{F_j/Q-1-c_jx}{s_j},
       \frac{G_j/Q-1+s_jx}{c_j}\right]\right)
\]
be the lower forbidden-niche roof. Include the exact 45° frame in these min/max operations.

The intersection of **both** handed finite families with B is
\[
E=\left\{(x,y):x\in\operatorname{proj}_xB,\ 
\max(N(x),1-U(x))\le y\le\min(U(x),1-N(x))\right\}.
\tag{MW.5}
\]
Every fiber is a closed interval or empty; the full finite-hallway body is exactly described by these inequalities. Thus
\[
|E|=\int_{\operatorname{proj}B}
[\,2\min(U(x),1-N(x))-1\,]_+dx.
\tag{MW.6}
\]

Partition the exact x-interval into \(100000\) rational cells. The committed [checker](computer-assisted/certified_mesh_witness_165.py) evaluates **lower** cellwise bounds on U and **upper** cellwise bounds on N, by using the monotonicity of their affine wall expressions. For an angle with \((c,s)=(C/D,T/D)\), at x-cell endpoints \(X_l=Qx_l,X_r=Qx_r\), the following are exact directed **lower bounds** on Q times each outer roof:
\[
\left\lfloor\frac{F_jD-CX_r}{T}\right\rfloor,\qquad
\left\lfloor\frac{G_jD+TX_l}{C}\right\rfloor.
\tag{MW.7}
\]
Exact directed **upper bounds** on Q times the lower forbidden inner roof are
\[
\left\lceil\frac{(F_j-Q)D-CX_l}{T}\right\rceil,\qquad
\left\lceil\frac{(G_j-Q)D+TX_r}{C}\right\rceil.
\tag{MW.8}
\]
Take their minimum for each angle, then maximum over all angles. The 45° angle uses
\[
\frac{F/Q}{1/\sqrt2}=\sqrt2(F/Q),\quad
\frac{F/Q-1}{1/\sqrt2}=\sqrt2(F/Q-1).
\]
Its full-cell lower/upper bounds come from the exact inequalities
\(\lfloor Q\sqrt2\rfloor\le Q\sqrt2\le\lceil Q\sqrt2\rceil\).
All computed interval bounds apply to **every real x** in each cell, not just the midpoint.

The checker obtains uniform bounds \(U(x)\ge1/2,\ N(x)\le1/2\) over the entire rectangle, so the line segment \(\operatorname{proj}B\times\{1/2\}\) belongs to E. Every fiber contains that line, and therefore **E is connected**, not merely a disconnected sum of pieces.

Let \(L_i\) be the exact nonnegative integer lower bound on Q times the fiber length on cell i. The integer evaluator gives
\[
\sum_iL_i=:\mathcal L_{32}.
\tag{MW.9}
\]
Since every cell has the exact width \(23340980/Q\), the lower area certificate is
\[
|E|\ge\frac{23340980\,\mathcal L_{32}}{10^{24}}
=\boxed{
\frac{33}{20}
+\frac{293836885298769959}{6250000000000000000000}}
\ >\ \frac{33}{20}.
\tag{MW.10}
\]
In decimal this conservative **lower** bound is \(1.6500470139016479\ldots\), strictly larger than the target. No floating-point area or optimizing routine contributes to this claim.

The full source records the exact \(\mathcal L_{32}\), support choice at \(45^\circ\), and uniform midline inequalities. All products fit signed 64-bit because \(n\le512\), \(|F_j|,|G_j|<3Q\) and \(|X|<1.2Q\); Python integers give the exact final numerator. The stated range guards are executed.

## 3. What this forces upon a complete global \(1.65\) certificate

**Theorem MW1 (necessary mesh density).** The finite full-turn relaxation using
\[
\Theta_{32}=\{2\arctan(j/32):j=0,\ldots,32\}
\cup\{\pi/4\}
\]
on both handed families has a **connected** ordinary-area admissible competitor of area \(>33/20\). Thus \(A_{32}>33/20\). A purported whole-root branch certificate at this mesh with every leaf \(\le33/20\) must be erroneous. Any next computational search should use a denser angle set or independent valid continuum constraints.

The same construction at n=24 and n=28 gives lower areas \(1.652004166\ldots\) and \(1.650741452\ldots\), respectively. At n=34, these reference-based **lower witnesses** are below 1.65; this shows only that this specific family ceases to obstruct, **not** that \(A_{34}\le1.65\). No n=34 global certificate is claimed.

The global premise \(A_F\le33/20\) is still open. **Our executable exact supports and local NL certificate supply a concrete residual-search gate:** to prove the premise by support-box covering, one must discharge *every* feasible support box outside the NL radius \(7/10000\), or use the explicit full-mesh finite area upper certificate at some \(n\ge34\). Neither covering is available yet.

The finite witness is an example of independent translations at separate orientations; it has **not** been shown to traverse the intermediate hallways continuously. The user’s requested full-turn-to-partial-turn bound remains conditional on the unproved \(A_F\le1.65\).
