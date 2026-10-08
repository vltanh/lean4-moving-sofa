# Clearance-free, univariate certification of rational two-handed motions

**Status (2026-10-08).** This is an exact **feasibility-decision theorem** for the rational-motion witnesses of [RP1–RP3](rational-polyomino-motion-witness-completeness.md). Every collision test for one axis-aligned rational square along one rational Cayley-rotation/affine-translation path reduces to finitely many **univariate rational polynomial sign tests of degree at most five**. It includes contact with hallway walls, nonmonotone motion, and collisions occurring on square edges but at no vertex. It does **not** improve the known area upper bounds, prove Romik optimal, or exhibit a larger sofa. Do not mistake exact verification of a proposed motion for a global geometry optimizer.

It refines the earlier RP2 general quantifier-elimination observation to an explicit small-degree calculation. Its use of physical hallway placements—not support-tightened caps—makes it applicable to partial turns and arbitrary rational backtracking histories. A standard-library rational-interval proof checker for strictly robust paths already exists in [RP](computer-assisted/check_rational_motion_witness.py). The new [exact all-time checker](computer-assisted/check_univariate_rational_motions.py) instead uses SymPy's **exact real-root isolation** and requires **no positive clearance**. Its algebraic test is independent of the sampling diagnostics used in previous searches.

## 1. The two physical hallway predicates

Work in the fixed physical coordinates
\[
H_-=\{X\le1,\ Y\le1,\ (X\ge0\ \vee\ Y\ge0)\},\qquad
H_+=\{X\le1,\ Y\ge0,\ (X\ge0\ \vee\ Y\le1)\}.
\]
Thus the *open* inner forbidden region is \(X<0,Y<0\) for the lower hallway and \(X<0,Y>1\) for the upper one. Outer-wall failures are respectively \(X>1\) or \(Y>1\), and \(X>1\) or \(Y<0\).

A rational motion piece on \(s\in[0,1]\) has the precise form
\[
p\longmapsto R(s)p+a(s),\qquad
R(s)=R_0
\begin{pmatrix}
(1-q^2s^2)/D & -2qs/D\\
2qs/D &(1-q^2s^2)/D
\end{pmatrix},\qquad
D=1+q^2s^2>0,
\]
\[
a(s)=a_0+s(a_1-a_0),
\]
where \(q,R_0,a_0,a_1\) are rational and \(R_0\) is a rational special-orthogonal matrix. Any two adjacent rational rotation knots with relative angle not 180 degrees determine \(q=\sin\Delta/(1+\cos\Delta)\in\mathbb Q\) exactly, thereby fixing this *specific* Cayley interpolation. If an intended path winds through a longer angle, its list of rational knots must encode that winding; endpoints alone never do.

For a *fixed* rational body point \(p\), clearing the positive denominator \(D\) yields
\[
X(s,p)=\frac{A_p(s)}{D(s)},\qquad
Y(s,p)=\frac{B_p(s)}{D(s)},
\quad A_p,B_p\in\mathbb Q[s],\quad
\deg A_p,\deg B_p\le3.
\tag{UV.1}
\]
The degree-three term comes only from the product of the quadratic denominator with the affine translation.

## 2. Every open inner collision can be moved to a square edge

Let \(C\) be one closed rational square. At a fixed motion time, its image is a convex rotated square. If some interior image point lies in the lower forbidden quadrant \(X<0,Y<0\), translate that point inside the image along the physical vector \((-1,-1)\) until the image boundary is reached. Both forbidden inequalities stay **strict**, so the boundary point is also forbidden. For the upper forbidden quadrant \(X<0,Y>1\), use direction \((-1,+1)\) instead. Thus an open inner collision exists **if and only if it occurs at some point of an image edge**.

An outer-wall collision occurs at some square vertex, because \(X\) and \(Y\) are affine in the preimage point. Consequently the full shape-time check needs only finitely many vertices and edges, not two-dimensional quantifier elimination over all square points.

For one preimage edge \(p_\lambda=(1-\lambda)p_0+\lambda p_1\), \(0\le\lambda\le1\), let
\[
F(s,\lambda)=D(s)X(s,p_\lambda),\qquad
G(s,\lambda)=
\begin{cases}
D(s)Y(s,p_\lambda),&\text{lower},\\
D(s)(1-Y(s,p_\lambda)),&\text{upper}.
\end{cases}
\]
Both are affine in \(\lambda\). An inner collision is \(F<0\) and \(G<0\).

Set
\[
A=F(s,0),\quad B=F(s,1),\quad
C'=G(s,0),\quad E=G(s,1),
\]
\[
U=B-A,\quad V=E-C',\quad
H=U-V,\quad L=C'-A,\quad
T=AH+UL.
\tag{UV.2}
\]
These are rational polynomials in \(s\). The difference polynomials \(U,V,H\) have degree at most **two** because the common affine translation cancels, while \(L\) has degree at most three and \(\deg T\le5\).

### Lemma UV1 (exact edge predicate)

For any fixed \(s\), there is an edge parameter \(\lambda\in[0,1]\) with \(F(s,\lambda)<0\) and \(G(s,\lambda)<0\) if and only if **at least one** of the following finite strict alternatives holds:

1. \(A<0,\ C'<0\);
2. \(B<0,\ E<0\);
3. \(H>0,\ L>0,\ H-L>0,\ T<0\);
4. \(H<0,\ L<0,\ L-H>0,\ T>0\).

**Proof.** The maximum of the two affine functions in \(\lambda\) is convex and piecewise affine, with at most one interior break. Its minimum on the closed interval is attained at an endpoint or where \(F=G\). The endpoint cases are 1–2. When \(H\ne0\), the crossing occurs at \(\lambda_*=L/H\), and \(F(\lambda_*)=T/H\). The conditions \(0<\lambda_*<1\), \(T/H<0\) become precisely alternatives 3–4 after separating the two signs of \(H\). When \(H=0\), the max is affine or the two functions agree everywhere, and an endpoint is sufficient. This proof permits tangencies and coincident lines without discarding any open collision. \(\square\)

## 3. Exact all-time decision by one-variable real-root isolation

Each outer-wall failure at a vertex is a single rational polynomial inequality of degree at most three, after multiplying by \(D>0\). Each edge alternative of UV1 is a conjunction of strict rational polynomial inequalities of degree at most five.

For any finite family \(P_1,\dots,P_k\in\mathbb Q[s]\), their signs are constant on every component of
\[
(0,1)\setminus\bigcup_{j=1}^k\{P_j=0\}.
\]
The nonzero product of these polynomials has finitely many real roots. Exact rational isolation of its squarefree part supplies one rational sample from each open component. Checking the Boolean sign formula at these samples is **complete**, because a strict violation at any root or at time \(0\) or \(1\) persists at nearby interior times by continuity. Identically zero condition polynomials cannot satisfy their corresponding strict \(>0\) alternatives.

**Theorem UV2 (no-clearance all-motion decision).** For any finite union of rational axis-aligned squares with pairwise disjoint interiors and any finite pair of rational piecewise-Cayley/affine rigid-motion trajectories, the full hallway containment of every square over every *real* intermediate time is decidable by finitely many exact univariate rational polynomial sign tests of degree at most five. No monotonicity, curvature assumptions, positive clearance or angular time sampling are required.

To turn a positive containment verdict into a **complete ambidextrous-sofa witness**, separately verify the union is connected, check both paths share one incoming pose with initial identity rotation, check their final positions in the appropriate *straight outgoing arms*, and compute its exact ordinary rational area. Those checks are elementary rational linear geometry. The theorem does **not** claim two paths supplied as unconstrained endpoint rotations necessarily represent a particular longer winding: every intended intermediate arc must be in the input.

### Rational tests performed locally

The executed exact implementation passed:

- A connected small-square witness with **two full motions and deliberately nonmonotone lower turning**;
- A stationary path with boundary contact and **zero positive margin**;
- An inscribed \(3/5\)-by-\(4/5\) rectangle that touches the unit-square outer walls at two **interior rational time parameters** during rotation without crossing them;
- A square whose endpoint poses are both safe but which collides with an outer wall at the intermediate rational rotation \((\cos t,\sin t)=(3/5,4/5)\);
- A rationally rotated square with **no forbidden vertex** but a strictly forbidden segment in the interior of an edge.

An independent 59-case random rational-pose screen compared the exact verdicts with direct floating-point point/time evaluations and found no sampled collision mistakenly accepted as safe. These numerical point/time tests are only negative controls; **UV1 plus exact root isolation** supplies the actual all-time proof.

## 4. Implication for the sharp problem

[RP1–RP3](rational-polyomino-motion-witness-completeness.md) already shows that **if a genuine sofa of area \(>M\) exists**, there is one with rational grid-square geometry, full piecewise rational motions and a positive margin. UV2 improves the associated **validator**, and can also handle candidate motions that touch corridor walls exactly rather than first needing to modify or shrink the body.

This is a meaningful strengthening of the falsification route but **does not make exhaustive rational witness enumeration computationally viable**, prove that an improving shape exists, exclude any range of arbitrary real sofas, or prove \(M\) is optimal. The separate optimality program still needs a genuinely universal geometric argument. No CI, Lean/Lake build, dependency installation or formalization was performed.
