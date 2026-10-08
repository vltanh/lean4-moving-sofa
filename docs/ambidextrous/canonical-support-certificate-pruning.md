# Canonical-support pruning of O'Keefe's four-hallway certificate space

**Status and scope.** This derives a strict, mathematically lossless reduction of the **search domain** of the external four-hallway relaxation reviewed in [EX](external-four-hallway-certified-bound-review.md), using one fact from our own work: support-depth tightening of an actual **connected component**. No assumption about a sofa's curvature, motion monotonicity, reference shape or weighted-cap maximality is used. This applies to the original four-3–4–5-hallway *finite* relaxation, not just to fully turning sofas. Labels CP are local.

The new necessary scalar bounds enclose all canonical offset vectors in a rectangle whose **eight-dimensional volume is only \(10925/118013952\approx0.0000925738\)** times the original source search box. Additional joint convex-support inequalities reject more boxes. **Volume reduction is not a proved runtime speedup or an improved numerical area bound**. The original source's global theorem \(353/200\) and the positive finite-hallway witness \(>M\) are unchanged.

We have not rerun O'Keefe's 436-million-leaf certificate. The finite tests below used exact rational arithmetic in under five seconds; the proofs of the necessary bounds are hand arguments.

## 1. Strengthened optimization: all offsets can be support-tight

Let \(H=\mathbb R\times[0,1]\) be the incoming strip, and let \(X_j(u_{j1},u_{j2})\) be one of the four standard or vertically reflected proper 3–4–5 hallway placements from the external paper:
\[
X_j(u)=\{f_j\le u_{j1}+1,\ g_j\le u_{j2}+1,\
(f_j\ge u_{j1}\ \text{or}\ g_j\ge u_{j2})\}.
\tag{CP.1}
\]
Here \(f_j,g_j\) are the **affine** hallway coordinates, so both reflected cases include their correct constants. This formulation is algebraically equivalent to the union of the two closed hallway arms in the source paper.

For a nonempty compact connected \(S\subset H\cap\bigcap_jX_j(u_j)\), translate \(S\) so that its minimum x and minimum y coordinates are zero. Translate every placed hallway along with it; it remains a member of the same parameterized hallway family. Its translated copy \(S^\circ\) lies in
\[
[0,W]\times[0,H_0]\subset[0,5]\times[0,1]
\tag{CP.2}
\]
by the source's one-3–4–5-hallway width lemma, with \(W\le5,H_0\le1\). Both coordinate minima are attained, not necessarily at the same point.

Define a new offset pair at **every** selected orientation by
\[
\boxed{\hat u_{j1}=\max_{p\in S^\circ}f_j(p)-1,\qquad
\hat u_{j2}=\max_{p\in S^\circ}g_j(p)-1.}
\tag{CP.3}
\]
Because the old outer walls contain \(S^\circ\), both new offsets are no larger than the old offsets after the translation. Every point of \(S^\circ\) still meets both new outer bounds. Whichever original inner-wall alternative protected the point continues to protect it, because the corresponding inner threshold has only **decreased**. Thus \(S^\circ\subset X_j(\hat u_j)\) for all j simultaneously.

**Lemma CP1 (canonical-support reduction).** Let \(G\) denote the external paper's supremum over eight independent offsets of the **largest connected-component area**. Then \(G\) is unchanged if the supremum is restricted to configurations having all eight offsets of the support-tight form CP.3 for a nonempty compact connected component \(S^\circ\) with both coordinate minima zero.

**Proof.** For any original offsets, take a connected component of the finite intersection with maximal area (the intersection is compact, and there are finitely many polygonal components). Translate that component and tighten all four hallway offsets as above. It is contained in a connected component of the new intersection, whose area is at least the old component's area. The reverse inequality follows from restriction to a subset of the original parameter domain. Taking suprema proves equality. QED.

**Crucial certification distinction.** This is a change of **global search representation**, not a statement that every original eight-offset vector satisfies the inequalities below. A certificate may cover only the new canonical-support region **provided CP1 is included in its soundness argument**. Existing box leaf enclosures remain valid when applied to that region. Discarding arbitrary boxes from an *unchanged* source theorem without CP1 would be invalid.

## 2. Explicit dramatically smaller rational root box

Order the four positions as the source does:
\[
L_{\alpha_1},L_{\alpha_2},\rho L_{\alpha_1},\rho L_{\alpha_2},
\quad
(\cos\alpha_1,\sin\alpha_1)=(4/5,3/5),\
(\cos\alpha_2,\sin\alpha_2)=(3/5,4/5).
\]
The eight **affine** coordinates are
\[
\begin{array}{ll}
f_1=(4x+3y)/5,&g_1=(-3x+4y)/5,\\
f_2=(3x+4y)/5,&g_2=(-4x+3y)/5,\\
f_3=(4x-3y+3)/5,&g_3=(-3x-4y+4)/5,\\
f_4=(3x-4y+4)/5,&g_4=(-4x-3y+3)/5.
\end{array}
\tag{CP.4}
\]

Write \(a_1,b_1,a_2,b_2,a_3,b_3,a_4,b_4\) for the support-tight offsets CP.3, in that order. Since every point is in \([0,5]\times[0,1]\) and there exist points with x=0 and with y=0, their intervals satisfy:
\[
\boxed{
\begin{array}{c|rrrrrrrr}
 &a_1&b_1&a_2&b_2&a_3&b_3&a_4&b_4\\
\hline
\mathrm{lower}&-1&-1&-1&-1&-2/5&-1&-1/5&-1\\
\mathrm{upper}&18/5&-1/5&14/5&-2/5&18/5&-1/5&14/5&-2/5
\end{array}.}
\tag{CP.5}
\]
For example \((-3x+4y)/5\le4/5\) on the box, but at some \(p\in S^\circ\) with \(p_x=0\) this same affine coordinate equals \(4p_y/5\ge0\). Hence \(b_1\in[-1,-1/5]\), rather than its original root interval \([-4,4/5]\). Similarly \(g_3=(-3x-4y+4)/5\le4/5\), while at the leftmost actual point \(g_3\ge0\), giving \(b_3\in[-1,-1/5]\). For \(a_3\), a bottommost point has \(f_3=(4x+3)/5\ge3/5\) and the global box gives \(f_3\le23/5\), hence \(a_3\in[-2/5,18/5]\). The other six intervals follow identically by swapping the two rational angles.

Compare to O'Keefe's **unrestricted-placement** normalized root intervals
\[
([-1,23/5],[-4,4/5],[-1,19/5],[-5,3/5])^{\times2}.
\tag{CP.6}
\]
All intervals in CP.5 are contained in those of CP.6. The exact product of the eight ratios of interval lengths is
\[
\boxed{\frac{\operatorname{vol}_8(\mathcal B_{\rm canonical})}
{\operatorname{vol}_8(\mathcal B_{\rm original})}
=\frac{10925}{118013952}\approx9.25738\cdot10^{-5}.}
\tag{CP.7}
\]
Therefore **99.9907426% of the old root box's eight-dimensional volume is excluded from a canonical-support search**, without changing its global connected-component optimum. This is only a geometric volume ratio; actual adaptive search costs depend on the remaining hard boxes and certificate design.

## 3. Coupled support-convexity constraints

The eight offset values are not independent even **inside** the smaller box. Let \(h=h_{\operatorname{conv}S^\circ}\) on vectors, positively homogeneous, and put
\[
\begin{array}{ll}
A_1=h(4,3)/5=a_1+1,&B_1=h(-3,4)/5=b_1+1,\\
A_2=h(3,4)/5=a_2+1,&B_2=h(-4,3)/5=b_2+1,\\
C_1=h(4,-3)/5=a_3+2/5,&D_1=h(-3,-4)/5=b_3+1/5,\\
C_2=h(3,-4)/5=a_4+1/5,&D_2=h(-4,-3)/5=b_4+2/5.
\end{array}
\tag{CP.8}
\]
Here the notation \(h(v)/5\) means \(h(v/5)\), not that the unit vector has been changed. Axis supports are \(h(e_x)=W\le5,\ h(e_y)=H_0\le1,\ h(-e_x)=h(-e_y)=0\).

From subadditivity \(h(v+w)\le h(v)+h(w)\) and exact rational vector identities, e.g.
\((4,3)/5=\frac34(3,4)/5+\frac7{20}e_x\), we obtain:
\[
\begin{array}{ll}
A_1\le\frac34 A_2+\frac7{20}W,
&A_2\le\frac34 A_1+\frac7{20}H_0,\\
B_1\le\frac34 B_2+\frac7{20}H_0,
&B_2\le\frac34 B_1,\\
C_1\le\frac34 C_2+\frac7{20}W,
&C_2\le\frac34 C_1,\\
D_1\le\frac34 D_2,
&D_2\le\frac34 D_1.
\end{array}
\tag{CP.9}
\]
Likewise the pointwise inequality for every \(0\le y\le H_0\) gives
\[
\boxed{
\begin{array}{ll}
0\le A_1-C_1\le6H_0/5,&
0\le A_2-C_2\le8H_0/5,\\
0\le B_1-D_1\le8H_0/5,&
0\le B_2-D_2\le6H_0/5.
\end{array}}
\tag{CP.10}
\]
The antipodal-width inequalities also require
\[
A_1+D_2\ge0,\quad A_2+D_1\ge0,\quad
B_1+C_2\ge0,\quad B_2+C_1\ge0.
\tag{CP.11}
\]
These are **necessary linear rational inequalities**, not sufficient conditions for a support function or a feasible hallway body. To reject a parameter subbox, compute the interval bounds of its eight supports and test whether any inequality cannot possibly hold for any offsets inside it, taking \(W\in[0,5]\) and \(H_0\in[0,1]\). Such rejection is logically sound and can be implemented as cheap integer comparisons **before polygon clipping**.

## 4. Exact shallow-tree pruning test

The standard-library rational [checker](computer-assisted/check_canonical_offset_pruning.py) enumerates uniform two-way and four-way subdivisions of every original offset interval and performs only the sound necessary box rejection in CP.5 and CP.9–CP.11. Its executed results:

| Original uniform subdivision | All boxes | Boxes meeting CP.5 | Boxes surviving paired constraints |
|---|---:|---:|---:|
| \(2^8\) | 256 | 16 | 16 |
| \(4^8\) | 65,536 | 4,096 | **405** |

The script also checks the inequalities on **54 explicit rational finite point sets** with independently attained bottom and left extrema; all pass. It verifies the exact volume ratio CP.7 with fractions. The committed [run record](computer-assisted/canonical-offset-pruning-checks.json) reports **0.01254 seconds** under a five-second external cap, with the exact executed source Git blob `9fd13ef92be9bf9201b761aa27721c4edd56e471` matching the repository source, SHA-256 `b5b9195f152168790ac7cc4f1decf7240ac918b10c989cd5a3297f5e1cb44453`. Only the 4^8 count and finite rational point sets were executed; the proof of canonical tightening and soundness of convexity inequalities is mathematical, not verified by this script. These numbers are **not** a certificate that the 405 remaining boxes satisfy any sharp area bound; the box tests are feasibility **necessary conditions** only. They show the mathematical pruning rule has substantial effect in a prescribed shallow grid, not that the old 436-million-leaf search would shrink by the same proportion. No full certificate was regenerated.

## 5. A separate consequence of horizontal gap compression

Our existing [GC4](horizontal-gap-compression.md) yields another potentially useful reformulation. In this four-proper-hallway relaxation, every **actual fixed-offset intersection** \(E(u)\) inside the incoming strip is compact and has interval-or-empty vertical sections. The geometry of each lower/upper hallway in a fixed x-fiber is an interval: its outer walls bound y from one side, and its two inner safe alternatives form one ray from the opposite side. Thus GC4 converts **each** such \(E(u)\) to a compact connected finite-hallway body of **equal total area**, possibly with **different hallway offsets** after compression.

Consequently, provided GC4's stated support-depth and area-preservation theorem is accepted,
\[
\boxed{\sup_u |E(u)|=
\sup_u\lambda^*(E(u))=G.}
\tag{CP.12}
\]
The easy direction is \(\lambda^*(E(u))\le|E(u)|\). For the other, apply GC4 to \(E(u)\) and choose canonical support offsets for its connectedification. This is **global** equality of two suprema, **not** the false pointwise statement that every disconnected \(E(u)\) has the same area as its largest original component.

This does **not** remove component bookkeeping from a fixed **parameter-box enclosure** \(\bigcap_j\widehat X_j(E)\): that inflated union need not be contained in four ordinary unit hallways with one common choice of offsets. In particular one may **not** replace the paper's \(\Gamma(E)\) by an unjustified total-area bound or claim the existing certificate's component tests were unnecessary. One can design a *new global search* that optimizes total actual finite-envelope area using CP.12, but certificate completeness and any runtime benefit remain to be demonstrated.

## 6. Transfer back to full and partial motions

This pruning is **valid for both** the full-turn and partial-turn global upper-bound routes: the externally selected four hallways are known to be visited when area exceeds a threshold \(T\ge5/3\). Below \(5/3\), their higher angle \(\alpha_2\) need not be visited by an arbitrary partial-turn sofa, so this change in certificate geometry **does not** bypass the paper's motion-angle threshold.

For a body in the incoming strip with actual height \(H_0\le1\) and outgoing normal span \(q\le1\), intersecting the two endpoint strips gives
\[
|S|\le\frac{H_0 q}{|\cos\theta_{\rm exit}|}.
\]
Together with the wrong-way \(45^\circ\) exclusion for \(|S|>\sqrt2 H_0\), this yields an **adaptive** angle-reach criterion: if
\[
|S|>\max\{\sqrt2 H_0,\ 5H_0 q/3\},
\]
then the proper \(53.13^\circ\) normal must be crossed on each applicable handed motion (with its own outgoing width \(q\)). In particular \(|S|>M\) and \(H_0q\le49/50\) suffice, since the rational bounds \(Y>59/200\), \(\arctan Y>Y-Y^3/3\) give
\[
M>\frac{39229021}{24000000}>\frac{49}{30}
\]
and \(\sqrt2 H_0<M\). This is useful for *future smaller-threshold multi-angle certificates on a subunit-width branch*. It is **not** a solution of the \(M\) problem: the present four-angle relaxation already has a connected witness with area above M, regardless of angle reach.

**Suggested efficient checker architecture:** (i) normalize a candidate connected component and tighten its supports; (ii) branch only inside CP.5, with cheap CP.9–CP.11 infeasibility tests; (iii) at surviving boxes, apply the source's exact \(\widehat X_j\) enclosure and, as needed, the correct contact-component or total-area test; (iv) at target values below \(5/3\) keep an explicit partial-motion angle-reach/width branch, not an assumed full turn. A sharp result still requires more angles and/or a continuum residual comparison.

This note is a new hand-proof improvement of **certificate-domain design**, not a new global optimal value theorem. We keep the external code/results attributed and do not copy the original repository's files or rerun its large checker. No CI, Lean/Lake compilation, dependency installation, manuscript build, or long search was used. All mathematics remains subject to independent review.
