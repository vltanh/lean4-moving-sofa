# External four-hallway certificate: 353/200 global upper bound and transfer to our research

**Scope and attribution.** This is a method and provenance review of Devin O'Keefe's repository [devinokeefe/ambidextrous-sofa-bounds](https://github.com/devinokeefe/ambidextrous-sofa-bounds), default branch \`main\`, accompanying *Upper bounds for the ambidextrous moving sofa problem*. Its source \`paper/tex/\` and Lean and independent-checker records were examined via the connected GitHub repository. This note **does not** claim to re-run the enormous main certificate, recompile its Lean development, or independently referee its full continuum proofs. The paper's method is credited to the author; its finite-hallway search builds on Kallus–Romik.

The repository claims and gives verification records for
\[
\boxed{\mu_{\mathrm{ambi}}\le353/200=1.765}
\tag{EX.1, external certified result}
\]
on the **original common-starting-position ambidextrous problem**, with arbitrary continuous partial or full motions. It also bounds motion through the stated Z-shaped corridor with corners separated by \(D\ge7\). This improves our previous independently written coarse bound \(2\sqrt2-1\), but **does not** prove Romik's sharp conjectured area
\[
M=1+4Y^2+\arctan Y,\quad4Y^3+3Y-1=0,\quad Y>0,
\quad M=1.64495521\ldots.
\]
No unrestricted optimality or uniqueness is claimed in the source.

**Pinning and trust.** Source repository tree at review: \`4375343b1cb773f3f46623dad84a20adeef799a8\`. The main [spec](https://github.com/devinokeefe/ambidextrous-sofa-bounds/blob/main/data/specs/c_3653_1765.json) is \`W=5\`, \`T=353/200\`, and four 3–4–5 hallways. GitHub [release v1.0](https://github.com/devinokeefe/ambidextrous-sofa-bounds/releases/tag/v1.0), published September 29, 2026, holds \`cert_c_3653_1765.txt.xz\` (compressed 123,530,660 bytes; release SHA-256 \`abb21237ec083cace3de3c066937254f8246dcb4b61f2e9130406d38b4186e56\`). The repository SHA256SUMS lists the **uncompressed** certificate SHA-256 \`cd4d83ea841546f3490f4235e8ede5bc551d259ff9e25f61be824c92cf297de8\`. The source records report three independent checkers (Lean, exact C, exact Python) accepting **436,160,442 leaves**, maximum depth 71. The [Lean run log](https://github.com/devinokeefe/ambidextrous-sofa-bounds/blob/main/runs/lean_353_200.txt) explicitly records \`checkCert 353/200 <file> = true\`. Its Lean theorem is **conditional on that Boolean**, with a compiled checker run supplying the Boolean rather than a kernel-reduced proof term for the 1.74-GB input. Their own trust statement mentions the Lean compiler/runtime and file parsing; the Lean source reports standard axioms only. None of those long checkers was run during this review, honoring the current short-computation restriction.

## 1. The geometry of the method

Use four hallways in the **sofa's fixed initial frame**:
\[
L_{\alpha_1}(u_1),\quad L_{\alpha_2}(u_2),\quad
\rho L_{\alpha_1}(v_1),\quad\rho L_{\alpha_2}(v_2),
\quad\sin\alpha_1=3/5,\ \sin\alpha_2=4/5.
\]
Their sines and cosines are rational: \((\cos,\sin)\alpha_1=(4/5,3/5)\), and \((\cos,\sin)\alpha_2=(3/5,4/5)\). No two separate motions are required to have identical translations or synchronous times. Thus the finite relaxation has **eight independent hallway offsets**, two per orientation, not one forced symmetric pair.

For affine oriented coordinates \(f_j,g_j\), an \(L\)-hallway at offsets \(u=(u_1,u_2)\) is the union
\[
X_j(u)=
\{u_1\le f_j\le u_1+1,\ g_j\le u_2+1\}
\cup\{f_j\le u_1+1,\ u_2\le g_j\le u_2+1\}.
\tag{EX.2}
\]
Write \(H=\mathbb R\times[0,1]\). The objective is the **largest connected-component area**
\[
G(A;B)=\sup_{u_1,u_2,v_1,v_2}
\lambda^*\left(H\cap\bigcap_{j=1}^{4}X_j(u_j)\right),
\tag{EX.3}
\]
where \(\lambda^*\) is the maximal connected-component area, not the sum of all component areas.

### The motion-angle reduction is global for the claimed threshold

For a body of area \(A>\sqrt2\), an attempt to turn the wrong way through \(\pm45^\circ\) would place it in a sideways hallway whose intersection with each incoming horizontal line has length \(\sqrt2\), contradicting \(A>\sqrt2\). The final perpendicular outgoing strip intersects the incoming strip in area \(1/|\cos\theta|\). By continuity, each handed motion must visit all its proper angles through
\[
\gamma_A=\arccos(1/A).
\]
For the computer-assisted contradiction threshold \(T=353/200\),
\[
\frac1T=\frac{200}{353}<\frac35=\cos\alpha_2
\quad\text{since }1000<1059.
\]
Thus both selected 3–4–5 angles are guaranteed to be visited in each motion **whenever its area exceeds \(T\)**, even if the turns are partial/nonmonotone. The paper then proves \(A\le\max\{T,G(A;B)\}=T\) from its certificate. This angle argument is independently useful for connecting finite geometry to general motions.

### Compactness without artificial support-function regularity

For a hallway of angle \(a\), any **connected** subset of its intersection with the incoming horizontal strip has horizontal projection length at most
\[
W_a=\frac{1+\sin a}{\cos a}+\frac{1+\cos a}{\sin a}.
\]
Both chosen angles yield \(W_a=5\): the summands are \(2+3\) or \(3+2\). Translate a candidate connected component into \(B_W=[0,5]\times[0,1]\).

Each hallway offset can then be restricted to an explicit interval \([\min_{B_W}f_j-1,\max_{B_W}f_j]\) or \([\min_{B_W}g_j-1,\max_{B_W}g_j]\), without losing that component. For the first two hallways these pairs are
\[
[-1,23/5]\times[-4,4/5],\quad
[-1,19/5]\times[-5,3/5];
\]
the reflected pair have the same ranges. **This is an exhaustive eight-dimensional root box**, not a local optimizer search.

## 2. The transferable certificate mechanism

For one hallway with \(u_1\in[a,b],u_2\in[c,d]\), the exact union of all its placements over the box is
\[
\boxed{\widehat X_j=
\{a\le f_j\le b+1,\ g_j\le d+1\}
\ \cup\
\{f_j\le a,\ c\le g_j\le d+1\}.}
\tag{EX.4}
\]
The formula follows by taking the union over the first and second hallway arms separately; the part of the second arm with \(f_j\ge a\) is already in the first. This retains **both outer walls and the inner disjunction**. It is generally tighter than our D3's conservative fixed outer rectangle minus universally forbidden robust quadrants, when the latter does not retain every hallway's varying outer bounds.

For a parameter box \(E\), define
\[
C(E)=B_W\cap\bigcap_j\widehat X_j(E),\qquad
\Gamma(E)=\lambda^*(C(E)).
\]
Then every parameter in the box satisfies
\[
\boxed{\lambda^*(B_W\cap\bigcap_jX_j(u_j))\le\Gamma(E).}
\tag{EX.5}
\]
Intersecting the two convex pieces of each hallway decomposes \(C(E)\) into at most \(2^4=16\) rational polygons, with disjoint interiors. Use exact rational polygon area; build the contact graph **including degenerate zero-area points/segments**, because they can connect positive-area pieces. A box passes if the **total** area of all pieces is at most the target, or—if total area exceeds the target—if the area of **each connected component** is at most it.

Binary bisection of one of the eight root-box coordinates creates a tree. The leaf tests and complete coverage of the root prove the desired bound without trusting any floating-point branch-search decisions. Search was floating-point, verification exact. This is an especially useful design to borrow into our FR finite-offset framework and D3 branch exclusion. The formal Lean checker separates **unverified choices of polygon slices/group labels** from verified area-upper-bound and separation predicates, so those algorithmic heuristics do not enter the trusted proposition.

According to the C log, **1,341,303** of the 436,160,442 leaves required the extra component test; most were discharged by total area alone. This suggests implementing component tests only at the hard leaves. Under our GC gap-compression theorem, a disconnected finite envelope may be transformed into a connected one with the same area but **different offsets**; that fact does *not* justify replacing \(\lambda^*(C(E))\) by a component-ignoring bound inside the **same fixed parameter box**.

## 3. What this already improves, and two exact barriers to sharp closure

**Genuine global improvement.** Using the paper's reported certificate and standard reduction, we may *cite* \(\mu_{\rm ambi}\le353/200\) as an externally established bound, subject to the stated verification trust. This strengthens our previous \(2\sqrt2-1\) for both full and partial turns. It does not rely on our unverified weighted-cap WV2, our full-turn reference admission, or minimum-width slack assumptions. In combination with GH's separate height-sensitive hand bound it yields
\[
\boxed{|S|\le\min\{353/200,\ 2\sqrt2 H-H^2\}.}
\tag{EX.6}
\]
The certificate itself has **not** been rerun here; do not misdescribe this as a new independent proof.

**Barrier 1: the four-angle relaxation is already above \(M\).** The source proves that its fixed four-hallway relaxation has an explicitly specified rational, connected arrangement of area
\[
\boxed{\frac{29\,092\,957\,301}{16\,800\,000\,000}=1.73172\ldots>M.}
\tag{EX.7}
\]
Hence *no amount of extra tree refinement or more precise leaf geometry for these same four angles* can prove \(G(\{\alpha_1,\alpha_2\};\{\alpha_1,\alpha_2\})\le M\). That area is for a finite-hallway intersection, **not** a fully turning sofa and therefore not a counterexample to Romik's candidate.

**Barrier 2: the \(53.13^\circ\) angle is not guaranteed near \(M\) for partial turns.** For an arbitrary body with area just above \(M\), the motion argument only forces angles up to \(\arccos(1/M)\), which is *below* \(\alpha_2=\arcsin(4/5)\). Equivalently, using \(0<Y<3/10\) and \(\arctan Y<Y\),
\[
M=1+4Y^2+\arctan Y
<1+4(3/10)^2+3/10=83/50<5/3.
\]
To guarantee \(\alpha_2\) using the paper's elementary area/endpoint criterion would require an area threshold at least \(1/\cos\alpha_2=5/3\), which exceeds the conjectural area \(M\). The present 1.765 proof avoids this because its threshold is above 5/3. For the **full-turn-only class**, all intermediate angles are available anyway, but Barrier 1 remains.

Our earlier FR3 establishes the broader geometric obstruction: any **fixed finite** orientation-only relaxation strictly exceeds \(M\), because a reference curved boundary segment is not supported by finitely many sampled hallway walls. This agrees with the source's conclusion that substantially more angles or a continuum structural/local theorem are needed.

## 4. What should actually be borrowed next

1. **Exact per-box union and component-aware clipping** from EX.4–EX.5, instead of loose robust removed-quadrant union or a total-area-only coarse bound. Reuse its rational \(3\)-\(4\)-\(5\) orientation data and proven compact box as an independently sourced benchmark. Do not copy unchecked external code into Lean or describe the external certificate as ours. The external repository has no explicit license in the reviewed top-level tree; attribute conceptual methods and link to original code rather than duplicating it without permission.
2. **Separate discovery from checker soundness.** An untrusted search may propose a tree; all leaves and root coverage must be checked with exact arithmetic and rational polygon/touch predicates. Degenerate contacts must be kept. This is a general template for a legitimate local exclusion of nonreference parameter regions.
3. **Do not launch another massive \(353/200\) search.** The provided main certificate has ~1.74 GB uncompressed and the reported Python checker took over 5 hours; the external C/Lean runs were many minutes. Those violate our short-computation instructions. Use the cited 1.765 result directly, and reserve computer checks for small proposed **structural** statements or local residual boxes.
4. **A viable road to \(M\) must hybridize finite and continuum methods.** Certify exclusions outside a rigorously defined near-reference critical region with interval boxes, then prove a separate sharp actual-area theorem on that *entire remaining region*, including facets, separated faces, clipping and possible partial-angle deficits. Our existing TC/MT/ME and MF are not such a complete local-neighborhood theorem. The paper's source data show that merely adding more short finite-angle certificates will not by itself prove equality with M.

### Review verdict

**Import into the roadmap:** the externally certified **global bound \(353/200\)**, the four-3–4–5-hallway root box, its exact union-of-offset-box leaf enclosure, the component-aware checker, and the motion-angle reduction. **Do not infer:** global sharpness \(M\), a completed partial-to-full motion, curvature domination of a maximizer, area monotonicity of symmetrization, or a rigorous new numerical proof run in our repository.

All statements here are either credited externally or proved by the displayed elementary algebra; no CI, Lean/Lake build, large checker execution, or manuscript build was performed during this review.

## 5. Independent short exact replay of the four-angle obstruction

The source's constructive lower bound (EX.7) was also recomputed with a **separately written**, standard-library \`fractions.Fraction\` polygon clipping routine, not by importing its Python checker. Choose its exact decimal-rational original offsets
\[
u_{\alpha_1}=v_{\alpha_1}=(1260/10000,4425/10000),\quad
u_{\alpha_2}=v_{\alpha_2}=(1322/10000,5397/10000).
\]
Shift x by +3 into \([0,5]\times[0,1]\), changing offsets for each angle by \((u_1,u_2)\mapsto(u_1+3\cos a,u_2-3\sin a)\). For each of four frames, clip every retained polygon by \(f\le u_1+1,g\le u_2+1\), then split it into the **interior-disjoint** parts \(\{g\ge u_2\}\) and \(\{g\le u_2,f\ge u_1\}\). Use exact shoelace areas and an exact segment-intersection/containment contact graph, including degenerate pieces. This independent replay gave **7 nonempty polygons, 1 connected component, area exactly \(29\,092\,957\,301/16\,800\,000\,000\)**, matching the paper's rational witness, in about **0.0114 seconds** under an external five-second limit.

The first scratch implementation inserted line-clipping intersections in the wrong vertex order; it produced nonsensical self-crossing polygons and failed the expected fraction check. Reordering intersections before the entering vertex corrected it and yielded the exact match. This is a documented **small rational witness verification**, **not** an independent validation of the 436-million-leaf upper-bound certificate or of the paper's general continuum motion reduction.
