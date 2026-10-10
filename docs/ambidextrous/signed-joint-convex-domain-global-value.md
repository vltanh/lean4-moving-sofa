# A convex-domain variational formulation using signed full-turn fiber area

**Status (October 8, 2026):** An exact *universal* reduction for the **complete conventional two-turn value**, not an upper-bound proof or a counterexample. The supremum of a **signed, joint, nonseparable fiber-area functional** over **all compact convex subsets of one fixed rectangle** equals exactly the true supremum of areas of *connected full-turn sofas*. This domain is convex under Minkowski interpolation, despite the separate [FH1](feasible-hull-minkowski-nonconvexity.md) proof that actual feasible-hull supports are **not** Minkowski-convex.

The equality needs no support-curvature cap, face alignment, reflection symmetry, fixed ordinary-area clipping correction, or assumed nonempty fibers of arbitrary inputs. It uses only **canonical support tightening**, the elementary width-five bound, and **ordinary-area-preserving horizontal gap compression** [GC4](horizontal-gap-compression.md). It does **not** establish concavity or a sharp value for the new signed functional; neither can be inferred from this equivalence. Arbitrary partial turns are not yet treated.

## 1. Define the joint signed fiber length for an arbitrary convex hull

Fix the incoming strip \(0\le y\le1\). Let \(K\subset\mathbb R\times[0,1]\) be a nonempty compact convex set, including lower-dimensional cases. Write its horizontal projection as \(I=[l,r]\), and let \(a_K(x)\), \(b_K(x)\) be its upper and lower vertical boundary functions on \(I\).

For the lower conventional quarter-turn normals
\[
u_t=(\cos t,\sin t),\qquad
v_t=(-\sin t,\cos t),\qquad 0<t<\pi/2,
\]
the canonical lower forbidden quadrant has vertical roof
\[
m_{K,t}(x)=\min\left\{
\frac{h_K(u_t)-1-x\cos t}{\sin t},\
\frac{h_K(v_t)-1+x\sin t}{\cos t}
\right\}.
\]
Define its **positive** complete lower niche roof
\[
n_K(x)=\max\left\{0,\sup_{0<t<\pi/2}m_{K,t}(x)\right\}.
\tag{SJ.1}
\]
For the upper-handed quarter, vertically reflect \(K\) about \(y=1/2\):
\[
\rho(x,y)=(x,1-y),\qquad n_K^+(x)=n_{\rho K}(x).
\]
Each ambient lower forbidden union is downward closed in \(y\), the reflected upper union is upward closed, and a section of \(K\) is a closed interval. Therefore the complete canonical envelope has, for every \(x\in I\),
\[
E(K)_x=
\begin{cases}
[L_K(x),U_K(x)],&L_K(x)\le U_K(x),\\
\varnothing,&L_K(x)>U_K(x),
\end{cases}
\]
where
\[
L_K(x)=\max\{b_K(x),n_K(x)\},\qquad
U_K(x)=\min\{a_K(x),1-n_K^+(x)\}.
\tag{SJ.2}
\]
Define the **signed joint-fiber length and signed objective**
\[
\boxed{
\ell_K(x)=U_K(x)-L_K(x),\qquad
\mathscr S(K)=\int_{l}^{r}\ell_K(x)\,dx.
}\tag{SJ.3}
\]
The profiles are bounded and measurable on the bounded interval \(I\): they are obtained by support suprema, minima and maxima of continuous wall functions in \(x\); endpoint directions contribute no positive-height niche inside the unit strip. The sign of \(\ell_K\) is retained; it is not replaced by its positive part. This is not the old **separable** weighted one-turn objective.

The **ordinary** total envelope area is, without any connectedness assumption,
\[
\boxed{|E(K)|=\int_I(\ell_K(x))_+\,dx
=\mathscr S(K)+\int_I(-\ell_K(x))_+\,dx
\ge\mathscr S(K).}\tag{SJ.4}
\]
The last term is the *empty-fiber pinching correction*—not the two-cap clipping credit \(G\). This is an exact equality for every convex input \(K\); there is no approximation, sampled hallway, or hidden positive-part error.

## 2. A fixed convex box contains every genuine full-turn competitor

Let \(S\) be a connected full-conventional-two-turn sofa, compact and contained in a unit incoming horizontal strip, with actual horizontal projection \([l,r]\) and vertical span \(H\le1\). Its canonical supporting lower hallway at the **single rational orthogonal frame**
\[
u=(3/5,4/5),\qquad v=(-4/5,3/5)
\]
contains every point. For any \(p=(x,y)\in S\), support against an actual rightmost point yields
\[
h_S(u)-p\cdot u\ge\frac35(r-x)-\frac45H.
\]
Support against an actual leftmost point similarly gives
\[
h_S(v)-p\cdot v\ge\frac45(x-l)-\frac35H.
\]
At least one depth is at most one, so
\[
x\ge r-\frac{5+4H}{3}\ge r-3
\quad\text{or}\quad
x\le l+\frac{5+3H}{4}\le l+2.
\tag{SJ.5}
\]
Connectedness makes the horizontal projection the **whole interval** \([l,r]\). If \(W=r-l>5\), the open central interval \((l+2,r-3)\) would contain an \(x\) belonging to neither permitted region. Hence \(W\le5\).

Translate the body's horizontal center to zero and its lowest \(y\) to zero. Its actual hull is then contained in the **fixed** rectangle
\[
\boxed{B=[-5/2,5/2]\times[0,1].}\tag{SJ.6}
\]
This is the elementary compact-box argument from [FR1](full-turn-compact-finite-reduction.md), repeated here to keep the new reduction independent of the stronger, separately reviewed \(2\sqrt2\) width theorem.

Let
\[
\mathcal K_B=\{K\subseteq B:K\ne\varnothing,\ K\text{ compact convex}\}.
\]
This is a *Minkowski-convex* domain: for every \(K_0,K_1\in\mathcal K_B\) and \(0\le t\le1\), \((1-t)K_0+tK_1\in\mathcal K_B\). Unlike the domain of **actual feasible hulls**, it does not require extreme-point retention or a nonempty fiber at any chosen abscissa.

## 3. The exact equality of sharp full-turn suprema

Let \(A_F\) denote the **true** supremum of ordinary areas of all compact connected sofas with complete conventional motions of both handedness from a common unit incoming strip. There is no assumption that \(A_F=M\).

**Theorem SJ1 (universal convex-domain signed reformulation).**
\[
\boxed{
A_F=\sup_{K\in\mathcal K_B}\mathscr S(K).
}\tag{SJ.7}
\]

**Proof, lower inequality.** Let \(S\) be any connected full-turn feasible sofa. By Section 2, position its hull \(K=\operatorname{conv}S\) in \(\mathcal K_B\). Canonical support tightening implies \(S\subseteq E(K)\). Since \(S\) is connected, its horizontal projection is the *entire* \(I=\operatorname{proj}_x K\). Thus **every** \(E(K)_x\) is nonempty; equivalently \(\ell_K(x)\ge0\) for all \(x\in I\). Formula SJ.4 gives
\[
|S|\le |E(K)|=\mathscr S(K)\le\sup_{\mathcal K_B}\mathscr S.
\]
Taking the supremum over \(S\) proves \(A_F\le\sup_{\mathcal K_B}\mathscr S\).

**Proof, upper inequality.** Take **any** \(K\in\mathcal K_B\), including a hull with inadmissible extreme points, crossing niches, negative signed fibers or disconnected envelope. By SJ.4,
\[
\mathscr S(K)\le|E(K)|.
\]
If \(E(K)\) is empty the right side is zero and there is nothing to prove because \(A_F>0\) (a sufficiently small disk completes both turns). Otherwise \(E(K)\) is compact, inside the unit incoming strip, has interval-or-empty vertical fibers, and satisfies the two continuous canonical quarter-turn families defined by the actual supports of \(K\). **GC4** compresses its empty horizontal projection gaps, then fills its vertical sections, yielding a **compact connected actual full-turn sofa** \(T_K\) of *exactly the same ordinary area*, with continuous motions and their straight arms:
\[
|E(K)|=|T_K|\le A_F.
\]
Therefore \(\mathscr S(K)\le A_F\) for every \(K\in\mathcal K_B\). Taking the supremum proves the reverse inequality and SJ.7. \(\square\)

No universal sharp estimate has been assumed. The key fact is that the negative signed-fiber correction can be discarded when **upper-bounding the signed value** of an arbitrary hull, whereas every actual connected sofa has **zero** correction. That is why the two suprema coincide although the objectives disagree on individual pinched hulls.

**Attainment observation.** The existing [FR1](full-turn-compact-finite-reduction.md) supplies a maximizing connected full-turn \(S_*\). Its centered hull \(K_*=\operatorname{conv}S_*\in\mathcal K_B\) satisfies
\[
\mathscr S(K_*)=|E(K_*)|=A_F,
\]
because otherwise \(E(K_*)\) would have larger ordinary area and GC4 would produce a competitor exceeding \(A_F\). Thus the signed supremum is attained at an **actual admissible hull**, even though its interpolation domain contains many inadmissible hulls.

## 4. What this solves and the next genuinely global test

SJ1 supplies an exact **joint and nonseparable** full-turn variational formulation on a **convex support domain**, without splitting the ordinary area into \(\Psi(U)+\Psi(V)+G\). It also circumvents two independently proved obstructions at the **level of global values**:

- [FH1](feasible-hull-minkowski-nonconvexity.md) proves that the class of *actual feasible hull supports* is not Minkowski-convex, even with unit span and fixed axes. SJ1 instead optimizes over **all** convex supports within \(B\), so its domain really is convex.
- [PM1](pinching-failure-of-global-envelope-concavity.md) proves that the **ordinary total envelope area** is not globally Minkowski-concave, due to a positive pinching correction of order \(\varepsilon^{3/2}\). SJ1 uses the **signed** objective \(\mathscr S\), which does not include that positive part.

**Neither obstruction proves that \(\mathscr S\) is concave.** Its global concavity and a sharp calibration at Romik's support are **new independent mathematical obligations**. The numerical signed-Jensen probes in the local research work have not found a violation, but finite hull samples cannot establish global concavity, especially near moving support-wall ties and nonsmooth curvature atoms. No such theorem is asserted.

A successful future proof could show \(\mathscr S(K)\le M\) on **all of** \(\mathcal K_B\) by a direct joint geometric calibration, perhaps via concavity plus a justified first-variation certificate at Romik's candidate. By SJ1 this would establish the **full-turn sharp value** without an explicit pairwise clipping-deficit theorem. It would still not settle arbitrary **partial, backtracking or otherwise non-complete motions**. Those require a separate admission/completion theorem or a full original-motion analogue of SJ1.

**Honest status:** SJ1 is a mathematically exact change of the optimization domain, not a proof of \(\sup\mathscr S=M\) or of unrestricted ambidextrous optimality. No larger feasible sofa was found; no CI, Lean/Lake compilation, formalization, or sampled-area certificate is used in this proof.
