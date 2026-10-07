# Minimum-width slack can be positive: a general first-order law and a feasible stadium

**Status.** This is a pen-and-paper negative control on the tempting global assertion \(G_s\le0\) in the reviewed minimum-width identity MF2. The assertion is **false even when the input is an actual connected, canonically saturated full-turn sofa, the vertical direction is a global minimum-width normal, the two caps coincide, and all open-quarter support curvatures are between zero and one**. The counterexample is a scaled version of the genuine circular-stadium two-turn body already constructed in HC. Its area is subcritical; it does not refute the conjectured upper bound \(|S|\le M\).

The new positive result is an exact first-order formula, which also explains why the reference-scale family SM1 has a *smaller-order*, negative \(s^{3/2}\) correction. Labels MS are local; no computational output is a premise.

## 1. General regular, vertically symmetric full-turn inputs

Let \(B\) be a compact downward convex cap in \(\mathbb R\times[0,1]\) with horizontal projection \(I=[l,r]\), \(W=r-l>2\), and positive horizontal top face \(J=[a,b]\times\{1\}\) of length \(T=b-a>1\). Assume:

1. \(0\le h_B+h_B''\le1\) a.e. on both open upper coordinate quarters (with no interior curvature atoms);
2. \(A_B(x)\ge1/2\) on all \(I\), and the full positive niche height \(n_B(x)\le1/2\) throughout \(I\);
3. the full canonical two-turn envelope of
\[
K=\{(x,y):x\in I,\ 1-A_B(x)\le y\le A_B(x)\}
\]
has connected interval fibers, contains its reference face/extreme support witnesses, and has actual hull \(K\).

These conditions hold for the explicit HC stadium below; the theorem itself only needs a feasible symmetric hull as in (3). The strip \(K\) has height one and top/bottom horizontal faces both equal to \(J\). Its two downward caps \(U,V\) are both \(B\).

**Lemma MS1 (positive niche on the full interior face).** For any cap \(B\) as above with \(W>2\) and unit open-quarter curvature upper bound, its positive full niche satisfies
\[
\boxed{\operatorname{proj}_x N(B)\subset(a,b),\qquad
n_B(x)>0\quad(a<x<b).}\tag{MS.1}
\]

**Proof.** Put \(L=\pi/2\), \(f(t)=h_B(t)\), \(g(t)=h_B(t+L)\). For each \(0<t<L\) the forbidden quadrant meets the baseline \(y=0\) in the (possibly empty) open interval
\[
(d(t),e(t)),\qquad
d(t)=\frac{1-g(t)}{\sin t},\quad e(t)=\frac{f(t)-1}{\cos t}.
\]
The unit-curvature tangency identities of SR/CW yield \(d'(t),e'(t)\ge0\), together with endpoint traces
\[
d(0+)=a,\quad d(L-)=l+1,\qquad
e(0+)=r-1,\quad e(L-)=b.
\]
Since \(W>2\), \(l+1<r-1\). Therefore every interval \((d(t),e(t))\) contains \((l+1,r-1)\); their union is exactly \((a,b)\). Indeed every \(x\in(a,r-1)\) belongs to one of the intervals for t sufficiently close to zero, while every \(x\in(l+1,b)\) belongs for t sufficiently close to L; these two ranges overlap. The inequalities at y=0 are strict, so at such an x the same canonical forbidden quadrant contains \((x,y)\) for all sufficiently small \(y>0\); hence \(n_B(x)>0\). Outside \((a,b)\), no open baseline interval occurs and no positive-height forbidden point occurs either, as the quadrant is downward-closed in y. QED.

## 2. Uniformly scaled bodies in their true minimum-width frame

For \(s>0\) small put \(k=1-s\), and let
\[
K_s=kK+(0,s),\qquad E_s=E_{\rm full}(K_s).
\]
Scaling any point by \(k\le1\) multiplies every canonical wall depth by k; the shifted scaled actual sofa inside \(K_s\) therefore retains both complete motions. Canonical saturation supplies a compact connected feasible \(E_s\) with the *same actual hull* \(K_s\), exactly as in SAT1: every abscissa already occurs in the scaled original body, and each full-envelope fiber is a nonempty closed interval. Thus no sampled feasibility assumption is needed.

The rectangle \(J\times[0,1]\subset K\) has horizontal length \(T>1\). Its width in an arbitrary normal n is at least \(\min\{T,1\}=1\) (the function \(T|\cos\theta|+|\sin\theta|\) is concave on each coordinate quarter, with minima at the quarter endpoints). Consequently \(K\) has global minimum width one, attained vertically. The same holds for \(K_s\) with minimum width \(k\). Put \(W_s=kW\) and \(J_s=kJ\), and translate vertically so \(K_s\subset\{s\le y\le1\}\).

The downward upper and reflected-lower caps of \(K_s\) coincide; call them \(U_s\). Their roof and upper support are
\[
A_s(x)=s+kA_B(x/k),\qquad
h_s(t)=k h_B(t)+s\sin t\quad(0\le t\le\pi).
\]
Thus their upper-quarter curvature densities are \(k\rho_B\in[0,1]\), their horizontal width is \(W_s>2\) for s small enough, and their top-face interval is \(J_s\). By the intercept monotonicity in Lemma MS1, the full positive niche roof \(n_s\) of \(U_s\) vanishes outside \(J_s\). Over \(J_s\), the actual top of \(K_s\) equals one and its bottom equals s.

Consequently the reviewed *exact* minimum-width correction MF2 simplifies to
\[
\boxed{G_s=2\int_{J_s}\min\{n_s(x),s\}\,dx-sW_s.}\tag{MS.2}
\]

## 3. A universal first-order face-length law

**Theorem MS2 (small-slack asymptotic).** Under the stated regular symmetric full-turn hypotheses,
\[
\boxed{\lim_{s\downarrow0}\frac{G_s}{s}=2T-W.}\tag{MS.3}
\]

**Proof.** Rescale the integral in MS.2 by writing \(x=kz\):
\[
\frac{G_s}{s}
=2k\int_J\min\{n_s(kz)/s,1\}\,dz-kW.
\]
For each fixed \(z\in(a,b)\), Lemma MS1 gives \(n_B(z)>0\). Choose one interior angle witnessing a strictly positive forbidden height at \(z\). Since the support functions \(h_s\) converge uniformly to \(h_B\), and \(kz\to z\), that same angle witnesses a fixed positive height in \(N(U_s)\) for all sufficiently small s. Hence \(n_s(kz)/s\to+\infty\). The integrand is between zero and one, and the endpoints have measure zero. Dominated convergence therefore gives
\[
\int_J\min\{n_s(kz)/s,1\}\,dz\to |J|=T.
\]
Since \(k\to1\), the limit is \(2T-W\), as claimed. QED.

**Consequences.** If \(2T>W\), the correction \(G_s\) is strictly *positive* for every sufficiently small s>0, even though the frame is a **global** minimum-width frame and the two caps are identical and unit-curvature-controlled. If \(2T<W\), the correction is strictly negative for all sufficiently small s. If \(2T=W\), the linear coefficient vanishes: the sign requires a finer endpoint-niche calculation. Romik's reference belongs to this borderline case, and SM1's explicitly negative order-\(s^{3/2}\) correction is consistent with this formula.

Thus \(-sW\) is not an automatically available area credit: the two terms \(\int\min(n_s,s)\) may already consume more than it at first order.

## 4. An explicit canonically saturated feasible counterexample to \(G_s\le0\)

Use the exactly specified HC stadium cap
\[
h_B(\theta)=\frac14+\frac45|\cos\theta|+\frac34\sin\theta,\qquad0\le\theta\le\pi.
\]
It has width \(W=21/10\), top face \(J=[-4/5,4/5]\) of length \(T=8/5>1\), open-quarter curvature density \(\rho_B=1/4\), and \(A_B\ge3/4>1/2\) throughout its projection.

HC.2 proves the full niche height is
\[
H_N(B)=\frac{31}{20}-\frac{3\sqrt2}{4}<\frac12,
\]
and its positive niche is confined to J. Consequently the actual symmetric envelope
\[
E_0=(B\setminus N(B))\cap\rho(B\setminus N(B))
\]
is connected through its retained midline, has both full canonical turns and all the outer cap support witnesses (in particular its face endpoints and all outer circular flanks) survive. Its true hull is
\[
K=\{(x,y):1-A_B(x)\le y\le A_B(x)\}.
\]
Every point on the top outer flank outside J and on the two top-face endpoints is retained; the reflected bottom flank points are also retained. Thus the hull equality is not merely presumed.

Form \(K_s=(1-s)K+(0,s)\) and saturate it as in Section 2. It has global minimum width \(1-s\), both full conventional motions, coinciding caps of quarter density \((1-s)/4\le1\), and a connected full envelope of its actual hull.

Theorem MS2 now gives the **exact rational first-order coefficient**
\[
\boxed{\lim_{s\downarrow0}\frac{G_s}{s}
=2\frac85-\frac{21}{10}=\frac{11}{10}>0.}\tag{MS.4}
\]
Hence **for all sufficiently small s>0, \(G_s>0\)**.

**Theorem MS3 (negative control).** The unconditional claim “transport a connected full-turn sofa to its global minimum-width frame, then the signed correction \(G_s\) in MF2 is nonpositive” is false. It fails even for the explicit smooth-open-quarter, x- and vertically symmetric stadium-envelope family with common positive top/bottom faces and canonically saturated actual hull.

There is no contradiction with \(|S|\le M\). At s=0 the HC stadium differs from the unique equality cap of the existing regular SR/AF comparison, giving \(\Psi(B)<M/2\). By continuity the same strict deficit persists for small s and pays this small positive \(G_s\). The example only refutes the *stronger sign shortcut*, not the combined required inequality \(G_s\le\Delta(U_s)+\Delta(V_s)\).

## 5. What this changes in the two-frontier strategy

The minimum-width transport MF1 and its signed identity MF2 are valid and remain useful. But neither face overlap, global minimum width, unit curvature, positive aligned faces, nor left-right/vertical symmetry is sufficient to deduce \(G_s\le0\). The correct proof must retain the **weighted cap deficits** alongside the slab term. A route claiming to close full turns by proving \(G_s\le0\) for all minimum-width data is impossible.

For partial turns the circular completion allowance CC2 is still an *actual* extra cost; its cubic size cannot be erased by assuming a universally negative minimum-width correction. The SB class closes by an *actual safe strip bridge* and SM's exact reference-specific deficit, not by a general sign convention.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long computation was used. This is a self-reviewed hand argument based on existing HC, MF, SR/AF and canonical-saturation dependencies. Unrestricted full-turn and partial-turn optimality remain unproved.
