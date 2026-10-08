# Near-Romik failure of vertical height-padding normalization

**Status (October 8, 2026):** An exact *near-optimal-area negative control*, based on the established full-turn reference and regular-cap geometry, not a proof of Romik optimality. There exist compact connected, canonically saturated, **both-reflection-symmetric** sofas with **both complete quarter turns**, actual incoming vertical span **strictly below one**, and ordinary area arbitrarily close to Romik's \(M\) **from below**, for which vertical Minkowski padding of the **actual convex hull** up to exact span one strictly **decreases** the ordinary area of the padded hull's complete canonical envelope.

This strengthens the low-area height-padding failure [VP1](vertical-padding-ordinary-area-obstruction.md). It rules out the inference “a sufficiently near-Romik body can always be vertically padded to exact unit height without losing full-turn ordinary area.” It does **not** refute a theorem specifically for a hypothetical body of area \(>M\), nor any different height-normalization operation. All area inequalities concern *ordinary* completed sofa area; the exact signed-fiber formula is used only when the surviving fibers are proved nonempty.

## 1. A regular symmetric family already known to approach \(M\)

Let \(\Sigma\) be Romik's feasible full-turn candidate, with symmetric convex hull \(K_*=\operatorname{conv}\Sigma\), horizontal width \(2m\), and coinciding top/bottom face intervals \(J_*\) of length \(m>1\). Its positive complete lower niche is strictly below height \(1/2\), with explicit ceiling \(13/30\).

For \(0<\varepsilon\le1/16\), form the *horizontally padded hull*
\[
K_\varepsilon=K_*+[-\varepsilon/2,\varepsilon/2]e_x,\qquad
W_\varepsilon=2m+\varepsilon,\qquad
T_\varepsilon=|J_\varepsilon|=m+\varepsilon.
\tag{NH.1}
\]
These exact widths follow because Minkowski addition adds the horizontal segment to the projection and to each nonempty top/bottom face. The family is symmetric about both horizontal and vertical axes (with the vertical reflection centered at height \(1/2\)), and still has vertical span one.

The completely saturated two-handed canonical envelope \(E_\varepsilon=E(K_\varepsilon)\) is a **compact connected full-turn sofa of actual hull \(K_\varepsilon\)**, containing the full midline across its projection. The complete positive niche is confined to the open top-face interval \(J_\varepsilon\), strictly positive at every \(x\in\operatorname{int}J_\varepsilon\), and its height is uniformly bounded by
\[
\sup_x n_{K_\varepsilon}(x)<223/480<1/2.
\tag{NH.2}
\]
These geometric facts were proved (with whole-continuum turning angles and no sampled-area hypothesis) in [NR1–NR5](near-reference-positive-minwidth-slack.md) and [MS1](minimum-width-positive-slack-counterexample.md). The signed-cap calibration there also gives
\[
\boxed{|E_\varepsilon|<M,\qquad |E_\varepsilon|\longrightarrow M
\quad(\varepsilon\downarrow0).}\tag{NH.3}
\]
That strict area comparison imports the branch's **self-reviewed** SR/AF dependencies and should not be represented as independently refereed.

## 2. Shrink to a genuine connected subunit-height sofa

Fix such \(\varepsilon>0\), then take \(0<s<1/100\), \(k=1-s\). Center the scaled hull vertically:
\[
\boxed{B_{\varepsilon,s}=kK_\varepsilon+(s/2)e_y.}\tag{NH.4}
\]
Its vertical span is \([s/2,1-s/2]\), exactly \(1-s\), and its horizontal projection width is \(kW_\varepsilon\). Its top and bottom horizontal face interval is \(J_{\varepsilon,s}=kJ_\varepsilon\), of length \(kT_\varepsilon\), where its lower hull roof is exactly \(s/2\).

The copied body \(kE_\varepsilon+(s/2)e_y\) is a genuine connected full-turn sofa: every support depth is multiplied by \(k\le1\), and all incoming/outgoing full-quarter endpoint strip widths also shrink. Its midline is still \(y=1/2\) over the whole scaled horizontal projection. Consequently the canonical saturation
\[
F_{\varepsilon,s}=E(B_{\varepsilon,s})
\]
is compact, connected, has nonempty interval fibers containing the whole midline, and has **actual convex hull exactly \(B_{\varepsilon,s}\)**, because it contains the copied body whose actual hull is \(B_{\varepsilon,s}\).

In particular \(F_{\varepsilon,s}\) has both complete actual motions and height \(1-s\). The family of support functions tends uniformly to \(h_{K_\varepsilon}\) as \(s\downarrow0\). The full niche areas are continuous at this regular cap ([HV2](one-turn-height-and-approximation.md)) and the convex hulls converge, giving
\[
\boxed{|F_{\varepsilon,s}|\longrightarrow|E_\varepsilon|
\quad(s\downarrow0).}\tag{NH.5}
\]
For every fixed \(\varepsilon\), choose \(s\) small enough that \(|F_{\varepsilon,s}|<M\); together with NH.3 this permits strictly sub-\(M\) sofas approaching \(M\) as \(\varepsilon,s\to0\).

## 3. Now restore the hull's vertical span to exactly one

Perform the proposed simplest normalization:
\[
\boxed{B^+_{\varepsilon,s}
=B_{\varepsilon,s}+[-s/2,s/2]e_y
=kK_\varepsilon+[0,s]e_y.}\tag{NH.6}
\]
This has exact vertical span \([0,1]\), the same horizontal projection as \(B_{\varepsilon,s}\), and both reflection symmetries. Its full canonical envelope \(F^+_{\varepsilon,s}=E(B^+_{\varepsilon,s})\) is again **connected and full-turn feasible** for sufficiently small \(s\). The strict midline clearance follows directly from the **whole-angle inner-corner formula** rather than an unjustified uniform bound after dividing by \(\sin t\) near an endpoint. For \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\), write
\[
c_K(t)=(h_K(u_t)-1)u_t+(h_K(v_t)-1)v_t.
\]
With \(c_\varepsilon=c_{K_\varepsilon}\), and using
\((u_t\cdot e_y)u_t+(v_t\cdot e_y)v_t=e_y\), the exact centered-shrink identity is
\[
\begin{aligned}
c_{B_{\varepsilon,s}}(t)
 &=k\,c_\varepsilon(t)-s(u_t+v_t)+(s/2)e_y,\\
c_{B^+_{\varepsilon,s}}(t)
 &=c_{B_{\varepsilon,s}}(t)+(s/2)e_y.
\end{aligned}
\]
Therefore, since \((u_t+v_t)_y=\sin t+\cos t\ge0\), the lower sweep's entire inner-corner height is bounded by
\[
c_{B^+_{\varepsilon,s},y}(t)
\le k\,(223/480)+s
\le223/480+s<1/2
\quad(0<s\le1/100).
\tag{NH.6a}
\]
Every point of a lower forbidden quadrant lies *below its own inner corner*, so this is a uniform strict ceiling for the whole angular continuum, including the endpoint limits. By the hull's vertical reflection symmetry the upper forbidden sweep lies strictly above the midline.

Both hulls contain the entire midline over their horizontal projections, because \(K_\varepsilon\) does and centered shrink/padding preserve it. Hence the full envelopes have nonempty interval fibers meeting that segment and are connected. The *same* argument works for \(B_{\varepsilon,s}\), whose corner heights are even lower.

Write \(n_{\varepsilon,s}(x)\) for the lower *ambient* complete forbidden-sweep roof of \(B_{\varepsilon,s}\), and \(b_{\varepsilon,s}(x)\) for its lower convex-hull boundary. The exact vertical-padding formula [VP.2](vertical-padding-ordinary-area-obstruction.md), now with padding amount \(s\), gives
\[
\begin{aligned}
|F^+_{\varepsilon,s}|-|F_{\varepsilon,s}|
&=s\,kW_\varepsilon
-2\int_{kI_\varepsilon}\left[
 (n_{\varepsilon,s}(x)-b_{\varepsilon,s}(x)+s)_+
 -(n_{\varepsilon,s}(x)-b_{\varepsilon,s}(x))_+
 \right]dx.
\end{aligned}\tag{NH.7}
\]
The integral is everywhere nonnegative. On \(J_{\varepsilon,s}\), the lower hull boundary is exactly \(b_{\varepsilon,s}=s/2\). Whenever
\(n_{\varepsilon,s}(x)>s/2\), the bracket in NH.7 is **exactly \(s\)**. Hence the rigorous bound
\[
\frac{|F^+_{\varepsilon,s}|-|F_{\varepsilon,s}|}{s}
\le kW_\varepsilon
-2\left|\left\{x\in kJ_\varepsilon:
  n_{\varepsilon,s}(x)>s/2\right\}\right|.
\tag{NH.8}
\]

For every fixed \(z\in\operatorname{int}J_\varepsilon\), [MS1](minimum-width-positive-slack-counterexample.md) provides an *actual strictly positive* forbidden niche point at \(z\) witnessed by some interior angle. Uniform support convergence under NH.4 implies the same fixed angle still witnesses a forbidden point of positive height at \(kz\) for all sufficiently small \(s\). Thus
\[
n_{\varepsilon,s}(kz)>s/2
\quad\text{eventually, for every }z\in\operatorname{int}J_\varepsilon.
\]
By dominated convergence after \(x=kz\),
\[
\lim_{s\downarrow0}
\frac1k
\left|\{x\in kJ_\varepsilon:
  n_{\varepsilon,s}(x)>s/2\}\right|=T_\varepsilon.
\tag{NH.9}
\]
Combine NH.8–NH.9 with the *exact* face and width data NH.1:
\[
\boxed{
\limsup_{s\downarrow0}
\frac{|F^+_{\varepsilon,s}|-|F_{\varepsilon,s}|}{s}
\le W_\varepsilon-2T_\varepsilon
=(2m+\varepsilon)-2(m+\varepsilon)
=-\varepsilon<0.
}\tag{NH.10}
\]
Consequently, **for each fixed \(\varepsilon>0\)** there is \(s_\varepsilon>0\) such that
\[
\boxed{
|E(B^+_{\varepsilon,s})|<|E(B_{\varepsilon,s})|
\quad\text{for all }0<s<s_\varepsilon.
}\tag{NH.11}
\]
This is an ordinary-area comparison between *two entire canonically saturated two-turn envelopes*, not just a signed auxiliary inequality, a local solver report, or a finite-angle comparison.

## 4. The near-Romik height-repair obstruction

Choose \(\varepsilon_j\downarrow0\) and \(s_j\downarrow0\) with \(s_j<s_{\varepsilon_j}\) and \(|F_{\varepsilon_j,s_j}|<M\). Then NH.3, NH.5 and NH.11 give
\[
\boxed{
|F^+_{\varepsilon_j,s_j}|<
|F_{\varepsilon_j,s_j}|<M,\qquad
|F_{\varepsilon_j,s_j}|\longrightarrow M.
}\tag{NH.12}
\]

**Theorem NH1 (near-reference failure of unconditional height-padding repair).** No statement of the form “all connected, canonically saturated, full-turn sofas with area sufficiently close to \(M\) can have their actual hull padded vertically to height one without decreasing the resulting full-envelope area” is correct, even with both reflection symmetries, curvature-controlled round flanks, aligned positive faces, and actual hull retention before padding.

This does **not** exclude a different normalization procedure, or a theorem with the strict premise \(|S|>M\). The latter is presently hypothetical, so the near-M counterexample does not resolve sharp optimality. It identifies an explicit new obstruction to the simple way of evading the smooth-disk concavity counterexample [SCX1](signed-global-scale-concavity-obstruction.md) by insisting on exact height-one inputs.

No CI, Lean/Lake build, numerical area certificate, or formalization is used. The near-reference strict signed-cap bound imported in NH.3 remains self-reviewed as noted above.
