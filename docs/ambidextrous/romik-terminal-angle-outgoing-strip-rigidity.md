# Outgoing-arm strip beats a missing terminal niche: explicit \(3/2\)-power angular rigidity at Romik

**Date:** October 8, 2026. **Status:** An exact **ordinary-area** theorem for the *original partial-turn geometric formulation*, including the **entire outgoing straight-arm strips**, not just the visited inner-corner wedges. It proves an explicit sharp-sign penalty when either conventional turning interval stops sufficiently shortly before \(90^\circ\), and it combines with the new [FA2 four-independent-source-arc area calibration](four-independent-corner-ray-local-calibration.md) to give a strict **two-parameter angular plus four-source stability inequality** near Romik.

This directly addresses the user's objection that the earlier multi-peak structural examples were only *from below*: the theorem **excludes any greater-than-\(M\)** sofa for *all* perturbations in the specified Hausdorff-small middle-source class **and** both near-complete partial terminal angles. It is **not a global partial-turn completion theorem**; the outgoing angles outside the small \([L-1/100,L]\) window and arbitrary supports changed near reference axis/switching normals remain uncovered. It does not claim the full unrestricted conjecture is proved.

The only substantive source inputs are the exact reference terminal support and circular flank/niche contacts in [TC.1](tail-paired-cut-deficit.md), the canonical whole-body endpoint strip from [OS1](original-motion-signed-convex-domain.md), and the four-source complete-turn area comparison [FA2](four-independent-corner-ray-local-calibration.md). No separate two-cap clipping-deficit inequality is used.

## 1. Exact reference terminal flank versus its inner-wall niche tail

Let \(L=\pi/2\), \(\beta=\arctan Y\), \(4Y^3+3Y-1=0\), and
\[
m=\frac1{3\sin\beta},\qquad
a=-\frac m2,\quad b=\frac m2,\quad J_*=[a,b].
\]
The Romik hull \(K_*\) has both bottom/top faces exactly over \(J_*\) and two matching circular lower/upper flanks. For
\[
0\le u\le\tfrac12\sin\beta
\]
the **outer** left lower flank and **inner** right lower niche tail obey the exact dual formulas
\[
\boxed{
b_{K_*}(a-u)=q(u),\qquad
n_*(b-u)=q(u),\qquad
q(u)=\tfrac12-\sqrt{\tfrac14-u^2}.
}\tag{EP.1}
\]
The first is a genuine **convex-hull boundary**, the second a **carved inner-wall ray envelope**; they are geometrically distinct curves with the same circular profile. (The reference is horizontally symmetric and vertically symmetric, so corresponding top/left alternatives hold.)

For an early stopping angle \(\alpha=L-\delta\) with \(0<\delta<\beta\), the full **outgoing straight-arm strip** has normal \(u_\alpha=(\cos\alpha,\sin\alpha)\). Its lower inner boundary is
\[
\boxed{
e_\alpha(x)
=\frac{h_{K_*}(u_\alpha)-1-x\cos\alpha}{\sin\alpha}
=\frac{\cos\alpha(b-x)+(\sin\alpha-1)/2}{\sin\alpha}.
}\tag{EP.2}
\]
The last identity uses Romik's exact *terminal-phase outer support*
\(
h_{K_*}(u_t)=\frac12+\frac m2\cos t+\frac12\sin t
\)
for \(L-\beta\le t\le L\). At the **complete** endpoint \(\alpha=L\), \(e_L(x)=0\) and the outgoing-strip constraint is automatic.

### Saved inner niche from omitting the terminal turning angles

By the explicit reference exposed-wall chart [TC.1](tail-paired-cut-deficit.md), all one-turn positive niche roof values whose **unique active wall parameter** lies in \((L-\delta,L]\) occur in the rightmost inner-face interval
\[
b-\frac{\sin\delta}{2}\le x\le b.
\]
Other positive niche roof values have an attaining parameter before \(L-\delta\), so deleting only the late angular constraints cannot lower them. The actual saved ordinary niche area is therefore bounded by the entire old terminal tail:
\[
\boxed{\begin{aligned}
\operatorname{Saved}_-(\delta)
&\le\int_{b-\sin\delta/2}^{b}n_*(x)\,dx\\
&=\int_0^{\sin\delta/2}q(u)\,du
\le\frac{(\sin\delta)^3}{12}.
\end{aligned}}\tag{EP.3}
\]
The final inequality uses
\[
q(u)=\frac{u^2}{1/2+\sqrt{1/4-u^2}}\le2u^2.
\]
This is a **whole-continuum** exposure comparison; no angular sample or assumption that the new partial motion retains the full reference contact pattern is used. It follows simply because the full reference one-turn niche chart is explicit.

## 2. The outgoing straight strip removes *more* old sofa on the opposite outer flank

Take
\[
c=\cos\alpha=\sin\delta,\quad
s=\sin\alpha=\cos\delta,\quad
r=\frac14\sqrt{m\,c}.
\tag{EP.4}
\]
For \(0<\delta\le1/100\), the exact reference bounds
\(1<m<117/100\) and \(\sin\beta>1/4\) imply
\[
0<r<\frac1{16}<\frac12\sin\beta.
\]
Thus the full left **outer** circular flank \(x=a-u\), \(0<u<r\), is in the range EP.1. Importantly, **neither complete reference niche reaches any abscissa \(x<a\)**. The original saturated full-turn sofa therefore contains the entire vertical lower-flank interval
\[
q(u)\le y\le e_\alpha(a-u)
\]
whenever the upper endpoint exceeds the lower endpoint and remains below the upper hull roof.

The elementary estimates
\[
q(u)\le2u^2\le\frac{mc}{8}
\tag{EP.5}
\]
and
\[
\begin{aligned}
e_\alpha(a-u)
&=\frac{c(m+u)+(s-1)/2}{s}\\
&\ge mc-\frac{c^2}{2}
\qquad(0<\delta\le1/100)
\end{aligned}\tag{EP.6}
\]
show that
\[
\boxed{
e_\alpha(a-u)-q(u)\ge\frac34\,mc
\qquad(0\le u\le r).
}\tag{EP.7}
\]
The bound follows because \(m>1\), \(c\le1/100\) and
\(7/8-c/(2m)>3/4\).
Also \(e_\alpha(a-u)<1/10\) throughout this range, using \(m<117/100\), \(u<1/16\), \(c\le1/100\), \(s>99/100\). The existing upper hull and upper-handed complete-turn survivor roof exceed \(1/2\) on the flank, so **all this lower region was part of the complete reference sofa**.

Every point with \(y<e_\alpha(x)\), however, violates the necessary **outgoing whole-body strip** for the partial lower-turn motion: it is not protected by the outgoing inner wall. It is removed regardless of which earlier inner-ray angles were visited. Integrating the actual removed lower **ordinary area** on the outer flank therefore gives
\[
\boxed{\begin{aligned}
\operatorname{Loss}_-(\delta)
&\ge\int_0^r(e_\alpha(a-u)-q(u))\,du\\
&\ge\frac34 mc\,r
=\frac{3}{16}m^{3/2}(\sin\delta)^{3/2}.
\end{aligned}}\tag{EP.8}
\]

Notice the decisive mismatch of powers: the **new** outgoing loss has order \(\delta^{3/2}\), whereas the old terminal niche being omitted has area only \(O(\delta^3)\). The outgoing loss occurs **outside** the old central face while the missing niche saving occurs **inside** it, so they are geometrically disjoint and their ordinary areas may be subtracted without any signed-fiber or overlap correction.

## 3. A strict fixed-hull two-angle estimate with explicit constants

The identical analysis after vertical reflection applies to the independent upper turn at \(\gamma=L-\delta_+\). The upper outgoing-strip loss is near the **top** of the same outer left flank; the lower one lies below height \(1/10\) and the upper one above \(9/10\), so they are disjoint. The two saved niche tails also lie in disjoint upper/lower half-strips because the complete Romik niches have height less than \(1/2\).

For \(0\le\delta_\pm\le1/100\), set \(\alpha=L-\delta_-\), \(\gamma=L-\delta_+\). Compare the ordinary partial-turn canonical envelope with the complete reference envelope: a point gained can only come from one of the **missing angular niche tails**, whereas every point in the two just-identified outbound flank strips is **lost**. Therefore
\[
\boxed{
\begin{aligned}
|E_{\alpha,\gamma}(K_*)|
\le M-\sum_{\sigma\in\{-,+\}}
\left[\frac{3}{16}m^{3/2}(\sin\delta_\sigma)^{3/2}
-\frac{(\sin\delta_\sigma)^3}{12}\right].
\end{aligned}}\tag{EP.9}
\]

For \(0\le\delta\le1/100\), \(\sin\delta\ge(99/100)\delta\), \(m>1\),
and \((99/100)^{3/2}>49/50\) by exact squaring. Moreover
\[
\frac{3}{16}\frac{49}{50}-\frac1{12000}
>\frac16.
\]
Consequently the bracket in EP.9 is **strictly larger than**
\(\delta^{3/2}/6\) for every \(\delta>0\).

**Theorem EP1 (both near-right-angle terminal angles are strictly optimal on Romik's fixed hull).**
\[
\boxed{
|E_{L-\delta_-,L-\delta_+}(K_*)|
\le M-\frac16(\delta_-^{3/2}+\delta_+^{3/2}),
\qquad 0\le\delta_\pm\le1/100.
}\tag{EP.10}
\]
The complete angles attain equality \(M\). Thus neither single early stop nor simultaneous early stopping, with their **required whole-body outgoing strips**, can improve the reference area in this explicit two-dimensional terminal-angle neighborhood.

This is an **ordinary area** estimate. In particular it remains valid even if a hypothetical partial-turn raw envelope has empty fibers; no unproved signed-fiber equality or connectedification is needed.

## 4. The strict penalty survives four independent **nonsymmetric middle source arc** changes

The preceding comparison extends **uniformly** to the four independently varied upper and reflected-lower middle support arcs of [FA2](four-independent-corner-ray-local-calibration.md), because that class **does not change any terminal-phase support normal or outer flank**.

Fix the two nested source intervals \(J_0\Subset J_1\Subset(\beta,L-\beta)\) from FA2, sufficiently close to \(\pi/4\) that their actual old niche walls have a **strict negative-height margin near both face endpoints \(x=a,b\)**. For any hull \(K\) satisfying FA.2 and the FA2 small-Hausdorff/support-curvature hypotheses:

- the two **actual outer flanks** at \(x=a-u\) for \(0\le u\le1/16\) are literally the original reference circular flanks, since their supporting normal arcs lie outside \(J_0\);
- both final outgoing-strip support values \(h_K(u_\alpha),h_{\rho K}(u_\gamma)\) agree exactly with the reference for \(\delta_\pm\le1/100\), as those normal directions lie outside \(J_0\);
- neither **complete** new niche touches the exterior flank \(x<a\), by FA1's central-rectangle containment;
- the middle-arc support changes have no effect on the active *terminal niche tail* near \(x=b\), by the strict old exposed-contact margin and the fact their source parameters lie in \(J_0\), far from \(L\). Thus **the same pointwise missing-angle upper bound EP.3 holds**.

All constants in EP.5–EP.9 therefore apply **identically** to this whole (possibly vertically asymmetric) actual-hull class. The two outbound loss regions remain vertically disjoint, with nonempty full reference-like upper/lower fibers on the exterior flank.

Combine the resulting partial-versus-full comparison
\[
|E_{\alpha,\gamma}(K)|
\le|E_{L,L}(K)|-\tfrac16(\delta_-^{3/2}+\delta_+^{3/2})
\]
with the exact **four-independent-arc full-area coercivity** FA.10.

**Theorem EP2 (joint four-arc/early-exit strict local maximality).** There exist an explicit choice of compact interior middle interval \(J_0\) and a sufficiently small positive Hausdorff radius \(\varepsilon_*>0\) such that **every actual convex hull** \(K\) whose upper/reflected lower support differences from Romik are independently supported in \(J_0\), with
\(d_{\mathrm H}(K,K_*)<\varepsilon_*\), and **every pair of correct-handed conventional terminal magnitudes** \(\alpha,\gamma\in[L-1/100,L]\), satisfies
\[
\boxed{
|E_{\alpha,\gamma}(K)|
\le M-
\frac12\left(1-\frac{|J_0|}{\pi}\right)
\int_{J_0}\bigl(
|\phi_U'|^2+|\psi_U'|^2+
|\phi_V'|^2+|\psi_V'|^2
\bigr)dt
-\frac16\left[(L-\alpha)^{3/2}+(L-\gamma)^{3/2}\right].
}\tag{EP.11}
\]
The full reference shape with \(\alpha=\gamma=L\) is the only equality hull and endpoint pair within this domain. This theorem **rules out** an actual area-\(>M\) counterexample inside the entire stated middle-arc support neighborhood **even when it stops either turn early**, has arbitrary high-curvature spikes, lacks any reflection symmetry and changes its newly exposed inner-ray contact patterns.

The theorem is an *explicitly delimited local exclusion*. It neither establishes global optimality nor asserts that arbitrary above-\(M\) original motions can be reduced to this support neighborhood. Correct-handed motions with much smaller terminal angles remain a separate global challenge.

## 5. Stronger: the **entire Romik terminal circular phase** \(\delta\le\beta\)

The \(1/100\)-radian restriction of EP1–EP2 arose only from using the convenient interval
\(0<u<\sqrt{mc}/4\) and very conservative pointwise constants. An elementary wider interval permits an improvement covering the **whole reference last contact phase** \(0\le\delta\le\beta=\arctan Y\), i.e.
\[
\boxed{L-\beta\le\alpha,\gamma\le L},
\]
where \(L-\beta\approx73.404^\circ\). The analysis still uses the **true outgoing strip** and the actual stationary inner-ray tail.

**Lemma EP3 (uniform outer-flank outgoing loss).** Let \(\delta\in(0,\beta]\), \(c=\sin\delta,\ s=\cos\delta\), \(m=1/(3\sin\beta)\) and
\[
\boxed{r_\delta=\frac15\sqrt{m c}.}\tag{EP.12}
\]
Since \(c\le\sin\beta<3/10\) and \(m\sin\beta=1/3\),
\[
r_\delta\le\frac1{5\sqrt3}<\frac18
<\frac12\sin\beta.
\]
The last inequality uses the exact bound \(\sin\beta>1/4\). Thus all \(a-u\), \(0<u<r_\delta\), lie on the same **unchanged outer circle** EP.1, and
\[
q(u)\le2u^2\le\frac2{25}mc.
\tag{EP.13}
\]
The outgoing inner line EP.2 obeys
\[
e_{L-\delta}(a-u)
\ge mc-\frac{c^2}{2},
\qquad
e_{L-\delta}(a-u)-q(u)
\ge\left(\frac{23}{25}-\frac{c}{2m}\right)mc
>\frac34 mc.
\tag{EP.14}
\]
Here \(m>1\) and \(c<3/10\) give the final strict margin. Also \(e_{L-\delta}(a-u)<1/2\): use \(c<3/10\), \(m<117/100\), \(u<1/8\), \(s\ge\cos\beta>19/20\). Thus the removed lower region lies **entirely in the true full reference sofa**, below its midline and outside both full-turn positive niches. Its area is at least
\[
\boxed{
\operatorname{Loss}_-(\delta)
>\frac34mc\cdot r_\delta
=\frac3{20}m^{3/2}(\sin\delta)^{3/2}.
}\tag{EP.15}
\]
The vertically reflected upper outgoing loss is disjoint and has the same estimate, with its own \(\delta_+\).

The omitted **late inner-ray contact tail** remains bounded exactly as in EP.3, because \(\delta\le\beta\):
\[
\operatorname{Saved}_-(\delta)\le(\sin\delta)^3/12,
\tag{EP.16}
\]
and likewise for the upper hand.

Consequently, the net area penalty per early-stopped hand satisfies
\[
\begin{aligned}
\operatorname{Loss}-\operatorname{Saved}
&\ge(\sin\delta)^{3/2}
\left(\frac3{20}m^{3/2}
-\frac{(\sin\delta)^{3/2}}{12}\right)\\
&>\frac2{15}(\sin\delta)^{3/2}
>\frac18\delta^{3/2}.
\end{aligned}\tag{EP.17}
\]
For the first lower estimate, \(m>1\) and \(c<3/10\) imply
\(c^{3/2}<1/5\), hence \(\frac3{20}-\frac1{60}=\frac2{15}\).
For the second, \(\sin\delta\ge\delta-\delta^3/6>
(49/50)\delta\) on \((0,3/10)\), while the exact squared comparison
\((49/50)^3>(24/25)^2\) gives
\((\sin\delta)^{3/2}>(24/25)\delta^{3/2}\).
Thus the coefficient is at least
\((2/15)(24/25)=16/125>1/8\). All inequalities are strict for \(\delta>0\).

**Theorem EP4 (both terminal angles: full terminal-phase rigidity on the fixed reference hull).**
For all \(\delta_-,\delta_+\in[0,\beta]\),
\[
\boxed{
|E_{L-\delta_-,L-\delta_+}(K_*)|
\le M-\frac18(\delta_-^{3/2}+\delta_+^{3/2}).
}\tag{EP.18}
\]

**Theorem EP5 (the above-\(M\) exclusion with four independent moving outer-wall paths).**
Retain FA2's independent four source arc perturbations on a sufficiently small middle interval \(J_0\ni\pi/4\), with its actual support differences supported there and its positive Hausdorff-small radius. Choose \(J_0\) small enough that **every middle-source reference wall** on \(J_0\) has a strictly negative height at the entire *terminal inner tail* abscissa range
\[
x\in[b-\tfrac12\sin\beta,b].
\]
This is possible: at the reference midpoint \(t=\pi/4\) the whole corner tent is
\(H_*-|x|\), and its right baseline endpoint \(H_*=R+1/2-\sqrt2\) lies strictly **to the left of** \(b-\tfrac12\sin\beta\) by Romik's exact support and root bounds. Shrinking \(J_0\) and the Hausdorff perturbation radius preserves a strict margin uniformly.

All four modified support normals belong to \(J_0\), so the terminal *outer circular arcs* and **outgoing supports** on \([L-\beta,L]\) are unchanged. The same frozen-ray exclusion at the tail means the *full and truncated niche saving* there is still bounded by EP.16, even when the new middle contact geometry is arbitrarily complicated or the new support curvature has atoms. Outside \(J_*\) the complete envelope contains the old exterior lower and upper circular flanks, since both full niches remain confined to \(J_*\). Therefore EP.15–EP.17 apply to the actual new full envelope **uniformly**, once for each independent handed final strip.

Combining with the four-arc ordinary-area theorem FA2 gives
\[
\boxed{
\begin{aligned}
|E_{L-\delta_-,L-\delta_+}(K)|
&\le M-\frac12\left(1-\frac{|J_0|}{\pi}\right)
\int_{J_0}\bigl(
|\phi_U'|^2+|\psi_U'|^2+
|\phi_V'|^2+|\psi_V'|^2
\bigr)dt\\
&\hspace{22mm}-\frac18(\delta_-^{3/2}+\delta_+^{3/2}),
\quad\delta_\pm\in[0,\beta].
\end{aligned}}\tag{EP.19}
\]
There is **no symmetry restriction**, no upper support-curvature assumption, no assertion that the new middle inner-ray contact chart is stable, and no unearned completion of partial turns. Equality within this domain requires **both full conventional angles and exactly Romik's outer supports**.

This is a strictly **stronger original partial-turn local theorem** than EP2: it excludes a genuine full \(16.6^\circ\) angular interval of independent right/left early stops, rather than a \(0.57^\circ\) interval. It is still a fixed-neighborhood result and does **not** prove that an arbitrary area-\(>M\) counterexample can be brought into this domain.


No CI, Lean/Lake build, finite-angle numerical area certificate, or formal kernel check enters the mathematical argument.
