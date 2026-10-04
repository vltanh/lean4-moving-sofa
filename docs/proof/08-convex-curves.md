# 8. Convex curves and Mamikon's theorem

[Contents](README.md) · [← 7. The injectivity condition](07-injectivity.md) · [9. The upper bound and the optimality of Gerver's sofa →](09-optimality.md)

This chapter prepares the tools of [Chapter 9](09-optimality.md), following Baek's Chapter 7. The
upper bound $\mathcal{Q}$ of Chapter 9 is a *quadratic* functional on a *convex domain*, a set in
which convex combinations make sense.

- §8.1 sets up these notions and proves the fact that drives the whole argument (Theorem 8.7): a
  concave quadratic functional attains its maximum at a point where all its directional derivatives
  are nonpositive.
- §8.2 introduces the *curve area functional*
  $\mathcal{J}(\mathbf{x}) = \frac12 \int \mathbf{x} \times d\mathbf{x}$, the signed area swept by
  the segment from the origin to a point moving along a curve $\mathbf{x}$.
- §8.3 evaluates it on an arc $\mathbf{u}_K^{a,b}$ of the boundary of a convex body $K$. There it
  equals $\frac12 \int_{(a,b)} h_K \, d\sigma_K$, a quadratic functional of $K$ (Theorem 8.16).
- §8.4 proves Mamikon's theorem for convex bodies with corners and edges (Theorem 8.21): the area
  swept by tangent segments of lengths $\alpha(t)$ is $\frac12 \int \alpha(t)^2 \, dt$. When the far
  ends of the segments depend linearly on $K$, this area is a *convex* quadratic functional of $K$
  (Theorem 8.22). This is how Chapter 9 shows that $\mathcal{Q}$ is concave.

The paper computes several areas with the Jordan curve theorem and Green's theorem. The
formalization uses neither and computes these areas directly; the end of §8.2 lists the
replacements.

Throughout, $u_t = (\cos t, \sin t)$ and $v_t = (-\sin t, \cos t)$. A convex body $K$ has the
support function $h_K$, the supporting line $l_K(t)$ and half-plane $H_K(t)$ of normal angle $t$,
the edge $e_K(t) = K \cap l_K(t)$ with end points $v_K^-(t)$ and $v_K^+(t)$ (the latter farther in
the direction $v_t$), the point $v_K(a, b) = l_K(a) \cap l_K(b)$, and the surface area measure
$\sigma_K$ ([Chapter 2](02-preliminaries.md), [Chapter 6](06-surface-area.md)). Two facts of
Chapter 6 are used repeatedly. The edge $e_K(t)$ runs from $v_K^-(t)$ in the direction $v_t$ and
has length $\sigma_K(\lbrace t \rbrace)$
([Proposition 6.10](06-surface-area.md#proposition-610-atoms-baek-proposition-212)). And
$dv_K^+ = v_t \, d\sigma_K$
([Theorem 6.12](06-surface-area.md#theorem-612-differential-gaussminkowski-theorem-baek-theorem-522)),
so that $v_K^-(b) - v_K^+(a) = \int_{(a, b)} v_t \, \sigma_K(dt)$ for $a < b$.

## 8.1 Convex domains and quadratic functionals

### Definition 8.1 (convex domain; Baek, Definitions 7.1.1–7.1.4)

A *convex domain* is a set $\mathcal{V}$ with operations
$c_\lambda : \mathcal{V} \times \mathcal{V} \to \mathcal{V}$, $\lambda \in [0, 1]$, for which some
injective map $e$ from $\mathcal{V}$ into a real vector space satisfies
$e(c_\lambda(v, w)) = (1 - \lambda) e(v) + \lambda e(w)$. A map $f$ between convex domains is
*convex-linear* if $f(c_\lambda(v, w)) = c_\lambda(f(v), f(w))$. A map of two variables is
*convex-bilinear* if it is convex-linear in each variable. A functional
$f : \mathcal{V} \to \mathbb{R}$ is *quadratic* if $f(v) = g(v, v)$ for a convex-bilinear
$g : \mathcal{V} \times \mathcal{V} \to \mathbb{R}$. Here $\mathbb{R}$, and every real vector space,
is a convex domain with $c_\lambda(x, y) = (1 - \lambda) x + \lambda y$.

*Lean: [`ConvexDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L26),
[`ConvexDomain.IsConvexLinear`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L37),
[`ConvexDomain.IsConvexBilinear`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L42),
[`ConvexDomain.IsQuadratic`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L57),
[`realDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L32),
[`vectorDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L149).*

The Lean structure carries the operation for every real $\lambda$; only $\lambda \in [0, 1]$ is
used. Baek remarks that convex domains are the cancellative convex spaces of Stone; nothing depends
on this.

### Theorem 8.2 (convex bodies; Baek, Theorem 7.1.1)

The planar convex bodies $\mathcal{K}$ form a convex domain under Minkowski combinations
$c_\lambda(K_1, K_2) = (1 - \lambda) K_1 + \lambda K_2$, and $K \mapsto h_K$ embeds it into the
vector space of functions $\mathbb{R} \to \mathbb{R}$.

*Proof.* A Minkowski combination of nonempty compact convex sets is nonempty, compact and convex.
For $p_1 \in K_1$ and $p_2 \in K_2$,
$\langle (1 - \lambda) p_1 + \lambda p_2, u_t \rangle = (1 - \lambda) \langle p_1, u_t \rangle + \lambda \langle p_2, u_t \rangle$,
and $p_1$, $p_2$ vary independently. Taking the maximum gives, for $\lambda \in [0, 1]$,

```math
h_{(1 - \lambda) K_1 + \lambda K_2}(t) = (1 - \lambda)\, h_{K_1}(t) + \lambda\, h_{K_2}(t) .
```

A convex body is the intersection of its supporting half-planes
([Lemma 2.7](02-preliminaries.md#lemma-27-the-support-function) (3)), so $h_K$ determines $K$, and
$K \mapsto h_K$ is injective. $\square$

*Lean: [`theorem7_1_1`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L247),
[`convexBodyDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L259),
[`convexBodyComb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L231),
[`supp_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L209),
[`isConvexBody_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L203),
[`eq_of_supp_eq`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L200).*

### Theorem 8.3 (convex-linear quantities; Baek, Theorem 7.1.2)

For fixed angles $t, a, b$, the following are convex-linear in $K \in \mathcal{K}$:

1. the support value $h_K(t)$;
2. the points $v_K^+(a)$, $v_K^-(a)$ and $v_K(a, b)$;
3. the surface area measure:
   $\sigma_{(1 - \lambda) K_1 + \lambda K_2} = (1 - \lambda)\, \sigma_{K_1} + \lambda\, \sigma_{K_2}$.

*Proof.* (1) is the display in the proof of Theorem 8.2. (2) For $b \ne a, a + \pi$, the point
$v_K(a, b)$ solves $\langle p, u_a \rangle = h_K(a)$, $\langle p, u_b \rangle = h_K(b)$:

```math
v_K(a, b) = h_K(a)\, u_a + \frac{h_K(b) - h_K(a) \cos(b - a)}{\sin(b - a)}\, v_a .
```

This is linear in $h_K(a)$ and $h_K(b)$. The vertices $v_K^+(a)$ and $v_K^-(a)$ are the limits of
$v_K(a, b)$ as $b \to a$ from above and from below
([Theorem 2.9](02-preliminaries.md#theorem-29-limits-of-vertices-baek-theorem-213)), and limits
preserve combinations. (3) By
[Theorem 6.12](06-surface-area.md#theorem-612-differential-gaussminkowski-theorem-baek-theorem-522),
$\sigma_K = \langle v_t, dv_K^+ \rangle$ on each interval $(a, b]$. By (2), $v_K^+$ is
convex-linear in $K$, and the Lebesgue–Stieltjes measure of a combination of functions of bounded
variation is the combination of their measures (Baek's Proposition 5.1.1), so $dv_K^+$ and
$\sigma_K$ are convex-linear in $K$. $\square$

*Lean: [`theorem7_1_2_supp`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L264),
[`theorem7_1_2_vertices`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L296),
[`theorem7_1_2_sigma`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L393),
[`cvx_vplus_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L277).*

The paper assumes $a < b < a + \pi$ in (2). The Lean statement holds for all $a, b$, because the
formalization defines $v_K(a, b)$ by the formula above for all $a$ and $b$
([`vint`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L78); REPORT.md, Section 5).

### Theorem 8.4 (the area is quadratic; Baek, Theorem 7.1.3)

For every convex body $K$,

```math
\lvert K \rvert = \frac12 \int_{[0, 2\pi)} h_K \, d\sigma_K ,
```

and $K \mapsto \lvert K \rvert$ is a quadratic functional on $\mathcal{K}$, with the convex-bilinear
form $(K_1, K_2) \mapsto \frac12 \int_{[0, 2\pi)} h_{K_1} \, d\sigma_{K_2}$.

*Proof.* The formula is the area formula,
[Theorem 6.13](06-surface-area.md#theorem-613-area-formula-schneider-remark-512) (Schneider,
*Convex Bodies*, Remark 5.1.2). The form is convex-linear in $K_1$ by Theorem 8.3 (1) and in $K_2$
by Theorem 8.3 (3). Its integrals are finite, as $h_{K_1}$ is continuous and $[0, 2\pi)$ is
bounded. $\square$

*Lean: [`theorem7_1_3`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L414),
[`theorem7_1_3_quadratic`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L445),
[`area_eq_half_integral_supp`](../../MovingSofaOptimality/External/AreaFormula.lean#L558),
[`cvx_integral_supp_sigma_bilin`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L420).*

### Definition 8.5 (directional derivative, concavity; Baek, Definitions 7.1.5, 7.1.6)

For a functional $f$ on a convex domain $\mathcal{V}$ and $K, K' \in \mathcal{V}$, the *directional
derivative* of $f$ at $K$ towards $K'$ is the one-sided derivative

```math
Df(K; K') = \left. \frac{d}{d\lambda} \right|_{\lambda = 0} f\bigl(c_\lambda(K, K')\bigr) ,
```

taken within $[0, 1]$. The functional $f$ is *concave* if
$f(c_\lambda(K_1, K_2)) \ge (1 - \lambda) f(K_1) + \lambda f(K_2)$ for all $K_1, K_2$ and
$\lambda \in [0, 1]$, and *convex* if the reverse inequality holds.

*Lean: [`ConvexDomain.dirDeriv`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L62),
[`ConvexDomain.IsConcave`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L94),
[`ConvexDomain.IsConvexFun`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L98).*

### Lemma 8.6 (derivative of a quadratic functional; Baek, Lemma 7.1.4)

Let $f(K) = g(K, K)$ with $g$ convex-bilinear. For $\lambda \in [0, 1]$,

```math
f\bigl(c_\lambda(K, K')\bigr) = (1 - \lambda)^2 g(K, K) + \lambda (1 - \lambda) \bigl(g(K, K') + g(K', K)\bigr) + \lambda^2 g(K', K') , \tag{8.1}
```

and $Df(K; K') = g(K, K') + g(K', K) - 2 g(K, K)$. In particular $Df(K; \cdot)$ is convex-linear.

*Proof.* Expanding $g(c_\lambda(K, K'), c_\lambda(K, K'))$ in each variable gives (8.1). As a
polynomial in $\lambda$, the right side of (8.1) is
$g(K, K) + \lambda\, \bigl(g(K, K') + g(K', K) - 2 g(K, K)\bigr) + \lambda^2 \bigl(g(K, K) - g(K, K') - g(K', K) + g(K', K')\bigr)$,
whose derivative at $0$ is the stated one. $\square$

*Lean: [`lemma7_1_4`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L82),
[`cvx_bilin_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L68).*

The Lean statement gives the formula for $Df(K; K')$; the convex-linearity in $K'$ follows from it
and is not stated separately.

### Theorem 8.7 (maximum of a concave quadratic functional; Baek, Theorem 7.1.5)

Let $f$ be a concave quadratic functional on a convex domain $\mathcal{V}$, and $K \in \mathcal{V}$.
Then $f(K') \le f(K)$ for every $K' \in \mathcal{V}$ if and only if $Df(K; K') \le 0$ for every
$K' \in \mathcal{V}$.

![The graph of a concave parabola p over the interval from 0 to 1, falling from f(K) at lambda = 0 to f(K') at lambda = 1; a dashed chord joins its two ends, a green segment at lambda = 1/2 marks the gap between the parabola above and the chord below, and a dashed orange line, the tangent at lambda = 0 with slope Df(K; K'), lies above the parabola](figures/08-convex-curves/midpoint.svg)

*Figure 8.1.* The proof of Theorem 8.7. Along the segment from $K$ to $K'$, the functional is the
quadratic polynomial $p(\lambda) = A + \delta \lambda + E \lambda^2$ of (8.1). Concavity at the
midpoint alone says that $p(\frac12)$ lies above the chord, by the gap $-E/4 \ge 0$ (green); with
the slope $\delta = Df(K; K') \le 0$ (orange) this gives $f(K') = A + \delta + E \le A = f(K)$.

*Proof.* Along a segment, $f$ is a quadratic polynomial whose slope at $0$ is the directional
derivative, and concavity makes its leading coefficient nonpositive. Fix $K'$ and write
$p(\lambda) = f(c_\lambda(K, K')) = A + \delta \lambda + E \lambda^2$ by (8.1), with $A = f(K)$,
$\delta = Df(K; K')$ and $E = g(K, K) - g(K, K') - g(K', K) + g(K', K')$.

If $K$ maximizes $f$, then $\delta \lambda + E \lambda^2 = p(\lambda) - p(0) \le 0$ for
$\lambda \in (0, 1]$. Dividing by $\lambda$ and letting $\lambda \to 0$ gives $\delta \le 0$. (The
Lean proof argues by contradiction with the single value
$\lambda = \min(1, \delta / (2(\lvert E \rvert + 1)))$.)

Conversely, let $\delta \le 0$. Concavity at $\lambda = \frac12$ gives
$p(\frac12) \ge \frac12 (p(0) + p(1))$, that is,

```math
A + \tfrac12 \delta + \tfrac14 E \ \ge\ A + \tfrac12 \delta + \tfrac12 E ,
```

so $E \le 0$ (Figure 8.1). Then $f(K') = p(1) = A + \delta + E \le A = f(K)$. $\square$

*Lean: [`theorem7_1_5`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L103).*

### Definition 8.8 (equality modulo linear functionals; Baek, Definition 7.1.7)

For functionals $f, g$ on a convex domain $\mathcal{V}$, write $f \equiv_{\mathcal{V}} g$ (or
$f(K) \equiv_K g(K)$) if $f - g$ is convex-linear.

*Lean: [`ConvexDomain.EqModLinear`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L145).*

### Lemma 8.9 (shifting the arguments of a convex-bilinear map; Baek, Lemma 7.1.6)

Let $h$ be a convex-bilinear map on a real vector space $V$ and $c_1, c_2 \in V$. Then
$h(K, K) \equiv_K h(K + c_1, K + c_2)$.

*Proof.* A convex-linear map $g$ on $V$ satisfies $g(x + d) = g(x) + g(d) - g(0)$: both sides are
twice $g$ at the midpoint of $x$ and $d$. Applying this in each argument,

```math
h(K + c_1, K + c_2) - h(K, K) = h(K, c_2) - h(K, 0) + h(c_1, K + c_2) - h(0, K + c_2) ,
```

and each term is convex-linear in $K$. $\square$

For a bilinear $h$ the difference is $h(c_1, K) + h(K, c_2) + h(c_1, c_2)$, as in Baek's proof. Baek
states the lemma on a convex domain, where $K + c$ is not defined, and the paper's proof treats $h$ as
bilinear (REPORT.md, E18).

*Lean: [`lemma7_1_6`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L163).*

## 8.2 The curve area functional

### Definition 8.10 (curve area functional; Baek, Definitions 7.2.4–7.2.6, 7.2.8)

The *cross product* of $p = (p_1, p_2)$ and $q = (q_1, q_2)$ is $p \times q = p_1 q_2 - p_2 q_1$.
Let $C^\mathrm{BV}[a, b]$ be the real vector space of continuous maps
$\mathbf{x} : [a, b] \to \mathbb{R}^2$ of bounded variation, and $d\mathbf{x}$ the
Lebesgue–Stieltjes measure of $\mathbf{x}$, a vector measure on $[a, b]$
([Chapter 6](06-surface-area.md)). The *curve area functional* of $\mathbf{x}$ is

```math
\mathcal{J}(\mathbf{x}) = \frac12 \int_a^b \mathbf{x}(t) \times d\mathbf{x}(t) ,
```

the diagonal of the bilinear form
$\mathcal{B}(\mathbf{x}_1, \mathbf{x}_2) = \frac12 \int_a^b \mathbf{x}_1 \times d\mathbf{x}_2$. For
points $p, q$, $\mathcal{J}(p, q) = \frac12 (p \times q)$.

*Lean: [`cross`](../../MovingSofaOptimality/Basic/Plane.lean#L49),
[`crossCLM`](../../MovingSofaOptimality/Convex/CurveArea.lean#L286),
[`IsCBV`](../../MovingSofaOptimality/Convex/CurveArea.lean#L521),
[`MovingSofaOptimality.CBV`](../../MovingSofaOptimality/Convex/CurveArea.lean#L533),
[`lsMeasure`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L57),
[`curveBilin`](../../MovingSofaOptimality/Convex/CurveArea.lean#L525),
[`curveArea`](../../MovingSofaOptimality/Convex/CurveArea.lean#L530),
[`segArea`](../../MovingSofaOptimality/Convex/CurveArea.lean#L668).*

For a continuously differentiable curve,
$\mathcal{J}(\mathbf{x}) = \frac12 \int_a^b \mathbf{x}(t) \times \mathbf{x}'(t) \, dt$
([`curveArea_eq_integral`](../../MovingSofaOptimality/Convex/CurveArea.lean#L652)). The integrand is
twice the rate at which the segment from the origin $O$ to $\mathbf{x}(t)$ sweeps area, counted
positively when it turns counterclockwise. So $\mathcal{J}(\mathbf{x})$ is the signed area swept by
that segment. If $\mathbf{x}$ runs once counterclockwise around the boundary of a region, it is the
area of the region (Green's theorem); the formalization never uses this.

### Proposition 8.11 (quadratic; Baek, Proposition 7.2.2)

$\mathcal{J}$ is a quadratic functional on $C^\mathrm{BV}[a, b]$, with
$\mathcal{J}(\mathbf{x}) = \mathcal{B}(\mathbf{x}, \mathbf{x})$.

*Proof.* $\mathcal{B}$ is linear in $\mathbf{x}_1$, as the integral of a linear expression. It is
linear in $\mathbf{x}_2$, since the Lebesgue–Stieltjes measure of a linear combination of curves is
the combination of their measures
([Proposition 6.2](06-surface-area.md#proposition-62-linearity-baek-proposition-511)). $\square$

*Lean: [`proposition7_2_2`](../../MovingSofaOptimality/Convex/CurveArea.lean#L609),
[`cbvDomain`](../../MovingSofaOptimality/Convex/CurveArea.lean#L572),
[`cvx_lsMeasure_comb`](../../MovingSofaOptimality/Convex/CurveArea.lean#L559),
[`cvx_curveBilin_comb_left`](../../MovingSofaOptimality/Convex/CurveArea.lean#L578).*

### Proposition 8.12 (segments; Baek, Propositions 7.2.4, 7.2.5)

1. The segment $s \mapsto p + s (q - p)$, $s \in [0, 1]$, has curve area functional
   $\mathcal{J}(p, q)$.
2. If $\langle p, u_t \rangle = h$ and $q - p = d\, v_t$, then $\mathcal{J}(p, q) = hd/2$.
3. If $p$, $q$ and $O$ lie on a line, then $\mathcal{J}(p, q) = 0$.

*Proof.* (1) Along the segment,
$\mathbf{x} \times \mathbf{x}' = (p + s(q - p)) \times (q - p) = p \times q$ for every $s$. (2)
Since $p \times v_t = \langle p, u_t \rangle$,
$p \times q = p \times (q - p) = d\,(p \times v_t) = hd$. (3) A line through $O$ is
$\lbrace \langle \cdot, u_t \rangle = 0 \rbrace$ for some $t$, so (3) is (2) with $h = 0$. $\square$

*Lean: [`proposition7_2_4`](../../MovingSofaOptimality/Convex/CurveArea.lean#L672),
[`proposition7_2_4_line`](../../MovingSofaOptimality/Convex/CurveArea.lean#L686),
[`proposition7_2_5`](../../MovingSofaOptimality/Convex/CurveArea.lean#L695).*

Baek's Proposition 7.2.4 also assumes that $q$ lies on the line $l(t, h)$; this follows from the
other hypotheses (REPORT.md, Section 5).

### Proposition 8.13 (additivity; Baek, Proposition 7.2.6)

If $a \le b \le c$ and $\mathbf{x} \in C^\mathrm{BV}[a, c]$, then
$\mathcal{J}(\mathbf{x}|_{[a, c]}) = \mathcal{J}(\mathbf{x}|_{[a, b]}) + \mathcal{J}(\mathbf{x}|_{[b, c]})$.

*Proof.* Split the integral over $[a, b]$ and $(b, c]$. The measure $d\mathbf{x}$ has no atoms,
since $\mathbf{x}$ is continuous. Its restriction to $[a', b'] \subseteq [a, c]$ is the
Lebesgue–Stieltjes measure of $\mathbf{x}|_{[a', b']}$. $\square$

*Lean: [`proposition7_2_6`](../../MovingSofaOptimality/Convex/CurveArea.lean#L703).*

**What is not formalized.** The paper continues §7.2 with Jordan arcs and curves and their
orientations (its Definitions 7.2.1–7.2.3, 7.2.7, 7.2.9), the Jordan curve theorem (Theorem 7.2.1),
Green's theorem for rectifiable Jordan curves (Theorem 7.2.3: $\mathcal{J}$ of a counterclockwise
Jordan curve is the area it encloses) and a criterion for the orientation (Proposition 7.2.7). It
uses them in four places: to evaluate $\mathcal{J}(\mathbf{u}_K^{a,b})$ (Theorem 7.3.2), to identify
the region between a convex arc and its tangents (Lemma 7.3.5 (1)), to bound the parts of the niche
from below (Lemmas 8.2.2 and 8.2.3) and to compute the niche of Gerver's sofa (Theorem 8.4.1 (2)).
The formalization replaces them, in this order, by an explicit parametrization (Theorem 8.16), a
difference of areas (Lemma 8.19), regions between graphs and Fubini's theorem
([Chapter 9](09-optimality.md)), and a description of the niche as the region under a curve
([Theorem 10.19](10-gerver.md)) (REPORT.md, Section 7).

## 8.3 Convex curves

### Definition 8.14 (convex curve; Baek, Definition 7.3.1)

For a convex body $K$ and $a < b < a + \pi$, the *convex curve* from $v_K^+(a)$ to $v_K^-(b)$ is

```math
\mathbf{u}_K^{a,b} = \lbrace v_K^+(a) \rbrace \cup \bigcup_{t \in (a, b)} e_K(t) \cup \lbrace v_K^-(b) \rbrace ,
```

the part of $\partial K$ traversed counterclockwise between the normal angles $a$ and $b$. Its curve
area functional is the number

```math
\mathcal{J}(\mathbf{u}_K^{a,b}) = \frac12 \int_{(a, b)} h_K \, d\sigma_K , \qquad \text{the diagonal of} \qquad \mathcal{B}(K_1, K_2) = \frac12 \int_{(a, b)} h_{K_1} \, d\sigma_{K_2} .
```

*Lean: [`convexCurve`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L29),
[`convexCurveArea`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L33),
[`convexCurveBilin`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L37).*

The paper defines $\mathcal{J}(\mathbf{u}_K^{a,b})$ through a parametrization of the arc and proves
the formula as its Theorem 7.3.2. The formalization takes the formula as the definition
([`convexCurveArea`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L33)), and Theorem 8.16
below shows that it is the curve area functional of a parametrization of the arc. The formula is
the sum of thin triangles: the piece of the arc at normal angle $t$, of length $\sigma_K(dt)$, is the
base of a triangle with apex $O$ and height $h_K(t)$, of area $\frac12 h_K(t)\, \sigma_K(dt)$
(Figure 8.2).

![A convex body K, light blue, the convex hull of an ellipse and a point P above it. A thick arc of its boundary runs from v_K^+(a) on the right, up the ellipse, along a straight edge to the corner P, along a second edge and down the ellipse to v_K^-(b) on the left. The region swept by the segment from the origin O, inside K, to the arc is shaded orange, with thin rays to points of the arc; two darker triangles O Q1 P and O P Q2 are the contributions of the two edges. The supporting line of the first edge and the perpendicular from O to it, of length h_K(t1), are drawn](figures/08-convex-curves/curve-area.svg)

*Figure 8.2.* The curve area functional of a convex arc, for the convex hull $K$ of an ellipse and a
point $P$. The segment from $O$ to the arc $\mathbf{u}_K^{a,b}$ sweeps the orange region, of area
$\frac12 \int_{(a,b)} h_K\, d\sigma_K$. An edge $e_K(t_1)$ is an atom of $\sigma_K$ of mass equal to
its length, and contributes the dark triangle of area
$\frac12 h_K(t_1)\, \sigma_K(\lbrace t_1 \rbrace)$. The corner $P$, whose normal angles fill an
interval on which $\sigma_K = 0$, contributes nothing.

### Lemma 8.15 (cutting a convex body along a chord; Baek, Lemma 7.3.1)

Let $a < b < a + \pi$. If $v_K^+(a) = v_K^-(b)$, then $v_K(a, b) = v_K^+(a)$ and
$\mathbf{u}_K^{a,b}$ is this single point. If $v_K^+(a) \ne v_K^-(b)$, then:

1. $v_K(a, b)$ does not lie on the line $l'$ through $v_K^+(a)$ and $v_K^-(b)$;
2. the closed half-plane $H'$ bounded by $l'$ that contains $v_K(a, b)$ has the normal angle
   $t' + \pi$ for some $t' \in (a, b)$;
3. $K' = K \cap H'$ is a convex body, with the edges (i) $e_{K'}(t) = \lbrace v_K^+(a) \rbrace$ for
   $t \in (t' - \pi, a]$, (ii) $e_{K'}(t) = e_K(t)$ for $t \in (a, b)$, (iii)
   $e_{K'}(t) = \lbrace v_K^-(b) \rbrace$ for $t \in [b, t' + \pi)$, and (iv) $e_{K'}(t' + \pi)$ the
   segment from $v_K^-(b)$ to $v_K^+(a)$.

*Lean: [`lemma7_3_1`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L194),
[`lemma7_3_1_degenerate`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L165).*

*Proof sketch.* Everything happens in the cone $X = H_K(a) \cap H_K(b)$, which contains $K$ and has
the apex $P = v_K(a, b)$. Write $P = v_K^+(a) + \alpha v_a$ and $v_K^-(b) = P + \beta v_b$. Then
$\alpha \ge 0$ because $v_K^+(a) \in H_K(b)$, and $\beta \ge 0$ because $v_K^-(b) \in H_K(a)$.

If $P \in K$, then $P$ lies on the edges $e_K(a)$ and $e_K(b)$, whose ends in the directions $v_a$
and $-v_b$ are $v_K^+(a)$ and $v_K^-(b)$. So $\alpha \le 0$ and $\beta \le 0$, that is,
$P = v_K^+(a) = v_K^-(b)$. For $t \in (a, b)$, the apex is the only point of $X$ on the line
$\lbrace \langle \cdot, u_t \rangle = h_K(t) \rbrace$, so $e_K(t) = \lbrace P \rbrace$.

If $P \notin K$, then $\alpha, \beta > 0$, so $v_K^+(a) \ne v_K^-(b)$ and the three points are not
collinear, which is (1). The difference $v_K^-(b) - v_K^+(a) = \alpha v_a + \beta v_b$ is a positive
multiple of $v_{t'}$ for some $t' \in (a, b)$, which is (2). (Baek's proof writes this difference
with the opposite sign; [`REPORT.md`](../../REPORT.md), E27.) Let $T = X \cap H'$, the triangle with
vertices $v_K^+(a)$, $P$, $v_K^-(b)$. Then $K'$ lies in $T$, contains the side of $T$ on $l'$, and
meets the other two sides only at $v_K^+(a)$ and $v_K^-(b)$. This gives (i), (iii) and (iv). For
(ii), let $t \in (a, b)$. The function $\langle \cdot, u_t \rangle$ decreases along both sides of
the cone away from the apex. So at each point of $X \setminus T$ it is smaller than at some point of
the chord, hence than at $v_K^+(a)$ or at $v_K^-(b)$. Therefore $e_K(t) \subseteq T$, and
$e_{K'}(t) = e_K(t)$. $\square$

![The convex body K of Figure 8.2, grey, cut along the dashed chord l' from v_K^-(b) to v_K^+(a); the part K' of K beyond the chord, containing the thick arc, is blue. The supporting lines at a and b meet at v_K(a, b) above the arc, and the orange region R lies between the arc and the two tangent segments, inside the triangle with vertices v_K^+(a), v_K(a, b), v_K^-(b)](figures/08-convex-curves/cut.svg)

*Figure 8.3.* Lemmas 8.15 and 8.19 for the body $K$ of Figure 8.2. The chord $l'$ cuts off the
convex body $K'$ (blue), whose boundary is the arc $\mathbf{u}_K^{a,b}$ and the chord. The triangle
with vertices $v_K^+(a)$, $v_K(a, b)$, $v_K^-(b)$ is the union of $K'$ and the region $R$ (orange)
between the arc and its two end tangents.

### Theorem 8.16 (the curve area functional of a convex arc; Baek, Theorem 7.3.2)

Let $a < b < a + \pi$. There is a curve $\gamma \in C^\mathrm{BV}[0, 1]$ with
$\gamma([0, 1]) = \mathbf{u}_K^{a,b}$, $\gamma(0) = v_K^+(a)$ and $\gamma(1) = v_K^-(b)$, injective
unless $\mathbf{u}_K^{a,b}$ is a single point, such that

```math
\mathcal{J}(\gamma) = \frac12 \int_{(a, b)} h_K \, d\sigma_K .
```

Moreover $K \mapsto \mathcal{J}(\mathbf{u}_K^{a,b})$ is a quadratic functional on $\mathcal{K}$,
with the convex-bilinear form $\mathcal{B}$ of Definition 8.14.

*Lean: [`theorem7_3_2`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1070),
[`theorem7_3_2_quadratic`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1116),
[`cvxArc`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L720),
[`cvxQuantile`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L540),
[`cvx_map_cvxQuantile`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L641),
[`cvxArc_image`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L947),
[`cvxArc_injOn`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L998),
[`cvxArc_curveArea`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1033).*

![Left: the graph of r = F(t) for t from a to b, the normalized distribution function of the surface area measure of K on (a, b); it rises along the ellipse, jumps up at t1 and at t2, the jumps drawn orange and labelled edge, and is flat between t1 and t2, labelled corner, before rising to 1 at b. Right: the body K with its arc from gamma(0) on the right to gamma(1) on the left, the two edges orange, and thirteen black points equally spaced along the arc](figures/08-convex-curves/quantile.svg)

*Figure 8.4.* The parametrization of the proof of Theorem 8.16. Left: the normalized distribution
function $F(t) = \sigma_K((a, t]) / L$ of the arc of Figure 8.2. It jumps at the normal angles
$t_1, t_2$ of the two edges, by their lengths over $L$, and is flat on $(t_1, t_2)$, the normal
angles of the corner $P$. Its generalized inverse $\theta(r)$ is read off sideways: it is constant
(equal to $t_i$) while $r$ runs through a jump, and it jumps across the flat part. Right: the curve
$\gamma(s) = v_K^+(a) + L \int_0^s v_{\theta(r)}\, dr$ runs along the arc at constant speed, here
shown at $s = 0, \frac1{12}, \dots, 1$.

*Proof.* The idea is to parametrize the arc by normalized arc length: the arc has length
$L = \sigma_K((a, b))$, and its tangent at arc length $Lr$ is $v_{\theta(r)}$, where $\theta(r)$ is
the normal angle there.

If $v_K^+(a) = v_K^-(b)$, the arc is a single point $p$ (Lemma 8.15): the edges $e_K(t)$,
$t \in (a, b)$, are $\lbrace p \rbrace$, so $v_K^+ = p$ on $[a, b)$ and $\sigma_K((a, b)) = 0$, as in the
paper (which reads this off Schneider's description of $\sigma_K$, here off its definition). The
constant curve has the required properties, and both sides of the formula vanish. Otherwise $L > 0$,
since $L = 0$ would give $v_K^-(b) - v_K^+(a) = \int_{(a, b)} v_t \, \sigma_K(dt) = 0$. The generalized inverse

```math
\theta(r) = \inf \lbrace t \in [a, b] : \sigma_K((a, t]) \ge L r \rbrace \quad (\text{or } b), \qquad r \in [0, 1],
```

is nondecreasing. It pushes the Lebesgue measure on $(0, 1)$ forward to $\sigma_K|_{(a, b)} / L$
(the quantile transform,
[`cvx_map_cvxQuantile`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L641)). Put

```math
\gamma(s) = v_K^+(a) + L \int_0^s v_{\theta(r)} \, dr .
```

Then $\gamma$ is $L$-Lipschitz, so $\gamma \in C^\mathrm{BV}[0, 1]$, and
$\gamma'(r) = L\, v_{\theta(r)}$ for almost every $r$.

*$\gamma$ traces the arc edge by edge.* Let $r \in (0, 1)$ and $\theta = \theta(r)$, so that
$\theta \in (a, b)$ and $\sigma_K((a, \theta)) \le Lr \le \sigma_K((a, \theta])$. Split $(0, r)$
into the set where $\theta(s) < \theta$, which the quantile transform maps onto
$\sigma_K|_{(a, \theta)} / L$, and the rest, where $\theta(s) = \theta$. This gives

```math
\gamma(r) = v_K^+(a) + \int_{(a, \theta)} v_t \, \sigma_K(dt) + \lambda\, v_\theta = v_K^-(\theta) + \lambda\, v_\theta , \qquad \lambda = Lr - \sigma_K((a, \theta)) \in [0, \sigma_K(\lbrace \theta \rbrace)] ,
```

a point of the edge $e_K(\theta)$. Conversely, every point $v_K^-(t) + \lambda v_t$ of an edge
$e_K(t)$, $t \in (a, b)$, is $\gamma(r)$ for $r = (\sigma_K((a, t)) + \lambda) / L$. For $r = 1$ the
same computation gives $\gamma(1) = v_K^+(a) + \int_{(a, b)} v_t \, \sigma_K(dt) = v_K^-(b)$. So
$\gamma([0, 1]) = \mathbf{u}_K^{a,b}$, with the right end points.

*The curve area functional.* Since $\gamma(r)$ lies on $l_K(\theta(r))$,
$\gamma(r) \times \gamma'(r) = L\, \langle \gamma(r), u_{\theta(r)} \rangle = L\, h_K(\theta(r))$
for almost every $r$. By the quantile transform,

```math
\mathcal{J}(\gamma) = \frac12 \int_0^1 L\, h_K(\theta(r)) \, dr = \frac12 \int_{(a, b)} h_K \, d\sigma_K .
```

*Injectivity.* Let $m = \frac12(a + b)$. Every velocity $L\, v_{\theta(r)}$ makes an angle of at
most $\frac12 (b - a) < \frac\pi2$ with $v_m$, so for $s_1 < s_2$

```math
\langle \gamma(s_2) - \gamma(s_1), v_m \rangle \ \ge\ L \cos\tfrac{b - a}{2}\, (s_2 - s_1) > 0 .
```

Finally, $\mathcal{B}$ is convex-bilinear by Theorem 8.3 (1) and (3). $\square$

The paper argues instead with the convex body $K'$ of Lemma 8.15, which is bounded by the arc and
the chord. Green's theorem gives the first equality below, and the area formula (Theorem 8.4) the
second:

```math
\lvert K' \rvert = \mathcal{J}(\mathbf{u}_K^{a,b}) + \mathcal{J}\bigl(v_K^-(b), v_K^+(a)\bigr) = \frac12 \int_{(a, b)} h_K \, d\sigma_K + \mathcal{J}\bigl(v_K^-(b), v_K^+(a)\bigr) . \tag{8.2}
```

The formalization proves only the second equality
([`cvx_area_cut`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1384)), and uses it in Lemma
8.19. It follows from Theorem 8.4 for $K'$ and Lemma 8.15 (3): on the period
$(t' - \pi, t' + \pi]$, the measure $\sigma_{K'}$ equals $\sigma_K$ on $(a, b)$, has an atom of mass
$\lvert v_K^+(a) - v_K^-(b) \rvert$ at $t' + \pi$, and vanishes elsewhere. By Proposition 8.12 (2),
the atom contributes $\mathcal{J}(v_K^-(b), v_K^+(a))$.

### Lemma 8.17 (the bilinear form along the vertices; Baek, Lemma 7.3.3)

For $a < b < a + \pi$,

```math
\mathcal{B}(K_1, K_2) = \frac12 \int_{(a, b)} v_{K_1}^+(t) \times dv_{K_2}^+(t) = \frac12 \int_{(a, b)} v_{K_1}^-(t) \times dv_{K_2}^+(t) .
```

In particular $\mathcal{J}(\mathbf{u}_K^{a,b}) = \frac12 \int_{(a, b)} v_K^+ \times dv_K^+$.

*Proof.* On $(a, b)$, $dv_{K_2}^+ = v_t \, d\sigma_{K_2}$. Both vertices $v_{K_1}^\pm(t)$ lie on
$l_{K_1}(t)$, so $v_{K_1}^\pm(t) \times v_t = \langle v_{K_1}^\pm(t), u_t \rangle = h_{K_1}(t)$.
$\square$

*Lean: [`lemma7_3_3`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1124),
[`lemma7_3_3_self`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1142),
[`cvx_integral_cross_dvplus`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L524).*

### Lemma 8.18 (concatenation; Baek, Lemma 7.3.4)

For $a < b < c < a + \pi$, the curve $\mathbf{u}_K^{a,c}$ is the union of $\mathbf{u}_K^{a,b}$,
$e_K(b)$ and $\mathbf{u}_K^{b,c}$, which meet only at $v_K^-(b)$ and $v_K^+(b)$, and

```math
\mathcal{J}(\mathbf{u}_K^{a,c}) = \mathcal{J}(\mathbf{u}_K^{a,b}) + \mathcal{J}\bigl(v_K^-(b), v_K^+(b)\bigr) + \mathcal{J}(\mathbf{u}_K^{b,c}) .
```

*Proof.* Two edges $e_K(t)$ and $e_K(s)$ with $t < s < t + \pi$ meet at most at $v_K^-(s)$
([`cvx_edge_inter_eq_vminus`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L64)), which gives
the set identities. For the formula, split $(a, c) = (a, b) \cup \lbrace b \rbrace \cup (b, c)$. The
atom at $b$ contributes $\frac12 h_K(b)\, \sigma_K(\lbrace b \rbrace)$. The edge $e_K(b)$ runs from
$v_K^-(b)$ to $v_K^+(b)$ in the direction $v_b$ and has length $\sigma_K(\lbrace b \rbrace)$, so by
Proposition 8.12 (2) this is $\mathcal{J}(v_K^-(b), v_K^+(b))$. $\square$

*Lean: [`lemma7_3_4`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1151).*

### Lemma 8.19 (the region between an arc and its tangents; Baek, Lemma 7.3.5)

Let $a < b < a + \pi$ with $v_K^+(a) \ne v_K^-(b)$, let $T$ be the triangle with vertices
$v_K^+(a)$, $v_K(a, b)$, $v_K^-(b)$, and

```math
R = T^\circ \setminus \bigcap_{t \in [a, b]} H_K(t) .
```

Then $R$ lies in the interior of $H_K(a) \cap H_K(b)$, is disjoint from
$\bigcap_{t \in [a, b]} H_K(t)$, and

```math
\lvert R \rvert = \mathcal{J}\bigl(v_K^+(a), v_K(a, b)\bigr) + \mathcal{J}\bigl(v_K(a, b), v_K^-(b)\bigr) - \mathcal{J}(\mathbf{u}_K^{a,b}) .
```

*Lean: [`lemma7_3_5`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1633),
[`convexCurveRegion`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1616),
[`cvx_area_cut`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1384),
[`cvx_area_triangle`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1584).*

The paper's statement (1) is that the boundary of $R$, the two tangent segments followed by the arc
backwards, is a counterclockwise Jordan curve; the paper then reads $\lvert R \rvert$ off it with
Green's theorem. The Lean statement defines $R$ directly, as $T^\circ$ minus the half-planes, and
states its area, which is how the paper uses (1); so (3) holds by definition, and the paper's
argument for it (the region enclosed by $\Gamma$ is simply connected) is not needed. Mathlib has
neither the Jordan curve theorem nor Green's theorem (REPORT.md, Sections 6 and 7).

*Proof.* The idea is that $R$ is the triangle $T$ minus the body $K'$ of Lemma 8.15 (Figure 8.3).
The vertices of $T$ lie in $H_K(a) \cap H_K(b)$, hence so does $T$, and $R \subseteq T^\circ$ lies
in the interior of that intersection. Disjointness holds by definition.

For the area, let $K'$ and $t'$ be as in Lemma 8.15. The half-planes $H_K(t)$, $t \in [a, b]$, cut
out exactly $K'$ from $T$: $T \cap \bigcap_{t \in [a, b]} H_K(t) = K'$. Indeed $K' \subseteq T \cap K$.
Conversely, $K'$ is the intersection of its supporting half-planes $H_{K'}(t)$,
$t \in (t' - \pi, t' + \pi]$. By Lemma 8.15 (3), these are the $H_K(t)$ for $t \in [a, b]$, and the
supporting half-planes of $T$ for the other $t$, since $K'$ and $T$ touch them at the same vertex
$v_K^+(a)$ or $v_K^-(b)$, or along the chord. So a point of $T$ in every $H_K(t)$, $t \in [a, b]$,
lies in every $H_{K'}(t)$, that is, in $K'$. The boundary of $T$ has measure zero, so
$\lvert R \rvert = \lvert T \rvert - \lvert K' \rvert$.
The triangle is positively oriented, so $\lvert T \rvert$ is the sum of $\mathcal{J}$ over its three
sides,

```math
\lvert T \rvert = \mathcal{J}\bigl(v_K^+(a), v_K(a, b)\bigr) + \mathcal{J}\bigl(v_K(a, b), v_K^-(b)\bigr) + \mathcal{J}\bigl(v_K^-(b), v_K^+(a)\bigr) ,
```

and $\lvert K' \rvert$ is given by (8.2). Subtracting gives the formula. $\square$

## 8.4 Mamikon's theorem

### Definition 8.20 (Mamikon region and its area; Baek, Definitions 7.4.1, 7.4.2)

Let $a < b < a + \pi$. For $\alpha : [a, b] \to \mathbb{R}$, the *Mamikon region* is the union of
the tangent segments from $v_K^+(t)$ to $v_K^+(t) + \alpha(t)\, v_t$, $t \in [a, b]$. For
$\mathbf{z} \in C^\mathrm{BV}[a, b]$ with $\mathbf{z}(t) \in l_K(t)$ for every $t$, put

```math
\mathcal{M}_K(a, b; \mathbf{z}) = \mathcal{J}\bigl(v_K^+(a), \mathbf{z}(a)\bigr) + \mathcal{J}(\mathbf{z}|_{[a, b]}) + \mathcal{J}\bigl(\mathbf{z}(b), v_K^-(b)\bigr) - \mathcal{J}(\mathbf{u}_K^{a,b}) .
```

*Lean: [`mamikonRegion`](../../MovingSofaOptimality/Convex/Mamikon.lean#L558),
[`mamikon`](../../MovingSofaOptimality/Convex/Mamikon.lean#L563).*

$\mathcal{M}_K(a, b; \mathbf{z})$ is $\mathcal{J}$ of the closed path that goes out along the first
tangent segment, along $\mathbf{z}$, back along the last tangent segment, and back along the arc.
When the segments from $v_K^+(t)$ to $\mathbf{z}(t)$ sweep the region between the arc and
$\mathbf{z}$ once, this is the area of that region (Figure 8.5). The formalization uses only the
number $\mathcal{M}_K$.

![Left: a lens K, light blue, the intersection of two discs, with a corner at its top. A thick arc of its boundary runs from v_K^+(a) on the right, over the corner, to v_K^-(b) on the left; orange tangent segments start on the arc and point counterclockwise, turning about the corner where the arc has its corner, and end on an orange curve z from z(a) to z(b); the region between the arc and z is shaded. Right: the same vectors alpha(t) v_t drawn from a common point Q form a shaded fan bounded by the curve Q + alpha(t) v_t](figures/08-convex-curves/mamikon.svg)

*Figure 8.5.* Mamikon's theorem for a lens $K$. Left: the tangent segments from $v_K^+(t)$ to
$\mathbf{z}(t) = v_K^+(t) + \alpha(t)\, v_t$, $t \in [a, b]$. Across the corner of the lens,
$v_K^+$ stays put while $t$ increases, and the segments turn about the corner. Right: the same
vectors $\alpha(t)\, v_t$, drawn from a common point $Q$. The two shaded regions have the same area,
$\frac12 \int_a^b \alpha(t)^2\, dt$.

### Theorem 8.21 (Mamikon's theorem; Baek, Theorem 7.4.1)

Let $a < b < a + \pi$ and let $\mathbf{z} \in C^\mathrm{BV}[a, b]$ satisfy
$\mathbf{z}(t) \in l_K(t)$ for $t \in [a, b]$. Then
$\alpha(t) = \langle \mathbf{z}(t) - v_K^+(t), v_t \rangle$ is bounded and measurable on $[a, b]$,
$\mathbf{z}(t) = v_K^+(t) + \alpha(t)\, v_t$, and

```math
\mathcal{M}_K(a, b; \mathbf{z}) = \frac12 \int_a^b \alpha(t)^2 \, dt .
```

*Lean: [`theorem7_4_1`](../../MovingSofaOptimality/Convex/Mamikon.lean#L569),
[`cvx_mamikon_core`](../../MovingSofaOptimality/Convex/Mamikon.lean#L425),
[`cvx_ibp_cross_vplus`](../../MovingSofaOptimality/Convex/Mamikon.lean#L171).*

For a smooth convex curve this is Mnatsakanian's theorem, known as Mamikon's theorem: the region
swept by tangent segments has the area of the region swept by the same vectors moved to a common
point (Figure 8.5, right), which is $\frac12 \int \alpha^2$ by the area formula in polar
coordinates. Baek's version holds for every convex body. Across a corner of $K$ the segments turn
about the corner and sweep a fan of area $\frac12 \int \alpha^2$. Across an edge, $\alpha$ jumps
down by the length of the edge while $\mathbf{z}$ stays continuous.

*Proof.* Write $\mathbf{v} = v_K^+$. Both $\mathbf{z}(t)$ and $\mathbf{v}(t)$ lie on $l_K(t)$, so
$\mathbf{z}(t) - \mathbf{v}(t) = \alpha(t)\, v_t$. The function $\alpha$ is measurable since $v_K^+$
is, bounded since $K$ is bounded and $\mathbf{z}$ is continuous on a compact interval, and
right-continuous and of bounded variation since $\mathbf{z}$ and $\mathbf{v}$ are (Theorem 2.9,
Lemma 6.11). As measures on $(a, b)$,

```math
\mathbf{z} \times d\mathbf{z} - \mathbf{v} \times d\mathbf{v} + d(\mathbf{z} \times \mathbf{v}) = (\mathbf{z} - \mathbf{v}) \times d(\mathbf{z} + \mathbf{v}) = (\mathbf{z} - \mathbf{v}) \times d(\mathbf{z} - \mathbf{v}) = \alpha v_t \times d(\alpha v_t) = \alpha v_t \times (v_t\, d\alpha + \alpha\, dv_t) = \alpha^2\, dt .
```

The first equality is the product rule $d(\mathbf{z} \times \mathbf{v}) = d\mathbf{z} \times \mathbf{v} + \mathbf{z} \times d\mathbf{v}$
([Lemma 6.4](06-surface-area.md#lemma-64-product-rule-baek-lemma-513), as $\mathbf{z}$ is
continuous) with the bilinearity of $\times$. The second uses
$(\mathbf{z} - \mathbf{v}) \times d\mathbf{v} = 0$, as $d\mathbf{v} = v_t\, \sigma_K$ (Theorem 6.12)
is parallel to $\mathbf{z} - \mathbf{v}$. The last two are the product rule for $\alpha v_t$, with
$v_t$ continuous, $v_t \times v_t = 0$, $dv_t = -u_t\, dt$ and $v_t \times (-u_t) = 1$. Integrate
over $(a, b)$: $\int \mathbf{z} \times d\mathbf{z} = 2\mathcal{J}(\mathbf{z})$;
$\int \mathbf{v} \times d\mathbf{v} = \int h_K\, d\sigma_K = 2\mathcal{J}(\mathbf{u}_K^{a,b})$
(Lemma 8.17); and
$d(\mathbf{z} \times \mathbf{v})((a, b)) = \mathbf{z}(b) \times v_K^-(b) - \mathbf{z}(a) \times v_K^+(a)$.
These are twice the terms of Definition 8.20. $\square$

In the paper's last line $\alpha u_t$ should read $\alpha v_t$, with $dv_t = -u_t\, dt$; the result is
unaffected (REPORT.md, E27). The measurability claim is read on $[a, b]$, where $\mathbf{z}$ is
constrained (REPORT.md, Section 6).

### Theorem 8.22 (Mamikon areas are convex; Baek, Theorem 7.4.2)

Let $a < b < a + \pi$, and let $K \mapsto \mathbf{z}_K \in C^\mathrm{BV}[a, b]$ satisfy
$\mathbf{z}_K(t) \in l_K(t)$ and
$\mathbf{z}_{(1 - \lambda) K_1 + \lambda K_2}(t) = (1 - \lambda)\, \mathbf{z}_{K_1}(t) + \lambda\, \mathbf{z}_{K_2}(t)$
for $t \in [a, b]$. Then $K \mapsto \mathcal{M}_K(a, b; \mathbf{z}_K)$ is a convex quadratic
functional on $\mathcal{K}$.

*Proof.* The function $\alpha_K(t) = \langle \mathbf{z}_K(t) - v_K^+(t), v_t \rangle$ is
convex-linear in $K$, by the hypothesis on $\mathbf{z}_K$ and Theorem 8.3 (2). By Theorem 8.21,
$\mathcal{M}_K(a, b; \mathbf{z}_K) = \frac12 \int_a^b \alpha_K^2\, dt$, the diagonal of the
convex-bilinear form $\frac12 \int_a^b \alpha_{K_1} \alpha_{K_2}\, dt$. It is convex because, at
each $t$,

```math
(1 - \lambda)\, \alpha_{K_1}^2 + \lambda\, \alpha_{K_2}^2 - \bigl((1 - \lambda)\, \alpha_{K_1} + \lambda\, \alpha_{K_2}\bigr)^2 = \lambda (1 - \lambda)\, (\alpha_{K_1} - \alpha_{K_2})^2 \ \ge\ 0 . \qquad \square
```

*Lean: [`theorem7_4_2`](../../MovingSofaOptimality/Convex/Mamikon.lean#L611).*
