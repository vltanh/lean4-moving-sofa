# 8. Convex curves and Mamikon's theorem

[Contents](README.md) · [← 7. The injectivity condition](07-injectivity.md) · [9. The upper bound and the optimality of Gerver's sofa →](09-optimality.md)

This chapter prepares the tools of [Chapter 9](09-optimality.md), following Baek's Chapter 7. The
upper bound $\mathcal{Q}$ of Chapter 9 is a *quadratic* functional on a *convex domain*, a set in
which convex combinations make sense; §8.1 sets up these notions and proves the fact that drives the
whole argument (Theorem 8.7): a concave quadratic functional attains its maximum at a point where
all its directional derivatives are nonpositive. §8.2 introduces the *curve area functional*
$\mathcal{J}(\mathbf{x}) = \frac12 \int \mathbf{x} \times d\mathbf{x}$, the signed area swept by the
segment from the origin to a point moving along a curve $\mathbf{x}$. §8.3 evaluates it on an arc
$\mathbf{u}_K^{a,b}$ of the boundary of a convex body $K$, where it equals
$\frac12 \int_{(a,b)} h_K \, d\sigma_K$, a quadratic functional of $K$ (Theorem 8.16). §8.4 proves
Mamikon's theorem for convex bodies with corners and edges (Theorem 8.21): the area swept by tangent
segments of lengths $\alpha(t)$ is $\frac12 \int \alpha(t)^2 \, dt$. When the far ends of the
segments depend linearly on $K$, this area is a *convex* quadratic functional of $K$ (Theorem 8.22),
which is how Chapter 9 shows that $\mathcal{Q}$ is concave.

The paper defines $\mathcal{J}$ of a convex arc through a parametrization of the arc as a Jordan
arc, and computes the areas of the regions it needs with the Jordan curve theorem and Green's
theorem (its Theorems 7.2.1 and 7.2.3 and Proposition 7.2.7). The formalization uses none of them.
It defines $\mathcal{J}$ for every continuous curve of bounded variation, and computes each area
that the paper reads off a Jordan curve directly: the curve area functional of a convex arc through
an explicit injective parametrization by arc length (Theorem 8.16, Figure 8.4), and the area of the
region between a convex arc and its two end tangents as a triangle minus a convex body (Lemma 8.19).
[Chapter 9](09-optimality.md) does the same for the parts of the niche (REPORT.md, Section 6).

Throughout, $u_t = (\cos t, \sin t)$ and $v_t = (-\sin t, \cos t)$; a convex body $K$ has the
support function $h_K$, the supporting line $l_K(t)$ and half-plane $H_K(t)$ of normal angle $t$,
the edge $e_K(t) = K \cap l_K(t)$ with end points $v_K^-(t)$ and $v_K^+(t)$ (the latter farther in
the direction $v_t$), the point $v_K(a, b) = l_K(a) \cap l_K(b)$, and the surface area measure
$\sigma_K$ ([Chapter 2](02-preliminaries.md), [Chapter 6](06-surface-area.md)).

## 8.1 Convex domains and quadratic functionals

### Definition 8.1 (convex domain; Baek, Definitions 7.1.1–7.1.4)

A *convex domain* is a set $\mathcal{V}$ with operations
$c_\lambda : \mathcal{V} \times \mathcal{V} \to \mathcal{V}$, $\lambda \in [0, 1]$, for which some
injective map $e$ from $\mathcal{V}$ into a real vector space satisfies
$e(c_\lambda(v, w)) = (1 - \lambda) e(v) + \lambda e(w)$. A map $f$ between convex domains is
*convex-linear* if $f(c_\lambda(v, w)) = c_\lambda(f(v), f(w))$; a map of two variables is
*convex-bilinear* if it is convex-linear in each variable; and a functional
$f : \mathcal{V} \to \mathbb{R}$ is *quadratic* if $f(v) = g(v, v)$ for a convex-bilinear
$g : \mathcal{V} \times \mathcal{V} \to \mathbb{R}$. Here $\mathbb{R}$, and every real vector space,
is a convex domain with $c_\lambda(x, y) = (1 - \lambda) x + \lambda y$.

*Lean: [`ConvexDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L27),
[`ConvexDomain.IsConvexLinear`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L38),
[`ConvexDomain.IsConvexBilinear`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L43),
[`ConvexDomain.IsQuadratic`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L48),
[`realDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L33),
[`vectorDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L151).*

The Lean structure carries the operation for every real $\lambda$, and only $\lambda \in [0, 1]$ is
ever used. Baek remarks that convex domains are the cancellative convex spaces of Stone; nothing
depends on this.

### Theorem 8.2 (convex bodies; Baek, Theorem 7.1.1)

The planar convex bodies $\mathcal{K}$ form a convex domain under Minkowski combinations
$c_\lambda(K_1, K_2) = (1 - \lambda) K_1 + \lambda K_2$, and $K \mapsto h_K$ embeds it into the
vector space of functions $\mathbb{R} \to \mathbb{R}$.

*Proof.* A Minkowski combination of nonempty compact convex sets is nonempty, compact and convex.
For $\lambda \in [0, 1]$, a point of $(1 - \lambda) K_1 + \lambda K_2$ that maximizes
$\langle \cdot, u_t \rangle$ is the combination of maximizers in $K_1$ and $K_2$, so

```math
h_{(1 - \lambda) K_1 + \lambda K_2}(t) = (1 - \lambda)\, h_{K_1}(t) + \lambda\, h_{K_2}(t) .
```

A convex body is the intersection of its supporting half-planes, so $h_K$ determines $K$, and the
map $K \mapsto h_K$ is injective. $\square$

*Lean: [`theorem7_1_1`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L212),
[`convexBodyDomain`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L224),
[`convexBodyComb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L198),
[`supp_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L176),
[`isConvexBody_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L170),
[`eq_of_supp_eq`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L170).*

### Theorem 8.3 (convex-linear quantities; Baek, Theorem 7.1.2)

For fixed angles $t, a, b$, the following are convex-linear in $K \in \mathcal{K}$:

1. the support value $h_K(t)$;
2. the points $v_K^+(a)$, $v_K^-(a)$ and $v_K(a, b)$;
3. the surface area measure:
   $\sigma_{(1 - \lambda) K_1 + \lambda K_2} = (1 - \lambda)\, \sigma_{K_1} + \lambda\, \sigma_{K_2}$.

*Proof.* (1) is the display in the proof of Theorem 8.2. (2) For $b \ne a, a + \pi$, the point
$v_K(a, b)$ is the solution of $\langle p, u_a \rangle = h_K(a)$, $\langle p, u_b \rangle = h_K(b)$:

```math
v_K(a, b) = h_K(a)\, u_a + \frac{h_K(b) - h_K(a) \cos(b - a)}{\sin(b - a)}\, v_a ,
```

linear in $h_K(a), h_K(b)$. The vertices $v_K^+(a)$ and $v_K^-(a)$ are the limits of $v_K(a, b)$ as
$b \to a$ from above and from below ([Theorem 2.9](02-preliminaries.md)), and limits preserve
combinations. (3) In the formalization $\sigma_K$ is the Lebesgue–Stieltjes measure of the function
$t \mapsto \langle v_K^+(t), v_t \rangle + \int_0^t h_K$ ([Chapter 6](06-surface-area.md)), which is
convex-linear in $K$ by (1) and (2); the Stieltjes measure of a combination of such functions is the
combination of their measures. $\square$

*Lean: [`theorem7_1_2_supp`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L229),
[`theorem7_1_2_vertices`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L258),
[`theorem7_1_2_sigma`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L279),
[`cvx_vplus_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L240),
[`cvx_sigmaFun_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L265).*

The paper assumes $a < b < a + \pi$ in (2); the Lean statement holds for all $a, b$, the formula for
$v_K(a, b)$ being the definition of [`vint`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L69)
(REPORT.md, Section 5).

### Theorem 8.4 (the area is quadratic; Baek, Theorem 7.1.3)

For every convex body $K$,

```math
\lvert K \rvert = \frac12 \int_{[0, 2\pi)} h_K \, d\sigma_K ,
```

and $K \mapsto \lvert K \rvert$ is a quadratic functional on $\mathcal{K}$, with the convex-bilinear
form $(K_1, K_2) \mapsto \frac12 \int_{[0, 2\pi)} h_{K_1} \, d\sigma_{K_2}$.

*Proof sketch.* The formula is Schneider's (*Convex Bodies*, Remark 5.1.2). The formalization proves
it in
[`MovingSofaOptimality/External/AreaFormula.lean`](../../MovingSofaOptimality/External/AreaFormula.lean)
by a change of variables from an interior point, along the arc-length parametrization of
$\partial K$ whose normal angle pushes Lebesgue measure forward to $\sigma_K$. When $K$ has empty
interior it is a segment or a point, and both sides vanish. The form is convex-linear in $K_1$ by
Theorem 8.3 (1) and in $K_2$ by Theorem 8.3 (3), the integrand being continuous on a bounded
interval. $\square$

*Lean: [`theorem7_1_3`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L296),
[`theorem7_1_3_quadratic`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L332),
[`area_eq_half_integral_supp`](../../MovingSofaOptimality/External/AreaFormula.lean#L592),
[`cvx_integral_supp_sigma_bilin`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L302).*

### Definition 8.5 (directional derivative, concavity; Baek, Definitions 7.1.5, 7.1.6)

For a functional $f$ on a convex domain $\mathcal{V}$ and $K, K' \in \mathcal{V}$, the *directional
derivative* of $f$ at $K$ towards $K'$ is the one-sided derivative

```math
Df(K; K') = \left. \frac{d}{d\lambda} \right|_{\lambda = 0} f\bigl(c_\lambda(K, K')\bigr) ,
```

taken within $[0, 1]$. The functional $f$ is *concave* if
$f(c_\lambda(K_1, K_2)) \ge (1 - \lambda) f(K_1) + \lambda f(K_2)$ for all $K_1, K_2$ and
$\lambda \in [0, 1]$, and *convex* if the reverse inequality holds.

*Lean: [`ConvexDomain.dirDeriv`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L53),
[`ConvexDomain.IsConcave`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L98),
[`ConvexDomain.IsConvexFun`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L102).*

### Lemma 8.6 (derivative of a quadratic functional; Baek, Lemma 7.1.4)

Let $f(K) = g(K, K)$ with $g$ convex-bilinear. For $\lambda \in [0, 1]$,

```math
f\bigl(c_\lambda(K, K')\bigr) = (1 - \lambda)^2 g(K, K) + \lambda (1 - \lambda) \bigl(g(K, K') + g(K', K)\bigr) + \lambda^2 g(K', K') , \tag{8.1}
```

and $Df(K; K') = g(K, K') + g(K', K) - 2 g(K, K)$. In particular $Df(K; \cdot)$ is convex-linear.

*Proof.* Expand $g(c_\lambda(K, K'), c_\lambda(K, K'))$ in each variable. The right side of (8.1) is
the polynomial
$g(K, K) + \lambda\, \bigl(g(K, K') + g(K', K) - 2 g(K, K)\bigr) + \lambda^2 \bigl(g(K, K) - g(K, K') - g(K', K) + g(K', K')\bigr)$,
whose derivative at $0$ is the stated one. $\square$

*Lean: [`lemma7_1_4`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L81),
[`cvx_bilin_comb`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L58).*

### Theorem 8.7 (maximum of a concave quadratic functional; Baek, Theorem 7.1.5)

Let $f$ be a concave quadratic functional on a convex domain $\mathcal{V}$, and $K \in \mathcal{V}$.
Then $f(K') \le f(K)$ for every $K' \in \mathcal{V}$ if and only if $Df(K; K') \le 0$ for every
$K' \in \mathcal{V}$.

![The graph of a concave parabola p over the interval from 0 to 1, falling from f(K) at lambda = 0 to f(K') at lambda = 1; a dashed chord joins its two ends, a green segment at lambda = 1/2 marks the gap between the parabola above and the chord below, and a dashed orange line, the tangent at lambda = 0 with slope Df(K; K'), lies above the parabola](figures/08-convex-curves/midpoint.svg)

*Figure 8.1.* The proof of Theorem 8.7. Along the segment from $K$ to $K'$, the functional is the
quadratic polynomial $p(\lambda) = A + \delta \lambda + E \lambda^2$ of (8.1). Concavity at the
midpoint alone says that $p(\frac12)$ lies above the chord, by the gap $-E/4 \ge 0$ (green); with
the slope $\delta = Df(K; K') \le 0$ (orange) this gives $f(K') = A + \delta + E \le A = f(K)$.

*Proof.* Fix $K'$ and write $p(\lambda) = f(c_\lambda(K, K')) = A + \delta \lambda + E \lambda^2$ by
(8.1), with $A = f(K)$, $\delta = Df(K; K')$ and $E = g(K, K) - g(K, K') - g(K', K) + g(K', K')$.

If $K$ maximizes $f$, then $\delta \lambda + E \lambda^2 = p(\lambda) - p(0) \le 0$ for
$\lambda \in (0, 1]$; dividing by $\lambda$ and letting $\lambda \to 0$ gives $\delta \le 0$. (The
Lean proof argues by contradiction with the single value
$\lambda = \min(1, \delta / (2(\lvert E \rvert + 1)))$.)

Conversely, let $\delta \le 0$. Concavity at $\lambda = \frac12$ gives
$p(\frac12) \ge \frac12 (p(0) + p(1))$, that is,

```math
A + \tfrac12 \delta + \tfrac14 E \ \ge\ A + \tfrac12 \delta + \tfrac12 E ,
```

so $E \le 0$: the gap $p(\frac12) - \frac12(p(0) + p(1)) = -E/4$ is nonnegative (Figure 8.1). Then
$f(K') = p(1) = A + \delta + E \le A = f(K)$. $\square$

*Lean: [`theorem7_1_5`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L107).*

The proof uses concavity only at the midpoint of each segment.

### Definition 8.8 (equality modulo linear functionals; Baek, Definition 7.1.7)

For functionals $f, g$ on a convex domain $\mathcal{V}$, write $f \equiv_{\mathcal{V}} g$ (or
$f(K) \equiv_K g(K)$) if $f - g$ is convex-linear.

*Lean: [`ConvexDomain.EqModLinear`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L147).*

### Lemma 8.9 (shifting the arguments of a bilinear form; Baek, Lemma 7.1.6)

Let $h$ be a bilinear form on a real vector space $V$ and $c_1, c_2 \in V$. Then
$h(K, K) \equiv_K h(K + c_1, K + c_2)$.

*Proof.* The difference $h(c_1, K) + h(K, c_2) + h(c_1, c_2)$ is affine in $K$. $\square$

*Lean: [`lemma7_1_6`](../../MovingSofaOptimality/Convex/ConvexDomain.lean#L157).*

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
$\mathcal{B}(\mathbf{x}_1, \mathbf{x}_2) = \frac12 \int_a^b \mathbf{x}_1 \times d\mathbf{x}_2$; and
for points $p, q$, $\mathcal{J}(p, q) = \frac12 (p \times q)$.

*Lean: [`cross`](../../MovingSofaOptimality/Basic/Plane.lean#L35),
[`crossCLM`](../../MovingSofaOptimality/Convex/CurveArea.lean#L322),
[`IsCBV`](../../MovingSofaOptimality/Convex/CurveArea.lean#L341),
[`MovingSofaOptimality.CBV`](../../MovingSofaOptimality/Convex/CurveArea.lean#L353),
[`lsMeasure`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L54),
[`curveBilin`](../../MovingSofaOptimality/Convex/CurveArea.lean#L345),
[`curveArea`](../../MovingSofaOptimality/Convex/CurveArea.lean#L350),
[`segArea`](../../MovingSofaOptimality/Convex/CurveArea.lean#L468).*

For a continuously differentiable curve,
$\mathcal{J}(\mathbf{x}) = \frac12 \int_a^b \mathbf{x}(t) \times \mathbf{x}'(t) \, dt$
([`curveArea_eq_integral`](../../MovingSofaOptimality/Convex/CurveArea.lean#L452)). The integrand is
twice the rate at which the segment from the origin $O$ to $\mathbf{x}(t)$ sweeps area, counted
positively when it turns counterclockwise. So $\mathcal{J}(\mathbf{x})$ is the signed area swept by
that segment; if $\mathbf{x}$ runs once counterclockwise around the boundary of a region, it is the
area of the region (Green's theorem). The formalization never uses the last statement.

### Proposition 8.11 (quadratic; Baek, Proposition 7.2.2)

$\mathcal{J}$ is a quadratic functional on $C^\mathrm{BV}[a, b]$, with
$\mathcal{J}(\mathbf{x}) = \mathcal{B}(\mathbf{x}, \mathbf{x})$.

*Proof.* $\mathcal{B}$ is linear in $\mathbf{x}_1$, an integral of a linear expression, and linear
in $\mathbf{x}_2$, since the Lebesgue–Stieltjes measure of a linear combination of curves is the
combination of their measures. $\square$

*Lean: [`proposition7_2_2`](../../MovingSofaOptimality/Convex/CurveArea.lean#L395),
[`cbvDomain`](../../MovingSofaOptimality/Convex/CurveArea.lean#L374),
[`cvx_lsMeasure_comb`](../../MovingSofaOptimality/Convex/CurveArea.lean#L361),
[`cvx_curveBilin_comb_left`](../../MovingSofaOptimality/Convex/CurveArea.lean#L379).*

### Proposition 8.12 (segments; Baek, Propositions 7.2.4, 7.2.5)

1. The segment $s \mapsto p + s (q - p)$, $s \in [0, 1]$, has curve area functional
   $\mathcal{J}(p, q)$.
2. If $\langle p, u_t \rangle = h$ and $q - p = d\, v_t$, then $\mathcal{J}(p, q) = hd/2$.
3. If $p$, $q$ and $O$ lie on a line, then $\mathcal{J}(p, q) = 0$.

*Proof.* (1) Along the segment,
$\mathbf{x} \times \mathbf{x}' = (p + s(q - p)) \times (q - p) = p \times q$. (2) Since
$p \times v_t = \langle p, u_t \rangle$, $p \times q = p \times (q - p) = d\,(p \times v_t) = hd$.
(3) is (2) with $h = 0$. $\square$

*Lean: [`proposition7_2_4`](../../MovingSofaOptimality/Convex/CurveArea.lean#L472),
[`proposition7_2_4_line`](../../MovingSofaOptimality/Convex/CurveArea.lean#L483),
[`proposition7_2_5`](../../MovingSofaOptimality/Convex/CurveArea.lean#L492).*

Baek's Proposition 7.2.4 also assumes $q$ on the line $l(t, h)$; this follows from the other
hypotheses (REPORT.md, Section 5).

### Proposition 8.13 (additivity; Baek, Proposition 7.2.6)

If $a \le b \le c$ and $\mathbf{x} \in C^\mathrm{BV}[a, c]$, then
$\mathcal{J}(\mathbf{x}|_{[a, c]}) = \mathcal{J}(\mathbf{x}|_{[a, b]}) + \mathcal{J}(\mathbf{x}|_{[b, c]})$.

*Proof.* Split the integral over $[a, b]$ and $(b, c]$. The measure $d\mathbf{x}$ has no atoms,
$\mathbf{x}$ being continuous, and its restriction to $[a', b'] \subseteq [a, c]$ is the
Lebesgue–Stieltjes measure of $\mathbf{x}|_{[a', b']}$. $\square$

*Lean: [`proposition7_2_6`](../../MovingSofaOptimality/Convex/CurveArea.lean#L504).*

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
([Theorem 10.19](10-gerver.md)).

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

*Lean: [`convexCurve`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L28),
[`convexCurveArea`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L32),
[`convexCurveBilin`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L36).*

The paper defines $\mathcal{J}(\mathbf{u}_K^{a,b})$ through a parametrization of the arc and proves
the formula as Theorem 7.3.2. The formalization takes the formula as the definition
([`convexCurveArea`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L32)), and Theorem 8.16
below shows that it is the curve area functional of a parametrization of the arc. Each piece of the
arc, of length $\sigma_K(dt)$ at normal angle $t$, is the base of a thin triangle with apex $O$ and
height $h_K(t)$, of area $\frac12 h_K(t)\, \sigma_K(dt)$ (Figure 8.2).

![A convex body K, light blue, the convex hull of an ellipse and a point P above it. A thick arc of its boundary runs from v_K^+(a) on the right, up the ellipse, along a straight edge to the corner P, along a second edge and down the ellipse to v_K^-(b) on the left. The region swept by the segment from the origin O, inside K, to the arc is shaded orange, with thin rays to points of the arc; two darker triangles O Q1 P and O P Q2 are the contributions of the two edges. The supporting line of the first edge and the perpendicular from O to it, of length h_K(t1), are drawn](figures/08-convex-curves/curve-area.svg)

*Figure 8.2.* The curve area functional of a convex arc, for the convex hull $K$ of an ellipse and a
point $P$. The segment from $O$ to the arc $\mathbf{u}_K^{a,b}$ sweeps the orange region, of area
$\frac12 \int_{(a,b)} h_K\, d\sigma_K$. An edge $e_K(t_1)$ is an atom of $\sigma_K$ of mass equal to
its length, and contributes the dark triangle of area
$\frac12 h_K(t_1)\, \sigma_K(\lbrace t_1 \rbrace)$; the corner $P$, whose normal angles fill an
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

*Lean: [`lemma7_3_1`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L287),
[`lemma7_3_1_degenerate`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L258).*

*Proof sketch.* $K$ lies in the cone $X = H_K(a) \cap H_K(b)$, whose vertex $v_K(a, b)$ satisfies
$v_K(a, b) = v_K^+(a) + \alpha v_a$ and $v_K^-(b) = v_K(a, b) + \beta v_b$ with
$\alpha, \beta \ge 0$. If $v_K(a, b) \in K$, it is a common point of the two supporting lines, hence
equal to both $v_K^+(a)$ and $v_K^-(b)$, and every edge $e_K(t)$, $t \in (a, b)$, reduces to it.
Otherwise $\alpha, \beta > 0$, so the three points are not collinear, which is (1), and
$v_K^-(b) - v_K^+(a) = \alpha v_a + \beta v_b$ is a positive multiple of $v_{t'}$ for some
$t' \in (a, b)$, which is (2); Baek's proof writes this difference with the opposite sign
([`REPORT.md`](../../REPORT.md), E26). The triangle $T = X \cap H'$ has the normal angles $a$, $b$ and
$t' + \pi$; $K'$ lies in $T$ and contains its side on $l'$, which gives (i), (iii) and (iv). For
(ii), every point of $K \setminus T$ lies strictly inside $H_K(t)$ for $t \in (a, b)$, so
$e_K(t) \subseteq T$ and $e_K(t) = e_{K'}(t)$. $\square$

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

*Lean: [`theorem7_3_2`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1211),
[`theorem7_3_2_quadratic`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1251),
[`cvxArc`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L821),
[`cvxQuantile`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L632),
[`cvx_map_cvxQuantile`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L703),
[`cvxArc_image`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1065),
[`cvxArc_injOn`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1123),
[`cvxArc_curveArea`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1157).*

![Left: the graph of r = F(t) for t from a to b, the normalized distribution function of the surface area measure of K on (a, b); it rises along the ellipse, jumps up at t1 and at t2, the jumps drawn orange and labelled edge, and is flat between t1 and t2, labelled corner, before rising to 1 at b. Right: the body K with its arc from gamma(0) on the right to gamma(1) on the left, the two edges orange, and thirteen black points equally spaced along the arc](figures/08-convex-curves/quantile.svg)

*Figure 8.4.* The parametrization of the proof of Theorem 8.16. Left: the normalized distribution
function $F(t) = \sigma_K((a, t]) / L$ of the arc of Figure 8.2. It jumps at the normal angles
$t_1, t_2$ of the two edges, by their lengths over $L$, and is flat on $(t_1, t_2)$, the normal
angles of the corner $P$. Its generalized inverse $\theta(r)$ is read off sideways: it is constant
(equal to $t_i$) while $r$ runs through a jump, and it jumps across the flat part. Right: the curve
$\gamma(s) = v_K^+(a) + L \int_0^s v_{\theta(r)}\, dr$ runs along the arc at constant speed, here
shown at $s = 0, \frac1{12}, \dots, 1$.

*Proof.* Let $L = \sigma_K((a, b))$, the length of the arc. If $L = 0$, then
$v_K^-(b) - v_K^+(a) = \int_{(a, b)} v_t \, \sigma_K(dt) = 0$ (Baek's Theorem 5.2.2,
$dv_K^+ = v_t\, d\sigma_K$; [Theorem 6.12](06-surface-area.md)), the arc is a point by Lemma 8.15,
and the constant curve works.

Let $L > 0$. The generalized inverse

```math
\theta(r) = \inf \lbrace t \in [a, b] : \sigma_K((a, t]) \ge L r \rbrace \quad (\text{or } b), \qquad r \in [0, 1],
```

is nondecreasing, and pushes the Lebesgue measure on $(0, 1)$ forward to $\sigma_K|_{(a, b)} / L$
(the quantile transform,
[`cvx_map_cvxQuantile`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L703)). Put

```math
\gamma(s) = v_K^+(a) + L \int_0^s v_{\theta(r)} \, dr .
```

Then $\gamma$ is Lipschitz, so $\gamma \in C^\mathrm{BV}[0, 1]$, and
$\gamma'(r) = L\, v_{\theta(r)}$ for almost every $r$. For $r \in (0, 1)$ the point $\gamma(r)$ lies
on the edge $e_K(\theta(r))$: the arc is traced edge by edge, at constant speed $L$ (Figure 8.4).
Hence
$\gamma(r) \times \gamma'(r) = L\, \langle \gamma(r), u_{\theta(r)} \rangle = L\, h_K(\theta(r))$,
and by the quantile transform

```math
\mathcal{J}(\gamma) = \frac12 \int_0^1 L\, h_K(\theta(r)) \, dr = \frac12 \int_{(a, b)} h_K \, d\sigma_K .
```

The end points: $\gamma(0) = v_K^+(a)$, and
$\gamma(1) = v_K^+(a) + \int_{(a, b)} v_t \, \sigma_K(dt) = v_K^-(b)$ by Theorem 5.2.2; and the
image is the union of the edges. For injectivity, let $m = \frac12(a + b)$. Every velocity
$L\, v_{\theta(r)}$ makes an angle of at most $\frac12 (b - a) < \frac\pi2$ with $v_m$, so for
$s_1 < s_2$

```math
\langle \gamma(s_2) - \gamma(s_1), v_m \rangle \ \ge\ L \cos\tfrac{b - a}{2}\, (s_2 - s_1) > 0 .
```

Finally, $\mathcal{B}$ is convex-bilinear by Theorem 8.3 (1) and (3). $\square$

The paper argues instead with the convex body $K'$ of Lemma 8.15. Its boundary is a rectifiable
Jordan curve made of the arc and the chord, so Green's theorem and the area formula (Theorem 8.4)
give two expressions for $\lvert K' \rvert$:

```math
\lvert K' \rvert = \mathcal{J}(\mathbf{u}_K^{a,b}) + \mathcal{J}\bigl(v_K^-(b), v_K^+(a)\bigr) = \frac12 \int_{(a, b)} h_K \, d\sigma_K + \mathcal{J}\bigl(v_K^-(b), v_K^+(a)\bigr) . \tag{8.2}
```

The formalization keeps the second equality
([`cvx_area_cut`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1582)), which needs only
Theorem 8.4 and Lemma 8.15 (3), and uses it in Lemma 8.19.

### Lemma 8.17 (the bilinear form along the vertices; Baek, Lemma 7.3.3)

For $a < b < a + \pi$,

```math
\mathcal{B}(K_1, K_2) = \frac12 \int_{(a, b)} v_{K_1}^+(t) \times dv_{K_2}^+(t) = \frac12 \int_{(a, b)} v_{K_1}^-(t) \times dv_{K_2}^+(t) .
```

In particular $\mathcal{J}(\mathbf{u}_K^{a,b}) = \frac12 \int_{(a, b)} v_K^+ \times dv_K^+$.

*Proof.* On $(a, b)$, $dv_{K_2}^+ = v_t \, d\sigma_{K_2}$ (Baek's Theorem 5.2.2,
[Theorem 6.12](06-surface-area.md)), and
$v_{K_1}^\pm(t) \times v_t = \langle v_{K_1}^\pm(t), u_t \rangle = h_{K_1}(t)$, since both vertices
lie on $l_{K_1}(t)$. $\square$

*Lean: [`lemma7_3_3`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1271),
[`lemma7_3_3_self`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1287),
[`cvx_integral_cross_dvplus`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L610).*

### Lemma 8.18 (concatenation; Baek, Lemma 7.3.4)

For $a < b < c < a + \pi$, the curve $\mathbf{u}_K^{a,c}$ is the union of $\mathbf{u}_K^{a,b}$,
$e_K(b)$ and $\mathbf{u}_K^{b,c}$, which meet only at $v_K^-(b)$ and $v_K^+(b)$, and

```math
\mathcal{J}(\mathbf{u}_K^{a,c}) = \mathcal{J}(\mathbf{u}_K^{a,b}) + \mathcal{J}\bigl(v_K^-(b), v_K^+(b)\bigr) + \mathcal{J}(\mathbf{u}_K^{b,c}) .
```

*Proof.* Two edges $e_K(t)$ and $e_K(s)$ with $t < s < t + \pi$ meet at most at $v_K^-(s)$
([`cvx_edge_inter_eq_vminus`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L152)), which gives
the set identities. For the formula, split $(a, c) = (a, b) \cup \lbrace b \rbrace \cup (b, c)$. The
atom at $b$ contributes $\frac12 h_K(b)\, \sigma_K(\lbrace b \rbrace)$, and since $e_K(b)$ runs from
$v_K^-(b)$ to $v_K^+(b)$ in the direction $v_b$ with length $\sigma_K(\lbrace b \rbrace)$ (Baek's
Proposition 2.1.2, [Proposition 6.10](06-surface-area.md)), this is
$\mathcal{J}(v_K^-(b), v_K^+(b))$ by Proposition 8.12 (2). $\square$

*Lean: [`lemma7_3_4`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1295).*

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

*Lean: [`lemma7_3_5`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1830),
[`convexCurveRegion`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1824),
[`cvx_area_cut`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1582),
[`cvx_area_triangle`](../../MovingSofaOptimality/Convex/ConvexCurve.lean#L1772).*

The paper's statement (1) is that the boundary of $R$, the two tangent segments followed by the arc
backwards, is a counterclockwise Jordan curve; the paper then reads $\lvert R \rvert$ off it with
Green's theorem. The Lean statement defines $R$ directly and states its area, which is how the paper
uses (1).

*Proof.* The vertices of $T$ lie in $H_K(a) \cap H_K(b)$, hence so do $T$ and its interior, and
$R \subseteq T^\circ$ lies in the interior of that intersection. Disjointness holds by definition.
For the area, let $K'$ and $t'$ be as in Lemma 8.15. Inside $T$ the half-planes $H_K(t)$,
$t \in [a, b]$, cut out exactly $K'$: $T \cap \bigcap_{t \in [a, b]} H_K(t) = K'$. The boundary of
$T$ has measure zero, so $\lvert R \rvert = \lvert T \rvert - \lvert K' \rvert$ (Figure 8.3). The
triangle is positively oriented, so $\lvert T \rvert$ is the sum of $\mathcal{J}$ over its three
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

*Lean: [`mamikonRegion`](../../MovingSofaOptimality/Convex/Mamikon.lean#L541),
[`mamikon`](../../MovingSofaOptimality/Convex/Mamikon.lean#L546).*

$\mathcal{M}_K(a, b; \mathbf{z})$ is $\mathcal{J}$ of the closed path that goes out along the first
tangent segment, along $\mathbf{z}$, back along the last tangent segment, and back along the arc.
When the segments from $v_K^+(t)$ to $\mathbf{z}(t)$ sweep the region between the arc and
$\mathbf{z}$ once, this is its area, as in Figure 8.5; the formalization only uses the number
$\mathcal{M}_K$.

![Left: a lens K, light blue, the intersection of two discs, with a corner at its top. A thick arc of its boundary runs from v_K^+(a) on the right, over the corner, to v_K^-(b) on the left; orange tangent segments start on the arc and point counterclockwise, turning about the corner where the arc has its corner, and end on an orange curve z from z(a) to z(b); the region between the arc and z is shaded. Right: the same vectors alpha(t) v_t drawn from a common point Q form a shaded fan bounded by the curve Q + alpha(t) v_t](figures/08-convex-curves/mamikon.svg)

*Figure 8.5.* Mamikon's theorem for a lens $K$. Left: the tangent segments from $v_K^+(t)$ to
$\mathbf{z}(t) = v_K^+(t) + \alpha(t)\, v_t$, $t \in [a, b]$; across the corner of the lens, where
$v_K^+$ stays put while $t$ increases, they turn about the corner. Right: the same vectors
$\alpha(t)\, v_t$, drawn from a common point $Q$. The two shaded regions have the same area,
$\frac12 \int_a^b \alpha(t)^2\, dt$.

### Theorem 8.21 (Mamikon's theorem; Baek, Theorem 7.4.1)

Let $a < b < a + \pi$ and let $\mathbf{z} \in C^\mathrm{BV}[a, b]$ satisfy
$\mathbf{z}(t) \in l_K(t)$ for $t \in [a, b]$. Then
$\alpha(t) = \langle \mathbf{z}(t) - v_K^+(t), v_t \rangle$ is bounded and measurable on $[a, b]$,
$\mathbf{z}(t) = v_K^+(t) + \alpha(t)\, v_t$, and

```math
\mathcal{M}_K(a, b; \mathbf{z}) = \frac12 \int_a^b \alpha(t)^2 \, dt .
```

*Lean: [`theorem7_4_1`](../../MovingSofaOptimality/Convex/Mamikon.lean#L552),
[`cvx_mamikon_core`](../../MovingSofaOptimality/Convex/Mamikon.lean#L444),
[`cvx_integral_vvec_cross_dz`](../../MovingSofaOptimality/Convex/Mamikon.lean#L329),
[`cvx_ibp_cross_vplus`](../../MovingSofaOptimality/Convex/Mamikon.lean#L261).*

For a smooth convex curve this is the theorem of Mnatsakanian, known as Mamikon's theorem: the
region swept by tangent segments has the area of the region swept by the same vectors moved to a
common point (Figure 8.5, right), which is $\frac12 \int \alpha^2$ by the area formula in polar
coordinates. Baek's version holds for every convex body: across a corner of $K$ the segments turn
about the corner and sweep a fan of area $\frac12 \int \alpha^2$, and across an edge $\alpha$ jumps
down by the length of the edge, while $\mathbf{z}$ stays continuous.

*Proof.* Write $\mathbf{v} = v_K^+$. Both $\mathbf{z}(t)$ and $\mathbf{v}(t)$ lie on $l_K(t)$, so
their difference is a multiple of $v_t$, namely $\alpha(t)\, v_t$. The function $\alpha$ is
measurable since $v_K^+$ is, and bounded since $K$ is bounded and $\mathbf{z}$ is continuous on a
compact interval.

*Step 1: the arc term.* By Lemma 8.17 and $\mathbf{z}(t) \in l_K(t)$, as in its proof,
$\int_{(a, b)} \mathbf{z} \times d\mathbf{v} = \int_{(a, b)} h_K \, d\sigma_K = 2\mathcal{J}(\mathbf{u}_K^{a,b})$.
Integration by parts for the Lebesgue–Stieltjes measures of $\mathbf{z}$ and $\mathbf{v}$, whose
left limit at $b$ is $v_K^-(b)$, gives

```math
\int_{(a, b)} \mathbf{z} \times d\mathbf{v} = \mathbf{z}(b) \times v_K^-(b) - \mathbf{z}(a) \times v_K^+(a) + \int_{(a, b)} \mathbf{v} \times d\mathbf{z} .
```

Substituting into Definition 8.20, the two boundary cross products cancel against
$\mathcal{J}(v_K^+(a), \mathbf{z}(a))$ and $\mathcal{J}(\mathbf{z}(b), v_K^-(b))$, and

```math
2\, \mathcal{M}_K(a, b; \mathbf{z}) = \int_{(a, b)} (\mathbf{z} - \mathbf{v}) \times d\mathbf{z} = \int_{(a, b)} \alpha(t) \, \bigl(v_t \times d\mathbf{z}(t)\bigr) .
```

*Step 2: $v_t \times d\mathbf{z} = \alpha(t)\, dt$.* Since
$\mathbf{z}(t) \times v_t = \langle \mathbf{z}(t), u_t \rangle = h_K(t)$, the product rule for
$v_t \times \mathbf{z}(t)$, with $dv_t = -u_t\, dt$ and
$u_t \times \mathbf{z} = \langle \mathbf{z}, v_t \rangle$, gives

```math
v_t \times d\mathbf{z}(t) = -\,dh_K(t) + \langle \mathbf{z}(t), v_t \rangle \, dt .
```

The support function is Lipschitz with derivative $\langle v_K^+(t), v_t \rangle$ almost everywhere
([`cvx_supp_primitive`](../../MovingSofaOptimality/Convex/Mamikon.lean#L183)), so
$dh_K(t) = \langle \mathbf{v}(t), v_t \rangle\, dt$ and
$v_t \times d\mathbf{z} = \langle \mathbf{z} - \mathbf{v}, v_t \rangle \, dt = \alpha\, dt$.
Together, $2\mathcal{M}_K(a, b; \mathbf{z}) = \int_a^b \alpha^2 \, dt$. $\square$

The paper's proof computes the same measure as
$\mathbf{z} \times d\mathbf{z} - \mathbf{v} \times d\mathbf{v} + d(\mathbf{z} \times \mathbf{v}) = (\mathbf{z} - \mathbf{v}) \times d(\mathbf{z} - \mathbf{v})$;
in its last line $\alpha u_t$ should read $\alpha v_t$, which does not affect the result (REPORT.md,
E26). The measurability claim is read on $[a, b]$, where $\mathbf{z}$ is constrained (REPORT.md,
Section 6).

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

*Lean: [`theorem7_4_2`](../../MovingSofaOptimality/Convex/Mamikon.lean#L592).*
