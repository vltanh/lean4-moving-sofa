# 6. The surface area measure

[Contents](README.md) · [← 5. The rotation angle](05-rotation-angle.md) · [7. The injectivity condition →](07-injectivity.md)

The surface area measure $\sigma_K$ of a planar convex body $K$ is a measure on the angles that
records the lengths of the edges of $K$. The mass $\sigma_K(\lbrace t\rbrace)$ of an angle $t$ is the
length of the edge $e_K(t)$ with outer normal $u_t$, and where the boundary of $K$ is curved,
$\sigma_K$ has the radius of curvature as its density (Figure 6.2). The main result of the chapter
is the differential Gauss–Minkowski theorem
([Theorem 6.12](#theorem-612-differential-gaussminkowski-theorem-baek-theorem-522)): the vertex
$v_K^+(t)$ of $K$, as a function of the angle $t$, has the differential

```math
\mathrm{d}v_K^+(t) = v_t \, \sigma_K
```

in the sense of Lebesgue–Stieltjes measures. So $\sigma_K$ is a weak derivative of the boundary of
$K$, which need not be differentiable. [Chapter 7](07-injectivity.md) differentiates the arm lengths
of a cap with it, and [Chapters 8](08-convex-curves.md) and [9](09-optimality.md) compute areas with
it. The chapter covers Baek's Chapter 5 and its overview, §1.6 of the paper.

Baek takes $\sigma_K$ from Schneider's book, where $\sigma_K(X)$ is the length of the union of the
edges $e_K(t)$, $t \in X$. The formalization instead defines $\sigma_K$ as the Lebesgue–Stieltjes
measure of the nondecreasing function $G_K(t) = \langle v_K^+(t), v_t\rangle + \int_0^t h_K$
([Definition 6.8](#definition-68-surface-area-measure)). This is the classical identity
$\sigma_K = h_K'' + h_K$, read in the sense of measures. From this definition it proves the two
properties of $\sigma_K$ that the paper uses: the atoms of $\sigma_K$ are the lengths of the edges
([Proposition 6.10](#proposition-610-atoms-baek-proposition-212)), and
$\mathrm{d}v_K^+ = v_t\,\sigma_K$. It also proves two results that the paper cites from Schneider:
the area formula $\lvert K\rvert = \frac12 \int h_K \,\mathrm{d}\sigma_K$
([Theorem 6.13](#theorem-613-area-formula-schneider-remark-512)), one of the three results from
prior work in the formalization, and the weak continuity of $K \mapsto \sigma_K$
([Theorem 6.14](#theorem-614-weak-convergence-baek-theorem-413)).

*Outline.* §6.1 recalls Lebesgue–Stieltjes measures and proves the rules of calculus of Baek's §5.1,
one of them in corrected form. §6.2 defines $\sigma_K$ and computes its atoms. §6.3 proves the
differential Gauss–Minkowski theorem, §6.4 the area formula and §6.5 the weak continuity.

## 6.1 Lebesgue–Stieltjes measures

The measures of this section are finite signed Borel measures on a bounded interval $[a, b]$, or
pairs of them. A function $f\colon [a, b] \to \mathbb{R}$ has *bounded variation* if the sums
$\sum_i \lvert f(t_i) - f(t_{i-1})\rvert$ over the partitions $a = t_0 < \dots < t_n = b$ are
bounded (Baek, Definition 5.1.2).

### Definition 6.1 (Lebesgue–Stieltjes measure; Baek, Definition 5.1.3)

Let $f\colon [a, b] \to \mathbb{R}$ be right-continuous and of bounded variation. Its
*Lebesgue–Stieltjes measure* $\mathrm{d}f$ is the unique finite signed Borel measure on $[a, b]$
with

```math
\mathrm{d}f(\lbrace a\rbrace) = 0 , \qquad \mathrm{d}f\bigl((a, t]\bigr) = f(t) - f(a) \quad \text{for } t \in [a, b] .
```

For a pair $f = (f_1, f_2)$ of such functions, $\mathrm{d}f = (\mathrm{d}f_1, \mathrm{d}f_2)$. For a
bounded measurable function $g$ and a measure $\mu$, $g\,\mu$ is the measure
$X \mapsto \int_X g \,\mathrm{d}\mu$, and $\int_X g\,\mathrm{d}f$ is the integral of $g$ against
$\mathrm{d}f$ (Baek, Definitions 5.1.1 and 5.1.4). For pairs, both are taken componentwise.

*Lean: [`lsMeasure`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L57), [`clampFun`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L51), [`lsMeasure_singleton_left`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L200), [`lsMeasure_Ioc`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L212).*

The measure $\mathrm{d}f$ is the differential of $f$ made rigorous. For example
$\mathrm{d}(t^2) = 2t\,\mathrm{d}t$ on $[a, b]$, where $\mathrm{d}t$ is the Lebesgue measure: both
give an interval $(c, d]$ the mass $d^2 - c^2$.

The formalization takes $\mathrm{d}f$ from Mathlib, which attaches a vector measure to every
function $F$ of bounded variation on $\mathbb{R}$ (`BoundedVariationOn.vectorMeasure`), with mass
$F(d+) - F(c-)$ on $[c, d]$. It applies this to $f$ clamped to $[a, b]$, the function
$t \mapsto f(\max(a, \min(b, t)))$, which agrees with $f$ on $[a, b]$ and is constant outside. The
mass of $\lbrace a\rbrace$ is then $f(a+) - f(a)$. It vanishes because $f$ is right-continuous; for
the indicator function of $(0, \infty)$ on $[0, 1]$ it would be $1$.

### Proposition 6.2 (linearity; Baek, Proposition 5.1.1)

For functions $f, g$ of bounded variation on $[a, b]$ and real numbers $r, s$,
$\mathrm{d}(rf + sg) = r\,\mathrm{d}f + s\,\mathrm{d}g$.

*Lean: [`proposition5_1_1`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L248).*

*Proof.* Mathlib's vector measure of a function $F$ of bounded variation gives an interval $[c, d]$
the mass $F(d+) - F(c-)$, and one-sided limits are linear in $F$. So the two sides agree on every
closed interval. Two finite signed measures on $\mathbb{R}$ that agree on all closed intervals are
equal. $\square$

The proof does not use right-continuity, and the formalization proves the identity without it.

### Lemma 6.3 (integration by parts; Baek, Lemma 5.1.2)

For right-continuous functions $f, g$ of bounded variation on $[a, b]$,

```math
\int_{(a, b]} g(t)\,\mathrm{d}f(t) + \int_{(a, b]} f(t-)\,\mathrm{d}g(t) = f(b)\,g(b) - f(a)\,g(a) ,
```

where $f(t-)$ is the left limit of $f$ at $t$.

*Lean: [`lemma5_1_2`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L276).*

*Proof.* This is Proposition 4.5 of Revuz and Yor. Mathlib proves it for the vector measures of
functions of bounded variation on $\mathbb{R}$
(`BoundedVariationOn.setIntegral_Ioc_leftLim_smul_vectorMeasure_eq_sub`), with the right limits of
the functions in place of their values. Apply it to the clamped functions. On $[a, b]$ their right
limits are the values of $f$ and $g$, by right-continuity, and on $(a, b]$ the left limit of the
clamped $f$ is $f(t-)$. $\square$

### Lemma 6.4 (product rule; Baek, Lemma 5.1.3)

Let $f, g$ be right-continuous and of bounded variation on $[a, b]$, and let one of them be
continuous. Then $\mathrm{d}(fg) = g\,\mathrm{d}f + f\,\mathrm{d}g$ as measures on $[a, b]$:

```math
\mathrm{d}(fg)(X) = \int_X g\,\mathrm{d}f + \int_X f\,\mathrm{d}g \qquad \text{for every Borel set } X \subseteq [a, b] .
```

*Lean: [`lemma5_1_3`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L300).*

*Proof.* Mathlib writes the vector measure of a product of two functions of bounded variation as
$g(t+)\,\mathrm{d}f + f(t-)\,\mathrm{d}g$, and also as $g(t-)\,\mathrm{d}f + f(t+)\,\mathrm{d}g$.
If $f$ is continuous, use the first form: $f(t-) = f(t)$, and $g(t+) = g(t)$ by right-continuity. If
$g$ is continuous, use the second. $\square$

Baek's proof checks the identity on the intervals $(a, x]$ with Lemma 6.3.

### Proposition 6.5 (absolutely continuous functions; Baek, Proposition 5.1.4)

Let $f$ be right-continuous and of bounded variation on $[a, b]$.

1. $f$ is absolutely continuous on $[a, b]$ if and only if $\mathrm{d}f = r\,\mathrm{d}t$ for some
   measurable function $r$ that is integrable on $[a, b]$.
2. If $\mathrm{d}f = r\,\mathrm{d}t$ with $r$ measurable and bounded, then $f'(t) = r(t)$ for almost
   every $t \in [a, b]$.

*Lean: [`proposition5_1_4`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L455), [`proposition5_1_4_deriv`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L494),
[`absolutelyContinuousOnInterval_of_lsMeasure_eq`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L484).*

Baek asks for a *bounded* density in (1). Then the "only if" direction is false
(Proposition 6.6), so the text asks for an integrable density (REPORT.md, E11). The paper uses the
proposition once, in the proof of
[Theorem 7.23](07-injectivity.md#theorem-723-differential-inequality-baek-theorem-651), in the "if"
direction and with a bounded density, where it is correct.

*Proof.* (1) If $\mathrm{d}f = r\,\mathrm{d}t$, then
$f(t) - f(a) = \mathrm{d}f((a, t]) = \int_a^t r$ for $t \in [a, b]$. So $f$ is a constant plus the
indefinite integral of an integrable function, hence absolutely continuous. Conversely, an
absolutely continuous $f$ is differentiable almost everywhere, its derivative $f'$ is integrable,
and $f(t) - f(a) = \int_a^t f'$. So $\mathrm{d}f$ and $f'\,\mathrm{d}t$ agree on every interval
$(c, d] \subseteq [a, b]$. Neither charges $\lbrace a\rbrace$, so they are equal.

(2) By (1), $f$ agrees on $[a, b]$ with $f(a) + \int_a^t r$. By the Lebesgue differentiation
theorem, this indefinite integral has derivative $r(t)$ at almost every $t$. $\square$

### Proposition 6.6 (Baek's Proposition 5.1.4 as printed is false)

The function $f(t) = 2\sqrt t$ on $[0, 1]$ is right-continuous, of bounded variation and
absolutely continuous, but there is no bounded measurable $r$ with $\mathrm{d}f = r\,\mathrm{d}t$.

*Lean: [`proposition5_1_4_as_stated_false`](../../MovingSofaOptimality/Basic/LebesgueStieltjes.lean#L521).*

*Proof.* $f(t) = \int_0^t x^{-1/2}\,\mathrm{d}x$ is the indefinite integral of an integrable
function. So it is absolutely continuous, hence continuous and of bounded variation. Suppose that
$\mathrm{d}f = r\,\mathrm{d}t$ with $\lvert r\rvert \le C$. Then

```math
2\sqrt t = f(t) - f(0) = \int_0^t r \le C\,t \qquad \text{for } t \in [0, 1] ,
```

that is, $2 \le C\sqrt t$ for $t \in (0, 1]$. This fails for small $t$. $\square$

## 6.2 The surface area measure

The notation is that of [Chapter 2](02-preliminaries.md), recalled here (Figure 6.1). A *planar
convex body* $K$ is a nonempty compact convex subset of $\mathbb{R}^2$; its interior may be empty
([Definition 2.6](02-preliminaries.md#definition-26-convex-body-support-function-baek-definitions-211-and-216218)).
Its *support function* is $h_K(t) = \max_{p \in K} \langle p, u_t\rangle$, and its *supporting line*
is $l_K(t) = \lbrace p : \langle p, u_t\rangle = h_K(t)\rbrace$. The *edge* $e_K(t) = K \cap l_K(t)$
is a segment parallel to $v_t$, possibly a single point, with the *vertices* $v_K^-(t)$ and
$v_K^+(t)$ as its ends, farthest in the directions $-v_t$ and $v_t$. For $\sin(b - a) \ne 0$ the
point $v_K(a, b)$ is the intersection of $l_K(a)$ and $l_K(b)$
([Definition 2.8](02-preliminaries.md#definition-28-edges-and-vertices-baek-definitions-219-2110-and-2114)).
Angles are real numbers, and every function of the angle below has period $2\pi$. By
[Theorem 2.9](02-preliminaries.md#theorem-29-limits-of-vertices-baek-theorem-213), as $s \to t^+$
the points $v_K^\pm(s)$ and $v_K(t, s)$ tend to $v_K^+(t)$, and as $s \to t^-$ the points
$v_K^\pm(s)$ and $v_K(s, t)$ tend to $v_K^-(t)$. In particular $v_K^+$ is right-continuous.

![A convex body K, a disk cut by a chord. The supporting line l(t) with normal angle t contains the chord, the edge e(t), whose ends are the vertices v⁻(t) at the lower right and v⁺(t) at the upper left; the unit vector u_t points out of K, perpendicular to the line, and v_t points along the edge towards v⁺(t); a dashed segment from the origin O, perpendicular to l(t), has length h_K(t). Another supporting line l(s) touches K at a single point, where v⁺(s) = v⁻(s)](figures/06-surface-area/notation.svg)

*Figure 6.1.* A convex body $K$ and its supporting line $l_K(t)$, which meets $K$ in the edge
$e_K(t)$ from $v_K^-(t)$ to $v_K^+(t)$. The support value $h_K(t)$ is the signed distance from the
origin to $l_K(t)$. The edge $e_K(s)$ of a supporting line through a curved part of the boundary is a
single point.

*Lean: [`IsConvexBody`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L49), [`supp`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L52), [`edge`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L64), [`vplus`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L68), [`vminus`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L73), [`vint`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L78), [`tendsto_vplus_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L562),
[`tendsto_vplus_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L583).*

### Lemma 6.7 (one-sided derivatives of the support function)

For every convex body $K$ and every angle $t$, the support function $h_K$ has the right derivative
$\langle v_K^+(t), v_t\rangle$ and the left derivative $\langle v_K^-(t), v_t\rangle$ at $t$.

*Lean: [`hasDerivWithinAt_supp_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L630), [`hasDerivWithinAt_supp_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L647).*

*Proof.* This is
[Corollary 2.10](02-preliminaries.md#corollary-210-one-sided-derivatives-of-the-support-function),
restated for use in this chapter. $\square$

Two consequences are used below and in [Chapter 7](07-injectivity.md).

- *The support function is the integral of its right derivative.* The function $h_K$ is Lipschitz,
  and a Lipschitz function with a right derivative everywhere is the integral of it. So
  $h_K(d) - h_K(c) = \int_c^d \langle v_K^+(t), v_t\rangle\,\mathrm{d}t$ for $c \le d$.
- *The sandwich.* For $0 < \delta < \pi$,
  ```math
  \frac{h_K(t)\cos\delta - h_K(t - \delta)}{\sin\delta} \ \le\ \langle v_K^-(t), v_t\rangle \ \le\ \langle v_K^+(t), v_t\rangle \ \le\ \frac{h_K(t + \delta) - h_K(t)\cos\delta}{\sin\delta} .
  ```
  For the right inequality, write $u_{t + \delta} = \cos\delta\,u_t + \sin\delta\,v_t$; the point
  $v_K^+(t)$ lies in $K$, and $\langle v_K^+(t), u_t\rangle = h_K(t)$, so
  $h_K(t)\cos\delta + \langle v_K^+(t), v_t\rangle\sin\delta \le h_K(t + \delta)$. The left
  inequality is the same argument for $v_K^-(t)$ and $u_{t - \delta}$. The outer terms are the
  $v_t$-coordinates of $v_K(t - \delta, t)$ and $v_K(t, t + \delta)$. They depend only on support
  values, and as $\delta \to 0^+$ they tend to the inner terms, by Theorem 2.9. The formalization
  passes to limits with this sandwich: in the proof of Theorem 6.14, and in Chapters 5 and 7, where
  Baek uses weak convergence and the Portmanteau theorem instead.

### Definition 6.8 (surface area measure)

For a convex body $K$, the *distribution function* of $K$ is

```math
G_K(t) = \langle v_K^+(t), v_t\rangle + \int_0^t h_K(s)\,\mathrm{d}s \qquad (t \in \mathbb{R}) .
```

By [Lemma 6.9](#lemma-69-the-distribution-function), $G_K$ is nondecreasing and right-continuous.
The *surface area measure* $\sigma_K$ is its Lebesgue–Stieltjes measure on $\mathbb{R}$: the Borel
measure with $\sigma_K((a, b]) = G_K(b) - G_K(a)$ for all $a \le b$. We write $\sigma_K(t)$ for
$\sigma_K(\lbrace t\rbrace)$.

*Lean: [`sigmaFun`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L47), [`sigmaStieltjes`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L160), [`sigma`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L169), [`sigmaAt`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L172), [`sigma_Ioc`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L178), [`sigma_periodic`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L246).*

Since $v_K^+$, $v_t$ and $h_K$ have period $2\pi$,
$G_K(t + 2\pi) = G_K(t) + \int_0^{2\pi} h_K$, and $\sigma_K$ is $2\pi$-periodic:
$\sigma_K(X + 2\pi) = \sigma_K(X)$. Baek's measure on the circle $S^1 = \mathbb{R}/2\pi\mathbb{Z}$ is
the restriction of $\sigma_K$ to any interval of length $2\pi$, usually $[0, 2\pi)$ (REPORT.md,
Section 6). By Lemma 6.7, $G_K$ is the right derivative of $h_K$ plus a primitive of $h_K$. So
$\sigma_K = h_K'' + h_K$ in the sense of measures, the classical formula for the surface area measure
of a planar convex body. Two cases show what it means.

- If $K$ is a polygon, then between two consecutive normal angles of its edges the vertex
  $v_K^+(t)$ is a fixed corner $p$, and $h_K(t) = \langle p, u_t\rangle$. So $G_K$ is constant
  there: the derivative $-\langle p, u_t\rangle$ of $\langle p, v_t\rangle$ cancels $h_K$. At the
  normal angle of an edge, $G_K$ jumps by the length of the edge
  ([Proposition 6.10](#proposition-610-atoms-baek-proposition-212)). So $\sigma_K$ is a sum of
  atoms, one at the normal angle of each edge, of mass its length.
- If the boundary of $K$ is twice differentiable with curvature $\kappa > 0$, then
  $v_K^\pm(t)$ is the boundary point with outer normal $u_t$, $h_K$ is twice differentiable, and
  $h_K'' + h_K = 1/\kappa$ is the radius of curvature there.

Baek's overview gives two examples (Figure 6.2). For the rectangle $[-1, 1] \times [0, 1]$, the
measure $\sigma_K$ on $[0, 2\pi)$ has the atoms $1, 2, 1, 2$ at $0, \pi/2, \pi, 3\pi/2$, the lengths
of the right, top, left and bottom sides. For the half-disk
$\lbrace x^2 + y^2 \le 1,\ y \ge 0\rbrace$, $v_K^+(t) = u_t$ and $h_K(t) = 1$ for $t \in [0, \pi]$.
So $G_K(t) = t$ there, and $\sigma_K = \mathrm{d}t$ on $[0, \pi]$: the radius of curvature is $1$.
For $t \in (\pi, 2\pi)$ the vertex is the corner $(-1, 0)$ or $(1, 0)$, and the only atom is
$\sigma_K(3\pi/2) = 2$, the length of the diameter.

![Two panels. Left: the rectangle from -1 to 1 by 0 to 1 with outward arrows on its four sides labelled σ({0}) = 1, σ({π/2}) = 2, σ({π}) = 1 and σ({3π/2}) = 2, and below it the graph of G_K for the angles from -π/4 to 9π/4, a staircase with jumps of 1, 2, 1, 2 at 0, π/2, π, 3π/2 and of 1 at 2π, through the heights 1, 3, 4, 6 and 7. Right: the half-disk with outward arrows, labelled density 1 on the angles from 0 to π and σ({3π/2}) = 2, and the graph of its G_K, which is 0 before 0, rises with slope 1 to π at π, stays flat, jumps by 2 to π + 2 at 3π/2, stays flat and rises again after 2π](figures/06-surface-area/examples.svg)

*Figure 6.2.* The two examples of Baek's overview and their distribution functions $G_K$, computed
from Definition 6.8. Each jump of $G_K$ is an atom of $\sigma_K$, with the filled dot at the value
of $G_K$ and the open dot at its left limit; the slope of $G_K$ is the density of $\sigma_K$. The
total mass on $[0, 2\pi)$ is the perimeter, $6$ and $\pi + 2$.

### Lemma 6.9 (the distribution function)

For every convex body $K$, the function $G_K$ is nondecreasing and right-continuous.

*Lean: [`monotone_sigmaFun`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L110), [`continuousWithinAt_sigmaFun`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L151).*

*Proof.* Right-continuity: $v_K^+$ is right-continuous by Theorem 2.9, and the integral is
continuous in $t$.

Monotonicity: bound $\int_s^t h_K$ from below by the support values of the two vertices at the ends.
Let $s < t$, and put $p = v_K^+(t)$ and $q = v_K^+(s)$. Both points lie in $K$, so
$h_K(r) \ge \langle q, u_r\rangle$ and $h_K(r) \ge \langle p, u_r\rangle$ for every $r$. The
derivative of $r \mapsto \langle w, v_r\rangle$ is $-\langle w, u_r\rangle$, so for every
$m \in [s, t]$

```math
\int_s^t h_K \ \ge\ \int_s^m \langle q, u_r\rangle\,\mathrm{d}r + \int_m^t \langle p, u_r\rangle\,\mathrm{d}r = \langle q, v_s\rangle - \langle q, v_m\rangle + \langle p, v_m\rangle - \langle p, v_t\rangle ,
```

and therefore

```math
G_K(t) - G_K(s) = \langle p, v_t\rangle - \langle q, v_s\rangle + \int_s^t h_K \ \ge\ \langle p - q, v_m\rangle .
```

It remains to choose $m$ with $\langle p - q, v_m\rangle \ge 0$. The function
$\phi(r) = \langle p - q, u_r\rangle$ has $\phi(s) = \langle p, u_s\rangle - h_K(s) \le 0$ and
$\phi(t) = h_K(t) - \langle q, u_t\rangle \ge 0$. By the mean value theorem some $m \in (s, t)$ has
$\phi'(m) = \langle p - q, v_m\rangle = (\phi(t) - \phi(s))/(t - s) \ge 0$. $\square$

### Proposition 6.10 (atoms; Baek, Proposition 2.1.2)

For every convex body $K$ and every angle $t$, $\sigma_K(t)$ is the length of the edge $e_K(t)$, and

```math
v_K^+(t) = v_K^-(t) + \sigma_K(t)\,v_t .
```

*Lean: [`proposition2_1_2`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L294).*

*Proof.* The atom of a Lebesgue–Stieltjes measure at $t$ is the jump $G_K(t) - G_K(t-)$ of its
distribution function. As $s \to t^-$, $v_K^+(s) \to v_K^-(t)$ by Theorem 2.9, so
$G_K(t-) = \langle v_K^-(t), v_t\rangle + \int_0^t h_K$ and

```math
\sigma_K(t) = \langle v_K^+(t) - v_K^-(t), v_t\rangle .
```

Both vertices lie on $l_K(t)$, so $\langle v_K^+(t) - v_K^-(t), u_t\rangle = 0$, and
$v_K^+(t) - v_K^-(t) = \sigma_K(t)\,v_t$. Its length is $\sigma_K(t)$, which is nonnegative by the
definition of $v_K^\pm(t)$. $\square$

Baek derives Proposition 2.1.2 from Schneider's Theorem 4.2.3 (Baek's Theorem 2.1.1), the
description of $\sigma_K$ by lengths of edges recalled at the start of the chapter. The
formalization does not state that theorem in this form (REPORT.md, Section 8). Its arc-length form
is step 1 of the proof of the area formula (§6.4).

## 6.3 The differential Gauss–Minkowski theorem

### Lemma 6.11 (bounded variation; Baek, Lemma 5.2.1)

For every convex body $K$, the vertex $v_K^+$ has bounded variation on every interval $[a, b]$.

*Lean: [`lemma5_2_1`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L326).*

*Proof.* In the frame $u_t, v_t$,

```math
v_K^+(t) = h_K(t)\,u_t + \langle v_K^+(t), v_t\rangle\,v_t , \qquad \langle v_K^+(t), v_t\rangle = G_K(t) - \int_0^t h_K .
```

The functions $h_K$, its primitive, $u_t$ and $v_t$ are Lipschitz, and $G_K$ is nondecreasing
(Lemma 6.9). Lipschitz and monotone functions have bounded variation on $[a, b]$, and so do sums and
products of functions of bounded variation. $\square$

Baek's proof cuts $[0, 2\pi]$ into intervals on which each coordinate of $v_K^+$ is monotone. Its
last interval, $[3\pi/4, 2\pi]$, is not one of them and has to be cut further (REPORT.md, E26).

### Theorem 6.12 (differential Gauss–Minkowski theorem; Baek, Theorem 5.2.2)

Let $K$ be a convex body and $a < b$. Then

```math
\mathrm{d}v_K^+(t) = v_t\,\sigma_K \qquad \text{as pairs of measures on the half-open interval } (a, b] ,
```

where $\mathrm{d}v_K^+$ is the Lebesgue–Stieltjes measure of $v_K^+$ on $[a, b]$
(Definition 6.1, by Lemma 6.11 and the right-continuity of $v_K^+$). Equivalently, for all
$c \le d$,

```math
v_K^+(d) - v_K^+(c) = \int_{(c, d]} v_t \,\mathrm{d}\sigma_K(t) .
```

*Lean: [`theorem5_2_2`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L389), [`vplus_sub_vplus`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L378).*

Baek assumes $b \le a + 2\pi$; the formalization does not need it (REPORT.md, Section 5). On the left
endpoint $\lbrace a\rbrace$ the identity fails in general: $\mathrm{d}v_K^+$ gives it no mass by
Definition 6.1, while $\sigma_K$ may have an atom at $a$. Figure 6.3 shows the integrated form.

![A convex body K: the unit disk cut by a horizontal line at the bottom and by a chord on its upper right. The boundary from the vertex v⁺(a) at the lower right, a = -π/6, counterclockwise to the vertex v⁺(b) at the upper left, b = 3π/4, is drawn as a chain of arrows: short blue arrows v_t dt along the two arcs, and one long orange arrow σ({π/4}) v_{π/4} along the chord. A black arrow goes straight from v⁺(a) to v⁺(b)](figures/06-surface-area/gauss-minkowski.svg)

*Figure 6.3.* Theorem 6.12 in integrated form, for the unit disk cut by a horizontal line and by
a chord with normal angle $\pi/4$, from $a = -\pi/6$ to $b = 3\pi/4$. On the arcs $\sigma_K$ has the
density $1$, and the chain of vectors $v_t\,\mathrm{d}t$ follows the boundary; the chord is the atom
$\sigma_K(\pi/4) = 1.2$, crossed in one step $\sigma_K(\pi/4)\,v_{\pi/4}$. The vectors add up to
$v_K^+(b) - v_K^+(a)$.

*Proof.* The idea is to write $v_K^+$ in the frame $u_t, v_t$ through $G_K$ and an explicit
antiderivative, and to integrate $v_t$ against $\sigma_K$ by Fubini's theorem.

Both sides are pairs of finite signed measures on $(a, b]$, and such pairs are equal once they
agree on every interval $(c, d] \subseteq (a, b]$. As $\mathrm{d}v_K^+((c, d]) = v_K^+(d) - v_K^+(c)$, it suffices
to prove the integrated form. We prove it on $(a, b]$ for $a \le b$, and write $G = G_K$.

**Step 1. Fubini.** For $t \in (a, b]$, $v_t = v_b + \int_t^b u_s\,\mathrm{d}s$, since the derivative
of $s \mapsto v_s$ is $-u_s$. Integrate over $t$ against $\sigma_K$ and exchange the integrals. The
integrand $\mathbf{1}_{t \le s}\,u_s$ is bounded, and $\sigma_K((a, s]) = G(s) - G(a)$, so

```math
\int_{(a, b]} v_t\,\mathrm{d}\sigma_K(t) = \bigl(G(b) - G(a)\bigr)\,v_b + \int_a^b \bigl(G(s) - G(a)\bigr)\,u_s\,\mathrm{d}s .
```

**Step 2. An antiderivative.** Let $\Phi(t) = h_K(t)\,u_t - \bigl(\int_0^t h_K\bigr)\,v_t$. By
Lemma 6.7, $\Phi$ has at every $t$ the right derivative

```math
\langle v_K^+(t), v_t\rangle\,u_t + h_K(t)\,v_t - h_K(t)\,v_t + \Bigl(\int_0^t h_K\Bigr)\,u_t = G(t)\,u_t .
```

A continuous function with an integrable right derivative everywhere is the integral of it, so
$\int_a^b G(s)\,u_s\,\mathrm{d}s = \Phi(b) - \Phi(a)$. Also $\int_a^b u_s\,\mathrm{d}s = v_a - v_b$.

**Step 3. The vertex.** In the frame $u_t, v_t$, $v_K^+(t) = h_K(t)\,u_t + \langle v_K^+(t), v_t\rangle\,v_t = G(t)\,v_t + \Phi(t)$.
With steps 1 and 2,

```math
\int_{(a, b]} v_t\,\mathrm{d}\sigma_K = \bigl(G(b) - G(a)\bigr)\,v_b + \Phi(b) - \Phi(a) - G(a)\,(v_a - v_b) = \bigl(G(b)\,v_b + \Phi(b)\bigr) - \bigl(G(a)\,v_a + \Phi(a)\bigr) ,
```

which is $v_K^+(b) - v_K^+(a)$. $\square$

Baek's proof goes through polygons. For a polygon, $\sigma_K$ is a sum of atoms, and by
Proposition 6.10 each atom contributes the edge vector $\sigma_K(t)\,v_t = v_K^+(t) - v_K^-(t)$. The
sum over the edges with normal angles in $(a, b]$ telescopes to $v_K^+(b) - v_K^+(a)$, as in
Figure 6.3. A general $K$ is a Hausdorff limit of polygons with the same edges at $a$ and $b$, and
the weak convergence of the surface area measures (Theorem 6.14) passes the identity to the limit.
The formalization's proof uses neither polygons nor weak convergence. Baek's proof once writes
$u_t\,\sigma$ for $v_t\,\sigma$ (REPORT.md, E26).

With $(c, d] = (0, 2\pi]$, the periodicity of $v_K^+$ gives
$\int_{(0, 2\pi]} v_t\,\mathrm{d}\sigma_K(t) = 0$. Rotating by a quarter turn,
$\int_{(0, 2\pi]} u_t\,\mathrm{d}\sigma_K(t) = 0$: the boundary of $K$ closes up. This is one
direction of the Gauss–Minkowski correspondence between convex bodies and measures on the circle
(Baek, Remark 5.2.1).

## 6.4 The area formula

### Theorem 6.13 (area formula; Schneider, Remark 5.1.2)

For every convex body $K$,

```math
\lvert K\rvert = \frac12 \int_{[0, 2\pi)} h_K(t)\,\mathrm{d}\sigma_K(t) .
```

*Lean: [`area_eq_half_integral_supp`](../../MovingSofaOptimality/External/AreaFormula.lean#L558).*

Baek cites the formula from Schneider's Remark 5.1.2 as his Theorem 7.1.3
([Theorem 8.4](08-convex-curves.md#theorem-84-the-area-is-quadratic-baek-theorem-713)) and uses it
in his Theorem 7.3.2 and Lemma 8.3.5
([Theorem 8.16](08-convex-curves.md#theorem-816-the-curve-area-functional-of-a-convex-arc-baek-theorem-732)
and [Lemma 9.24](09-optimality.md#lemma-924-the-area-as-a-sum-over-arcs-baek-lemma-835)). His
Theorem 8.5.1
([Theorem 9.29](09-optimality.md#theorem-929-directional-derivatives-of-the-pieces-baek-theorems-851855)
(1)) uses its mixed-volume form, Schneider's Equation (5.19). It is one of the three results from
prior work that the formalization proves in
[`MovingSofaOptimality/External/`](../../MovingSofaOptimality/External). For a polygon, $K$ is the
union of the triangles over its edges with apex at an interior point $c$ (Figure 6.4). The triangle
over the edge with normal angle $t$ has base $\sigma_K(t)$ and height
$h_K(t) - \langle c, u_t\rangle$, and the terms $\langle c, u_t\rangle$ cancel because the boundary
closes up. The proof replaces the triangles by a change of variables along the boundary.

![A convex pentagon cut into five triangles that share the apex c, an interior point, one triangle over each edge. On the triangle over the right edge, whose outer normal u_t points to the lower right, the edge is drawn thick and labelled σ({t}), and a dashed segment from c perpendicular to the edge is labelled h_K(t) − ⟨c, u_t⟩](figures/06-surface-area/area-formula.svg)

*Figure 6.4.* The area formula for a pentagon. The triangle over the edge with normal angle $t$ has
base $\sigma_K(t)$ and height $h_K(t) - \langle c, u_t\rangle$, so
$\lvert K\rvert = \frac12 \sum_t \sigma_K(t)\,(h_K(t) - \langle c, u_t\rangle) = \frac12 \sum_t \sigma_K(t)\,h_K(t)$.

*Proof sketch.* The full proof is in [`MovingSofaOptimality/External/AreaFormula.lean`](../../MovingSofaOptimality/External/AreaFormula.lean) and
[`MovingSofaOptimality/External/AreaFormula/Param.lean`](../../MovingSofaOptimality/External/AreaFormula/Param.lean).

1. *Arc length.* Let $P = \sigma_K((0, 2\pi])$, the perimeter, and assume $P > 0$. Then
   $G_K(t + 2\pi) = G_K(t) + P$, so $G_K$ is unbounded in both directions. Its generalized
   inverse $\tau(y) = \min\lbrace t : y \le G_K(t)\rbrace$, the normal angle at arc length $y$,
   satisfies $\tau(y) \le t \iff y \le G_K(t)$. Hence $\tau$ pushes the Lebesgue measure on
   $(G_K(a), G_K(b)]$ forward to $\sigma_K$ on $(a, b]$. The curve
   $\gamma(y) = v_K^+(0) + \int_{G_K(0)}^{y} v_{\tau(r)}\,\mathrm{d}r$ is the arc-length
   parametrization of the boundary. Indeed $\gamma(G_K(t)) = v_K^+(t)$ by Theorem 6.12, so
   $\gamma(y)$ lies on the edge $e_K(\tau(y))$ and
   $\langle \gamma(y), u_{\tau(y)}\rangle = h_K(\tau(y))$. Moreover $\gamma$ is $P$-periodic,
   injective on every interval $[y_0, y_0 + P)$ when $K$ has interior points, and has
   $\gamma'(y) = v_{\tau(y)}$ wherever $\tau$ is continuous, that is, outside a countable set.
2. *Cones.* Let $c$ be an interior point of $K$. The cone map
   $\Psi(y, \lambda) = c + \lambda\,(\gamma(y) - c)$ on
   $[G_K(0), G_K(0) + P) \times (0, 1)$, without the countably many $y$ where $\tau$ jumps, is
   injective, because every ray from $c$ leaves $K$ once. Its image is $K$ up to a null set (the
   boundary, $c$, and countably many segments). Its Jacobian determinant has absolute value
   $\lambda\,\lvert(\gamma(y) - c) \times \gamma'(y)\rvert = \lambda\,(h_K(\tau(y)) - \langle c, u_{\tau(y)}\rangle)$.
   The change of variables formula, Tonelli's theorem and step 1 give
   ```math
   \lvert K\rvert = \int \int_0^1 \lambda\,\bigl(h_K(\tau(y)) - \langle c, u_{\tau(y)}\rangle\bigr)\,\mathrm{d}\lambda\,\mathrm{d}y = \frac12 \int_{(0, 2\pi]} \bigl(h_K(t) - \langle c, u_t\rangle\bigr)\,\mathrm{d}\sigma_K(t) .
   ```
3. *The apex.* $\int_{(0, 2\pi]} u_t\,\mathrm{d}\sigma_K(t) = 0$ (§6.3), so the terms with $c$ vanish.
4. *Empty interior.* If $K$ has no interior point, it lies in a line, and $\lvert K\rvert = 0$. For a
   point $c \in K$, both $\gamma(y) - c$ and $\gamma'(y)$ are parallel to that line, so
   $h_K(\tau(y)) - \langle c, u_{\tau(y)}\rangle = (\gamma(y) - c) \times \gamma'(y) = 0$ almost
   everywhere, and the right side vanishes too.
5. *The interval.* $\sigma_K$ and $h_K$ have period $2\pi$, so $[0, 2\pi)$ and $(0, 2\pi]$ give the
   same integral. $\square$

*Lean: [`af_tau`](../../MovingSofaOptimality/External/AreaFormula/Param.lean#L182), [`af_gamma`](../../MovingSofaOptimality/External/AreaFormula/Param.lean#L185), [`af_setIntegral_tau`](../../MovingSofaOptimality/External/AreaFormula/Param.lean#L221), [`af_hasDerivAt_gamma`](../../MovingSofaOptimality/External/AreaFormula/Param.lean#L348), [`af_gamma_injOn`](../../MovingSofaOptimality/External/AreaFormula/Param.lean#L381),
[`af_det_coneDeriv`](../../MovingSofaOptimality/External/AreaFormula.lean#L194), [`af_area_eq_of_interior`](../../MovingSofaOptimality/External/AreaFormula.lean#L411), [`af_integral_eq_zero`](../../MovingSofaOptimality/External/AreaFormula.lean#L486).*

## 6.5 Weak convergence

Convex bodies converge in the Hausdorff distance
$d_\mathrm{H}(K, L) = \sup_t \lvert h_K(t) - h_L(t)\rvert$ of
[Definition 2.11](02-preliminaries.md#definition-211-hausdorff-distance-baek-definition-2112), that
is, when their support functions converge uniformly.

### Theorem 6.14 (weak convergence; Baek, Theorem 4.1.3)

If convex bodies $K_n$ converge to a convex body $K$ in the Hausdorff distance, then
$\sigma_{K_n} \to \sigma_K$ weakly as measures on the circle: for every continuous $2\pi$-periodic
function $f$,

```math
\int_{[0, 2\pi)} f\,\mathrm{d}\sigma_{K_n} \to \int_{[0, 2\pi)} f\,\mathrm{d}\sigma_K .
```

*Lean: [`theorem4_1_3`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L840), [`hausdorffDist`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L83), [`HausdorffTendsto`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L86).*

Baek cites this from Schneider (Theorem 4.2.1) and uses it in four places:
his Theorem 4.1.4
([Theorem 5.6](05-rotation-angle.md#theorem-56-horizontal-sides-of-balanced-maximum-caps-baek-theorem-414)),
his Lemma 6.4.2 and Theorem 6.4.3
([Lemma 7.17](07-injectivity.md#lemma-717-convergence-of-the-arms-baek-lemma-642) and
[Theorem 7.18](07-injectivity.md#theorem-718-limit-inequality-baek-theorem-643)), and the proof of
Theorem 6.12. The formalization proves the theorem but uses it nowhere. Theorem 6.12 has a direct
proof, and the other three pass to the limit with the sandwich after Lemma 6.7, as step 1 below
does. Figure 6.5 shows an example.

![A graph over the angles from 0 to 2π: the straight line G(t) = t of the unit disk, and the staircases of the regular 4-gon, 8-gon and 16-gon inscribed in the unit circle, with jumps at the angles 2πk/n; the finer the polygon, the closer its staircase to the line](figures/06-surface-area/weak-convergence.svg)

*Figure 6.5.* The distribution functions of the regular $n$-gons inscribed in the unit circle, for
$n = 4, 8, 16$, and of the unit disk, $G(t) = t$. The measure $\sigma_{K_n}$ has $n$ atoms of mass
$2\sin(\pi/n)$ at the angles $2\pi k/n$, and converges weakly to $\sigma_K = \mathrm{d}t$.

*Proof sketch.* The idea is to show that the distribution functions converge at almost every angle,
to deduce the convergence for smooth test functions by integration by parts, and to approximate. The
full proof is in [`MovingSofaOptimality/Angle/HorizontalSide.lean`](../../MovingSofaOptimality/Angle/HorizontalSide.lean).

1. *Distribution functions.* Let $t$ be an angle with $\sigma_K(t) = 0$; all but countably many
   angles are such. Fix $\delta \in (0, \pi)$ and apply the sandwich after Lemma 6.7 to $K_n$. Its
   outer terms depend only on support values, which converge uniformly. So every limit point of
   $\langle v_{K_n}^+(t), v_t\rangle$ lies between the outer terms for $K$. As $\delta \to 0^+$
   these tend to $\langle v_K^-(t), v_t\rangle$ and $\langle v_K^+(t), v_t\rangle$, which are equal
   because $\sigma_K(t) = 0$ (Proposition 6.10). Hence
   $\langle v_{K_n}^+(t), v_t\rangle \to \langle v_K^+(t), v_t\rangle$, and
   $G_{K_n}(t) \to G_K(t)$.
2. *Smooth test functions.* For a continuously differentiable $g$ with $g(0) = g(2\pi)$, integration
   by parts against $G_K$ gives
   ```math
   \int_{[0, 2\pi)} g\,\mathrm{d}\sigma_K = g(0)\int_0^{2\pi} h_K - \int_0^{2\pi} g'(t)\,G_K(t)\,\mathrm{d}t .
   ```
   The first term converges because the support functions converge uniformly. The second converges
   by step 1 and dominated convergence, since $\lvert G_{K_n}(t)\rvert \le R\,(1 + \lvert t\rvert)$
   when $\lvert h_{K_n}\rvert \le R$.
3. *Continuous test functions.* With $g = 1$, the total masses converge, so they are bounded. A
   continuous $2\pi$-periodic $f$ is a uniform limit of functions $g$ as in step 2 (its averages over
   short intervals), and the bounded masses make the approximation uniform in $n$. $\square$

*Lean: [`ang_dplus_mul_sin_le`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L480), [`ang_le_dminus_mul_sin`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L488), [`ang_tendsto_sigmaFun`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L692),
[`ang_integral_sigma_eq`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L596), [`ang_tendsto_integral_sigmaFun`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L719), [`ang_exists_C1_approx`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L757).*
