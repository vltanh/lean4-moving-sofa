# 12. Uniqueness II: every maximum is Gerver's sofa

[Contents](README.md) · [← 11. Uniqueness I: approximating a maximizing cap](11-selection.md) · [13. The bridge to formal-conjectures →](13-bridge.md)

This chapter completes the proof that Gerver's sofa is the only moving sofa of maximum area, up to
a rotation and a translation (Theorem 12.1). [Chapter 11](11-selection.md) approximated a given
maximizing cap by penalized polygon maximizers whose defects $\sigma - \tau$ are small, and deduced
the pinned bounds. Here the floating defect bounds give every maximizing right-angle cap the
curvature bounds, and hence the injectivity condition (§12.1, §12.2). The pinned bounds give a
maximizing monotone sofa of smaller angle a rotated copy with a right-angle motion (§12.3).

A right-angle cap in $\mathcal{K}^\mathrm{i}$ with the sofa area of Gerver's sofa attains the
maximum of Baek's upper bound $\mathcal{Q}$. Equality in each of Mamikon's terms then forces its
support function to differ from that of Gerver's cap by $a\cos t$, so the cap is a horizontal
translate of Gerver's (§12.4). Finally, Gerver's sofa is the closure of its interior (§12.5), which
recovers the given set from its area (§12.6). The same arguments show that the maximizing
right-angle caps are exactly the horizontal translates of Gerver's cap, and that the rotation in
Theorem 12.1 can be taken to be the identity (§12.7).

## Theorem 12.1 (uniqueness of Gerver's sofa)

Let $G$ be Gerver's sofa. For every moving sofa $S$ with $|S| = |G|$ there are an angle $\theta$ and
a vector $v$ such that

```math
R_\theta S + v = G .
```

So the moving sofas of maximum area are exactly the moving sofas that a rotation about the origin
followed by a translation maps onto $G$.

*Lean: [`Baek.gerver_sofa_unique`](../../Challenge.lean#L688), [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L301),
[`MovingSofaUniqueness.Rigid`](../../MovingSofaUniqueness/Rigid.lean); the second sentence: [`isMaximal_iff_image_eq_gerver`](../../MovingSofaUniqueness/Main.lean#L316).*

Here $|\cdot|$ is the Lebesgue measure, $G$ is defined from the solution of Romik's system in the
box of [Chapter 10](10-gerver.md), and a moving sofa is a closed connected set with a motion around
the corner of the hallway ([Chapter 2](02-preliminaries.md)). The equality is one of sets, not up to
a null set. The converse in the second sentence holds because rigid maps preserve area and $|G|$ is
the maximum ([Theorem 9.33](09-optimality.md#theorem-933-optimality-of-gervers-sofa-baek-theorem-111)).
Not every rigid image of $G$ is a moving sofa, since a moving sofa starts in the horizontal side of
the hallway (Remark 12.29). In fact the rotation can be taken to be the identity (Theorem 12.28).

*Outline of the proof.* The proof follows the given sofa $S$, keeping a rigid image of it inside
each new set (Figure 12.1).

1. *Monotonization*
   ([Lemma 11.3](11-selection.md#lemma-113-the-monotonization-of-a-maximizing-sofa)). By
   [Theorem 5.1](05-rotation-angle.md#theorem-51-a-first-bound-on-the-rotation-angle-baek-theorem-151),
   $S$ moves with a rotation angle $\omega \in [\sec^{-1}(2.2), \pi/2]$. A translate $S + v_0$ lies
   in its monotonization $T$, a monotone sofa of angle $\omega$ with $|T| = |G|$, whose cap
   maximizes $\mathcal{A}_\omega$.
2. *Right angle* (§12.3). If $\omega < \pi/2$, the pinned bounds of that cap give a right-angle
   motion of the rotated copy $R_a T$, $a = \pi/2 - \omega$ (Proposition 12.13). Monotonizing
   $R_a T$ gives a monotone sofa $U$ of angle $\pi/2$ with $|U| = |G|$ that contains
   $R_a(S + v_0) + v_1$.
3. *Gerver's cap* (§12.1, §12.2, §12.4). The cap of $U$ maximizes $\mathcal{A}_{\pi/2}$, so it
   satisfies the injectivity condition (Corollary 12.10), and equality in Baek's upper bound makes
   $U$ a horizontal translate $G + (b, 0)$ (Proposition 12.19).
4. *Recovery* (§12.5, §12.6). So a rigid map $g$ maps $S$ into $G$. Since $S$ is closed, $G$ is the
   closure of its interior (Proposition 12.22) and $|g(S)| = |G|$, in fact $g(S) = G$
   (Lemma 12.23).

![A flow chart of five boxes joined by downward arrows. The boxes read: S, a moving sofa with area that of G; S + v0 contained in T, a monotone sofa of angle ω with the area of G whose cap maximizes the sofa area; R_a(S + v0) contained in R_a T, which moves with angle π/2; g1(S) contained in U = G + (b, 0), U monotone of angle π/2; and g(S) = G. The arrows are labelled translate and monotonize, rotate by a, translate and monotonize, and translate by (−b, 0)](figures/12-uniqueness/chain.svg)

*Figure 12.1.* The containment chain of the proof. Every arrow is a translation or a rotation, and
every box contains the image of $S$ under the maps so far; all the sets have area $|G|$. Here
$g_1(p) = R_a(p + v_0) + v_1$ and $g(p) = g_1(p) - (b, 0)$.

## 12.1 The curvature bounds

In §12.1 and §12.2 the rotation angle is $\pi/2$. For a right-angle cap $K$ and an angle $t$, the
supporting hallway $L_K(t)$ has the outer corner $\mathbf{y}_K(t)$ and the inner corner
$\mathbf{x}_K(t)$, and its outer walls touch $K$ at the vertices $A_K^\pm(t) = v_K^\pm(t)$ and
$C_K^\pm(t) = v_K^\pm(t + \pi/2)$. The *arm lengths*
$f_K^\pm(t) = (\mathbf{y}_K(t) - A_K^\pm(t)) \cdot v_t$ and
$g_K^\pm(t) = (\mathbf{y}_K(t) - C_K^\pm(t)) \cdot u_t$ are the distances from the outer corner to
these vertices
([Definition 7.4](07-injectivity.md#definition-74-arm-lengths-baek-definition-621)). Baek's
functions

```math
k_0(x) = \max\Bigl(|x - 1|, \frac{|x - 1| + 1}2\Bigr), \qquad m_0(x) = x - k_0(x)
```

([Definition 7.14](07-injectivity.md#definition-714-balancing-functions-baek-definition-634))
satisfy: $k_0$ is 1-Lipschitz, and $m_0$ is nondecreasing, with $m_0(x) = \frac32 x - 1$ on
$[0, 1]$, $\frac x2$ on $[1, 2]$ and $1$ on $[2, \infty)$.

Baek proves the injectivity condition for a balanced maximum cap $K$ from the bound
$\sigma_K \le k_0(g_K^+(t))\,\mathrm{d}t$ on $[0, \pi/2)$
([Theorem 7.18](07-injectivity.md#theorem-718-limit-inequality-baek-theorem-643)). It is the limit
of the bounds $\sigma_{K_n}(t) \le k_0(g_{K_n}^+(t))\delta + O(\delta^2)$ for maximum polygon caps
with step size $\delta$
([Theorem 7.15](07-injectivity.md#theorem-715-discrete-inequality-baek-theorem-633)), whose proof
uses the balance $\sigma = \tau$. For the polygon caps of
[Proposition 11.13](11-selection.md#proposition-1113-selection-note-20-proposition-1) the floating
defect bound $\sigma \le \tau + 2\eta\, w(t)$
([Proposition 11.16](11-selection.md#proposition-1116-floating-defects-note-20-proposition-2))
replaces the balance, and its errors add up to at most $2\eta$.

### Definition 12.2 (the curvature bounds)

A right-angle cap $K$ satisfies the *curvature bounds* if, as measures,

```math
\sigma_K \le k_0\bigl(g_K^+(t)\bigr)\,\mathrm{d}t \ \text{ on } [0, \pi/2), \qquad \sigma_K \le k_0\bigl(f_K^-(t - \pi/2)\bigr)\,\mathrm{d}t \ \text{ on } (\pi/2, \pi] . \tag{12.1}
```

*Lean: [`FirstCurvatureBound`](../../MovingSofaUniqueness/Curvature.lean#L38), [`SecondCurvatureBound`](../../MovingSofaUniqueness/Curvature.lean#L44).*

Let $\Theta_n$, $n = 2^{k+1}$, be the right-angle set $\Theta^{(k)}$ of
[Chapter 11](11-selection.md), with step size $\delta = (\pi/2)/n$
([Definition 7.10](07-injectivity.md#definition-710-steps-baek-definitions-631-and-632)). Its
normals are all floating, since $\Theta_n \subseteq (0, \pi/2)$.

### Lemma 12.3 (one normal of a polygon cap; note 20, (14) and (15))

Let $K$ be a polygon cap of $\Theta_n$ with step size $\delta$, let $t \in \Theta_n$, and put
$q = \tan(\delta/2)$. Then

```math
\tau_K(t) \le \max\Bigl(\tan\delta\,\bigl(g_K^-(t) - 1 + q\bigr),\ \tan\delta\,\bigl(1 - g_K^+(t) + q\bigr),\ 0\Bigr) + \max\bigl(2q - \sigma_K(t),\ 0\bigr) . \tag{12.2}
```

If moreover $\sigma_K(t) \le \tau_K(t) + e$ with $e \ge 0$, and $g_K^+(t) \le D$, then

```math
\sigma_K(t) \le k_0\bigl(g_K^+(t)\bigr)\,\delta + (D + 4)\,\delta^2 + e . \tag{12.3}
```

*Proof sketch.* (12.2) is the geometry of the inner wall in the proof of Theorem 7.15, whose Steps
1 to 3 hold for every polygon cap of $\Theta_n$. By
[Lemma 4.27](04-balanced.md#lemma-427-sides-of-the-polygon-niche-baek-lemma-345) (1), $\tau_K(t)$ is
the length of the side $X$ of the niche on the half-line $\vec b_K(t)$ that leaves the inner corner
$\mathbf{x}_K(t)$ along $-v_t$. Step 1 splits $X$ into a part beyond one of the inner walls
$d_K(t - \delta)$, $d_K(t)$, $d_K(t + \delta)$ and a part beyond the three inner walls
$b_K(t - \delta)$, $b_K(t)$, $b_K(t + \delta)$. By
[Lemma 7.13](07-injectivity.md#lemma-713-the-inner-wall-near-the-corner-baek-lemma-632), whose
computation uses only that $t - \delta$, $t$, $t + \delta$ are consecutive normals, the first part
has length at most the first maximum in (12.2). By Step 3, the second part has length at most
$\max(2q - \sigma_K(t), 0)$.

For (12.3), let $M = |g_K^+(t) - 1| \le D + 1$. As $g_K^-(t) \le g_K^+(t)$, the first maximum is at
most $\tan\delta\,(M + q) \le \delta M + (D + 3)\delta^2$, using $\tan\delta \le \delta + \delta^2$
and $q \le \delta$ for $\delta \le \pi/4$. If $\sigma_K(t) \ge 2q$, then
$\sigma_K(t) \le \tau_K(t) + e \le \delta M + (D + 3)\delta^2 + e$. If $\sigma_K(t) < 2q$, then
$2\sigma_K(t) \le \delta M + (D + 3)\delta^2 + 2q + e$, and $2q \le \delta + \delta^2$, so
$\sigma_K(t) \le \frac{M + 1}2\delta + (D + 4)\delta^2 + e$. Both $M$ and $\frac{M + 1}2$ are at
most $k_0(g_K^+(t))$. $\square$

*Lean: [`polygon_tau_le_geom`](../../MovingSofaUniqueness/Curvature.lean#L387), [`polygon_curvature_with_defect`](../../MovingSofaUniqueness/Curvature.lean#L500).*

### Lemma 12.4 (from normals to intervals)

Let $K$ be a polygon cap of $\Theta_n$ of diameter at most $D$, with $k_0(g_K^+) \le B$ on
$[0, \pi/2]$, and suppose that $\sigma_K(t) \le k_0(g_K^+(t))\,\delta + C\delta^2 + e(t)$ at every
grid normal $t \in \lbrace 0 \rbrace \cup \Theta_n$, with $C \ge 0$ and $e \ge 0$. Then for
$0 \le a \le b \le \pi/2$,

```math
\sigma_K\bigl([a, b)\bigr) \le \int_a^b k_0\bigl(g_K^+(u)\bigr)\,\mathrm{d}u + \Bigl(2B + \frac\pi2(C + D)\Bigr)\delta + \sum_{j=0}^{n-1} e(j\delta) ,
```

and the same bound holds for $\sigma_K((a, b))$ with $-\pi/2 \le a < b \le \pi/2$ and $b \ge 0$,
integrating from $\max(a, 0)$.

*Proof.* On each cell $[t, t + \delta]$ the cap has one vertex $A$ on the lines $l_K(s)$ and one
vertex $C$ on the lines $l_K(s + \pi/2)$, and $g_K^+(s) = (A - C) \cdot u_s$ there, as in the proof
of [Lemma 7.16](07-injectivity.md#lemma-716-arms-between-two-steps-baek-lemma-641). Its derivative
$(A - C) \cdot v_s$ lies in $[-D, 0]$, so $g_K^+$ is nonincreasing on the cell and drops by at most
$D\delta$. Since $k_0$ is 1-Lipschitz,
$k_0(g_K^+(t))\,\delta \le \int_t^{t + \delta} k_0(g_K^+) + D\delta^2$. The polygon $K$ has no edge
with normal in $(t, t + \delta)$, so $\sigma_K([t, t + \delta)) = \sigma_K(t)$. Summing over the at
most $n$ cells that meet $[a, b)$ costs $n(C + D)\delta^2 = \frac\pi2(C + D)\delta$, and the two
partial cells at the ends at most $2B\delta$. Open intervals that start below $0$ give the same
bound, since $\sigma_K$ vanishes on $(-\pi/2, 0)$ for a right-angle cap. $\square$

*Lean: [`polygon_arm_cell`](../../MovingSofaUniqueness/Curvature.lean#L224), [`polygon_step_with_error`](../../MovingSofaUniqueness/Curvature.lean#L337), [`polygon_Ico_with_errors`](../../MovingSofaUniqueness/Curvature.lean#L733),
[`polygon_Ioo_with_errors`](../../MovingSofaUniqueness/Curvature.lean#L900), [`polygonGridError`](../../MovingSofaUniqueness/Curvature.lean#L728).*

### Lemma 12.5 (passing to the limit)

Let polygon caps $K_n$ converge in the Hausdorff distance to a right-angle cap $K$, and suppose that

```math
\sigma_{K_n}\bigl((a, b)\bigr) \le \int_{\max(a, 0)}^b k_0\bigl(g_{K_n}^+(u)\bigr)\,\mathrm{d}u + \varepsilon_n
```

whenever $-\pi/2 \le a < b \le \pi/2$ and $\max(a, 0) \le b$, with $\varepsilon_n \to 0$. Then $K$
satisfies the first curvature bound.

*Proof.* This is Steps 2 to 4 of the proof of Theorem 7.18, which do not use that the caps are
maximal. The integrals on the right converge to those for $K$, because $g_{K_n}^+ \to g_K^+$ in
$L^1$ ([Lemma 7.17](07-injectivity.md#lemma-717-convergence-of-the-arms-baek-lemma-642)) and $k_0$
is 1-Lipschitz. The mass of an open interval has lower bounds, given by intersections of supporting
lines, that converge with $K_n$ and tend to $\sigma_K((a, b))$ (Step 3). So
$\sigma_K((a, b)) \le \liminf_n \sigma_{K_n}((a, b)) \le \int_{\max(a, 0)}^b k_0(g_K^+)$. Bounds on
these open intervals, including those that start below $0$, determine the inequality of measures on
$[0, \pi/2)$, including the normal $0$ (Step 4). $\square$

*Lean: [`k0_integral_tendsto`](../../MovingSofaUniqueness/Curvature.lean#L964), [`curvature_Ioo_limit`](../../MovingSofaUniqueness/Curvature.lean#L995), [`firstCurvature_of_Ioo`](../../MovingSofaUniqueness/Curvature.lean#L1039),
[`firstCurvature_of_polygon_errors`](../../MovingSofaUniqueness/Curvature.lean#L1104), [`lemma6_4_2`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L329).*

Because the intervals may start below $0$, the bound rules out an atom of $\sigma_K$ at the normal
$0$; note 20 stresses that the curvature bounds prove the absence of such an atom rather than
assume it.

### Proposition 12.6 (curvature bounds; note 20, Proposition 3)

Every right-angle cap $K$ that maximizes $\mathcal{A}_{\pi/2}$ with $\mathcal{A}_{\pi/2}(K) > 0$
satisfies the curvature bounds (12.1).

*Proof.* The selected polygon caps satisfy the discrete bound (12.3) with errors that add up to
$O(\eta)$; Lemmas 12.4 and 12.5 pass it to the limit. The second bound follows by reflection.

Take the selection of Proposition 11.13 for $\omega = \pi/2$: penalized maximizers $K_n$ of
$\Theta_{2^{k_n + 1}}$, with step sizes $\delta_n \to 0$, in a box $[-R, R] \times [0, 1]$,
converging to $K$. Put $\eta_n = d_\mathrm{H}(K_n, K) \to 0$; the sampled supports of $K_n$ are
within $\eta_n$ of those of $K$. The box bounds the diameter by $D = 2R + 2$, so $g_{K_n}^+ \le D$ and
$k_0(g_{K_n}^+) \le D + 1$. At every $t \in \Theta_{2^{k_n+1}}$, Proposition 11.16 gives
$\sigma_{K_n}(t) \le \tau_{K_n}(t) + 2\eta_n w_n(t)$, where $w_n(t)$ is the sample weight at $t$, so
Lemma 12.3 gives (12.3) with $e(t) = 2\eta_n w_n(t)$. At $t = 0$ the bound is trivial, as
$\sigma_{K_n}(0) = 0$. The weights at the distinct grid normals add up to at most the total weight,
which is at most one ([Lemma 11.7](11-selection.md#lemma-117-the-dyadic-penalty)), so the errors add
up to at most $2\eta_n$. By Lemma 12.4 the hypothesis of Lemma 12.5 holds with
$\varepsilon_n = A\delta_n + 2\eta_n \to 0$, $A = 2(D + 1) + \frac\pi2(2D + 4)$, which gives the
first bound.

For the second bound, the reflection $(x, y) \mapsto (-x, y)$ maps $K$ to a right-angle cap $K^\mathrm{m}$
with the same sofa area
([Proposition 3.21](03-monotone.md#proposition-321-mirror-symmetry-baek-proposition-254)), which is
therefore maximizing. It maps $\sigma_{K^\mathrm{m}}$ to $\sigma_K$ under $t \mapsto \pi - t$, and it
exchanges the arms: $g_{K^\mathrm{m}}^+(t) = f_K^-(\pi/2 - t)$
([Proposition 7.6](07-injectivity.md#proposition-76-mirror-image-baek-proposition-622)). So the
first bound for $K^\mathrm{m}$ is the second bound for $K$. $\square$

*Lean: [`curvature_of_maximal_positive`](../../MovingSofaUniqueness/Curvature.lean#L1380), [`firstCurvature_of_maximal_positive`](../../MovingSofaUniqueness/Curvature.lean#L1193),
[`sampled_grid_error_le`](../../MovingSofaUniqueness/Curvature.lean#L1154), [`diameter_le_box`](../../MovingSofaUniqueness/Curvature.lean#L1169), [`secondCurvature_of_mirror_first`](../../MovingSofaUniqueness/Curvature.lean#L1330),
[`sigma_eq_map_mirror`](../../MovingSofaUniqueness/Curvature.lean#L1321).*

Gerver's cap maximizes $\mathcal{A}_{\pi/2}$, so it satisfies the curvature bounds. Figure 12.2
shows the first of them, computed from Romik's rotation path: it is an equality on most of
$[0, \pi/2)$.

![A graph over the interval from 0 to π/2 with dashed vertical lines at t1, t2, t3, t4. A blue curve, the density r(t), is zero up to t1, then jumps to about 1.40 and decreases; an orange dashed curve k0(g(t)) starts near 1.42 and decreases to 0.5. The two curves coincide from t1 to about 0.62 and from t3 to t4; elsewhere the blue curve is lower and the gap between them is shaded](figures/12-uniqueness/curvature.svg)

*Figure 12.2.* The first curvature bound for Gerver's cap $\mathcal{C}(G)$, which maximizes
$\mathcal{A}_{\pi/2}$ by Baek's theorem ([Lemma 11.2](11-selection.md#lemma-112-the-maximum-value)):
the density $r(t) = A'(t) \cdot v_t$ of $\sigma_{\mathcal{C}(G)}$ on $[0, \pi/2)$ (blue) lies below
$k_0(g(t))$ (orange, dashed), computed from Romik's rotation path. Here
$t_1, \dots, t_4$ are $\varphi, \theta, \pi/2 - \theta, \pi/2 - \varphi$. The two agree from $t_1$
until $g(t) = 2$, near $t = 0.62$, and from $t_3$ to $t_4$; the gap is shaded.

## 12.2 The injectivity condition

Recall the injectivity condition for a right-angle cap $K$
([Definition 7.1](07-injectivity.md#definition-71-injectivity-condition-baek-definition-612)):
(1) $\sigma_K$ has a density on $[0, \pi/2)$ and on $(\pi/2, \pi]$; (2) the inner corner
$\mathbf{x}_K$ is continuously differentiable on $[0, \pi/2]$; (3)
$\mathbf{x}_K'(t) \cdot u_t < 0 < \mathbf{x}_K'(t) \cdot v_t$ for $t \in (0, \pi/2)$. The space
$\mathcal{K}^\mathrm{i}$ consists of the right-angle caps with the injectivity condition and area at
least $2.2$
([Definition 9.1](09-optimality.md#definition-91-caps-with-the-injectivity-condition-baek-definition-811)).
Under (1), $f_K^+ = f_K^-$ on $[0, \pi/2)$ and $g_K^+ = g_K^-$ on $(0, \pi/2]$; write
$f_K = f_K^-$ and $g_K = g_K^+$, which are continuous on $[0, \pi/2]$
([Propositions 7.20](07-injectivity.md#proposition-720-single-contact-points-baek-proposition-645)
and [7.22](07-injectivity.md#proposition-722-regularity-of-the-corners-baek-proposition-646)).

### Lemma 12.7 (the integral inequalities; note 20, (17))

Let $K$ be a right-angle cap with the curvature bounds. Then $K$ satisfies condition (1), and

```math
\int_0^t m_0\bigl(g_K(u)\bigr)\,\mathrm{d}u \le f_K(t) - 1 \quad \bigl(t \in [0, \pi/2)\bigr), \qquad \int_t^{\pi/2} m_0\bigl(f_K(u)\bigr)\,\mathrm{d}u \le g_K(t) - 1 \quad \bigl(t \in (0, \pi/2]\bigr) .
```

*Proof.* Condition (1) holds by the Radon–Nikodym theorem, since each restriction of $\sigma_K$ is
dominated by a measure with a density.
[Theorem 7.9](07-injectivity.md#theorem-79-derivative-of-the-arm-f-baek-theorem-625) gives
$f_K^+(t) - f_K^+(0) = \int_0^t g_K^+ - \sigma_K((0, t])$. Here $f_K^+ = f_K$ on $[0, \pi/2)$, and
$f_K(0) = 1$ because the vertex $A_K(0)$ is the right end $(h_K(0), 0)$ of the bottom edge. By the
first curvature bound, $\sigma_K((0, t]) \le \int_0^t k_0(g_K)$; as $m_0(x) = x - k_0(x)$, this is
the first inequality. The second is the same argument for $g$, with the identity
$g_K^+(\pi/2) - g_K^+(t) = \sigma_K((t + \pi/2, \pi]) - \int_t^{\pi/2} f_K^+$, the value
$g_K(\pi/2) = 1$ and the second curvature bound. $\square$

*Lean: [`injCond1_of_curvature`](../../MovingSofaUniqueness/Curvature.lean#L51), [`first_arm_integral_lower`](../../MovingSofaUniqueness/Curvature.lean#L130), [`second_arm_integral_lower`](../../MovingSofaUniqueness/Curvature.lean#L152),
[`gPlus_sub_gPlus`](../../MovingSofaUniqueness/Curvature.lean#L94).*

### Lemma 12.8 (the lower sequence; Baek, Lemmas 6.5.2 and 6.5.5)

Let $\mathcal{F}f(x) = 1 + \int_0^x m_0(f(\pi/2 - u))\,\mathrm{d}u$, $f_0 = 0$ and
$f_{n+1} = \max(f_n, \mathcal{F}f_n)$
([Definition 7.24](07-injectivity.md#definition-724-the-iteration-baek-definitions-651-and-652)).

1. If continuous functions $f, g \ge 0$ on $[0, \pi/2]$ satisfy the two inequalities of
   Lemma 12.7, then $f_n(t) \le f(t)$ for $t \in [0, \pi/2)$ and $f_n(\pi/2 - t) \le g(t)$ for
   $t \in (0, \pi/2]$, for every $n$.
2. $f_{11}(x) > 1$ for every $x \in (0, \pi/2]$ (Figure 12.3).

*Proof.* (1) Induction on $n$, as in the proof of
[Lemma 7.25](07-injectivity.md#lemma-725-lower-bounds-baek-lemma-652); $f_0 = 0 \le f, g$. If the
claim holds for $n$, then for $t \in [0, \pi/2)$, since $m_0$ is nondecreasing,
$\int_0^t m_0(f_n(\pi/2 - u))\,\mathrm{d}u \le \int_0^t m_0(g(u))\,\mathrm{d}u \le f(t) - 1$, so
$\mathcal{F}f_n(t) \le f(t)$; the bound for $g$ is symmetric. (2) is
[Lemma 7.28](07-injectivity.md#lemma-728-the-eleventh-bound-baek-lemma-655). $\square$

*Lean: [`lowerSeq_le_of_integral_bounds`](../../MovingSofaUniqueness/Curvature.lean#L619), [`lowerSeq`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L244), [`lowerOp`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L240), [`lemma6_5_5`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L408).*

![A graph over the interval from 0 to π/2 of the functions f1 to f11 of Baek's lower sequence, in grey from light to dark; f1 falls linearly from 1 to 0 and stays at 0, the next ones dip below the dashed line at height 1 less and less, and from f6 on they rise above it; f11 is orange and ends near 2.31. A blue dashed curve, the arm f of Gerver's cap, runs above f11 and ends near 2.42](figures/12-uniqueness/lower-sequence.svg)

*Figure 12.3.* Baek's lower sequence $f_1, \dots, f_{11}$ (grey, darker for larger $n$), computed
numerically, with $f_{11}$ in orange above the line at height one, and the arm $f$ of Gerver's cap
(blue, dashed), which lies above all of them, as Lemma 12.8 (1) predicts for a maximizing cap.

### Proposition 12.9 (injectivity; note 20, Proposition 3)

A right-angle cap $K$ with the curvature bounds satisfies the injectivity condition. Moreover
$f_K(t) > 1$ and $g_K(t) > 1$ for $t \in (0, \pi/2)$.

*Proof.* By Lemma 12.7, $K$ satisfies condition (1) and the integral inequalities, and $f_K, g_K$ are
continuous and nonnegative on $[0, \pi/2]$. By Lemma 12.8, for $t \in (0, \pi/2)$,
$1 < f_{11}(t) \le f_K(t)$ and $1 < f_{11}(\pi/2 - t) \le g_K(t)$. Under condition (1) the inner
corner is continuously differentiable with

```math
\mathbf{x}_K'(t) = -\bigl(f_K(t) - 1\bigr)u_t + \bigl(g_K(t) - 1\bigr)v_t
```

(Proposition 7.22), which is condition (2), and the strict inequalities give condition (3).
$\square$

*Lean: [`injectivity_of_curvature`](../../MovingSofaUniqueness/Curvature.lean#L691), [`arms_strict_of_curvature`](../../MovingSofaUniqueness/Curvature.lean#L674), [`proposition6_4_6_deriv`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L1117).*

*Remark (the formal route).* From (17), note 20 shows $f, g \ge 1$ by a maximum-deficit argument,
with $m_0(x) \ge \frac12 - \frac32(1 - x)_+$, and then $f(t) \ge 1 + t/2$ and
$g(t) \ge 1 + (\pi/2 - t)/2$. The formalization compares the arms with Baek's lower sequence
instead, as the library does for balanced maximum caps; this gives the strict inequalities that
condition (3) needs.

### Corollary 12.10 (maximizing right-angle caps; note 20, Proposition 3)

Every right-angle cap $K$ with $\mathcal{A}_{\pi/2}(K) = |G|$ lies in $\mathcal{K}^\mathrm{i}$.

*Proof.* By Lemma 11.2, $K$ maximizes $\mathcal{A}_{\pi/2}$, and
$\mathcal{A}_{\pi/2}(K) = |G| \ge 2.2 > 0$. Propositions 12.6 and 12.9 give the injectivity
condition, and $|K| \ge |K| - |\mathcal{N}(K)| = |G| \ge 2.2$. $\square$

*Lean: [`MovingSofaUniqueness.isKi_of_maximal_area`](../../MovingSofaUniqueness/Main.lean#L91), [`MovingSofaUniqueness.sofaArea_pos_of_isMaxCap`](../../MovingSofaUniqueness/Main.lean#L81),
[`IsKi`](../../MovingSofaOptimality/Optimality/Domain.lean#L205).*

## 12.3 The right-angle motion

[Theorem 5.2](05-rotation-angle.md#theorem-52-the-right-angle-baek-theorem-152) rotates a
balanced maximum sofa of angle $\omega < \pi/2$ into one with a right-angle motion. Its proof uses
the balance only through the pinned bounds of
[Theorem 5.6](05-rotation-angle.md#theorem-56-horizontal-sides-of-balanced-maximum-caps-baek-theorem-414),
which [Proposition 11.23](11-selection.md#proposition-1123-pinned-bounds-note-20-proposition-4)
provides for every maximizing cap. Let $c_\omega = \sec\omega - \tan\omega$, so that the corner of
$P_\omega$ is $o_\omega = (c_\omega, 1)$, $o_\omega - v_0 = c_\omega u_0$ and
$o_\omega - u_\omega = c_\omega v_\omega$
([Proposition 5.7](05-rotation-angle.md#proposition-57-the-corner-of-the-parallelogram-baek-proposition-421)).

### Lemma 12.11 (the triangle in the niche; Baek, Theorem 4.2.5)

Let $\omega \in [\sec^{-1}(2.2), \pi/2)$, and let $K$ be a cap of angle $\omega$ with
$\mathcal{A}_\omega(K) \ge 11/5$ and the pinned bounds $w_K^\circ \le \sigma_K(\pi/2)$ and
$z_K^\circ \le \sigma_K(\omega)$. Then for some $t \in (0, \omega)$ the points $O$,
$c_\omega u_0$ and $c_\omega v_\omega$ lie in the closure of the inner quadrant $Q_K^-(t)$.

*Proof.* This is the proof of
[Theorem 5.13](05-rotation-angle.md#theorem-513-the-triangle-lies-in-the-niche-baek-theorem-425),
with the pinned bounds as hypotheses. That proof uses the balance only through the bound
$w^\circ \le \sigma(\pi/2)$ of Theorem 5.6, in Step 3, for $K$ or, after the reduction of Step 1,
for the mirror image $K^\mathrm{m}$. For $K$ this bound is now a hypothesis. The mirror image
$K^\mathrm{m}$ is a cap with the same sofa area (Proposition 3.21), and the mirror exchanges the two
pinned bounds: $w_{K^\mathrm{m}}^\circ = z_K^\circ \le \sigma_K(\omega) = \sigma_{K^\mathrm{m}}(\pi/2)$.
The other steps use only that $K$ is a cap with $|K| \ge \mathcal{A}_\omega(K) \ge 11/5$. $\square$

*Lean: [`consumed_of_pinned`](../../MovingSofaUniqueness/AngleExtension.lean#L27), [`lemma4_2_2`](../../MovingSofaOptimality/Angle/RightAngle.lean#L310), [`lemma4_2_4`](../../MovingSofaOptimality/Angle/RightAngle.lean#L523), [`theorem4_2_5`](../../MovingSofaOptimality/Angle/RightAngle.lean#L764).*

### Lemma 12.12 (rotating inside the horizontal side; Baek, Theorem 1.5.2)

Let $S$ be a moving sofa with rotation angle $\omega < \pi/2$ such that
$(p - q) \cdot u_t \le 1$ for all $p, q \in S$ and $t \in [\omega, \pi/2]$. Then the rotated copy
$R_\beta S$, $\beta = \pi/2 - \omega$, moves with rotation angle $\pi/2$.

*Proof.* The motion is that of the proof of Theorem 5.2, which uses only this width bound. For
$\varphi \in [0, \beta]$, the height of $R_\varphi S$, its width in the direction $u_{\pi/2}$, is
the width of $S$ in the direction $u_{\pi/2 - \varphi}$, at most one. So $R_\beta S$ can first turn
back by $\beta$ inside the horizontal side $H_L$, with each intermediate copy $R_\varphi S$ placed
far to the left. Then it translates inside $H_L$ to the starting position of the motion of $S$, and
finally it follows that motion. The total rotation is $\beta + \omega = \pi/2$. $\square$

*Lean: [`right_angle_motion_of_width`](../../MovingSofaOptimality/Angle/RightAngle.lean#L994).*

### Proposition 12.13 (right-angle motion; note 20, Proposition 4)

Let $S$ be a monotone sofa of angle $\omega \in [\sec^{-1}(2.2), \pi/2]$ with
$|S| = |G|$. Then $R_a S$ moves with rotation angle $\pi/2$, where $a = \pi/2 - \omega$.

*Proof.* If $\omega = \pi/2$, then $a = 0$, and $S$ moves with rotation angle $\pi/2$. Otherwise
the cap $K = \mathcal{C}(S)$ maximizes $\mathcal{A}_\omega$, with
$\mathcal{A}_\omega(K) = |S| = |G| \ge 11/5$ (Lemma 11.3). So
Proposition 11.23 gives the pinned bounds, and Lemma 12.11 gives $t_0 \in (0, \omega)$ such that
$O$, $c_\omega u_0$ and $c_\omega v_\omega$ lie in the closure of $Q_K^-(t_0)$. As
$S = K \setminus \mathcal{N}(K)$
([Theorem 3.13](03-monotone.md#theorem-313-a-monotone-sofa-is-its-cap-minus-its-niche-baek-theorem-243)),
[Lemma 5.14](05-rotation-angle.md#lemma-514-the-width-of-the-sofa) shows that $S$ avoids the
triangle $\Delta$ with these vertices, except its far side, and that
$(p - q) \cdot u_t \le 1$ for $p, q \in S$ and $t \in [\omega, \pi/2]$ (Figure 12.4). A monotone
sofa moves with its angle ([Theorem 3.3](03-monotone.md#theorem-33-monotonization-baek-theorem-232)),
so Lemma 12.12 applies. $\square$

*Lean: [`MovingSofaUniqueness.maximal_monotone_has_right_angle`](../../MovingSofaUniqueness/Main.lean#L228),
[`right_angle_motion_of_pinned_bounds`](../../MovingSofaUniqueness/AngleExtension.lean#L87).*

![Top: a parallelogram P_ω, ω = 1.1, leaning left, filled blue except for a small orange triangle Δ at its obtuse bottom corner O; o_ω marks the opposite obtuse corner. Below: three horizontal strips of height one, each holding the pentagon P_ω minus Δ rotated by a different angle: by β (green, leaning right), by β/2 (purple, lying flat on the edge that Δ cut off) and by 0 (blue, leaning left as in the top panel)](figures/12-uniqueness/rotation.svg)

*Figure 12.4.* The extra rotation of Proposition 12.13, for $\omega = 1.1$. Top: the triangle
$\Delta$ (orange) at the corner $O$ of $P_\omega$, which lies in the closure of the niche, and the
pentagon $P_\omega \setminus \Delta$ (blue). Below: the pentagon rotated by $\varphi = \beta$,
$\beta/2$ and $0$, $\beta = \pi/2 - \omega$; for every $\varphi \in [0, \beta]$ it fits in a strip
of width one, so a sofa inside it can turn by $\beta$ in the horizontal side of the hallway before
it starts its own motion.

## 12.4 Equality in the upper bound

Recall Baek's upper bound ([Chapter 9](09-optimality.md)). Let $\varphi$ be Gerver's angle
([Definition 9.3](09-optimality.md#definition-93-gervers-angles-baek-definition-812)). For
$K \in \mathcal{K}^\mathrm{i}$, the canonical triple $x_K = (K, B_K, D_K)$ lies in the convex domain
$\mathcal{L}$ ([Theorem 9.12](09-optimality.md#theorem-912-the-triple-of-a-cap-baek-theorem-818)),
and $\mathcal{A}_{\pi/2}(K) \le \mathcal{Q}(x_K)$
([Theorem 9.18](09-optimality.md#theorem-918-the-upper-bound-baek-theorem-824)). The functional
$\mathcal{Q}$ is quadratic and concave on $\mathcal{L}$
([Proposition 9.14](09-optimality.md#proposition-914-the-upper-bound-is-quadratic-baek-proposition-821),
[Theorem 9.27](09-optimality.md#theorem-927-concavity-baek-theorem-838)), and attains its maximum at
Gerver's triple $x_G$
([Corollary 9.32](09-optimality.md#corollary-932-gervers-triple-is-the-maximum-baek-corollary-858)),
where $\mathcal{Q}(x_G) = \mathcal{A}_{\pi/2}(\mathcal{C}(G)) = |G|$
([Theorem 10.26](10-gerver.md#theorem-1026-the-upper-bound-is-attained-baek-theorem-846)). Its
concavity comes from three terms $\mathcal{S}_K$, $\mathcal{R}_B$ and $\mathcal{L}_D$ made of Mamikon
areas, which are convex
([Lemma 9.22](09-optimality.md#lemma-922-the-mamikon-terms-are-convex-baek-lemma-833)). The first is
a sum of four Mamikon areas
([Definition 9.21](09-optimality.md#definition-921-the-mamikon-terms-baek-definitions-832834), with
$\varphi^\mathrm{R} = \varphi$ and $\varphi^\mathrm{L} = \pi/2 - \varphi$):

```math
\mathcal{S}_K = \mathcal{M}_K(0, \varphi; \mathbf{l}^{\pi/2}) + \mathcal{M}_K(\varphi, \pi/2 - \varphi; \mathbf{y}) + \mathcal{M}_K(\pi/2 - \varphi, \pi/2; \mathbf{l}^{\pi - \varphi}) + \mathcal{M}_K(\pi/2, \pi; \mathbf{l}^{\pi}) ,
```

where $\mathbf{l}^T(t) = l_K(t) \cap l_K(T)$ follows the supporting line at $t$ to its intersection
with that at the *target* $T$
([Definition 9.19](09-optimality.md#definition-919-tangent-line-parametrization-baek-definition-831)),
and $\mathbf{y} = \mathbf{y}_K$ is the outer corner. By Mamikon's theorem
([Theorem 8.21](08-convex-curves.md#theorem-821-mamikons-theorem-baek-theorem-741)), for
$a < b < a + \pi$ and a continuous curve $\mathbf{z}$ of bounded variation with
$\mathbf{z}(t) \in l_K(t)$,

```math
\mathcal{M}_K(a, b; \mathbf{z}) = \frac12 \int_a^b \alpha(t)^2\,\mathrm{d}t , \qquad \alpha(t) = \bigl(\mathbf{z}(t) - v_K^+(t)\bigr) \cdot v_t ,
```

where $\alpha$ is the *tangent displacement*.

### Lemma 12.14 (equality in Baek's upper bound)

Let $K \in \mathcal{K}^\mathrm{i}$ with $\mathcal{A}_{\pi/2}(K) = |G|$. Then
$\mathcal{Q}(x_K) = \mathcal{Q}(x_G)$, and for every $c \in [0, 1]$ the combination
$(1 - c)x_G + c\,x_K$ attains equality in each of the three convexity inequalities, of
$\mathcal{S}$, $\mathcal{R}$ and $\mathcal{L}$.

*Proof.* $|G| = \mathcal{A}_{\pi/2}(K) \le \mathcal{Q}(x_K) \le \mathcal{Q}(x_G) = |G|$. A concave
functional is constant on the segment between two maximizers, so
$\mathcal{Q}((1 - c)x_G + c\,x_K) = (1 - c)\mathcal{Q}(x_G) + c\,\mathcal{Q}(x_K)$. On $\mathcal{L}$,
$\mathcal{Q} = (\mathcal{P} + \mathcal{S}) - \mathcal{S} - \mathcal{R} - \mathcal{L}$ with the first
term linear and the other three convex (proof of Theorem 9.27). So equality in the concavity of
$\mathcal{Q}$ forces equality in each of the three. $\square$

*Lean: [`ki_maximizer_equality_conditions`](../../MovingSofaUniqueness/Rigidity.lean#L624), [`ki_upperQL_eq_gerver_of_sofaArea_eq`](../../MovingSofaUniqueness/Rigidity.lean#L609),
[`MovingSofaOptimality.ConvexDomain.eq_on_segment_of_isMax`](../../MovingSofaUniqueness/Rigidity.lean#L149), [`mamikonSegmentEquality_iff`](../../MovingSofaUniqueness/Rigidity.lean#L527),
[`MamikonSegmentEquality`](../../MovingSofaUniqueness/Rigidity.lean#L517), [`MovingSofaUniqueness.kiExtensionTriple`](../../MovingSofaUniqueness/Mamikon.lean#L191).*

### Lemma 12.15 (equality in one Mamikon term)

Let $K_0, K_1$ be right-angle caps with condition (1), let $[a, b]$ lie in $[0, \pi/2]$ or in
$[\pi/2, \pi]$, let $c \in (0, 1)$, $K_c = (1 - c)K_0 + cK_1$, and $f = h_{K_1} - h_{K_0}$.

1. If $a < b \le T < a + \pi$ and
   $\mathcal{M}_{K_c}(a, b; \mathbf{l}^T) = (1 - c)\mathcal{M}_{K_0}(a, b; \mathbf{l}^T) + c\,\mathcal{M}_{K_1}(a, b; \mathbf{l}^T)$, then $f(t) = p\cos t + q\sin t$ on $[a, b]$ and at
   $t = T$, for some $p, q$.
2. If the same equality holds for the outer corner $\mathbf{y}$, then
   $f(t) = f(b) - \int_t^b f(u + \pi/2)\,\mathrm{d}u$ on $[a, b]$.

*Proof.* Equality in the convexity of $\frac12 \int \alpha^2$ forces equal tangent displacements,
and equal displacements are a linear differential equation for $f$.

Both curves are convex-linear in the cap
([Theorem 9.20](09-optimality.md#theorem-920-tangent-line-parametrization-baek-theorems-831-832) (2)
for $\mathbf{l}^T$; the outer corner is linear in the support function), so the displacements are
too, $\alpha_c = (1 - c)\alpha_0 + c\,\alpha_1$. By Mamikon's theorem the convexity gap is

```math
(1 - c)\,\mathcal{M}_{K_0} + c\,\mathcal{M}_{K_1} - \mathcal{M}_{K_c} = \frac{c(1 - c)}2 \int_a^b (\alpha_0 - \alpha_1)^2 .
```

Equality makes $\alpha_0 = \alpha_1$ almost everywhere, hence everywhere on $(a, b)$, where both are
continuous under condition (1). Under condition (1), $h_K$ is differentiable on $(a, b)$ with
$h_K'(t) = v_K^+(t) \cdot v_t$. For part 1, take $\mathbf{z} = \mathbf{l}^T$:
$\alpha(t) = \frac{h(T) - h(t)\cos(T - t)}{\sin(T - t)} - h'(t)$, so $\alpha_0 = \alpha_1$ is the
*tangent equation* $\sin(T - t)f'(t) + \cos(T - t)f(t) = f(T)$. The quotient
$(f(t) - f(T)\cos(T - t))/\sin(T - t)$ then has derivative zero, so
$f(t) = f(T)\cos(T - t) + C\sin(T - t)$ on $(a, b)$, and by continuity on $[a, b]$. For part 2,
take $\mathbf{z} = \mathbf{y}$: $\alpha(t) = h(t + \pi/2) - h'(t)$, so $f'(t) = f(t + \pi/2)$, which
integrates to the stated form. $\square$

*Lean: [`MovingSofaUniqueness.halfSquareIntegral_combo_gap`](../../MovingSofaUniqueness/Mamikon.lean#L56), [`halfSquareIntegral_combo_eq_iff`](../../MovingSofaUniqueness/Mamikon.lean#L92),
[`displacement_eqOn_of_mamikon_eq`](../../MovingSofaUniqueness/Rigidity.lean#L221), [`tangentKernel_of_mamikon_eq`](../../MovingSofaUniqueness/Rigidity.lean#L397), [`middleKernel_of_mamikon_eq`](../../MovingSofaUniqueness/Rigidity.lean#L449),
[`tangentKernel_of_equation`](../../MovingSofaUniqueness/Rigidity.lean#L308), [`integrated_middle_equation`](../../MovingSofaUniqueness/Rigidity.lean#L364).*

### Definition 12.16 (cap kernel)

Let $\varphi \in (0, \pi/4)$. A function $f$ is a *cap kernel* if $f(\pi/2) = 0$, if on each of
$[0, \varphi]$, $[\pi/2 - \varphi, \pi/2]$ and $[\pi/2, \pi]$ it has the form $p\cos t + q\sin t$,
with the same constants also at the targets $\pi/2$, $\pi - \varphi$ and $\pi$ respectively, and if

```math
f(t) = f(\pi/2 - \varphi) - \int_t^{\pi/2 - \varphi} f(u + \pi/2)\,\mathrm{d}u \qquad \text{for } t \in [\varphi, \pi/2 - \varphi] .
```

*Lean: [`CapKernel`](../../MovingSofaUniqueness/Rigidity.lean#L44), [`TangentKernel`](../../MovingSofaUniqueness/Rigidity.lean#L38).*

### Lemma 12.17 (the cap kernel is a horizontal translation)

1. If $K_0, K_1 \in \mathcal{K}^\mathrm{i}$ and the convexity inequality of $\mathcal{S}$ is an
   equality at some $c \in (0, 1)$, then $h_{K_1} - h_{K_0}$ is a cap kernel.
2. Every cap kernel satisfies $f(t) = a\cos t$ on $[0, \pi]$, with $a = -f(\pi)$.

*Proof.* (1) Each of the four Mamikon areas of $\mathcal{S}$ is convex (proof of Lemma 9.22), so equality
for their sum forces equality for each, and Lemma 12.15 turns the four equalities into the four
parts of Definition 12.16. Also $f(\pi/2) = 0$, since both caps have support $1$ at $\pi/2$.

(2) Solve in reverse order, as in note 20. On $[\pi/2, \pi]$, $f = p\cos t + q\sin t$ with
$f(\pi/2) = q = 0$, and the value at $\pi$ gives $p = a$. On $[\pi/2 - \varphi, \pi/2]$,
$f = p'\cos t + q'\sin t$ with $q' = 0$ from $f(\pi/2) = 0$, and at the target $\pi - \varphi \in [\pi/2, \pi]$, $p'\cos(\pi - \varphi) = a\cos(\pi - \varphi)$, so $p' = a$. On
$[\varphi, \pi/2 - \varphi]$, the integrand is $f(u + \pi/2) = a\cos(u + \pi/2) = -a\sin u$, so

```math
f(t) = a\cos(\pi/2 - \varphi) + a\int_t^{\pi/2 - \varphi} \sin u\,\mathrm{d}u = a\cos t .
```

On $[0, \varphi]$, $f = p''\cos t + q''\sin t$ with $q'' = f(\pi/2) = 0$ at the target, and the
value at $\varphi$ gives $p'' = a$. $\square$

*Lean: [`capKernel_of_mamikonS_eq`](../../MovingSofaUniqueness/Rigidity.lean#L655), [`capKernel_of_triple_midpoint`](../../MovingSofaUniqueness/Rigidity.lean#L712),
[`CapKernel.eq_horizontal_translation`](../../MovingSofaUniqueness/Rigidity.lean#L66), [`CapKernel.upper_left`](../../MovingSofaUniqueness/Rigidity.lean#L53).*

### Lemma 12.18 (caps with translated supports; note 20, (21))

Let $K$ and $C$ be right-angle caps with $h_K(t) - h_C(t) = a\cos t$ for $t \in [0, \pi]$. Then
$K = C + (a, 0)$ and

```math
K \setminus \mathcal{N}(K) = \bigl(C \setminus \mathcal{N}(C)\bigr) + (a, 0) .
```

*Proof.* A right-angle cap is the set of points $p$ with $p_y \ge 0$ and $p \cdot u_t \le h(t)$ for
$t \in [0, \pi]$, and its niche is the set of points with $p_y \ge 0$ in some inner quadrant
$\lbrace p \cdot u_t < h(t) - 1,\ p \cdot v_t < h(t + \pi/2) - 1 \rbrace$, $t \in (0, \pi/2)$.
Since $(p - (a, 0)) \cdot u_t = p \cdot u_t - a\cos t$ and
$(p - (a, 0)) \cdot v_t = p \cdot v_t - a\cos(t + \pi/2)$, both descriptions for $K$ at $p$ are those
for $C$ at $p - (a, 0)$. $\square$

*Lean: [`sofa_eq_translate_of_upper_support`](../../MovingSofaUniqueness/Rigid.lean#L334), [`cap_eq_translate_of_upper_support`](../../MovingSofaUniqueness/Rigid.lean#L353), [`mem_right_cap_iff`](../../MovingSofaUniqueness/Rigid.lean#L244), [`mem_right_niche_iff`](../../MovingSofaUniqueness/Rigid.lean#L266),
[`mem_cap_sub_horizontal_iff`](../../MovingSofaUniqueness/Rigid.lean#L287), [`mem_niche_sub_horizontal_iff`](../../MovingSofaUniqueness/Rigid.lean#L306).*

Note 20 obtains the lower supports from the bottom segment of the cap; the formal proof describes
the cap by its upper supports and the floor, which amounts to the same.

### Proposition 12.19 (Gerver's cap up to translation; note 20, Proposition 5)

Let $K \in \mathcal{K}^\mathrm{i}$ with $\mathcal{A}_{\pi/2}(K) = |G|$. Then
$K \setminus \mathcal{N}(K) = G + (a, 0)$ for some $a \in \mathbb{R}$.

*Proof.* Gerver's cap $\mathcal{C}(G)$ lies in $\mathcal{K}^\mathrm{i}$
([Theorem 9.2](09-optimality.md#theorem-92-these-caps-form-a-convex-domain-baek-theorem-811) (3)).
Lemma 12.14 at $c = \frac12$ gives equality in the convexity inequality of $\mathcal{S}$ between
$\mathcal{C}(G)$ and $K$, so by Lemma 12.17,
$h_K(t) - h_{\mathcal{C}(G)}(t) = a\cos t$ on $[0, \pi]$, with
$a = h_{\mathcal{C}(G)}(\pi) - h_K(\pi)$. By Lemma 12.18,
$K \setminus \mathcal{N}(K) = (\mathcal{C}(G) \setminus \mathcal{N}(\mathcal{C}(G))) + (a, 0)$, and
$\mathcal{C}(G) \setminus \mathcal{N}(\mathcal{C}(G)) = G$ because $G$ is a monotone sofa
(Theorem 3.13; Figure 12.5). $\square$

*Lean: [`MovingSofaUniqueness.ki_sofa_eq_gerver_translate`](../../MovingSofaUniqueness/Main.lean#L122), [`capKernel_of_triple_midpoint`](../../MovingSofaUniqueness/Rigidity.lean#L712),
[`theorem6_1_2`](../../MovingSofaOptimality/Gerver/Properties.lean#L181), [`theorem2_4_3`](../../MovingSofaOptimality/Monotone/CapNiche.lean#L230).*

![Top: Gerver's cap filled blue and its horizontal translate drawn dashed in green, overlapping; at one normal t each has a dashed supporting line, the two lines parallel, and a double arrow between them is labelled a cos t. Bottom: the graph of f(t) = a cos t from 0 to π, positive up to π/2 and negative after](figures/12-uniqueness/translation.svg)

*Figure 12.5.* Proposition 12.19. Top: Gerver's cap $\mathcal{C}(G)$ and its translate by $(a, 0)$;
their supporting lines at a normal $t$ lie $a\cos t$ apart, so
$h_{\mathcal{C}(G) + (a, 0)} - h_{\mathcal{C}(G)} = a\cos t$. Bottom: this difference on
$[0, \pi]$, the only solution of the four kernel equations (Lemma 12.17).

*Remark.* Note 20 also states a stability form, $d_\mathrm{H}(K, \mathcal{C}(G) + (a, 0))^2 \le 6(|G| - \mathcal{A}_{\pi/2}(K))$ for $K \in \mathcal{K}^\mathrm{i}$ (note 17). The uniqueness
theorem does not need it, and it is not formalized.

## 12.5 Gerver's sofa is the closure of its interior

Gerver's sofa is its cap $K_G$ minus its niche, and the niche is the region $\Gamma_<$ of the points
$q$ with $q_y \ge 0$ that lie strictly below a point of a curve $\Gamma$ with the same abscissa
([Theorems 10.11](10-gerver.md#theorem-1011-the-structure-of-gervers-sofa-baek-theorem-841-1-3-4)
and [10.17](10-gerver.md#theorem-1017-the-niche-is-the-region-under-gamma)). The curve $\Gamma$
consists of the contact curve $\mathbf{D} = \mathbf{x} - (\mathbf{x}' \cdot v_t)u_t$ on
$[0, \theta]$, the rotation path $\mathbf{x}$ on $[\varphi, \pi/2 - \varphi]$ and the contact curve
$\mathbf{B} = \mathbf{x} + (\mathbf{x}' \cdot u_t)v_t$ on $[\pi/2 - \theta, \pi/2]$
([Definition 10.14](10-gerver.md#definition-1014-the-curve-gamma)). A point of $G$ on $\Gamma$ is a
limit of the points just above it, provided the curve does not reach the top of the cap.

### Lemma 12.20 (the rotation path stays below height one)

Gerver's rotation path satisfies $\mathbf{x}(t)_y < 1$ for every $t \in [0, \pi/2]$.

*Proof.* Phase by phase, as for the bound $\mathbf{x}(t)_y \le 1$ in the proof of
[Lemma 10.10](10-gerver.md#lemma-1010-the-cap-k_g) (3): the explicit formulas of the five phases and
the enclosures of Romik's parameters bound $\mathbf{x}(t)_y$ by $0.95$, $0.99240672$, $0.88962658$,
$0.99240672$ and $0.9500001$. $\square$

Numerically, the path is highest at $t = \pi/4$, at height $0.6643$.

*Lean: [`MovingSofaOptimality.GerverParams.path_snd_lt_one`](../../MovingSofaUniqueness/RegularClosed.lean#L37), [`gs_path_snd_le_one`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L255).*

### Lemma 12.21 (removing the region under an envelope)

Let $K$ be a closed set that is the closure of its interior and contains the rectangle
$[a, b] \times [0, 1]$. Let $\Gamma$ be a compact set of points with abscissa
in $[a, b]$ and height in $[0, 1)$, and let $\Gamma_<$ be the set of points $q$ with $q_y \ge 0$
strictly below a point of $\Gamma$ with the same abscissa. If $K \setminus \Gamma_<$ is closed, it
is the closure of its interior.

*Proof.* Let $\bar\Gamma_\le$ be the set of points with $q_y \ge 0$ on or below a point of $\Gamma$;
it is compact and contains $\Gamma_<$. A point of $K \setminus \bar\Gamma_\le$ is a limit of
interior points of $K$ outside the closed set $\bar\Gamma_\le$, which are interior points of
$K \setminus \Gamma_<$. A point $p$ of $K \setminus \Gamma_<$ in $\bar\Gamma_\le$ is the highest
point of $\Gamma$ on its vertical line, so $p_x \in [a, b]$ and $p_y < 1$. The points
$(p_x, p_y + s)$, $0 < s \le 1 - p_y$, lie in the rectangle and outside $\bar\Gamma_\le$, and tend
to $p$. $\square$

*Lean: [`regularClosed_cap_sdiff_envelope`](../../MovingSofaUniqueness/RegularClosed.lean#L277), [`isCompact_envUnder`](../../MovingSofaUniqueness/RegularClosed.lean#L231), [`outside_closed_envelope_subset`](../../MovingSofaUniqueness/RegularClosed.lean#L265).*

### Proposition 12.22 (regular closedness; note 20, Proposition 6)

Gerver's sofa is the closure of its interior: $\overline{G^\circ} = G$.

*Proof.* Lemma 12.21 applies to the cap $K_G$ and the curve $\Gamma$ above, for which
$G = K_G \setminus \Gamma_<$; it remains to check its hypotheses. The abscissa is monotone along each
of the three pieces of $\Gamma$ (proof of
[Theorem 10.19](10-gerver.md#theorem-1019-the-niche-baek-theorem-841-2)), and the points
$\mathbf{D}(0)$, $\mathbf{x}(\pi/2 - \varphi)$, $\mathbf{x}(\varphi)$, $\mathbf{B}(\pi/2)$ have
increasing abscissas. So every point of $\Gamma$ has abscissa in $[a, b]$, where
$a = \mathbf{D}(0)_x$ and $b = \mathbf{B}(\pi/2)_x$ (Figure 12.6). Its height lies in $[0, 1)$, by
Lemma 12.20 and because the heights of $\mathbf{D}$ and $\mathbf{B}$ are monotone between the floor
and their junctions with the path. The points $(a, 1) = \mathbf{D}(0) + v_0$ and
$(b, 1) = \mathbf{B}(\pi/2) + u_{\pi/2}$ are the contact points $\mathbf{C}(0)$ and
$\mathbf{A}(\pi/2)$ of the cap, so the segment between them lies in $K_G$. So does the rectangle
$[a, b] \times [0, 1]$ under it, since a right-angle cap contains the vertical segment from each of
its points down to the floor. In particular $K_G$ is a convex set with nonempty interior, hence the
closure of its interior. Finally $G$ is closed, being a moving sofa. $\square$

*Lean: [`gerver_regularClosed`](../../MovingSofaUniqueness/RegularClosed.lean#L369), [`envelope_bounds_of_path_height`](../../MovingSofaUniqueness/RegularClosed.lean#L129), [`envelope_endpoint_order`](../../MovingSofaUniqueness/RegularClosed.lean#L96),
[`envelope_isCompact`](../../MovingSofaUniqueness/RegularClosed.lean#L114), [`theorem8_4_1_niche`](../../MovingSofaOptimality/Gerver/Properties.lean#L103).*

![Gerver's sofa filled blue, with its niche bounded above by an orange arch Γ that meets the floor at a and b; the arch is highest near 0.664, below the dashed line at height one; a dashed rectangle from a to b of height one lies in the cap, with its top corners (a, 1) and (b, 1) marked; a point p on the arch has an arrow pointing up into the sofa](figures/12-uniqueness/regular-closed.svg)

*Figure 12.6.* Proposition 12.22. The niche of $G$ is the region strictly under $\Gamma$ (orange),
which stays below height $0.665$; the dashed rectangle $[a, b] \times [0, 1]$ lies in the cap. Every
point $p$ of $\Gamma$ is the limit of the interior points just above it.

*Remark (the formal route).* Note 20 allows one point of the path at height one, which it shows to
be unique from the monotonicity of $-\alpha/\beta$. The path stays strictly below height one
(Lemma 12.20), so this case does not arise, and Lemma 12.21 and its Lean form assume heights in
$[0, 1)$.

## 12.6 Proof of Theorem 12.1

### Lemma 12.23 (recovering a set from its area)

Let $X \subseteq Y \subseteq \mathbb{R}^2$, with $X$ closed, $Y$ the closure of its interior,
$|Y| < \infty$ and $|X| = |Y|$. Then $X = Y$.

*Proof.* $|Y \setminus X| = |Y| - |X| = 0$. If an interior point $q$ of $Y$ were not in $X$, the
open set $Y^\circ \setminus X$ would contain a disk about $q$, of positive area, inside
$Y \setminus X$. So $Y^\circ \subseteq X$, and as $X$ is closed, $Y = \overline{Y^\circ} \subseteq X$.
$\square$

Both hypotheses on $Y$ are needed (Figure 12.7).

*Lean: [`eq_of_subset_of_measure_eq`](../../MovingSofaUniqueness/Rigid.lean#L57), [`eq_of_subset_of_null_sdiff`](../../MovingSofaUniqueness/Rigid.lean#L50),
[`interior_subset_of_null_sdiff`](../../MovingSofaUniqueness/Rigid.lean#L41), [`Rigid.recover`](../../MovingSofaUniqueness/Rigid.lean#L183).*

![Left: a unit square E filled blue with a segment of length one attached to its lower right corner, labelled hair. Right: Gerver's sofa filled blue with a small dashed orange circle around an interior point q, inside which the sofa is removed](figures/12-uniqueness/recovery.svg)

*Figure 12.7.* The hypotheses of Lemma 12.23. Left: the square $E$ and the closed connected set
$E \cup ([1, 2] \times \lbrace 0 \rbrace)$, which has the same area and is not the closure of its
interior; inside it, $E$ is a closed subset of full area. Right: a closed subset of $G$ that misses
an interior point $q$ misses a disk about $q$, and loses area.

### Lemma 12.24 (right-angle monotone sofas of maximum area)

Every monotone sofa $U$ of angle $\pi/2$ with $|U| = |G|$ is a horizontal translate of $G$:
$U = G + (b, 0)$ for some $b$.

*Proof.* Its cap $K = \mathcal{C}(U)$ is a right-angle cap
([Theorem 3.10](03-monotone.md#theorem-310-the-cap-of-a-moving-sofa-baek-theorem-241)) with
$\mathcal{A}_{\pi/2}(K) = |U| = |G|$
([Theorem 3.29](03-monotone.md#theorem-329-the-area-of-a-monotone-sofa-baek-theorem-2510)). By
Corollary 12.10, $K \in \mathcal{K}^\mathrm{i}$, so $K \setminus \mathcal{N}(K) = G + (b, 0)$ by
Proposition 12.19, and $U = K \setminus \mathcal{N}(K)$ by Theorem 3.13. $\square$

*Lean: [`right_angle_monotone_eq_gerver`](../../MovingSofaUniqueness/Main.lean#L248).*

### Proposition 12.25 (containment)

For every moving sofa $S$ with $|S| = |G|$ there is a rigid map $g$, a rotation about the origin
followed by a translation, with $g(S) \subseteq G$. Its rotation is by an angle
$a = \pi/2 - \omega \in [0, \pi/2 - \sec^{-1}(2.2)]$, where $\omega$ is a rotation angle of $S$.

*Proof.* As $|S| = |G| \ge 11/5$, Theorem 5.1 gives a rotation angle
$\omega \in [\sec^{-1}(2.2), \pi/2]$ for $S$. By Lemma 11.3 there are a vector $v_0$
and a monotone sofa $T$ of angle $\omega$ with $S + v_0 \subseteq T$ and $|T| = |G|$. By
Proposition 12.13, $R_a T$ moves with rotation angle $\pi/2$, where $a = \pi/2 - \omega$, and
$|R_a T| = |G|$. By Lemma 11.3 again, now at the angle $\pi/2$, there are $v_1$ and a monotone sofa
$U$ of angle $\pi/2$ with $R_a T + v_1 \subseteq U$ and $|U| = |G|$, and by Lemma 12.24,
$U = G + (b, 0)$. So

```math
R_a(S + v_0) + v_1 \subseteq R_a T + v_1 \subseteq U = G + (b, 0) ,
```

and $g(p) = R_a p + R_a v_0 + v_1 - (b, 0)$ maps $S$ into $G$. $\square$

*Lean: [`maximizer_contained_in_gerver`](../../MovingSofaUniqueness/Main.lean#L262), [`maximal_envelope`](../../MovingSofaUniqueness/Main.lean#L199), [`Rigid.trans`](../../MovingSofaUniqueness/Rigid.lean#L104).*

*Proof of Theorem 12.1.* Let $S$ be a moving sofa with $|S| = |G|$, and $g$ the rigid map of
Proposition 12.25, with $g(S) \subseteq G$. The set $g(S)$ is closed, since $S$ is closed by the
definition of a moving sofa and $g$ is a homeomorphism; $|g(S)| = |S| = |G|$, since $g$ preserves
area; $|G|$ is finite; and $G$ is the closure of its interior (Proposition 12.22). By Lemma 12.23,
$g(S) = G$, and writing $g(p) = R_\theta p + v$ gives the theorem. $\square$

*Lean: [`image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L301), [`Rigid.volume_image`](../../MovingSofaUniqueness/Rigid.lean#L171), [`Rigid.isClosed_image`](../../MovingSofaUniqueness/Rigid.lean#L164),
[`gerver_regularClosed`](../../MovingSofaUniqueness/RegularClosed.lean#L369), [`Baek.gerver_sofa_unique`](../../Challenge.lean#L688).*

Both Challenges state the theorem as [`Baek.gerver_sofa_unique`](../../Challenge.lean#L688), with the definitions of Baek's paper
in Mathlib's vocabulary. Version 5 of the Palomar entry derives it through the coercive certificate ([the coercive route](../../docs/coercive.md));
for versions 1 to 4, [`baek/Solution.lean`](../Solution.lean) derives it from [`image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L301) through the
identification of these definitions with the library's ([`Baek.isMovingSofa_iff_lib`](../Solution.lean#L36),
[`Baek.gerverSofa_eq_lib`](../Solution.lean#L59)). [Chapter 13](13-bridge.md) carries the theorem over to formal-conjectures'
statement [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../../Challenge.lean#L765).

## 12.7 The maximizing right-angle caps, and the rotation

The equality case describes all maximizing right-angle caps (Theorem 12.26). The proof also shows
that the rotation in Theorem 12.1 can be taken to be the identity: the rigid map of
Proposition 12.25 turns by $\pi/2 - \omega \in [0, \pi/2 - \sec^{-1}(2.2)]$, and Gerver's sofa is
wider than one in every direction other than the vertical (Lemma 12.27), so the map turns by zero
(Theorem 12.28).

### Theorem 12.26 (maximizing right-angle caps)

A right-angle cap $K$ has $\mathcal{A}_{\pi/2}(K) = |G|$ if and only if $K = K_G + (s, 0)$ for some
$s \in \mathbb{R}$, where $K_G = \mathcal{C}(G)$ is Gerver's cap. In this case
$K \setminus \mathcal{N}(K) = G + (s, 0)$. So the caps that maximize $\mathcal{A}_{\pi/2}$ are
exactly the horizontal translates of $K_G$, and every monotone sofa of angle $\pi/2$ with the area
of $G$ is a horizontal translate of $G$ (Lemma 12.24).

*Proof.* Let $\mathcal{A}_{\pi/2}(K) = |G|$. By Corollary 12.10, $K \in \mathcal{K}^\mathrm{i}$, and
as in the proof of Proposition 12.19, $h_K(t) - h_{K_G}(t) = s\cos t$ on $[0, \pi]$ for some $s$.
Lemma 12.18 with $C = K_G$ gives $K = K_G + (s, 0)$ and
$K \setminus \mathcal{N}(K) = (K_G \setminus \mathcal{N}(K_G)) + (s, 0) = G + (s, 0)$. Conversely,
the translate $C + (s, 0)$ of a right-angle cap $C$ has the support function $h_C(t) + s\cos t$. It
keeps the support values at the normals $\pi/2$ and $3\pi/2$, and the translate of a half-plane is a
half-plane with the same normal, so $C + (s, 0)$ is a right-angle cap. By the proof of Lemma 12.18,
its niche is $\mathcal{N}(C) + (s, 0)$, so $\mathcal{A}_{\pi/2}(C + (s, 0)) = \mathcal{A}_{\pi/2}(C)$.
Finally $\mathcal{A}_{\pi/2}(K_G) = |G|$
([Theorem 3.29](03-monotone.md#theorem-329-the-area-of-a-monotone-sofa-baek-theorem-2510)), which
is the maximum of $\mathcal{A}_{\pi/2}$ (Lemma 11.2). $\square$

*Lean: [`sofaArea_eq_gerver_iff`](../../MovingSofaUniqueness/Main.lean#L167), [`cap_eq_gerver_translate`](../../MovingSofaUniqueness/Main.lean#L153), [`translate_gerver_cap_sdiff_niche`](../../MovingSofaUniqueness/Main.lean#L138),
[`isMaxCap_iff_translate_gerver_cap`](../../MovingSofaUniqueness/Main.lean#L181), [`ki_supp_sub_gerver_eq`](../../MovingSofaUniqueness/Main.lean#L108), [`isCap_translate_horizontal`](../../MovingSofaUniqueness/Rigid.lean#L372),
[`niche_translate_horizontal`](../../MovingSofaUniqueness/Rigid.lean#L390), [`sofaArea_translate_horizontal`](../../MovingSofaUniqueness/Rigid.lean#L398), [`right_angle_monotone_eq_gerver`](../../MovingSofaUniqueness/Main.lean#L248).*

### Lemma 12.27 (the width of Gerver's sofa)

For every $r \in [0, \pi]$ with $r \ne \pi/2$ there are $p, q \in G$ with $(p - q) \cdot u_r > 1$:
the width of $G$ exceeds one in every direction other than the vertical.

*Proof.* Let $\Gamma$, $a = \mathbf{D}(0)_x$ and $b = \mathbf{B}(\pi/2)_x$ be as in §12.5, and
$x_- = \mathbf{C}(\pi/2)_x = \mathbf{x}(\pi/2)_x - 1$. The points $(a, 1) = \mathbf{C}(0)$,
$(b, 1) = \mathbf{A}(\pi/2)$, $(x_-, 0) = \mathbf{C}(\pi/2)$ and $(1, 0) = \mathbf{A}(0)$ lie in
$K_G$ ([Lemma 10.10](10-gerver.md#lemma-1010-the-cap-k_g)). A point of the niche lies strictly
below a point $\gamma$ of $\Gamma$ with the same abscissa, so $\gamma_y > 0$. The abscissa is
strictly monotone along each of the three pieces of $\Gamma$, and the only points of $\Gamma$ with
abscissa $a$ or $b$ are $\mathbf{D}(0)$ and $\mathbf{B}(\pi/2)$, of height zero. So the points of the
niche have abscissas in $(a, b)$. Since $(a, 1)$ and $(b, 1)$ lie in $K_G$,
$x_- = -h_{K_G}(\pi) \le a$ and $b \le h_{K_G}(0) = 1$, so none of the four points lies in the niche,
and all four lie in $G$. The abscissas of $\mathbf{D}(0)$, $\mathbf{x}(\pi/2 - \varphi)$,
$\mathbf{x}(\varphi)$ and $\mathbf{B}(\pi/2)$ increase (§12.5), and $\mathbf{x}_x$ decreases from $0$
(Lemma 10.10 (3)), so $a < \mathbf{x}(\pi/2 - \varphi)_x < \mathbf{x}(\varphi)_x \le 0$ and
$b > \mathbf{x}(\varphi)_x > \mathbf{x}(\pi/2 - \varphi)_x \ge \mathbf{x}(\pi/2)_x = x_- + 1$. For
$r < \pi/2$,

```math
\bigl((b, 1) - (x_-, 0)\bigr) \cdot u_r = (b - x_-)\cos r + \sin r > \cos r + \sin r \ge 1 ,
```

and for $r > \pi/2$,

```math
\bigl((a, 1) - (1, 0)\bigr) \cdot u_r = (1 - a)\lvert\cos r\rvert + \sin r > \lvert\cos r\rvert + \sin r \ge 1 .
```

$\square$

*Lean: [`gerver_width_gt_one`](../../MovingSofaUniqueness/RegularClosed.lean#L475), [`gerver_corner_points`](../../MovingSofaUniqueness/RegularClosed.lean#L436), [`envUnderStrict_fst_mem_Ioo`](../../MovingSofaUniqueness/RegularClosed.lean#L169),
[`gerver_niche_eq_envUnderStrict`](../../MovingSofaUniqueness/RegularClosed.lean#L341), [`gerver_contactC_zero`](../../MovingSofaUniqueness/RegularClosed.lean#L352), [`gerver_contactA_pi_div_two`](../../MovingSofaUniqueness/RegularClosed.lean#L361).*

### Theorem 12.28 (no rotation is needed)

Every moving sofa $S$ with $|S| = |G|$ is a translate of $G$: $S + v = G$ for some vector $v$. In
particular $S$ moves with rotation angle $\pi/2$.

*Proof.* By Proposition 12.25 and the proof of Theorem 12.1, a rigid map $g(p) = R_\psi p + w$ with
$\psi \in [0, \pi/2 - \sec^{-1}(2.2)]$ maps $S$ onto $G$. The motion of a moving sofa starts with a
translate of it in $H_L$, so $(p - q) \cdot u_{\pi/2} \le 1$ for all $p, q \in S$. Since
$(g(p) - g(q)) \cdot u_{\psi + \pi/2} = R_\psi(p - q) \cdot R_\psi u_{\pi/2} = (p - q) \cdot u_{\pi/2}$,
the width of $G$ in the direction $u_{\psi + \pi/2}$ is at most one. If $\psi > 0$, then
$\psi + \pi/2 \in (\pi/2, \pi)$, and this contradicts Lemma 12.27. So $\psi = 0$, and $g$ is the
translation by $w$. Gerver's sofa moves with rotation angle $\pi/2$, and so does its translate
$S$. $\square$

*Lean: [`translate_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L336), [`isMovingSofaWithAngle_pi_div_two_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L368),
[`maximizer_contained_in_gerver`](../../MovingSofaUniqueness/Main.lean#L262), [`snd_sub_le_one_of_isMovingSofa`](../../MovingSofaUniqueness/Rigid.lean#L192),
[`dot_sub_vvec_le_one_of_mem_image`](../../MovingSofaUniqueness/Rigid.lean#L207), [`Rigid.eq_translate_of_angle_eq_zero`](../../MovingSofaUniqueness/Rigid.lean#L156).*

### Remark 12.29 (rotated copies of Gerver's sofa)

A rotated copy $R_\theta G$ fits into the horizontal side $H_L$, after a translation, only if
$\theta$ is a multiple of $\pi$. Its height is the width of $G$ in the direction
$R_{-\theta} u_{\pi/2} = (\sin\theta, \cos\theta)$, and by Lemma 12.27, applied to
$\pm(\sin\theta, \cos\theta)$, this width is at most one only if $\sin\theta = 0$. A moving sofa starts
in $H_L$, so $R_\theta G$ is a moving sofa only if $\sin\theta = 0$; for instance $R_{\pi/2} G$ is
not one. So not every rigid image of $G$ is a moving sofa, and the moving sofas of maximum area are
the moving sofas that a rigid map takes onto $G$ (Theorem 12.1), all of them translates of $G$
(Theorem 12.28).

*Lean: [`sin_eq_zero_of_rot_gerver_mem_horizSide`](../../MovingSofaUniqueness/Main.lean#L382), [`sin_eq_zero_of_isMovingSofa_rot_gerver`](../../MovingSofaUniqueness/Main.lean#L396),
[`not_isMovingSofa_rot_pi_div_two_gerver`](../../MovingSofaUniqueness/Main.lean#L405), [`fst_eq_zero_of_gerver_width_le_one`](../../MovingSofaUniqueness/RegularClosed.lean#L505),
[`isMaximal_iff_image_eq_gerver`](../../MovingSofaUniqueness/Main.lean#L316).*
