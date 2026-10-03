# Appendix B. Rigorous numerics for Gerver's sofa

[Contents](README.md) · [← Appendix A](appendix-a.md)

Three facts about Gerver's sofa hold for numerical reasons: Romik's equations have exactly one
solution in the box $\varphi \in [0.039, 0.04]$, $\theta \in [0.68, 0.69]$
([Theorem 10.8](10-gerver.md#theorem-108-gervers-sofa-is-well-defined-romik-section-4)); its parameters lie in narrow intervals around Romik's values; and
the six curve areas whose signed sum is $\lvert G \rvert$ lie in intervals that add up to
$[2.2192, 2.2199]$ ([Theorem 10.21](10-gerver.md#theorem-1021-the-area-of-gervers-sofa)). This appendix explains how Lean proves them.
Every numerical step derives an enclosure $x \in [L, U]$ from enclosures of the operands by one of a
few interval lemmas (§B.1). The side condition of each step is an inequality between decimal
numbers, which the tactic `norm_num` proves, and Lean's kernel checks the proof term. No
`native_decide`, no floating-point arithmetic and no external oracle is used.

The interval steps fill two generated files. [`Num.lean`](../../MovingSofaOptimality/External/Romik/Num.lean)
encloses Romik's reduced system and its derivatives (§B.2), and
[`AreaBounds.lean`](../../MovingSofaOptimality/Gerver/AreaBounds.lean) the six curve areas (§B.3).
Python scripts choose the endpoints and write the files (§B.4); since Lean checks every step, the
scripts need not be trusted. The other numerical facts about Gerver's sofa, the signs and
one-variable inequalities of Lemmas [10.6](10-gerver.md#lemma-106-signs-and-junctions) and
[10.16](10-gerver.md#lemma-1016-the-one-variable-facts), need little precision. They are proved by
hand: `linarith` and `nlinarith` combine the enclosures of the parameters with Taylor polynomials of
low degree ([`Frame.lean`](../../MovingSofaOptimality/Gerver/Frame.lean),
[`NicheBounds.lean`](../../MovingSofaOptimality/Gerver/NicheBounds.lean)).

## B.1 Interval arithmetic

### Lemma B.1 (interval steps)

Let $x \in [a, b]$ and $y \in [c, d]$, and let $L$, $U$ be real numbers.

1. If $L \le a + c$ and $b + d \le U$, then $x + y \in [L, U]$.
2. If $L \le a - d$ and $b - c \le U$, then $x - y \in [L, U]$; if $L \le -b$ and $-a \le U$, then
   $-x \in [L, U]$.
3. If $L \le \min(ac, ad, bc, bd)$ and $\max(ac, ad, bc, bd) \le U$, then $xy \in [L, U]$. When
   $a, c \ge 0$ it suffices that $L \le ac$ and $bd \le U$, and similarly when each interval has a
   known sign.
4. If $k > 0$, $L \le a/k$ and $b/k \le U$, then $x/k \in [L, U]$; if $c > 0$, $a \ge 0$,
   $L \le a/d$ and $b/c \le U$, then $x/y \in [L, U]$.
5. If $L \le a$ and $b \le U$, then $x \in [L, U]$.

*Lean: [`MovingSofaOptimality/Basic/Interval.lean`](../../MovingSofaOptimality/Basic/Interval.lean), which both generators use: [`iv_add`](../../MovingSofaOptimality/Basic/Interval.lean#L39), [`iv_sub`](../../MovingSofaOptimality/Basic/Interval.lean#L43),
[`iv_neg`](../../MovingSofaOptimality/Basic/Interval.lean#L47), [`iv_mul`](../../MovingSofaOptimality/Basic/Interval.lean#L102), [`iv_mul_nonneg`](../../MovingSofaOptimality/Basic/Interval.lean#L69), [`iv_mul_nonneg_nonpos`](../../MovingSofaOptimality/Basic/Interval.lean#L76), [`iv_mul_nonpos_nonneg`](../../MovingSofaOptimality/Basic/Interval.lean#L85), [`iv_mul_nonpos`](../../MovingSofaOptimality/Basic/Interval.lean#L92),
[`iv_div_const`](../../MovingSofaOptimality/Basic/Interval.lean#L51), [`iv_div`](../../MovingSofaOptimality/Basic/Interval.lean#L58), [`iv_mono`](../../MovingSofaOptimality/Basic/Interval.lean#L36).*

*Proof.* Sums, differences and quotients by a positive constant are monotone in each operand. The
product $xy$ is affine in $x$ for fixed $y$ and in $y$ for fixed $x$, so it lies between the least
and the largest of the four corner products; the signs of the intervals tell which corners these
are. The quotient $x/y$ with $x \ge 0$ and $y \ge c > 0$ increases with $x$ and decreases with $y$.
$\square$

A generated proof is a chain of such steps, one per node of the expression tree of the quantity
enclosed. The step

```lean
have h4 := iv_mul_nonneg (L := (0.1029339014 : ℝ)) (U := (0.106011725 : ℝ)) h3 hs (by norm_num)
```

encloses the product of the quantities that `h3` and `hs` enclose, $2 + \theta - \varphi \in [2.64, 2.651]$
and $\sin\varphi \in [0.0389901142, 0.0399893342]$. The generator chose the decimal endpoints by
rounding the exact products of the endpoints outward, and `norm_num` checks the side condition
$0 \le 2.64 \wedge 0 \le 0.0389901142 \wedge L \le 2.64 \cdot 0.0389901142 \wedge 2.651 \cdot 0.0399893342 \le U$.
Figure B.1 shows a whole chain.

![A tree of nine boxes. At the top, D = 2c - (2 + theta - phi) s with the interval from 1.8923884882 to 1.8970660986, step h5 by iv_sub. Below it 2c between 1.9984002132 and 2, step h1, and (2 + theta - phi) s between 0.1029339014 and 0.106011725, step h4, both by iv_mul_nonneg. Below 2c the green leaf c = cos phi between 0.9992001066 and 1; below the product the node 2 + theta - phi between 2.64 and 2.651, step h3, and the green leaf s = sin phi between 0.0389901142 and 0.0399893342; below that 2 + theta between 2.68 and 2.69, step h2 by iv_add, and the leaf phi between 0.039 and 0.04; at the bottom the leaf theta between 0.68 and 0.69](figures/appendix-b/enclosure.svg)

*Figure B.1.* The generated lemma [`rom_D_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L454), which encloses
$D = 2\cos\varphi - (2 + \theta - \varphi)\sin\varphi$ on the box (Proposition 10.7). The leaves
(green) are the hypotheses on the atoms; each internal node is one step `h1` to `h5`, with the
interval lemma that proves it. The enclosure $[1.8923885, 1.8970661]$ is wider than the true range
$[1.8924285, 1.8955063]$, because the chain treats $\varphi$, $\cos\varphi$ and $\sin\varphi$ as
independent.

The atoms of the chains are the angles and numbers that enter the formulas: $\varphi$, $\theta$,
$\cos\varphi$, $\sin\varphi$, $\cos\theta$, $\sin\theta$ and $\pi$. The cosines and sines are
enclosed by Taylor polynomials.

### Lemma B.2 (cosine, sine and $\pi$)

Let $0 \le x \le 1$, $k \ge 0$, and let $c_n(x) = \sum_{i < n} (-1)^i \frac{x^{2i}}{(2i)!}$ and
$s_n(x) = \sum_{i < n} (-1)^i \frac{x^{2i+1}}{(2i+1)!}$ be the partial sums of the Taylor series. Then

```math
c_{2k}(x) \le \cos x \le c_{2k+1}(x) , \qquad s_{2k}(x) \le \sin x \le s_{2k+1}(x) ,
```

and $3.14159265358979323846 < \pi < 3.14159265358979323847$.

*Lean: [`cos_ge_taylor`](../../MovingSofaOptimality/Basic/Interval.lean#L142), [`cos_le_taylor`](../../MovingSofaOptimality/Basic/Interval.lean#L147), [`sin_ge_taylor`](../../MovingSofaOptimality/Basic/Interval.lean#L152), [`sin_le_taylor`](../../MovingSofaOptimality/Basic/Interval.lean#L158), [`rom_pi_mem20`](../../MovingSofaOptimality/External/Romik/Calc.lean#L29), [`rom_pi_mem6`](../../MovingSofaOptimality/External/Romik/Calc.lean#L27), [`ga_pi_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L377).*

*Proof.* For $0 \le x \le 1$ the terms $x^n/n!$ decrease in $n$, so the Taylor series of $\cos x$ and
$\sin x$ are alternating series with decreasing terms, and their sums lie between any two
consecutive partial sums (Mathlib's `Antitone.alternating_series_le_tendsto` and
`Antitone.tendsto_le_alternating_series`). The bounds on $\pi$ are Mathlib's `Real.pi_gt_d20` and
`Real.pi_lt_d20`. $\square$

On an interval the monotonicity of $\cos$ and $\sin$ on $[0, 1]$ turns these into enclosures: for
$\theta \in [0.68, 0.69]$, $\cos\theta \in [c_6(0.69), c_7(0.68)]$, rounded outward to
$[0.7712460149, 0.7775727188]$ ([`rom_cos_box'`](../../MovingSofaOptimality/External/Romik/Calc.lean#L49)). Near a point $x_0$ the Lipschitz bound
$\lvert \cos x - \cos x_0 \rvert \le \lvert x - x_0 \rvert$ widens an enclosure at $x_0$ by
$\lvert x - x_0 \rvert$ ([`rom_lip_mem`](../../MovingSofaOptimality/External/Romik/Calc.lean#L96)). Every evaluation of a partial sum is a rational computation
for `norm_num`.

## B.2 Romik's equations

[`Num.lean`](../../MovingSofaOptimality/External/Romik/Num.lean) defines the functions of
[Proposition 10.7](10-gerver.md#proposition-107-reduction-to-two-equations), $K$, $D$, $N_b = D\, b_1$, $U$, $V$ and
$H = D\, U + N_b V = (H_1, H_2)$, their partial derivatives in $\varphi$ and $\theta$, the
Newton-type map $G$ and the parameters $a_1$, $b_1$, $b_2$, $c_1$, $\kappa_2$, …, $\kappa_5$ of a
solution, all as explicit expressions in the seven atoms: 48 definitions. It proves:

- 21 derivative formulas [`rom_H1_hasDerivAt_φ`](../../MovingSofaOptimality/External/Romik/Num.lean#L367), …: each applies Mathlib's rules for sums, products
  and division by constants, `Real.hasDerivAt_cos` and `Real.hasDerivAt_sin` along the expression
  tree, and `ring` identifies the result with the stated derivative;
- 27 enclosures on the box, 11 at the point $z_0 = (0.0391773648, 0.6813015094)$ and 16 on the
  square $T$ of radius $10^{-10}$ about $z_0$, with 329 interval steps in all.

Let $M$ be the matrix with rows $(-0.1481, -0.2886)$ and $(-2.7218, 0.6267)$, the rounding to four
decimals of the inverse Jacobian $DH(z^\ast)^{-1}$ at the zero $z^\ast$ of $H$, whose rows are
$(-0.148147, -0.288600)$ and $(-2.721766, 0.626658)$. The Newton-type map is
$G(z) = z - M H(z)$; in the file,
$G_1 = \varphi + 0.1481\, H_1 + 0.2886\, H_2$ and $G_2 = \theta + 2.7218\, H_1 - 0.6267\, H_2$
([`rom_G1`](../../MovingSofaOptimality/External/Romik/Num.lean#L148), [`rom_G2`](../../MovingSofaOptimality/External/Romik/Num.lean#L152)). As $M$ is invertible, $G(z) = z$ exactly when $H(z) = 0$ ([`rom_Gz_eq_iff`](../../MovingSofaOptimality/External/Romik/Fix.lean#L52)).

### Lemma B.3 (the derivatives of $G$ on the box)

For $(\varphi, \theta) \in [0.039, 0.04] \times [0.68, 0.69]$,

```math
\Bigl\lvert \frac{\partial G_1}{\partial\varphi} \Bigr\rvert \le 0.03 , \qquad \Bigl\lvert \frac{\partial G_1}{\partial\theta} \Bigr\rvert \le 0.012 , \qquad \Bigl\lvert \frac{\partial G_2}{\partial\varphi} \Bigr\rvert \le 0.3 , \qquad \Bigl\lvert \frac{\partial G_2}{\partial\theta} \Bigr\rvert \le 0.16 .
```

*Lean: [`rom_G1φ_bound`](../../MovingSofaOptimality/External/Romik/Fix.lean#L65), [`rom_G1θ_bound`](../../MovingSofaOptimality/External/Romik/Fix.lean#L71), [`rom_G2φ_bound`](../../MovingSofaOptimality/External/Romik/Fix.lean#L77), [`rom_G2θ_bound`](../../MovingSofaOptimality/External/Romik/Fix.lean#L83), [`rom_G1φ_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L844),
[`rom_G1θ_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L864), [`rom_G2φ_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L882), [`rom_G2θ_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L900), [`rom_cos_box`](../../MovingSofaOptimality/External/Romik/Calc.lean#L35), [`rom_sin_box`](../../MovingSofaOptimality/External/Romik/Calc.lean#L42), [`rom_cos_box'`](../../MovingSofaOptimality/External/Romik/Calc.lean#L49),
[`rom_sin_box'`](../../MovingSofaOptimality/External/Romik/Calc.lean#L56).*

*Proof.* The atoms are enclosed on the box: $\varphi$ and $\theta$ by hypothesis, $\cos\varphi$,
$\sin\varphi$, $\cos\theta$, $\sin\theta$ by Lemma B.2 with six and seven terms, and
$\pi \in [3.141592, 3.141593]$. Interval evaluation of the expression trees on a grid of ten decimals
encloses the four partial derivatives in $[-0.0265913, 0.0265988]$, $[-0.0106501, 0.0117004]$,
$[-0.2245028, 0.2963473]$ and $[-0.1099305, 0.1517703]$; Figure B.2 compares them with the true
ranges. $\square$

![Four horizontal bars on a common axis from -0.3 to 0.3, one for each partial derivative of G. For dG1/dphi and dG1/dtheta the light blue proved enclosures are short, about plus or minus 0.027 and 0.011, inside black ticks at plus or minus 0.03 and 0.012, and the orange true ranges are thin slivers near 0. For dG2/dphi the enclosure runs from -0.22 to 0.30 within ticks at plus or minus 0.3, the true range from -0.014 to 0.082; for dG2/dtheta the enclosure runs from -0.11 to 0.15 within plus or minus 0.16, the true range from -0.008 to 0.049](figures/appendix-b/slack.svg)

*Figure B.2.* The four partial derivatives of $G$ on the box: their true ranges (orange, computed on
a grid), the enclosures that Lemma B.3 proves (light blue), and the bounds used for the contraction
(black ticks). The enclosures are 4.6 to 17 times wider than the true ranges, but the bounds
need only make the rows sum to at most $\frac12$: $0.03 + 0.012 = 0.042$ and $0.3 + 0.16 = 0.46$.

### Lemma B.4 (contraction)

For $z, z'$ in the box, $\lVert G(z) - G(z') \rVert_\infty \le \frac12 \lVert z - z' \rVert_\infty$.

*Lean: [`rom_Gz_dist_le`](../../MovingSofaOptimality/External/Romik/Fix.lean#L123), [`rom_G1_lip`](../../MovingSofaOptimality/External/Romik/Fix.lean#L101), [`rom_G2_lip`](../../MovingSofaOptimality/External/Romik/Fix.lean#L112), [`rom_mvt`](../../MovingSofaOptimality/External/Romik/Fix.lean#L92).*

*Proof.* Change one coordinate at a time: the box is a product of intervals, so by the mean value
inequality and Lemma B.3,
$\lvert G_1(z) - G_1(z') \rvert \le 0.03 \lvert \varphi - \varphi' \rvert + 0.012 \lvert \theta - \theta' \rvert \le 0.042 \lVert z - z' \rVert_\infty$
and $\lvert G_2(z) - G_2(z') \rvert \le 0.46 \lVert z - z' \rVert_\infty$. $\square$

### Lemma B.5 (the residual at $z_0$)

```math
G(z_0) - z_0 \in [-9.915950597, -9.9155784208] \cdot 10^{-12} \times [-1.72760407234, -1.72726825567] \cdot 10^{-11} .
```

*Lean: [`rom_Gz_z0`](../../MovingSofaOptimality/External/Romik/Fix.lean#L149), [`rom_MH1_z0`](../../MovingSofaOptimality/External/Romik/Num.lean#L1159), [`rom_MH2_z0`](../../MovingSofaOptimality/External/Romik/Num.lean#L1178), [`rom_cos_φ₀`](../../MovingSofaOptimality/External/Romik/Calc.lean#L65), [`rom_sin_φ₀`](../../MovingSofaOptimality/External/Romik/Calc.lean#L72), [`rom_cos_θ₀`](../../MovingSofaOptimality/External/Romik/Calc.lean#L79),
[`rom_sin_θ₀`](../../MovingSofaOptimality/External/Romik/Calc.lean#L86).*

*Proof.* Interval evaluation at the point $z_0$, whose coordinates are exact decimals, on a grid of
22 decimals: Lemma B.2 encloses $\cos\varphi_0$ and $\sin\varphi_0$ with four and five terms and
$\cos\theta_0$ and $\sin\theta_0$ with eight and nine, to within $2 \cdot 10^{-16}$, and $\pi$ is
enclosed to 20 decimals. The values are small because $z_0$ is within $2 \cdot 10^{-11}$ of the
zero: $H(z_0) = (-1.28, -2.78) \cdot 10^{-11}$. $\square$

### Theorem B.6 (the zero of $H$)

$H$ has exactly one zero in the box, and it lies in the square
$T = [\varphi_0 - 10^{-10}, \varphi_0 + 10^{-10}] \times [\theta_0 - 10^{-10}, \theta_0 + 10^{-10}]$.

*Lean: [`rom_zero_unique`](../../MovingSofaOptimality/External/Romik/Fix.lean#L142), [`rom_exists_zero`](../../MovingSofaOptimality/External/Romik/Fix.lean#L180), [`rom_mapsTo_tiny`](../../MovingSofaOptimality/External/Romik/Fix.lean#L166), [`rom_Gz_eq_iff`](../../MovingSofaOptimality/External/Romik/Fix.lean#L52), [`rom_box`](../../MovingSofaOptimality/External/Romik/Fix.lean#L38),
[`rom_tiny`](../../MovingSofaOptimality/External/Romik/Fix.lean#L41).*

*Proof.* The zeros of $H$ are the fixed points of $G$. Two fixed points $z$, $z'$ in the box satisfy
$\lVert z - z' \rVert \le \frac12 \lVert z - z' \rVert$ by Lemma B.4, so $z = z'$. For existence, let
$r = 10^{-10}$ and $z \in T$, a subset of the box. The two coordinate bounds in the proof of
Lemma B.4, applied to $z$ and $z_0$, and Lemma B.5 give

```math
\lvert G(z)_1 - \varphi_0 \rvert \le 0.042\, r + 0.0992\, r < r , \qquad \lvert G(z)_2 - \theta_0 \rvert \le 0.46\, r + 0.1728\, r < r ,
```

so $G$ maps $T$ into itself (Figure B.3), and it is a $\frac12$-contraction of the complete
metric space $T$.
Banach's fixed point theorem (Mathlib's `ContractingWith.exists_fixedPoint'`) gives a fixed point in
$T$. $\square$

![A square from -1 to 1 in both coordinates, the square T in units of r = 10 to the minus 10 about z0 at its centre. A thin dashed green rectangle, about 0.08 wide and 0.92 tall, lies left of and below the centre, labelled as containing G(T); the orange point z* lies in it, at about (-0.1, -0.17)](figures/appendix-b/contraction.svg)

*Figure B.3.* The square $T$ about $z_0$, in units of $r = 10^{-10}$. By Lemmas B.4 and B.5 its image
$G(T)$ lies in the dashed green rectangle around $G(z_0)$, of half-widths $0.042\, r$ and
$0.46\, r$, which is inside $T$. The true image is much smaller: it has diameter below $0.001\, r$
and surrounds the zero $z^\ast$ of $H$ (orange), since $G$ is nearly constant near $z^\ast$.

### Proposition B.7 (enclosures of the parameters)

The solution of Romik's equations in the box satisfies
$\varphi \in [0.0391773647, 0.0391773649]$, $\theta \in [0.6813015093, 0.6813015095]$, and each of
$a_1$, $b_1$, $b_2$, $c_1$, $c_2$, $d_1$, $d_2$ and the coordinates of $\kappa_2, \dots, \kappa_5$ lies
in an interval of width at most $1.5 \cdot 10^{-8}$. In particular it satisfies the enclosures
[`GerverParams.Bounds`](../../MovingSofaOptimality/Gerver/Bounds.lean#L24), of width about $2 \cdot 10^{-7}$, which the rest of the numerics uses.

*Lean: [`rom_angles_mem`](../../MovingSofaOptimality/External/Romik.lean#L372), [`rom_a1_mem`](../../MovingSofaOptimality/External/Romik.lean#L391), [`rom_b1_mem`](../../MovingSofaOptimality/External/Romik.lean#L399), [`rom_b2_mem`](../../MovingSofaOptimality/External/Romik.lean#L407), [`rom_c1_mem`](../../MovingSofaOptimality/External/Romik.lean#L415), [`rom_c2_mem`](../../MovingSofaOptimality/External/Romik.lean#L423),
[`rom_d1_mem`](../../MovingSofaOptimality/External/Romik.lean#L432), [`rom_d2_mem`](../../MovingSofaOptimality/External/Romik.lean#L441), [`rom_kappa21_mem`](../../MovingSofaOptimality/External/Romik.lean#L456), [`rom_kappa31_mem`](../../MovingSofaOptimality/External/Romik.lean#L472), [`rom_kappa41_mem`](../../MovingSofaOptimality/External/Romik.lean#L488),
[`rom_kappa51_mem`](../../MovingSofaOptimality/External/Romik.lean#L508), [`romik_bounds`](../../MovingSofaOptimality/External/Romik.lean#L522).*

*Proof.* By Theorem B.6 and [Proposition 10.7](10-gerver.md#proposition-107-reduction-to-two-equations), the angles of the solution lie in
$T$, and its parameters are the functions of Proposition 10.7 of the atoms. On $T$ the cosines and
sines are enclosed by their enclosures at $z_0$, from the proof of Lemma B.5, widened by $10^{-10}$
([`rom_cos_tiny`](../../MovingSofaOptimality/External/Romik/Calc.lean#L103), …), and interval evaluation on a grid of 16 decimals encloses $a_1$, $b_1$, $b_2$, $c_1$ and the $\kappa_i$ ([`rom_a₁_tiny`](../../MovingSofaOptimality/External/Romik/Num.lean#L1279), …); $c_2$, $d_1$,
$d_2$ follow from the symmetry equations. [`romik_bounds`](../../MovingSofaOptimality/External/Romik.lean#L522) widens these enclosures to those of
[`GerverParams.Bounds`](../../MovingSofaOptimality/Gerver/Bounds.lean#L24), by `norm_num`. $\square$

## B.3 The area of Gerver's sofa

By [Theorem 10.21](10-gerver.md#theorem-1021-the-area-of-gervers-sofa), $\lvert G \rvert$ is a signed sum of six curve areas. Each is
split at the phase boundaries, where the contact curves are only continuous; on a phase each curve is
explicit, and its curve area is the integral of an explicit function.

### Lemma B.8 (trigonometric polynomials)

Let $F(t) = P(t) + Q(t) \cos t + R(t) \sin t$, where $P$ is a polynomial of degree at most 5 with
$P(0) = 0$ and $Q$, $R$ are polynomials of degree at most 2. Then
$F' = P' + (Q' + R) \cos t + (R' - Q) \sin t$, and $\int_a^b F'(t)\, dt = F(b) - F(a)$.

*Lean: [`ga_TP`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L56), [`ga_TP.F`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L74), [`ga_TP.dF`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L79), [`ga_TP.hasDerivAt`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L88), [`ga_TP.integral`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L114).*

*Proof.* The product rule, and the fundamental theorem of calculus for the continuous function
$F'$. $\square$

### Lemma B.9 (the curve area on a phase)

If a curve $z$ agrees on $[a, b]$ with a curve $Z$ that has a continuous derivative, then
$\mathcal{J}(z|_{[a, b]}) = \frac12 \int_a^b Z \times Z'$. On a phase written
$\mathbf{x} = R_t\, w + \kappa$ as in [Lemma 10.5](10-gerver.md#lemma-105-the-phases-in-the-rotating-frame),

```math
\mathbf{A} \times \mathbf{A}' = \rho_A\, \bigl(w_1 + 1 + \langle \kappa, u_t \rangle\bigr) , \qquad \mathbf{C} \times \mathbf{C}' = \rho_C\, \bigl(w_2 + 1 + \langle \kappa, v_t \rangle\bigr) ,
```

```math
\mathbf{B} \times \mathbf{B}' = (\rho_A - 1)\, \bigl(w_1 + \langle \kappa, u_t \rangle\bigr) , \qquad \mathbf{D} \times \mathbf{D}' = (1 - \rho_C)\, \bigl(-w_2 - \langle \kappa, v_t \rangle\bigr) ,
```

```math
\mathbf{x} \times \mathbf{x}' = w_1 \beta - w_2 \alpha - \alpha\, \langle \kappa, v_t \rangle + \beta\, \langle \kappa, u_t \rangle .
```

*Lean: [`ga_curveArea_eq`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L127), [`ga_cross_A`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L172), [`ga_cross_B`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L179), [`ga_cross_C`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L187), [`ga_cross_D`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L194), [`ga_cross_X`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L202),
[`ga_phase_A`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L214), [`ga_phase_X`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L256).*

*Proof.* The first claim is the formula $\mathcal{J}(Z|_{[a, b]}) = \frac12 \int_a^b Z \times Z'$ for a
continuously differentiable curve ([`curveArea_eq_integral`](../../MovingSofaOptimality/Convex/CurveArea.lean#L436); [Chapter 8](08-convex-curves.md)). For the formulas, $p \times v_t = \langle p, u_t \rangle$ and
$p \times u_t = -\langle p, v_t \rangle$, and by Lemma 10.5,
$\mathbf{A} \times \mathbf{A}' = \rho_A \langle \mathbf{A}, u_t \rangle$ with
$\langle \mathbf{A}, u_t \rangle = w_1 + 1 + \langle \kappa, u_t \rangle$; the others are alike. $\square$

On each phase the coefficients $\alpha$, $\beta$, $\rho_A$, $\rho_C$ and $w$ are polynomials in $t$,
$\cos t$ and $\sin t$ (Table 10.1), and the integrand of Lemma B.9 is
$p_0(t) + p_1(t) \cos t + p_2(t) \sin t$ with polynomials $p_i$ whose coefficients are polynomials in
the parameters. Its antiderivative is a trigonometric polynomial $F$ as in Lemma B.8; the generator
computes $F$ symbolically, the definitions [`ga_K_A2`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L483), … record its coefficients as functions of the
parameters, and Lean checks $F' = $ integrand by `ring` ([`ga_A2`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L670), …). The phases on which a curve is
constant contribute nothing: $\mathbf{A}$ on phase 1 and $\mathbf{C}$ on phase 5 ([`ga_A1`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L343), [`ga_C5`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L351)).

### Proposition B.10 (the six curve areas)

The six curve areas of Theorem 10.21 lie in the intervals of Table B.1.

*Lean: [`ga_curveArea_A_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L2954), [`ga_curveArea_C_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L2966), [`ga_segArea_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L2999), [`ga_curveArea_x_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3006),
[`ga_curveArea_B_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3016), [`ga_curveArea_D_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3025), [`curveArea_split_five`](../../MovingSofaOptimality/Convex/CurveArea.lean#L516), [`ga_A2_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L682), [`ga_num_A2`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L498),
[`ga_segArea_eq`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L368), [`ga_area_lower`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3037), [`gv_area_mem`](../../MovingSofaOptimality/Gerver/Niche.lean#L467).*

*Proof.* Additivity of $\mathcal{J}$ splits each curve area at the phase boundaries
([`curveArea_split_five`](../../MovingSofaOptimality/Convex/CurveArea.lean#L516), [`proposition7_2_6`](../../MovingSofaOptimality/Convex/CurveArea.lean#L487)), and Lemmas B.8 and B.9 write each phase's part as
$\frac12 (F(t_B) - F(t_A))$. An interval chain `ga_num_*` encloses this number from the enclosures
of the parameters ([`GerverParams.Bounds`](../../MovingSofaOptimality/Gerver/Bounds.lean#L24)), of the endpoints $t_A, t_B \in \lbrace 0, \varphi,
\theta, \frac\pi2 - \theta, \frac\pi2 - \varphi, \frac\pi2 \rbrace$ and of their cosines and sines
(Lemma B.2 with six and seven terms; [`ga_cos_φ_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L460), …), and of $\pi$, on a grid of 12 decimals.
The top edge contributes $\frac12\, \mathbf{A}(\frac\pi2) \times \mathbf{C}(0) = \frac12\bigl((a_1 + \kappa_{5,1}) - (\frac34 + \kappa_{5,2})(1 - 2a_1)\bigr)$.
`linarith` adds the enclosures of the phases and proves the four-decimal bounds of the statements.
$\square$

| Curve area | Phases | Sum of the phase enclosures | Statement |
| --- | --- | --- | --- |
| $\mathcal{J}(\mathbf{A}\vert_{[0, \pi/2]})$ | 2 to 5 | $[0.720160254625, 0.720167853181]$ | $[0.7201, 0.7202]$ |
| $\mathcal{J}(\mathbf{C}\vert_{[0, \pi/2]})$ | 1 to 4 | $[1.333923346846, 1.333931220662]$ | $[1.3339, 1.3340]$ |
| $\mathcal{J}(\mathbf{A}(\pi/2), \mathbf{C}(0))$ | | $[0.806881343467, 0.806881887533]$ | $[0.8068, 0.8069]$ |
| $\mathcal{J}(\mathbf{x}\vert_{[t_1, t_4]})$ | 2 to 4 | $[0.601388395334, 0.601401080196]$ | $[0.6013, 0.6015]$ |
| $\mathcal{J}(\mathbf{B}\vert_{[t_3, t_5]})$ | 4, 5 | $[-0.003088290470, -0.003086650205]$ | $[-0.0031, -0.0030]$ |
| $\mathcal{J}(\mathbf{D}\vert_{[t_0, t_2]})$ | 1, 2 | $[-0.036959733404, -0.036958415850]$ | $[-0.0370, -0.0369]$ |

*Table B.1.* The six curve areas: the sums of the enclosures of their phases, which the generator
computes, and the enclosures that the Lean statements keep, rounded outward to four decimals. With
the signs of Theorem 10.21 the sums give $2.2195158 \le \lvert G \rvert \le 2.2195475$, and the
rounded enclosures $2.2192 \le \lvert G \rvert \le 2.2199$, the bounds of the Challenge.

## B.4 The generators

Two Python scripts write the two generated files. They work in exact rational arithmetic
(`fractions.Fraction`), with `sympy` for the symbolic steps, and round every endpoint outward to a
decimal grid.

| Lean file | Generator | Contents |
| --- | --- | --- |
| [`Num.lean`](../../MovingSofaOptimality/External/Romik/Num.lean) | [`mk_num.py`](../../scripts/romik/mk_num.py) | 48 definitions, 21 derivative formulas, 54 enclosures with 329 steps |
| [`AreaBounds.lean`](../../MovingSofaOptimality/Gerver/AreaBounds.lean) | [`gen.py`](../../scripts/area/gen.py) | 15 antiderivatives `ga_K_*`, 22 interval chains `ga_num_*` with 878 steps |

*Table B.2.* The generated files. Running `python3 scripts/romik/mk_num.py` rewrites `Num.lean`,
and `python3 gen.py emit <file>` in [`scripts/area`](../../scripts/area) writes `AreaBounds.lean` to `<file>`. Both
reproduce the committed files exactly.

- **Romik's system** ([`scripts/romik/`](../../scripts/romik)). [`gen.py`](../../scripts/romik/gen.py) builds each
  function of §B.2 as an expression tree over the seven atoms; run as a script, it checks with
  `sympy` that the stated partial derivatives are the derivatives (`check_partials`). It writes the
  Lean definitions, the derivative proofs (Mathlib's rules applied along the tree) and the interval
  chains (`gen_regime`, one `have` per node, choosing
  [`iv_mul_nonneg`](../../MovingSofaOptimality/Basic/Interval.lean#L69) when both factors are
  nonnegative).
  [`drive.py`](../../scripts/romik/drive.py) fixes the enclosures of the atoms in the three regimes: Taylor
  sums for the cosines and sines, the decimal bounds on $\pi$, and grids of 10, 22 and 16 decimals.
  [`mk_num.py`](../../scripts/romik/mk_num.py) assembles the file.
- **The area** ([`scripts/area/`](../../scripts/area)). [`gen.py`](../../scripts/area/gen.py) writes, for each
  curve and phase, the integrand of Lemma B.9 in the rotating frame, splits it as
  $p_0 + p_1 \cos t + p_2 \sin t$, finds the antiderivative of Lemma B.8 by repeated
  differentiation, and asserts that its derivative is the integrand. Its interval chains choose, for
  each product, the lemma for the signs of the factors. It asserts that the six enclosures have
  width at most $0.002$ and give an area of at least $2.2$, and assembles the file from the
  templates `tpl_head.lean.in`, `tpl_generic.lean.in` and `tpl_phase.lean.in`.

The generators decide nothing that Lean does not check. A definition they write is only a
definition; the identities between the definitions and the geometry ([`rom_eq_mk`](../../MovingSofaOptimality/External/Romik.lean#L160), [`ga_A2`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L670), …) and
the derivative formulas are proved in Lean; and if a generator chose an endpoint too tight,
`norm_num` would fail on its side condition and the build would fail. The audit script
[`scripts/Audit.lean`](../../scripts/Audit.lean) confirms that the theorems that use these files depend
only on the axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
