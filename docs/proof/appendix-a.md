# Appendix A. Gerver's four constants

[Contents](README.md) · [← 13. The bridge to formal-conjectures](13-bridge.md) · [Appendix B. Rigorous numerics for Gerver's sofa →](appendix-b.md)

This appendix proves that Gerver's system
([Definition 13.3](13-bridge.md#definition-133-gervers-system-and-gervers-four-constants)) has at
most one solution on its whole domain $0 \le \varphi \le \theta \le \pi/4$, $A, B \ge 0$ (Theorem
A.1). formal-conjectures defines Gerver's four constants as the unique solution, so its Gerver's
sofa rests on this theorem, together with the existence of a solution
([Theorem 13.13](13-bridge.md#theorem-1313-gervers-system-has-exactly-one-solution)). The proof uses
only elementary bounds on the sine, the cosine and $\pi$, and no numerical certificate. Every
algebraic identity below was checked symbolically, and every constant recomputed.

The proof eliminates $A$ and $B$, which are explicit functions $\hat A$, $\hat B$ of the angles, and
studies two functions of the angles on the triangle
$\Delta = \lbrace 0 \le \varphi \le \theta \le \pi/4 \rbrace$: $F$, the third equation with
$A = \hat A$ and $B = \hat B$, and $G$, the second. A solution is a common zero of $F$ and $G$. A
chain of estimates confines every solution to the thin strip $\varphi < 1/20$ (Figure A.1). On that
strip $F$ decreases strictly in $\varphi$ and increases in $\theta$, while $H = G + \tfrac{9}{10} F$
decreases in $\varphi$ and strictly in $\theta$; two functions with these patterns have at most one
common zero (Figures A.2 and A.3).

Throughout, $\varphi$ and $\theta$ are variables, $E_1, \dots, E_4$ are the left sides of Gerver's
equations (Definition 13.3), and $g = \theta - \varphi$. The letters $F$, $G$, $H$ and $C$ denote
functions of the angles in this appendix; they are not Gerver's sofa, the horizontal strip or a
contact point.

### Theorem A.1 (Gerver's constants are unique)

If $(A, B, \varphi, \theta)$ and $(A', B', \varphi', \theta')$ both solve Gerver's system, then
$A = A'$, $B = B'$, $\varphi = \varphi'$ and $\theta = \theta'$.

*Lean:
[`MovingSofaBridge.GerverConstants.spec_unique`](../../MovingSofaBridge/GerverConstants.lean#L1283),
[`MovingSofaBridge.GerverConstants.angles_unique`](../../MovingSofaBridge/GerverConstants.lean#L1269).*

*Outline of the proof.* The steps, with the key estimate of each:

| § | Step | Key estimate |
| --- | --- | --- |
| A.1 | The angles determine $A$ and $B$; a solution is a zero of $Q$ | $3\cos\varphi - \cos\theta \ge 2\cos\varphi > 0$ |
| A.2 | No solution on the edges $\varphi = 0$, $\varphi = \theta$ | $(t - 1)\cos t - \sin t + 1 > 0$ for $0 < t < 1$ |
| A.3 | Every solution has $\varphi < 1/2$ | $3s^2 - \tfrac7{10} s - \tfrac3{10} > 0$ for $s \ge \tfrac{23}{48}$ |
| A.4 | $Q$ decreases strictly in $\varphi$ for $\varphi \le 1/2$ | an upper bound of $\partial_\varphi Q$ that decreases in $\theta$ and is nonpositive on the diagonal |
| A.5 | Every solution has $\varphi < 1/20$ | $Q(\tfrac1{20}, \tfrac\pi4) \le -0.0142$ |
| A.6 | The residuals $F$, $G$, $H$ and their derivatives | $\partial_\theta F$, $\partial_\theta G$ share the factor $C = 1 - \hat A - g > 0$ |
| A.7 | Bounds on the strip $\varphi \le 1/20$ | $0 \le \hat A \le \tfrac4{25}$, $\tfrac7{10} \le \hat B \le 2$, $1.99 \le 3\cos\varphi - \cos\theta \le 2.3$ |
| A.8 | The signs of the partial derivatives | $\partial_\varphi F \le -\tfrac23$, $\partial_\varphi G \le \tfrac35 = \tfrac9{10} \cdot \tfrac23$ |
| A.9 | Uniqueness | the monotonicity of $F$ and $H$ |

![The triangle 0 ≤ φ ≤ θ ≤ π/4 in the (φ, θ)-plane. Its edges φ = 0 and φ = θ (purple) carry no solution. On the part φ ≤ 1/2 (orange) ∂Q/∂φ is negative, and the corner φ ≥ 1/2 (grey) has no solution. On the segment φ = 1/20 (green) Q increases in θ up to a negative value at θ = π/4. In the thin strip φ ≤ 1/20 (blue) the partial derivatives of F and H have their signs; the zero set of Q, a curve from the origin to the top edge, lies in it, and Gerver's angles (φ, θ) are a point of it](figures/appendix-a/triangle.svg)

*Figure A.1.* The triangle $\Delta$ and the steps of the proof. The edges $\varphi = 0$ and
$\varphi = \theta$ (purple) carry no solution (§A.2), nor does the corner $\varphi \ge 1/2$ (grey,
§A.3). On $\varphi \le 1/2$ (orange) the reduced function $Q$ decreases in $\varphi$ (§A.4), and on
the segment $\varphi = 1/20$ (green) it increases in $\theta$ up to a negative value (§A.5); so the
zero set of $Q$ (black) lies in the strip $\varphi < 1/20$ (blue), where the signs of §A.8 hold. The
dot is Gerver's angles.

## A.1 The reduced equations

### Definition A.2 (the reduced functions)

For real $\varphi$, $\theta$ let

```math
\begin{aligned}
D(\varphi, \theta) &= 3\cos\varphi - \cos\theta, & N(\varphi, \theta) &= g\cos\theta + 3\sin\varphi - \sin\theta - \cos\theta + 1, \\
k(\varphi, \theta) &= 1 + \tfrac12 g, & o(\varphi, \theta) &= \tfrac\pi2 - \varphi - \theta + \tfrac12 g + \tfrac14 g^2,
\end{aligned}
```

let $\hat A = N / D$ and $\hat B = \hat A k + o$, and let

```math
Q(\varphi, \theta) = N \bigl(\cos\varphi - k \sin\varphi\bigr) - D \bigl(\sin\varphi + \tfrac12 - \tfrac12 \cos\varphi + o \sin\varphi\bigr).
```

*Lean: [`MovingSofaBridge.GerverConstants.den`](../../MovingSofaBridge/GerverConstants.lean#L77),
[`MovingSofaBridge.GerverConstants.num`](../../MovingSofaBridge/GerverConstants.lean#L79),
[`MovingSofaBridge.GerverConstants.slope`](../../MovingSofaBridge/GerverConstants.lean#L82),
[`MovingSofaBridge.GerverConstants.offset`](../../MovingSofaBridge/GerverConstants.lean#L84),
[`MovingSofaBridge.GerverConstants.reconstructedA`](../../MovingSofaBridge/GerverConstants.lean#L96),
[`MovingSofaBridge.GerverConstants.reconstructedB`](../../MovingSofaBridge/GerverConstants.lean#L98),
[`MovingSofaBridge.GerverConstants.reducedQ`](../../MovingSofaBridge/GerverConstants.lean#L87).*

### Lemma A.3 (elimination)

On $\Delta$, $D \ge 2\cos\varphi > 0$. For all $A$, $B$, $\varphi$, $\theta$,

```math
E_1 - 2E_3 = N - A D, \qquad E_4 = A k + o - B, \qquad Q = D\,(E_3 - E_4 \sin\varphi) + (\cos\varphi - k\sin\varphi)(E_1 - 2E_3).
```

So every solution has $A = \hat A(\varphi, \theta)$, $B = \hat B(\varphi, \theta)$ and
$Q(\varphi, \theta) = 0$, and two solutions with the same angles are equal.

*Lean:
[`MovingSofaBridge.GerverConstants.den_pos`](../../MovingSofaBridge/GerverConstants.lean#L101),
[`MovingSofaBridge.GerverConstants.eliminate_B`](../../MovingSofaBridge/GerverConstants.lean#L111),
[`MovingSofaBridge.GerverConstants.eliminate_eq4`](../../MovingSofaBridge/GerverConstants.lean#L117),
[`MovingSofaBridge.GerverConstants.Spec.coefficients`](../../MovingSofaBridge/GerverConstants.lean#L144).*

*Proof.* On $\Delta$, $\cos\varphi > 0$ and $\cos\theta \le \cos\varphi$, so $D \ge 2\cos\varphi$.
The three identities are polynomial identities in $A$, $B$, $\varphi$, $\theta$ and the sines and
cosines. At a solution, $E_1 = E_3 = 0$ gives $A D = N$, so $A = \hat A$; then $E_4 = 0$ gives
$B = \hat A k + o = \hat B$, and the third identity gives $Q = 0$. $\square$

The documentation of the Lean module compares these identities with those of RuifengCao/sofa-formal
(`Sofa/GerverConst.lean`), an earlier formalization of Baek's proof (see the
[prior work](../prior-work.md) page).

## A.2 The boundary of the domain

### Lemma A.4 (no solution on the boundary)

Every solution has $0 < \varphi < \theta$.

*Lean:
[`MovingSofaBridge.GerverConstants.Spec.phi_pos`](../../MovingSofaBridge/GerverConstants.lean#L170),
[`MovingSofaBridge.GerverConstants.Spec.phi_lt_theta`](../../MovingSofaBridge/GerverConstants.lean#L210).*

*Proof.* *The edge $\varphi = 0$.* Then $E_3 = A$, so $A = 0$. If also $\theta = 0$, then
$E_2 = 4 - 2B$ gives $B = 2$, and $E_4 = \pi/2 - 2$ would force $\pi = 4$. If $\theta > 0$, then
$E_1 = f(\theta)$ with $f(t) = (t - 1)\cos t - \sin t + 1$. Now $f(0) = 0$ and
$f'(t) = (1 - t)\sin t > 0$ on $(0, \theta)$, since $\theta \le \pi/4 < 1$; so $f(\theta) > 0$,
against $E_1 = 0$.

*The edge $\varphi = \theta$.* Then $E_1 = -2B\sin\varphi$ with $\sin\varphi > 0$, so $B = 0$;
$E_4 = A + \pi/2 - 2\varphi = 0$ gives $A = 2\varphi - \pi/2 \le 0$, so $A = 0$; and then
$E_3 = -\sin\varphi - \tfrac12(1 - \cos\varphi) < 0$. $\square$

## A.3 A first bound on φ

### Lemma A.5 (A ≤ B, and an inequality between the angles)

Every solution has $A \le B$ and

```math
3\sin^2\varphi - \sin\varphi \cos\varphi \le (\theta - \varphi)(\cos\varphi - \sin\varphi).
```

*Lean:
[`MovingSofaBridge.GerverConstants.Spec.A_le_B`](../../MovingSofaBridge/GerverConstants.lean#L272),
[`MovingSofaBridge.GerverConstants.Spec.angle_inequality`](../../MovingSofaBridge/GerverConstants.lean#L282).*

*Proof.* On $\Delta$: $0 \le \sin\varphi \le \cos\varphi$, $\cos\theta \le \cos\varphi$,
$\cos\theta + \sin\theta \ge 1$ (its square is $1 + 2\sin\theta\cos\theta$), and $o \ge 0$, since
$\pi/2 - \varphi - \theta \ge 0$. By Lemma A.3, $B = A k + o \ge A$, as $k \ge 1$ and $A \ge 0$.

From $E_3 = 0$ and $B \ge A$,
$A\cos\varphi = \sin\varphi + \tfrac12(1 - \cos\varphi) + B\sin\varphi \ge \sin\varphi + A\sin\varphi$,
so

```math
\sin\varphi \le A(\cos\varphi - \sin\varphi). \tag{A.1}
```

From $A D = N$, with $(\theta - \varphi)\cos\theta \le \theta - \varphi$ and
$\sin\theta + \cos\theta \ge 1$,

```math
2A\cos\varphi \le A(3\cos\varphi - \cos\theta) = N \le \theta - \varphi + 3\sin\varphi. \tag{A.2}
```

Multiply (A.1) by $2\cos\varphi \ge 0$ and use (A.2) times $\cos\varphi - \sin\varphi \ge 0$:
$2\sin\varphi\cos\varphi \le (\theta - \varphi + 3\sin\varphi)(\cos\varphi - \sin\varphi)$, which
rearranges to the claim. $\square$

### Lemma A.6 (φ < 1/2)

Every solution has $\varphi < 1/2$.

*Lean:
[`MovingSofaBridge.GerverConstants.Spec.phi_lt_half`](../../MovingSofaBridge/GerverConstants.lean#L305).*

*Proof.* Suppose $\varphi \ge 1/2$, and let $s = \sin\varphi$. Then
$\theta - \varphi \le \pi/4 - 1/2 < 3/10$, as $\pi < 3.15$, and
$s \ge \sin\tfrac12 \ge \tfrac12 - \tfrac1{48} = \tfrac{23}{48}$ by $\sin x \ge x - x^3/6$. Lemma
A.5, with $s\cos\varphi \le s$ and $0 \le \cos\varphi - \sin\varphi \le 1 - s$, gives

```math
3s^2 - s \le 3s^2 - s\cos\varphi \le \tfrac3{10}(1 - s), \qquad \text{that is} \qquad 3s^2 - \tfrac7{10} s - \tfrac3{10} \le 0 .
```

But $3s^2 - \tfrac7{10} s - \tfrac3{10}$ increases for $s \ge \tfrac7{60}$ and equals
$\tfrac{41}{768} > 0$ at $s = \tfrac{23}{48}$. $\square$

## A.4 The φ-derivative of Q

### Lemma A.7 (Q decreases in φ)

For $0 \le \varphi \le 1/2$ and $\varphi < \theta \le \pi/4$, $\partial Q / \partial\varphi < 0$.

*Lean:
[`MovingSofaBridge.GerverConstants.reducedQ_phi_deriv`](../../MovingSofaBridge/GerverConstants.lean#L459),
[`MovingSofaBridge.GerverConstants.qPhi_le_min`](../../MovingSofaBridge/GerverConstants.lean#L524),
[`MovingSofaBridge.GerverConstants.qPhiMinTheta_neg`](../../MovingSofaBridge/GerverConstants.lean#L497),
[`MovingSofaBridge.GerverConstants.qPhiMin_diagonal_nonpos`](../../MovingSofaBridge/GerverConstants.lean#L513),
[`MovingSofaBridge.GerverConstants.qPhi_neg`](../../MovingSofaBridge/GerverConstants.lean#L543).*

*Proof.* Write $Q = N J - D Z$ with $J = \cos\varphi - k\sin\varphi$ and
$Z = \sin\varphi\,(1 + o) + \tfrac12(1 - \cos\varphi)$. With

```math
\partial_\varphi N = D, \qquad \partial_\varphi D = -3\sin\varphi, \qquad \partial_\varphi k = -\tfrac12, \qquad \partial_\varphi o = -k - \tfrac12,
```

the derivative is

```math
\partial_\varphi Q = q(\varphi, \theta) = -D\, o \cos\varphi - N \bigl(\tfrac12 \sin\varphi + k\cos\varphi\bigr) + 3\sin\varphi\, Z .
```

Let $q_{\min}$ be $q$ with $o$ replaced by
$m = \tfrac12 g + \tfrac14 g^2 = o - (\pi/2 - \varphi - \theta)$, also inside $Z$. Then

```math
q - q_{\min} = \bigl(3\sin^2\varphi - D\cos\varphi\bigr)\bigl(\tfrac\pi2 - \varphi - \theta\bigr) \le 0,
```

since for $\varphi \le 1/2$, $\sin\varphi \le 1/2$ and $\cos\varphi \ge 1 - \varphi^2/2 \ge 7/8$, so
$D\cos\varphi \ge 2\cos^2\varphi \ge 49/32 > 3/4 \ge 3\sin^2\varphi$. On the diagonal,
$q_{\min}(\varphi, \varphi) = (\sin\varphi - \cos\varphi)(1 - \cos\varphi + 2\sin\varphi) \le 0$.
And $q_{\min}$ decreases strictly in $\theta$ on $\Delta$: with $c = \cos\varphi$,
$s = \sin\varphi$,

```math
\partial_\theta q_{\min} = \tfrac14 \Bigl(-6g(c^2 - s^2) - 6s(c - s) - 2c^2 - 4c(c - \cos\theta) - 2c - c\sin\theta\,(2 - g^2) - 2s\sin\theta\,(1 - g)\Bigr),
```

where every term is at most $0$, since $0 \le g \le \pi/4 < 1$, $0 \le s \le c$ and
$\cos\theta \le c$, and $-2c < 0$. So for $\theta > \varphi$,
$q(\varphi, \theta) \le q_{\min}(\varphi, \theta) < q_{\min}(\varphi, \varphi) \le 0$. $\square$

## A.5 Every solution has φ < 1/20

### Lemma A.8 (Q on the line φ = 1/20)

1. $\partial Q / \partial\theta\,(1/20, \theta) > 0$ for $1/20 \le \theta \le \pi/4$.
2. $Q(1/20, \pi/4) < 0$.

*Lean:
[`MovingSofaBridge.GerverConstants.cut_frame_bounds`](../../MovingSofaBridge/GerverConstants.lean#L570),
[`MovingSofaBridge.GerverConstants.qTheta_cut_pos`](../../MovingSofaBridge/GerverConstants.lean#L597),
[`MovingSofaBridge.GerverConstants.reducedQ_cut_boundary_neg`](../../MovingSofaBridge/GerverConstants.lean#L640).*

*Proof.* At $\varphi = 1/20$: $0.0499 \le \sin\tfrac1{20} \le \tfrac1{20}$ and
$0.998 \le \cos\tfrac1{20} \le 1$, from $\sin x \ge x - x^3/6 = 0.049979\ldots$ and
$\cos x \ge 1 - x^2/2 = 0.99875$. For $1/20 \le \theta \le \pi/4$, $g \in [0, 3/4]$, so $k \le 11/8$
and $o \le \pi/2 - 1/10 < 2$; hence, with $J$ and $Z$ as in the proof of Lemma A.7,

```math
J \ge 0.998 - \tfrac{11}8 \cdot \tfrac1{20} = 0.92925 \ge \tfrac9{10}, \qquad Z \le \tfrac1{20} \cdot 3 + \tfrac12 (1 - 0.998) = 0.151 .
```

(1) From $\partial_\theta N = (1 - g)\sin\theta$, $\partial_\theta D = \sin\theta$,
$\partial_\theta J = -\tfrac12\sin\varphi$ and $\partial_\theta Z = \tfrac12 (g - 1)\sin\varphi$,

```math
\partial_\theta Q = \bigl((1 - g) J - Z\bigr)\sin\theta + \tfrac12 \bigl(3(1 - g)\cos\varphi - 3\sin\varphi + \sin\theta - 1\bigr)\sin\varphi .
```

The first term is nonnegative, since
$(1 - g) J \ge \tfrac14 \cdot \tfrac9{10} = 0.225 > 0.151 \ge Z$. The second bracket is positive: if
$\theta \le 1/2$, then $g \le 9/20$ and it is at least
$3 \cdot \tfrac{11}{20} \cdot 0.998 - 0.15 - 1 = 0.4967$; if $\theta > 1/2$, then
$\sin\theta \ge \tfrac{23}{48}$ and it is at least
$3 \cdot \tfrac14 \cdot 0.998 - 0.15 + \tfrac{23}{48} - 1 = 0.0777\ldots$.

(2) With $3.14 < \pi < 3.144$, $g = \pi/4 - 1/20 \in [0.735, 0.736]$ and
$\cos\tfrac\pi4 = \sin\tfrac\pi4 = \tfrac{\sqrt2}2 \in [0.707, 0.708]$:

```math
\begin{aligned}
N &= (g - 2)\tfrac{\sqrt2}2 + 3\sin\tfrac1{20} + 1 \le -1.264 \cdot 0.707 + 1.15 = 0.256352 \le 0.257, \\
D &= 3\cos\tfrac1{20} - \tfrac{\sqrt2}2 \ge 2.994 - 0.708 = 2.286, \\
J &\le 1 - \bigl(1 + \tfrac12 \cdot 0.735\bigr) \cdot 0.0499 = 0.9317\ldots \le 0.932, \\
o &= \tfrac32 g + \tfrac14 g^2 \ge 1.2375\ldots \ge 1.237, \qquad Z \ge 0.0499 \cdot 2.237 = 0.1116\ldots \ge 0.111,
\end{aligned}
```

so $Q = N J - D Z \le 0.257 \cdot 0.932 - 2.286 \cdot 0.111 = -0.014222 < 0$. The exact value is
$Q(1/20, \pi/4) = -0.0195845687\ldots$. $\square$

### Lemma A.9 (φ < 1/20)

Every solution has $\varphi < 1/20$.

*Lean:
[`MovingSofaBridge.GerverConstants.Spec.phi_lt_twentieth`](../../MovingSofaBridge/GerverConstants.lean#L701).*

*Proof.* Suppose $\varphi \ge 1/20$. By Lemmas A.4 and A.6, $1/20 \le \varphi < 1/2$ and
$\varphi < \theta \le \pi/4$. By Lemma A.7, $Q(\cdot, \theta)$ does not increase on
$[1/20, \varphi]$, and by Lemma A.8 (1), $Q(1/20, \cdot)$ does not decrease on $[1/20, \pi/4]$. So,
with Lemma A.3 and Lemma A.8 (2),

```math
0 = Q(\varphi, \theta) \le Q(\tfrac1{20}, \theta) \le Q(\tfrac1{20}, \tfrac\pi4) < 0 . \qquad \square
```

## A.6 The residuals F and G

### Definition A.10 (the residuals)

Let $C = 1 - \hat A - g$ and

```math
\begin{aligned}
F &= E_3(\hat A, \hat B, \varphi, \theta) = \hat A\cos\varphi - (\hat B + 1)\sin\varphi + \tfrac12(\cos\varphi - 1), \\
G &= E_2(\hat A, \hat B, \varphi, \theta) = -3C\sin\theta + (\hat A - 1)\sin\varphi + (1 - 2\hat B)\cos\varphi + 3\cos\theta, \\
H &= G + \tfrac9{10} F .
\end{aligned}
```

*Lean:
[`MovingSofaBridge.GerverConstants.remainder`](../../MovingSofaBridge/GerverConstants.lean#L738),
[`MovingSofaBridge.GerverConstants.firstResidual`](../../MovingSofaBridge/GerverConstants.lean#L740),
[`MovingSofaBridge.GerverConstants.secondResidual`](../../MovingSofaBridge/GerverConstants.lean#L743),
[`MovingSofaBridge.GerverConstants.separatingResidual`](../../MovingSofaBridge/GerverConstants.lean#L747).*

The function $F$ is $Q / D$: both $Q$ and $D F$ equal $N J - D Z$.

### Lemma A.11 (the residuals and their derivatives)

1. Every solution has $F(\varphi, \theta) = 0$ and $H(\varphi, \theta) = 0$.
2. On $\Delta$, with $M = 3\sin\theta + \sin\varphi - 2k\cos\varphi$,

   ```math
   \begin{aligned}
   \partial_\varphi \hat A &= 1 + \frac{3\hat A\sin\varphi}{D}, & \partial_\theta \hat A &= \frac{C\sin\theta}{D}, \\
   \partial_\varphi \hat B &= \frac{3k\hat A\sin\varphi}{D} - \frac{\hat A + 1}2, & \partial_\theta \hat B &= \frac{kC\sin\theta}{D} - \frac C2, \\
   \partial_\varphi F &= -\hat B\cos\varphi + \frac{\hat A\sin\varphi\,(3\cos\varphi + \cos\theta - 6k\sin\varphi)}{2D}, & \partial_\theta F &= C \Bigl(\frac{J\sin\theta}{D} + \frac{\sin\varphi}2\Bigr), \\
   \partial_\varphi G &= \frac{3\hat A M\sin\varphi}{D} + 2\hat A\cos\varphi + 2\hat B\sin\varphi, & \partial_\theta G &= C\,T, \quad T = \frac{M\sin\theta}{D} + \cos\varphi - 3\cos\theta,
   \end{aligned}
   ```

   and
   $D\,T = 3 + 3\cos^2\varphi + \sin\varphi\sin\theta - 10\cos\varphi\cos\theta - 2k\cos\varphi\sin\theta$.

*Lean:
[`MovingSofaBridge.GerverConstants.Spec.residuals_zero`](../../MovingSofaBridge/GerverConstants.lean#L775),
[`MovingSofaBridge.GerverConstants.firstResidual_phi_deriv`](../../MovingSofaBridge/GerverConstants.lean#L820),
[`MovingSofaBridge.GerverConstants.firstResidual_theta_deriv`](../../MovingSofaBridge/GerverConstants.lean#L831),
[`MovingSofaBridge.GerverConstants.secondResidual_phi_deriv`](../../MovingSofaBridge/GerverConstants.lean#L841),
[`MovingSofaBridge.GerverConstants.secondResidual_theta_deriv`](../../MovingSofaBridge/GerverConstants.lean#L855),
[`MovingSofaBridge.GerverConstants.secondThetaFactor_identity`](../../MovingSofaBridge/GerverConstants.lean#L872).*

*Proof.* (1) At a solution $A = \hat A$ and $B = \hat B$ (Lemma A.3), so $F = E_3 = 0$ and
$G = E_2 = 0$. (2) The quotient and product rules, with $\partial_\varphi N = D$,
$\partial_\theta N = (1 - g)\sin\theta$, $\partial_\varphi D = -3\sin\varphi$,
$\partial_\theta D = \sin\theta$, $\partial_\varphi k = -\tfrac12$, $\partial_\theta k = \tfrac12$,
$\partial_\varphi o = -k - \tfrac12$ and $\partial_\theta o = \tfrac12(g - 1)$. For instance

```math
\partial_\theta \hat A = \frac{(1 - g)\sin\theta \cdot D - N\sin\theta}{D^2} = \frac{(1 - g - \hat A)\sin\theta}{D} = \frac{C\sin\theta}D ,
```

and the factor $C$ passes to the $\theta$-derivatives of $\hat B$, $F$ and $G$. The formula for
$D\,T$ uses $\sin^2\theta + \cos^2\theta = 1$. $\square$

![The strip 0 ≤ φ ≤ 1/20, φ ≤ θ ≤ π/4, stretched horizontally. The zero set of F (blue) rises from the origin to the top edge, with F positive to its left; the zero set of H (orange) falls from the top edge to the right edge, with H positive below it. They cross at one point, Gerver's angles (φ, θ)](figures/appendix-a/zero-sets.svg)

*Figure A.2.* The strip $0 \le \varphi \le 1/20$, $\varphi \le \theta \le \pi/4$, stretched
horizontally fourteen times. The zero set of $F$ (blue) rises from the origin to the top edge; the
zero set of $H$ (orange) falls from the top edge, at $\varphi = 0.0143\ldots$, to the right edge, at
$\theta = 0.6533\ldots$. They cross once, at Gerver's angles. The zero set of $G$ alone (not drawn)
rises, from $\theta = 0.6628\ldots$ at $\varphi = 0$ to $\theta = 0.6901\ldots$ at $\varphi = 1/20$,
like that of $F$; adding $\tfrac9{10} F$ tilts it so that it falls.

## A.7 Bounds on the strip

### Lemma A.12 (bounds on the strip)

On the strip $\Delta_{1/20} = \lbrace 0 \le \varphi \le 1/20,\ \varphi \le \theta \le \pi/4 \rbrace$
the bounds of Table A.1 hold.

| Quantity | Bound | Reason |
| --- | --- | --- |
| $\sin\varphi$, $\cos\varphi$ | $[0, \tfrac1{20}]$, $[0.998, 1]$ | $\sin\varphi \le \varphi$; $\cos\varphi \ge 1 - \tfrac12 \varphi^2 \ge 1 - \tfrac1{800}$ |
| $\sin\theta$, $\cos\theta$ | $[0, \tfrac45]$, $[\tfrac7{10}, 1]$ | $\theta \le \tfrac\pi4 < \tfrac45$; $\cos\theta \ge \cos\tfrac\pi4 = \tfrac{\sqrt2}2$ |
| $\cos\theta + \sin\theta$ | $\ge 1$ | its square is $1 + 2\sin\theta\cos\theta$ |
| $k = 1 + \tfrac12 g$ | $[1, \tfrac75]$ | $0 \le g \le \tfrac45$ |
| $D$ | $[1.99, 2.3]$ | $3 \cdot 0.998 - 1$ and $3 - 0.7$ |
| $N$ | $[0, \tfrac3{10}]$ | see the proof |
| $\hat A = N / D$ | $[0, \tfrac4{25}]$ | $0.3 / 1.99 = 0.1507\ldots$ |
| $o$ | $[\tfrac7{10}, \tfrac85]$ | $o \ge \tfrac{3\pi}8 - \tfrac32\varphi \ge 1.05$; $o \le \tfrac\pi2 - 2\varphi$ |
| $\hat B = \hat A k + o$ | $[\tfrac7{10}, 2]$ | $\tfrac4{25} \cdot \tfrac75 + \tfrac85 = 1.824$ |
| $J = \cos\varphi - k\sin\varphi$ | $[\tfrac9{10}, 1]$ | $0.998 - \tfrac75 \cdot \tfrac1{20} = 0.928$ |
| $C = 1 - \hat A - g$ | $> 0$ | $1 - \tfrac4{25} - \tfrac45 = \tfrac1{25}$ |

*Table A.1.* Bounds on the strip $\Delta_{1/20}$.

*Lean:
[`MovingSofaBridge.GerverConstants.smallBounds`](../../MovingSofaBridge/GerverConstants.lean#L983),
[`MovingSofaBridge.GerverConstants.SmallBounds`](../../MovingSofaBridge/GerverConstants.lean#L969),
[`MovingSofaBridge.GerverConstants.num_nonneg`](../../MovingSofaBridge/GerverConstants.lean#L950),
[`MovingSofaBridge.GerverConstants.baseNumerator_le`](../../MovingSofaBridge/GerverConstants.lean#L934).*

*Proof.* *The numerator.* $N(\varphi, \cdot)$ has the derivative $(1 - g)\sin\theta \ge 0$ on
$[\varphi, \pi/4]$, and $N(\varphi, \varphi) = 2\sin\varphi + 1 - \cos\varphi \ge 0$; so $N \ge 0$.
For the upper bound, $N = b(\theta) - \varphi\cos\theta + 3\sin\varphi$ with
$b(t) = (t - 1)\cos t - \sin t + 1$. The difference $(\tfrac12 t^2 - \tfrac13 t^3) - b(t)$ vanishes
at $0$ and has the derivative $(1 - t)(t - \sin t) \ge 0$ on $[0, 4/5]$, and
$\tfrac12 t^2 - \tfrac13 t^3$ increases there to $\tfrac{56}{375} < \tfrac3{20}$ at $t = 4/5$; so
$N \le \tfrac3{20} + \tfrac3{20}$.

*The offset.* With $\theta = \varphi + g$, $o = \tfrac\pi2 - 2\varphi - \tfrac12 g + \tfrac14 g^2$.
As $g \le \pi/4 - \varphi$, $o \ge \tfrac{3\pi}8 - \tfrac32\varphi \ge 1.125 - 0.075$; as
$g^2 \le 2g$, $o \le \tfrac\pi2 - 2\varphi < 1.6$.

The other bounds follow from these, as Table A.1 indicates. $\square$

The true ranges are narrower: on a grid of the strip, $\hat A \le 0.112$,
$1.391 \le \hat B \le 1.571$ and $C \ge 0.152$. The proof needs only the cruder bounds.

## A.8 The signs of the partial derivatives

### Lemma A.13 (signs on the strip)

On $\Delta_{1/20}$,

```math
\partial_\varphi F \le -\tfrac23, \qquad 0 \le \partial_\theta F \le \tfrac12 C, \qquad \partial_\varphi G \le \tfrac35, \qquad \partial_\theta G \le -\tfrac23 C .
```

Hence $\partial_\varphi H \le 0$ and $\partial_\theta H < 0$.

*Lean:
[`MovingSofaBridge.GerverConstants.SmallBounds.firstPhi_le`](../../MovingSofaBridge/GerverConstants.lean#L1074),
[`MovingSofaBridge.GerverConstants.SmallBounds.firstThetaFactor_bounds`](../../MovingSofaBridge/GerverConstants.lean#L1094),
[`MovingSofaBridge.GerverConstants.SmallBounds.secondPhi_le`](../../MovingSofaBridge/GerverConstants.lean#L1107),
[`MovingSofaBridge.GerverConstants.SmallBounds.secondThetaFactor_le`](../../MovingSofaBridge/GerverConstants.lean#L1130),
[`MovingSofaBridge.GerverConstants.SmallBounds.separating_signs`](../../MovingSofaBridge/GerverConstants.lean#L1156).*

*Proof.* All bounds come from Table A.1, with $C > 0$ and Lemma A.11.

1. $\partial_\varphi F$. Here $\hat A\sin\varphi \le \tfrac4{25} \cdot \tfrac1{20} = \tfrac1{125}$
   and $3\cos\varphi + \cos\theta - 6k\sin\varphi \le 4$, so the second term is at most
   $\tfrac4{125} / (2 \cdot 1.99) < \tfrac1{100}$; and
   $\hat B\cos\varphi \ge 0.7 \cdot 0.998 = 0.6986$. So
   $\partial_\varphi F \le -0.6986 + 0.01 < -\tfrac23$.
2. $\partial_\theta F = C\,(J\sin\theta / D + \tfrac12\sin\varphi)$, and
   $0 \le J\sin\theta / D \le 0.8 / 1.99 < \tfrac9{20}$ and $\tfrac12\sin\varphi \le \tfrac1{40}$,
   so the bracket lies in $[0, \tfrac12]$.
3. $\partial_\varphi G$. Here $M \le 3 \cdot \tfrac45 + \tfrac1{20} \le \tfrac52$, so
   $3\hat A M\sin\varphi / D \le (3 \cdot \tfrac1{125} \cdot \tfrac52) / 1.99 < \tfrac1{25}$;
   $2\hat A\cos\varphi \le \tfrac8{25}$ and $2\hat B\sin\varphi \le \tfrac15$. So
   $\partial_\varphi G \le \tfrac{14}{25} < \tfrac35$.
4. $\partial_\theta G = C\,T$. With $10\cos\varphi\cos\theta \ge 9.98\cos\theta$,
   $2k\cos\varphi\sin\theta \ge 1.996\sin\theta$ and
   $\sin\varphi\sin\theta \le \tfrac1{20}\sin\theta$,

   ```math
   D\,T \le 6 - \bigl(9.98\cos\theta + 1.946\sin\theta\bigr) = 6 - 1.946(\cos\theta + \sin\theta) - 8.034\cos\theta \le 6 - 1.946 - 8.034 \cdot 0.7 = -1.5698,
   ```

   so $T \le -1.5698 / 2.3 = -0.6825\ldots < -\tfrac23$.
5. $H$. By (1) and (3), $\partial_\varphi H \le \tfrac35 - \tfrac9{10} \cdot \tfrac23 = 0$; by (2)
   and (4),
   $\partial_\theta H \le C\,\bigl(-\tfrac23 + \tfrac9{10} \cdot \tfrac12\bigr) = -\tfrac{13}{60} C < 0$.
   $\square$

The weight $\tfrac9{10}$ is the one for which the bound $\tfrac35$ on $\partial_\varphi G$ and the
bound $-\tfrac23$ on $\partial_\varphi F$ cancel, while $-\tfrac23 + \tfrac9{10} \cdot \tfrac12$
stays negative. It tilts the zero set of $G$, which rises with $\varphi$, into one that falls
(Figure A.2).

## A.9 Uniqueness

*Proof of Theorem A.1.* Let $(A, B, \varphi, \theta)$ and $(A', B', \varphi', \theta')$ solve
Gerver's system. By Lemmas A.4 and A.9, $0 < \varphi < 1/20$, $\varphi < \theta \le \pi/4$, and the
same for $\varphi'$, $\theta'$; by Lemma A.11 (1), $F$ and $H$ vanish at $(\varphi, \theta)$ and at
$(\varphi', \theta')$. The segments used below lie in $\Delta_{1/20}$, where Lemma A.13 applies.

**Step 1. $\theta \ge \theta'$.** Suppose $\theta < \theta'$ (Figure A.3). As $F(\varphi, \cdot)$
does not decrease on $[\varphi, \pi/4]$, $F(\varphi, \theta') \ge F(\varphi, \theta) = 0$. If
$\varphi' < \varphi$, then $F(\cdot, \theta')$ decreases strictly on $[0, \varphi]$, and
$F(\varphi', \theta') > F(\varphi, \theta') \ge 0$, against $F(\varphi', \theta') = 0$; so
$\varphi \le \varphi'$. As $H(\varphi, \cdot)$ decreases strictly on $[\varphi, \pi/4]$,
$H(\varphi, \theta') < H(\varphi, \theta) = 0$; and as $H(\cdot, \theta')$ does not increase on
$[0, \varphi']$, $H(\varphi', \theta') \le H(\varphi, \theta') < 0$, against
$H(\varphi', \theta') = 0$.

**Step 2. $\theta = \theta'$.** Step 1 with the two solutions exchanged gives $\theta' \ge \theta$.

**Step 3. $\varphi = \varphi'$.** $F(\cdot, \theta)$ decreases strictly on
$[0, \max(\varphi, \varphi')]$ and vanishes at $\varphi$ and at $\varphi'$.

**Step 4. $A = A'$ and $B = B'$**, by Lemma A.3. $\square$

![The stretched strip with the zero sets of F and H drawn faint. From Gerver's angles (φ, θ) an arrow rises to a higher level θ′, where F is positive and H negative. On the horizontal line at height θ′, F is positive left of φ (blue part) and H is negative right of φ (orange part), so no point of that line is a zero of both](figures/appendix-a/uniqueness.svg)

*Figure A.3.* Step 1 of the proof, drawn at Gerver's angles $(\varphi, \theta)$ and the level
$\theta' = 0.735$. Going up from $(\varphi, \theta)$, $F$ does not decrease and $H$ decreases, so at
$(\varphi, \theta')$, $F \ge 0$ and $H < 0$. Along the line at height $\theta'$, $F$ is positive
left of $\varphi$ (blue), and $H$ is negative from $\varphi$ on (orange): no point of the line is a
common zero.
