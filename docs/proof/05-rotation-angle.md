# 5. The rotation angle

[Contents](README.md) · [← 4. Balanced maximum sofas](04-balanced.md) · [6. The surface area measure →](06-surface-area.md)

This chapter shows that a moving sofa of maximum area may be assumed to turn through the full right
angle. Two results do this. A moving sofa of area at least $2.2$ admits a movement whose rotation
angle lies in $[\sec^{-1}(2.2), \pi/2]$ (Theorem 5.1; Baek, Theorem 1.5.1): turning the wrong way
or too little confines the sofa to a region of area $\sqrt2$ or $\sec \omega < 2.2$. And a balanced
maximum sofa of area at least $2.2$ whose rotation angle $\omega$ lies in this interval has a rotated
copy that turns through $\pi/2$ (Theorem 5.2; Baek, Theorem 1.5.2). With [Theorem 4.40](04-balanced.md#theorem-440-balanced-maximum-sofas-baek-theorem-356), every moving
sofa of area at least $2.2$ has area at most that of a balanced maximum sofa of rotation angle
$\pi/2$, which is how [Chapter 9](09-optimality.md) uses them (§5.5).

The proof of Theorem 5.2 follows Chapter 4 of Baek's paper. The cap of a balanced maximum sofa lies
in the parallelogram $P_\omega$, and the main step shows that the sofa avoids the small triangle
$\Delta_\omega$ at the corner $O$ of $P_\omega$ (Theorem 5.13; Baek, Theorem 4.2.5). Then the sofa has
width at most one in every direction $u_t$, $t \in [\omega, \pi/2]$, that it has not turned through,
so it can first turn by $\pi/2 - \omega$ inside the horizontal side of the hallway (Lemma 5.14). To
find $\Delta_\omega$ in the niche, the area bound $\lvert K \rvert \ge 2.2$ gives a corner $q_0$ of the
cap far from $O$ on the $x$-axis, a right triangle with hypotenuse one gives a lower bound $g$ for the
bottom side of the sofa, balance moves this bound to the top side (§5.2), and the supporting hallway
of angle $\pi/2 - \omega$ through the two points found encloses $\Delta_\omega$ (Figure 5.6).

## 5.1 A first bound on the rotation angle

A movement $\Phi_s(p) = R_{\theta(s)}\, p + c(s)$ of a moving sofa ([Chapter 2](02-preliminaries.md))
has *rotation angle* $\omega$ if $\theta(1) = -\omega$: the sofa turns clockwise by $\omega$ on its way
from $H_L$ to $V_L$. Write $\sec^{-1}(2.2) = \arccos(1/2.2) = 1.0989$, about $62.96°$.

### Theorem 5.1 (a first bound on the rotation angle; Baek, Theorem 1.5.1)

Every moving sofa $S$ with $\lvert S \rvert \ge 2.2$ admits a movement with a rotation angle
$\omega \in [\sec^{-1}(2.2), \pi/2]$.

*Lean: [`theorem1_5_1`](../../MovingSofaOptimality/Intro/RotationAngleBound.lean#L163), [`arcsec22`](../../MovingSofaOptimality/Intro/RotationAngleBound.lean#L23).*

![Two panels. Left: a horizontal strip H between two grey lines, crossed by a hallway turned clockwise by 45 degrees, drawn as green walls forming a sideways V opening to the left; the part of the strip inside the hallway is blue, and a horizontal segment across it is marked with its length root 2. Right: the same strip crossed by a green strip slanted by the angle omega = 1; their intersection, a blue parallelogram, has its base on the lower line marked sec omega](figures/05-rotation-angle/two-bounds.svg)

*Figure 5.1.* The two area bounds. Left: every horizontal line meets a hallway $L'$ turned by
$\pi/4$ (green) in a segment of length $\sqrt2$, so a sofa in a horizontal strip of width one and in
$L'$ has area at most $\sqrt2$. Right: a translate of $V_\omega$ meets the strip in a parallelogram of
base $\sec \omega$ and height one, here for $\omega = 1$.

*Proof.* Take a movement with rotation angle $\omega$. At the start $S + c(0) \subseteq H_L$, so $S$ lies
in a horizontal strip of width one.

*Case $\omega \le -\pi/4$.* Then $\theta$ runs from $0$ to $-\omega \ge \pi/4$, and by the
intermediate value theorem $\theta(s) = \pi/4$ at some time $s$: $R_{\pi/4} S + c(s) \subseteq L$. So $S$
lies in the hallway $L' = R_{-\pi/4}(L - c(s))$, turned clockwise by $\pi/4$. In the coordinates
$(X, Y) = R_{\pi/4}\, p + c(s)$ of $L$, a horizontal line keeps $X - Y = k$ fixed, and the points of $L$
with $X - Y = k$ have $Y$ in the interval from $\min(0, -k)$ to $\min(1, 1 - k)$, of length one; as $x$
changes by $\sqrt2$ when $Y$ changes by one, every horizontal line meets $L'$ in a segment of length
$\sqrt2$ (Figure 5.1, left). By Cavalieri's principle $\lvert S \rvert \le \sqrt2 < 2.2$.

*Case $\lvert \omega \rvert < \sec^{-1}(2.2)$.* At the end $R_{-\omega} S + c(1) \subseteq V_L$, so $S$
lies in a translate of $V_\omega = R_\omega V$, which meets every horizontal line in a segment of length
$\sec \omega$ (Figure 5.1, right). So $\lvert S \rvert \le \sec \omega < 2.2$, since
$\cos \omega > \cos(\sec^{-1}(2.2)) = 1/2.2$.

Since $\sec^{-1}(2.2) > \pi/4$, the two cases contradict $\lvert S \rvert \ge 2.2$ whenever
$\omega < \sec^{-1}(2.2)$. If $\omega \le \pi/2$ we are done. If $\omega > \pi/2$, the intermediate
value theorem gives a time $s_0$ with $\theta(s_0) = -\pi/2$. Stop the movement there. The rotation
$R_{-\pi/2}$ turns second coordinates into first ones, so the first coordinates of
$R_{-\pi/2} S + c(s_0)$ are, up to a common shift, the second coordinates of $S + c(0) \subseteq H_L$,
which lie in $[0, 1]$. So a horizontal translation takes the sofa into
$V_L = [0, 1] \times (-\infty, 1]$. Each point moves along a horizontal line from a point of $L$ to a
point of $V_L$, and $L$ meets every horizontal line in an interval, so the sofa stays in $L$. This
movement has rotation angle $\pi/2$. $\square$

Gerver's version of this argument gives the bound $\pi/3$ of his Theorem 1
([§4.1](04-balanced.md#41-gervers-balancing-argument-and-its-gap)). The constant $2.2$
is below the area $2.2195$ of Gerver's sofa, so the theorem applies to every moving sofa of
maximum area.

### Theorem 5.2 (the right angle; Baek, Theorem 1.5.2)

Let $S_\omega$ be a balanced maximum sofa with $\lvert S_\omega \rvert \ge 2.2$ and rotation angle
$\omega \in [\sec^{-1}(2.2), \pi/2]$. Then the rotated copy $R_{\pi/2 - \omega}\, S_\omega$ admits a movement
with rotation angle $\pi/2$.

*Lean: [`theorem1_5_2`](../../MovingSofaOptimality/Angle/RightAngle.lean#L1031).*

The proof is in §5.5; §5.2 to §5.4 prepare it.

## 5.2 Horizontal side lengths

For a cap $K$ with rotation angle $\omega$ and $t \in (0, \omega)$, recall from
[Chapter 3](03-monotone.md) the ends $W_K(t) = b_K(t) \cap l(\pi/2, 0)$ and
$Z_K(t) = d_K(t) \cap l(\omega, 0)$ of the wedge $T_K(t)$ on the bottom of the fan, and the wedge gaps

```math
w_K(t) = \bigl(A^-_K(0) - W_K(t)\bigr) \cdot u_0 > 0 , \qquad z_K(t) = \bigl(C^+_K(\omega) - Z_K(t)\bigr) \cdot v_\omega > 0 .
```

### Definition 5.3 (wedge gap infima; Baek, Definition 4.1.1)

For a cap $K$ with rotation angle $\omega$, $w^\circ_K = \inf_{t \in (0, \omega)} w_K(t)$ and
$z^\circ_K = \inf_{t \in (0, \omega)} z_K(t)$.

*Lean: [`wedgeGapWInf`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L34), [`wedgeGapZInf`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L37), [`wedgeGapW`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L67), [`wedgeGapZ`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L70).*

### Lemma 5.4 (continuity of the wedge gap; Baek, Lemma 4.1.1)

Let $\omega < \pi/2$, and let $K, K'$ be caps with rotation angle $\omega$ and Hausdorff distance
$\varepsilon = d_\mathrm{H}(K, K')$. Then $\lvert w^\circ_K - w^\circ_{K'} \rvert \le (1 + \sec \omega)\, \varepsilon$.

*Proof.* $W_K(t) = ((h_K(t) - 1)/\cos t, 0)$, and $\lvert h_K(t) - h_{K'}(t) \rvert \le \varepsilon$, so the
first coordinates of $W_K(t)$ and $W_{K'}(t)$ differ by at most $\varepsilon \sec t \le \varepsilon \sec \omega$
for $t \in (0, \omega)$. As $\omega < \pi/2$, $A^-_K(0) = (h_K(0), 0)$, so these points differ by at most
$\varepsilon$. Hence $\lvert w_K(t) - w_{K'}(t) \rvert \le (1 + \sec \omega)\, \varepsilon$ for every $t$,
and the infima differ by at most as much. $\square$

*Lean: [`lemma4_1_1`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L413).*

The same holds for $z^\circ$, by the mirror image or the same argument on $l(\omega, 0)$.

### Theorem 5.5 (horizontal sides of maximum polygon caps; Baek, Theorem 4.1.2)

Let $K$ be a maximum polygon cap with an angle set $\Theta$ of rotation angle $\omega < \pi/2$. Then
$w^\circ_K \le \sigma_K(\pi/2)$ and $z^\circ_K \le \sigma_K(\omega)$.

*Proof.* We prove the first inequality; the second is the same argument on the line $l(\omega, 0)$,
or the first for the mirror image
([Lemma 4.21](04-balanced.md#lemma-421-mirror-image-baek-lemma-341)). For $t \in \Theta$ the segment $s_t$ from $W_K(t)$ to
$A^-_K(0)$, of length $w_K(t)$, lies on the right of the wall $b_K(t)$ and so avoids the wedge
$T_K(t)$ (Figure 5.2). The bottom side $e_K(3\pi/2)$ runs from $O$ to $A^-_K(0)$; its length $h_K(0)$ is the limit
of $w_K(t)$ as $t \to \omega$, since $W_K(t) \to l(\omega, 0) \cap l(\pi/2, 0) = O$. So the segment

```math
s = e_K(3\pi/2) \cap \bigcap_{t \in \Theta} s_t ,
```

which ends at $A^-_K(0)$, has length at least $w^\circ_K$ and avoids
$\mathcal{N}_\Theta(K) = \bigcup_{t \in \Theta} T_K(t)$. By
[Lemma 4.27](04-balanced.md#lemma-427-sides-of-the-polygon-niche-baek-lemma-345) (2) the niche covers a length
$\sigma_K(3\pi/2) - \tau_K(\pi/2)$ of $e_K(3\pi/2)$, so

```math
w^\circ_K + \sigma_K(3\pi/2) - \tau_K(\pi/2) \le \sigma_K(3\pi/2) ,
```

that is, $w^\circ_K \le \tau_K(\pi/2)$. Since $K$ is balanced
([Theorem 4.31](04-balanced.md#theorem-431-maximum-polygon-caps-are-balanced-baek-theorem-349)),
$\tau_K(\pi/2) = \sigma_K(\pi/2)$. $\square$

*Lean: [`theorem4_1_2`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L656).*

![A blue polygon cap with rotation angle 1.3 between the x-axis and the line y = 1, with an orange niche near the origin O. Three orange ticks on the x-axis mark the ends W_K(t) of the wedges; below the axis, three black bars run from each tick to the corner A at the right end of the bottom side. The part of the bottom side from the rightmost tick to A is thick green, and so is the top side of the cap; the two green segments have the same length](figures/05-rotation-angle/horizontal-side.svg)

*Figure 5.2.* Theorem 5.5 for the maximum polygon cap with $\omega = 1.3$ and the uniform angle set
with four intervals, computed numerically. The niche (orange) ends on the $x$-axis before every
$W_K(t)$, $t \in \Theta$ (ticks), so the bottom side keeps a free part at least as long as the gaps
$w_K(t)$ (bars). This free part (green) has the length $\tau_K(\pi/2)$ of the top side (green), by
balance.

### Theorem 5.6 (horizontal sides of balanced maximum caps; Baek, Theorem 4.1.4)

For $\omega < \pi/2$, every balanced maximum cap $K$ with rotation angle $\omega$ satisfies
$w^\circ_K \le \sigma_K(\pi/2)$ and $z^\circ_K \le \sigma_K(\omega)$.

*Proof.* Let $K_i \to K$ be the maximum polygon caps of
[Definition 4.33](04-balanced.md#definition-433-balanced-maximum-cap-baek-definitions-351352). By Lemma 5.4,
$w^\circ_{K_i} \to w^\circ_K$, and $w^\circ_{K_i} \le \sigma_{K_i}(\pi/2)$ by Theorem 5.5. It remains to see
that edge lengths are upper semicontinuous: $\limsup_i \sigma_{K_i}(t) \le \sigma_K(t)$. The paper
deduces this from the weak convergence of surface area measures (Baek's Theorem 4.1.3, Schneider's
Theorem 4.2.1 [7]), which [Chapter 6](06-surface-area.md) proves. The formalization proves it
directly: for every convex body $K$ and $\delta \in (0, \pi)$,

```math
\sigma_K(t) \sin\delta \le h_K(t + \delta) + h_K(t - \delta) - 2 h_K(t) \cos\delta ,
```

because $v^\pm_K(t) = h_K(t)\, u_t + a_\pm v_t$ with $a_+ - a_- = \sigma_K(t)$, and
$v^+_K(t) \cdot u_{t + \delta} \le h_K(t + \delta)$, $v^-_K(t) \cdot u_{t - \delta} \le h_K(t - \delta)$. The
right side is continuous in $K$, so the inequality passes to the limit along $K_i$, and divided by
$\sin\delta$ it tends to $\sigma_K(t)$ as $\delta \to 0^+$. The same argument gives the bound for
$z^\circ_K$. $\square$

*Lean: [`theorem4_1_4`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L1264), [`ang_le_sigmaAt_of_tendsto`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L1244), [`ang_sigmaAt_mul_sin_le`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L695).*

## 5.3 The triangle at the corner

From here on $\omega \in [\sec^{-1}(2.2), \pi/2)$, so $\omega > \pi/4$.

### Proposition 5.7 (the corner of the parallelogram; Baek, Proposition 4.2.1)

For $\omega \in [0, \pi/2)$ let $c_\omega = \tan((\pi/2 - \omega)/2)$. Then
$o_\omega - v_0 = c_\omega u_0$ and $o_\omega - u_\omega = c_\omega v_\omega$, the bottom side of $P_\omega$ is
the segment from $O$ to $(\sec \omega, 0)$, and $c_\omega = \sec \omega - \tan \omega$.

*Proof.* By the half-angle formula $c_\omega = (1 - \sin\omega)/\cos\omega = \sec\omega - \tan\omega$,
and $o_\omega = (c_\omega, 1)$, so $o_\omega - v_0 = (c_\omega, 0)$. The identity $c_\omega(1 + \sin\omega) =
\cos\omega$ gives $o_\omega - u_\omega = (c_\omega - \cos\omega, 1 - \sin\omega) = c_\omega(-\sin\omega, \cos\omega)$.
The bottom side is $\lbrace (x, 0) : 0 \le x \cos\omega \le 1 \rbrace$. $\square$

*Lean: [`proposition4_2_1`](../../MovingSofaOptimality/Angle/RightAngle.lean#L49), [`cOmega`](../../MovingSofaOptimality/Angle/RightAngle.lean#L38).*

Let $\Delta_\omega$ be the triangle with the vertices $O$, $o_\omega - v_0 = c_\omega u_0$ and
$o_\omega - u_\omega = c_\omega v_\omega$ (Figure 5.3). Its two sides at $O$ lie on the bottom sides of
$P_\omega$, and its third side cuts off the corner.

![The parallelogram P_omega for omega = 1.1, with vertices O, (sec omega, 0), o_omega and (-tan omega, 1), drawn in black. At O a small orange triangle Delta_omega has its other two vertices on the two bottom sides of the parallelogram, at o_omega - v_0 on the x-axis and o_omega - u_omega on the lower left side; dashed segments of length one join these two points to o_omega](figures/05-rotation-angle/parallelogram.svg)

*Figure 5.3.* The parallelogram $P_\omega$ for $\omega = 1.1$ and the triangle $\Delta_\omega$ (orange) at
its corner $O$. The dashed segments from $o_\omega$, of length one, end at $o_\omega - v_0 = c_\omega u_0$
and $o_\omega - u_\omega = c_\omega v_\omega$; here $c_\omega = 0.2398$.

### Definition 5.8 (the clipped parallelogram; Baek, Definitions 4.2.2–4.2.3)

For $\omega \in [\sec^{-1}(2.2), \pi/2)$ let $d_{\omega, \min} = 1.25$ if $\omega < \tan^{-1}(2.2)$ and
$d_{\omega, \min} = 1.1$ otherwise, where $\tan^{-1}(2.2) = 1.1442$. For $d \in [0, \tan\omega]$ let

```math
R_{\omega, d} = P_\omega \cap H_-(0, d + c_\omega) \cap H_-(\omega + \pi/2, d + c_\omega) .
```

*Lean: [`dMin`](../../MovingSofaOptimality/Angle/RightAngle.lean#L98), [`clippedRegion`](../../MovingSofaOptimality/Angle/RightAngle.lean#L101).*

The half-plane $H_-(0, d + c_\omega)$ cuts $P_\omega$ at distance $d$ beyond the vertex
$c_\omega u_0$ of $\Delta_\omega$, and $H_-(\omega + \pi/2, d + c_\omega)$ is its mirror image under
$M_\omega$ (Figure 5.4).

### Lemma 5.9 (the clipped parallelogram is small; Baek, Lemma 4.2.2)

For $\omega \in [\sec^{-1}(2.2), \pi/2)$, $\lvert R_{\omega, d_{\omega, \min}} \rvert < 2.2$.

![The parallelogram P_omega for omega = 1.1, dashed, with its two acute corners shaded grey: they are cut off by a vertical dashed line at distance d + c_omega from O, normal to the bottom side, and by its mirror image, a steep dashed line normal to the lower left side. The remaining hexagon R_omega,d is blue; a bar below the x-axis marks the distance d + c_omega from O](figures/05-rotation-angle/clipped.svg)

*Figure 5.4.* The region $R_{\omega, d}$ (blue) for $\omega = 1.1$ and $d = d_{\omega, \min} = 1.25$: the
parallelogram $P_\omega$ (dashed) without the two corner triangles (grey) beyond the lines at distance
$d + c_\omega$ from $O$, normal to its two bottom sides. Its area is $1.9446$.

*Proof.* The line $x = d + c_\omega$ cuts from the corner $(\sec\omega, 0)$ of $P_\omega$ a right triangle
with the leg $\sec\omega - d - c_\omega = \tan\omega - d$ on the $x$-axis and the angle $\pi/2 - \omega$ at
that corner, so of area $\frac12 (\tan\omega - d)^2 \cot\omega$; its mirror image is cut from the
opposite corner. As $\lvert P_\omega \rvert = \sec\omega$, for $0 \le d \le \tan\omega$

```math
\lvert R_{\omega, d} \rvert = \sec\omega - (\tan\omega - d)^2 \cot\omega = c_\omega + 2d - d^2 \cot\omega .
```

The formalization proves the inequality $\le$, by horizontal slices, which suffices. Here
$\tan\omega \ge \tan(\sec^{-1}(2.2)) = \sqrt{96}/5 = 1.9596$, so $d_{\omega, \min} \le \tan\omega$.

If $\omega < \tan^{-1}(2.2)$, then $\cot\omega > 1/2.2$, and $c_\omega$, which decreases in $\omega$, is
at most $c_{\sec^{-1}(2.2)} = 2.2 - \sqrt{96}/5 = 0.2404$. So
$\lvert R_{\omega, 1.25} \rvert < 0.2405 + 2.5 - 1.5625/2.2 = 2.0303$.

If $\omega \ge \tan^{-1}(2.2)$, then $\lvert R_{\omega, 1.1} \rvert = 2.2 + c_\omega - 1.21 \cot\omega$, and
$c_\omega < 1.21 \cot\omega$: multiplying by $\sin\omega\cos\omega$ and dividing by $1 - \sin\omega > 0$,
this is $\sin\omega < 1.21\,(1 + \sin\omega)$. $\square$

*Lean: [`lemma4_2_2`](../../MovingSofaOptimality/Angle/RightAngle.lean#L304).*

Baek's proof bounds the first case by $\sqrt{146}/5 - (\sqrt{96}/5 - 1.25)^2/2.2 = 2.1877$, and the
second by splitting $R_{\omega, 1.1}$ into a quadrilateral and two pieces of rectangles; the formula
above treats both cases alike.

### Lemma 5.10 (two convex functions; Baek, Lemma 4.2.3)

For every $d \ge 1$, the functions $(1 - d\cot\omega)^2$ and $\cos^2\omega$ are convex on
$[\pi/4, \pi/2]$.

*Proof.* The second derivative of the first function is

```math
\frac{d^2}{d\omega^2} (1 - d\cot\omega)^2 = 2d \csc^4\omega \,\bigl(2d + d\cos 2\omega - \sin 2\omega\bigr) \ge 2d\csc^4\omega\, (d - 1) \ge 0 ,
```

and that of $\cos^2\omega = (1 + \cos 2\omega)/2$ is $-2\cos 2\omega \ge 0$ on $[\pi/4, \pi/2]$. $\square$

*Lean: [`lemma4_2_3`](../../MovingSofaOptimality/Angle/RightAngle.lean#L335).*

### Definition 5.11 (the points q0 and q1; Baek, Definition 4.2.4)

For $\omega \in [\sec^{-1}(2.2), \pi/2)$ and $d \in [d_{\omega, \min}, \tan\omega]$ let

```math
r_y = 1 - d\cot\omega , \qquad g = \sqrt{1 - r_y^2} , \qquad q_0 = o_\omega - v_0 + d\, u_0 , \qquad q_1 = o_\omega - g\, u_0 .
```

*Lean: [`calcRy`](../../MovingSofaOptimality/Angle/RightAngle.lean#L419), [`calcG`](../../MovingSofaOptimality/Angle/RightAngle.lean#L421), [`calcQ0`](../../MovingSofaOptimality/Angle/RightAngle.lean#L423), [`calcQ1`](../../MovingSofaOptimality/Angle/RightAngle.lean#L425).*

### Lemma 5.12 (two inequalities; Baek, Lemma 4.2.4)

Let $\omega \in [\sec^{-1}(2.2), \pi/2)$ and $d \in [d_{\omega, \min}, \tan\omega]$ with $r_y \ge 0$. Then

1. $(q_0 - (o_\omega - v_0)) \cdot u_{\pi/2 - \omega} > 1$;
2. $(q_1 - (o_\omega - u_\omega)) \cdot v_{\pi/2 - \omega} > 1$.

*Lean: [`lemma4_2_4`](../../MovingSofaOptimality/Angle/RightAngle.lean#L517).*

Baek's statement takes $\omega \in [\tan^{-1}(2.2), \pi/2)$, but its proof also treats the angles below
$\tan^{-1}(2.2)$, and Theorem 5.13 uses the lemma on all of $[\sec^{-1}(2.2), \pi/2)$; this is the range
stated here (REPORT.md, E9).

*Proof.* (1) The left side is $d\, u_0 \cdot u_{\pi/2 - \omega} = d\sin\omega \ge d_{\omega, \min}\sin\omega$,
and $\sin$ increases, so it is at least $1.25 \sin(\sec^{-1}(2.2)) = 1.1134$ for
$\omega < \tan^{-1}(2.2)$ and at least $1.1 \sin(\tan^{-1}(2.2)) = 1.0014$ otherwise.

(2) The left side is $(u_\omega - g\, u_0) \cdot v_{\pi/2 - \omega} = -\cos 2\omega + g\cos\omega$. Since
$1 + \cos 2\omega = 2\cos^2\omega$, the claim is $g > 2\cos\omega$, or, both sides being nonnegative,
$1 - r_y^2 > 4\cos^2\omega$. As $0 \le r_y \le 1 - d_{\omega, \min}\cot\omega$, it suffices that

```math
f(\omega) = (1 - d_{\omega, \min}\cot\omega)^2 + 4\cos^2\omega < 1 .
```

On each of $[\sec^{-1}(2.2), \tan^{-1}(2.2))$ and $[\tan^{-1}(2.2), \pi/2)$ the constant $d_{\omega, \min}$
is fixed, so $f$ is convex by Lemma 5.10 and lies below the chord of its endpoint values (Figure 5.5).
These are $0.9576$ and $0.8714$ on the first interval, and $0.9349$ and exactly $1$ at $\pi/2$ on the
second. On the second interval a convex function with value below $1$ at the left end and $1$ at the
right end is below $1$ inside, which proves the strict inequality on $[\tan^{-1}(2.2), \pi/2)$, a line
that the paper leaves out (REPORT.md, E9). $\square$

![A plot of f(omega) = (1 - d cot omega)^2 + 4 cos^2 omega against omega from sec^-1 2.2 to pi/2, with a dashed horizontal line at 1. The curve has two convex pieces: on the short first interval it falls from 0.9576 to 0.8714; at tan^-1 2.2 it jumps to 0.9349, then falls to a minimum near 0.76 and rises to exactly 1 at pi/2. Both pieces stay below the dashed line except at the right end](figures/05-rotation-angle/margin.svg)

*Figure 5.5.* The left side $f(\omega)$ of the inequality in the proof of Lemma 5.12 (2), with
$d = d_{\omega, \min}$: two convex pieces, for $d = 1.25$ and $d = 1.1$, below $1$ except at
$\omega = \pi/2$. The margin is smallest near $\pi/2$.

## 5.4 The triangle lies in the niche

### Theorem 5.13 (the triangle lies in the niche; Baek, Theorem 4.2.5)

Let $\omega \in [\sec^{-1}(2.2), \pi/2)$, and let $K$ be a balanced maximum cap with rotation angle
$\omega$ and $\mathcal{A}_\omega(K) \ge 2.2$. Then for some $t \in (0, \omega)$ the three points $O$,
$o_\omega - v_0$ and $o_\omega - u_\omega$ lie in the closure of $Q^-_K(t)$.

*Lean: [`theorem4_2_5`](../../MovingSofaOptimality/Angle/RightAngle.lean#L791).*

![The proof of the theorem for omega = 1.1. A blue cap inside the dashed parallelogram; on its bottom side the corner q0 at the right end, the point r above it on the slanted right side, and the point s to the left of q0, with a dashed green right triangle s, q0, r whose hypotenuse from s to r is labelled 1. Thick blue segments of length g run from s to q0 on the x-axis and from q1 to o_omega on the top side. A green hallway turned by pi/2 - omega has its outer walls through q0 and q1 and its inner corner inside the cap; the region of the fan below its inner walls is light orange and contains the orange triangle Delta_omega at the origin](figures/05-rotation-angle/consumed.svg)

*Figure 5.6.* The proof of Theorem 5.13 for $\omega = 1.1$, with a cap $K$ (blue) whose corner $q_0$ on
the $x$-axis lies at $d = 1.5$ from $o_\omega - v_0$. The right triangle $s, q_0, r$ (green, dashed)
has hypotenuse one and gives the length $g$ (thick blue, below); balance puts the point $q_1$ at the
same distance $g$ from $o_\omega$ on the top side (thick blue, above). The hallway of angle
$t = \pi/2 - \omega$ whose outer walls pass through $q_0$ and $q_1$ (green) has the triangle
$\Delta_\omega$ (orange) below both of its inner walls (light orange).

*Proof.* **Step 1: a long cap.** One of $h_K(0)$ and $h_K(\omega + \pi/2)$ is at least
$d_{\omega, \min} + c_\omega$. Otherwise $K \subseteq R_{\omega, d_{\omega, \min}}$, and
$\lvert K \rvert < 2.2$ by Lemma 5.9, while $\lvert K \rvert \ge \mathcal{A}_\omega(K) \ge 2.2$. The mirror
image $K^\mathrm{m}$ is a balanced maximum cap
([Proposition 4.34](04-balanced.md#proposition-434-mirror-image-baek-proposition-351)) with
$h_{K^\mathrm{m}}(0) = h_K(\omega + \pi/2)$, and the statement for $K^\mathrm{m}$ with the angle $t$ is the
statement for $K$ with the angle $\omega - t$, since $M_\omega$ permutes the three points; so we may
assume $h_K(0) \ge d_{\omega, \min} + c_\omega$. Let $d = h_K(0) - c_\omega \ge d_{\omega, \min}$. The corner
$q_0 = (h_K(0), 0) = A^-_K(0)$ of $K$ lies in $K \subseteq P_\omega$, so $h_K(0) \le \sec\omega$ and
$d \le \tan\omega$; by Proposition 5.7, $q_0 = o_\omega - v_0 + d\, u_0$ is the point of
Definition 5.11.

**Step 2: the bottom side.** The lines $l_K(0)$ and $l_K(\omega) = l(\omega, 1)$ meet at
$r = (h_K(0), r_y)$ with $r_y = 1 - d\cot\omega$, and $r_y \ge 0$ since $q_0 \in P_\omega$. Let
$s = q_0 - g\, u_0$ with $g = \sqrt{1 - r_y^2}$: the triangle $s, q_0, r$ has a right angle at $q_0$ and
$\lvert r - s \rvert = 1$. For $t \in (0, \omega)$ the cap lies in the wedge of the two half-planes
$H_-(0, h_K(0))$ and $H_-(\omega, 1)$ with apex $r$, and $u_t$ lies between $u_0$ and $u_\omega$, so
$h_K(t) \le r \cdot u_t$ and

```math
h_K(t) - 1 \le r \cdot u_t - (r - s) \cdot u_t = s \cdot u_t .
```

So $s$ is not in the open half-plane $H^\circ_-(t, h_K(t) - 1)$: it lies on or to the right of
$W_K(t)$, and $w_K(t) \ge g$. Hence $g \le w^\circ_K$.

**Step 3: the top side.** By Theorem 5.6, $g \le w^\circ_K \le \sigma_K(\pi/2)$. The point $o_\omega$ lies
in $K$ and is the right end of the top side $e_K(\pi/2)$, so $q_1 = o_\omega - g\, u_0$ lies on that side,
and $q_1 \in K$.

**Step 4: the hallway.** Let $t = \pi/2 - \omega$, which lies in $(0, \pi/4) \subseteq (0, \omega)$, and
$X = \lbrace q_0, q_1 \rbrace \subseteq K$. Then $h_X \le h_K$, so $Q^-_X(t) \subseteq Q^-_K(t)$. The vector
$q_1 - q_0 = v_0 - (d + g)\, u_0$, with $d + g \ge 1 > \tan t$, is $-\alpha u_t + \beta v_t$ with
$\alpha = (d + g)\cos t - \sin t \ge 0$ and $\beta = \cos t + (d + g)\sin t \ge 0$. So
$q_0 \cdot u_t \ge q_1 \cdot u_t$ and $q_1 \cdot v_t \ge q_0 \cdot v_t$: the point $q_0$ lies on the outer
wall $a_X(t)$ and $q_1$ on $c_X(t)$, and

```math
Q^-_X(t) = H^\circ_-(t, q_0 \cdot u_t - 1) \cap H^\circ_-(t + \pi/2, q_1 \cdot v_t - 1) .
```

**Step 5: the three points.** By Lemma 5.12 (1), $c_\omega u_0 \cdot u_t < q_0 \cdot u_t - 1$, and by
Lemma 5.12 (2), $c_\omega v_\omega \cdot v_t < q_1 \cdot v_t - 1$. As $c_\omega u_0 \cdot u_t = c_\omega\cos t > 0$
and $c_\omega v_\omega \cdot v_t = c_\omega \cos(\omega - t) > 0$, both right sides are positive, so $O$
satisfies both inequalities. The two remaining ones hold because $c_\omega u_0 \cdot v_t =
-c_\omega\sin t < 0$ and $c_\omega v_\omega \cdot u_t = -c_\omega \sin(\omega - t) < 0$. So the three
points lie in $Q^-_X(t) \subseteq Q^-_K(t)$. $\square$

The formal proof shows that the three points lie in $Q^-_K(t)$ itself. It treats the mirror case
through the bound $z^\circ_K \le \sigma_K(\omega)$ of Theorem 5.6 for $K$, in place of the bound for
$w^\circ$ of the mirror image.

## 5.5 The full right angle

### Lemma 5.14 (the width of the sofa)

Let $K$ be a cap with rotation angle $\omega \in (0, \pi/2)$ such that for some $t_0 \in (0, \omega)$ the
points $O$, $c_\omega u_0$ and $c_\omega v_\omega$ lie in the closure of $Q^-_K(t_0)$. Then

1. every point $a\, u_0 + b\, v_\omega$ with $a, b \ge 0$ and $a + b < c_\omega$ lies in $\mathcal{N}(K)$;
2. $(p - q) \cdot u_t \le 1$ for all $p \in K$, $q \in K \setminus \mathcal{N}(K)$ and $t \in [\omega, \pi/2]$.

*Proof.* (1) The closure of $Q^-_K(t_0)$ is $\lbrace p : p \cdot u_{t_0} \le \alpha,\ p \cdot u_{t_0 + \pi/2} \le
\beta \rbrace$ with $\alpha = h_K(t_0) - 1$ and $\beta = h_K(t_0 + \pi/2) - 1$. It contains $c_\omega u_0$, with
$c_\omega u_0 \cdot u_{t_0} = c_\omega \cos t_0 > 0$, so $\alpha > 0$, and likewise $\beta > 0$. The point
$a\, u_0 + b\, v_\omega$ is the combination of $O$, $c_\omega u_0$ and $c_\omega v_\omega$ with the weights
$1 - (a + b)/c_\omega > 0$, $a/c_\omega$ and $b/c_\omega$; since $O$ satisfies both inequalities strictly, so
does the combination, and it lies in $Q^-_K(t_0)$. It also lies in the fan $F_\omega$, since
$u_0 \cdot u_\omega$, $v_\omega \cdot u_\omega$, $u_0 \cdot u_{\pi/2}$, $v_\omega \cdot u_{\pi/2}$ are nonnegative.

(2) Write $q = a\, u_0 + b\, v_\omega$; as $q \in P_\omega$, $a = q \cdot u_\omega/\cos\omega \ge 0$ and
$b = q_y/\cos\omega \ge 0$, and $a + b \ge c_\omega$ by (1). For $t \in [\omega, \pi/2]$ both $\cos t$ and
$\sin(t - \omega)$ are nonnegative, so

```math
q \cdot u_t = a\cos t + b\sin(t - \omega) \ge c_\omega \min\bigl(\cos t, \sin(t - \omega)\bigr) ,
```

while $p \cdot u_t \le o_\omega \cdot u_t = c_\omega\cos t + \sin t$, as $o_\omega$ is the vertex of $P_\omega$
farthest in these directions. If $\cos t \le \sin(t - \omega)$, then $(p - q) \cdot u_t \le \sin t \le 1$.
Otherwise, using $c_\omega(1 + \sin\omega) = \cos\omega$ and $c_\omega\cos\omega = 1 - \sin\omega$,

```math
(p - q) \cdot u_t \le c_\omega\cos t + \sin t - c_\omega\sin(t - \omega) = \cos(t - \omega) \le 1 . \qquad \square
```

*Lean: [`ang_width_le_one`](../../MovingSofaOptimality/Angle/RightAngle.lean#L923), [`ang_mem_niche_of_small`](../../MovingSofaOptimality/Angle/RightAngle.lean#L854), [`ang_dot_le_oPt`](../../MovingSofaOptimality/Angle/RightAngle.lean#L905).*

So a sofa $K \setminus \mathcal{N}(K)$ as in the lemma lies in the pentagon $P_\omega \setminus \Delta_\omega$,
up to the far side of $\Delta_\omega$, whose width in the direction $u_t$, $t \in [\omega, \pi/2]$, is
$\max(\sin t, \cos(t - \omega)) \le 1$ (Figure 5.7). Baek's proof of Theorem 1.5.2 asserts this width
bound without proof (REPORT.md, E10). The full parallelogram $P_\omega$ has width
$c_\omega\cos t + \sin t$ there, more than one for $\omega < t < \pi/2$.

![Three rows, each a horizontal strip with a light grey floor between two dark lines. In each row the blue pentagon P_omega minus Delta_omega, for omega = 1.1, rests on the floor, turned counterclockwise by pi/2 - omega in the first row, by half of that in the second, and not at all in the third; in all three it fits between the lines. The triangle Delta_omega is drawn dashed in orange at its place: in the middle row it sticks out below the floor](figures/05-rotation-angle/rotate.svg)

*Figure 5.7.* The pentagon $P_\omega \setminus \Delta_\omega$ for $\omega = 1.1$ (blue), turned by
$\varphi = \pi/2 - \omega$, $(\pi/2 - \omega)/2$ and $0$, always fits in a horizontal strip of width one.
With the triangle $\Delta_\omega$ (orange, dashed) it would not: in the middle position the corner $O$
sticks out below the floor.

*Proof of Theorem 5.2.* If $\omega = \pi/2$ there is nothing to prove. Let $\omega < \pi/2$, and let
$K = \mathcal{C}(S_\omega)$, a balanced maximum cap, so that $S_\omega = K \setminus \mathcal{N}(K)$ and
$\mathcal{A}_\omega(K) = \lvert S_\omega \rvert \ge 2.2$ (Baek's Theorems 2.4.3 and 2.5.10, in
[Chapter 3](03-monotone.md)). By Theorem 5.13 and Proposition 5.7 the cap satisfies the hypothesis of
Lemma 5.14, so $S_\omega$ has width at most one in every direction $u_t$, $t \in [\omega, \pi/2]$. For
$\varphi \in [0, \pi/2 - \omega]$, the height of $R_\varphi S_\omega$ is the width of $S_\omega$ in the
direction $u_{\pi/2 - \varphi}$, with $\pi/2 - \varphi \in [\omega, \pi/2]$; so a translation depending
continuously on $\varphi$ puts $R_\varphi S_\omega$ into $H_L$, far enough to the left. The movement of
$R_{\pi/2 - \omega}\, S_\omega$ has three phases:

1. turn clockwise by $\pi/2 - \omega$ inside $H_L$, through the positions $R_\varphi S_\omega$ for
   $\varphi$ from $\pi/2 - \omega$ down to $0$;
2. translate within $H_L$, which is convex, to the initial position of the movement of $S_\omega$;
3. follow the movement of $S_\omega$, with rotation angle $\omega$.

The rotation angle of the whole movement is $(\pi/2 - \omega) + \omega = \pi/2$. $\square$

*Lean: [`theorem1_5_2`](../../MovingSofaOptimality/Angle/RightAngle.lean#L1031), [`ang_phase_one`](../../MovingSofaOptimality/Angle/RightAngle.lean#L973).*

**How the results are used.** Let $S$ be a moving sofa with $\lvert S \rvert \ge 2.2$. By Theorem 5.1 it
moves with some rotation angle $\omega \in [\sec^{-1}(2.2), \pi/2]$, so by [Theorem 4.40](04-balanced.md#theorem-440-balanced-maximum-sofas-baek-theorem-356) there is a
balanced maximum sofa $S_\omega$ with $\lvert S \rvert \le \lvert S_\omega \rvert$. Then
$\lvert S_\omega \rvert \ge 2.2$, and by Theorem 5.2 a rotated copy of $S_\omega$ moves with rotation angle
$\pi/2$; by Theorem 4.40 again, its area is at most that of a balanced maximum sofa
$S_{\pi/2} = K \setminus \mathcal{N}(K)$ of rotation angle $\pi/2$. So

```math
\lvert S \rvert \le \lvert S_\omega \rvert \le \lvert S_{\pi/2} \rvert = \mathcal{A}_{\pi/2}(K) ,
```

and [Chapter 9](09-optimality.md) bounds $\mathcal{A}_{\pi/2}(K)$ by the area of Gerver's sofa for this balanced maximum cap
$K$ (Lean: [`gm_area_le`](../../MovingSofaOptimality/Main.lean#L285)). A moving sofa of area less than $2.2$ is smaller than Gerver's sofa anyway.
