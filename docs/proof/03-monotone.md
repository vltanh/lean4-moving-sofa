# 3. Monotone sofas, caps and niches

[Contents](README.md) · [← 2. Preliminaries](02-preliminaries.md) · [4. Balanced maximum sofas →](04-balanced.md)

This chapter reduces the moving sofa problem with a fixed rotation angle $\omega \in (0, \pi/2]$ to
a problem about convex bodies. Let $S$ be a moving sofa with rotation angle $\omega$ in standard
position. Its *monotonization* $\mathcal{I}(S)$, the part of the parallelogram $P_\omega$ that lies
in all the supporting hallways $L_S(t)$, $t \in [0, \omega]$, is again a moving sofa with rotation
angle $\omega$, and it contains $S$
([Theorem 3.3](#theorem-33-monotonization-baek-theorem-232), Baek's Theorem 2.3.2). The hard step
is that $\mathcal{I}(S)$ is connected
([Theorem 3.8](#theorem-38-the-monotonization-is-connected-baek-theorem-236)). So a moving sofa of
maximum area may be taken *monotone*, equal to its own monotonization.

A monotone sofa is described by a convex body. Its *cap* $K$ is the part of $P_\omega$ below the
outer walls of the supporting hallways, and its *niche* $\mathcal{N}(K)$ is the part of the fan
$F_\omega$ that the inner corners of the supporting hallways carve out; the sofa is
$K \setminus \mathcal{N}(K)$
([Theorems 3.12](#theorem-312-the-monotonization-is-the-cap-minus-the-niche-baek-theorem-242) and
[3.13](#theorem-313-a-monotone-sofa-is-its-cap-minus-its-niche-baek-theorem-243)). A cap is the
cap of a monotone sofa exactly when it contains its niche
([Theorem 3.26](#theorem-326-the-caps-of-monotone-sofas-baek-theorem-259)), and then the sofa has
the area $\mathcal{A}_\omega(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$
([Theorem 3.29](#theorem-329-the-area-of-a-monotone-sofa-baek-theorem-2510)). The moving sofa
problem with rotation angle $\omega$ thus becomes the maximization of the sofa area functional
$\mathcal{A}_\omega$ over caps, which [Chapter 4](04-balanced.md) carries out. The notation is that
of [Chapter 2](02-preliminaries.md).

## 3.1 Monotonization

### Proposition 3.1 (standard position; Baek, Propositions 1.2.1 and 2.3.1)

Let $S$ be a moving sofa with rotation angle $\omega \in (0, \pi/2]$.

1. Some translate $S + v$ is in standard position; it is a moving sofa with rotation angle
   $\omega$.
2. If $\omega < \pi/2$, the vector $v$ is unique.
3. If $\omega = \pi/2$, it is unique up to horizontal translations: any two such vectors have the
   same second coordinate.
4. A moving sofa with rotation angle $\omega$ in standard position lies in $P_\omega$.

*Proof.* The sofa is compact ([Proposition 2.5](02-preliminaries.md#proposition-25-moving-sofas-are-compact)),
and $h_{S + v}(t) = h_S(t) + \langle v, u_t \rangle$
([Lemma 2.7](02-preliminaries.md#lemma-27-the-support-function)). So $S + v$ is in standard
position if and only if

```math
\langle v, u_\omega \rangle = 1 - h_S(\omega), \qquad v_2 = 1 - h_S(\pi/2) .
```

For $\omega < \pi/2$ the vectors $u_\omega$ and $u_{\pi/2} = (0, 1)$ are independent, since
$\cos\omega \ne 0$, and the system has exactly one solution. For $\omega = \pi/2$ the two equations
coincide, and their solutions are the vectors with $v_2 = 1 - h_S(\pi/2)$. A translate of a moving
sofa is a moving sofa with the same rotation angle. Finally, (4) is
[Proposition 2.15](02-preliminaries.md#proposition-215-the-sofa-in-its-own-frame-baek-proposition-122)
(1) and (3): $S \subseteq H \cap V_\omega = P_\omega$. $\square$

*Lean: [`proposition2_3_1_exists`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L140), [`proposition2_3_1_unique`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L163),
[`proposition2_3_1_unique_horizontal`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L184), [`proposition2_3_1_subset`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L196),
[`mpc_isMovingSofaWithAngle_translate`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L626).*

In the rest of this section, $S$ is a moving sofa with rotation angle $\omega \in (0, \pi/2]$ in
standard position.

### Definition 3.2 (monotonization and monotone sofa; Baek, Definitions 2.3.6 and 2.3.7)

The *monotonization* of $S$ is

```math
\mathcal{I}(S) = P_\omega \cap \bigcap_{t \in [0, \omega]} L_S(t) .
```

A *monotone sofa* with rotation angle $\omega \in (0, \pi/2]$ is a set of the form
$\mathcal{I}(S')$, for a moving sofa $S'$ with rotation angle $\omega$ in standard position.

*Lean: [`monotonization`](../../MovingSofaOptimality/Sofa/Defs.lean#L137), [`IsMonotoneSofa`](../../MovingSofaOptimality/Sofa/Defs.lean#L142).*

Gerver's sofa is a monotone sofa with rotation angle $\pi/2$: it is the part of the strip $H$ that
lies in all its supporting hallways (Figure 3.1), a fact that Baek's paper states without proof
(its Theorem 8.4.1) and that [Chapter 10](10-gerver.md) proves ([`theorem8_4_1_monotone`](../../MovingSofaOptimality/Gerver/Properties.lean#L74)).

![Gerver's sofa, in translucent blue, between the dashed lines y = 0 and y = 1 that bound the strip H, with seven of its supporting hallways, turned by 0, 15, 30, 45, 60, 75 and 90 degrees, each shaded in translucent grey with its walls drawn; the shading is darkest where all the hallways overlap, which is the sofa](figures/03-monotone/intersection.svg)

*Figure 3.1.* Gerver's sofa $G$ is the part of the strip $H = P_{\pi/2}$ that lies in all its
supporting hallways $L_G(t)$, $t \in [0, \pi/2]$; seven of them are drawn. The outer walls touch
the top and the rounded ends of $G$, and the inner corners trace the arch of its niche.

### Theorem 3.3 (monotonization; Baek, Theorem 2.3.2)

$\mathcal{I}(S)$ is a moving sofa with rotation angle $\omega$, in standard position, and
$S \subseteq \mathcal{I}(S)$.

*Lean: [`theorem2_3_2`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L408).*

*Outline of the proof.* The inclusion is Proposition 3.4. The supporting hallways of
$\mathcal{I}(S)$ are those of $S$ (Lemma 3.7), and the movement of the hallways $L_S(t)$, read in
the frame of the hallway, moves $\mathcal{I}(S)$ through $L$. What needs a proof is that
$\mathcal{I}(S)$ is connected (Theorem 3.8); this gap is in the earlier derivations of Gerver's
sofa, which identify a maximum sofa with such an intersection without proving it connected
(Baek, §1.2). The proof is at the end of this section.

Since $\lvert \mathcal{I}(S) \rvert \ge \lvert S \rvert$, a moving sofa of maximum area with
rotation angle $\omega$ may be replaced by a monotone sofa.

### Proposition 3.4 (the sofa lies in its monotonization; Baek, Proposition 2.3.3)

$S \subseteq \mathcal{I}(S)$.

*Proof.* $S \subseteq P_\omega$ by Proposition 3.1 (4). For $t \in [0, \omega]$, $S$ lies in a
translate of $R_t(L)$ by
[Proposition 2.15](02-preliminaries.md#proposition-215-the-sofa-in-its-own-frame-baek-proposition-122)
(2), hence in $L_S(t)$ by
[Proposition 2.20](02-preliminaries.md#proposition-220-the-supporting-hallway-contains-the-sofa-baek-proposition-223).
$\square$

*Lean: [`proposition2_3_3`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L202).*

### Definition 3.5 (the region below the outer walls; Baek, Definitions 2.3.8, 2.3.10 and 2.3.11)

Let

```math
\mathcal{C}(S) = P_\omega \cap \bigcap_{t \in [0, \omega]} Q_S^+(t), \qquad J_\omega = [0, \omega] \cup [\pi/2, \omega + \pi/2] .
```

A set $X$ is *closed in the direction* of a vector $w$ if $x + \lambda w \in X$ for every $x \in X$
and $\lambda \ge 0$.

*Lean: [`capOf`](../../MovingSofaOptimality/Sofa/Defs.lean#L159), [`jSet`](../../MovingSofaOptimality/Sofa/Defs.lean#L162), [`ClosedInDirection`](../../MovingSofaOptimality/Sofa/Defs.lean#L147).*

By [Proposition 2.19](02-preliminaries.md#proposition-219-the-parts-of-the-supporting-hallway-baek-proposition-222),
$Q_S^+(t) = H_S(t) \cap H_S(t + \pi/2)$, so $\mathcal{C}(S) = P_\omega \cap \bigcap_{s \in J_\omega} H_S(s)$:
the angles of $J_\omega$ are the normal angles of the outer walls $a_S(t)$ and $c_S(t)$,
$t \in [0, \omega]$.

### Proposition 3.6 (Baek, Proposition 2.3.4)

$S \subseteq \mathcal{I}(S) \subseteq \mathcal{C}(S)$. Moreover $\mathcal{C}(S)$ is a convex body,
and $\mathcal{I}(S)$ is compact.

*Proof.* The first inclusion is Proposition 3.4, and the second holds because
$L_S(t) = Q_S^+(t) \setminus Q_S^-(t) \subseteq Q_S^+(t)$. The set $\mathcal{C}(S)$ is an
intersection of closed half-planes, so it is closed and convex; it contains $S$, so it is nonempty;
and every point $(x, y)$ of it has $0 \le y \le 1$, $x \le h_S(0)$ (from $Q_S^+(0)$) and
$x \ge -h_S(\omega + \pi/2)/\sin\omega$ (from $Q_S^+(\omega)$ and $y \ge 0$), so it is bounded. The
set $\mathcal{I}(S)$ is closed, since each $L_S(t)$ is a closed set minus an open one, and it lies
in the compact set $\mathcal{C}(S)$. $\square$

*Lean: [`proposition2_3_4`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L213), [`ms_capOf_bounds`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L99), [`ms_isCompact_capOf`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L119), [`ms_convex_capOf`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L85),
[`ms_isCompact_monotonization`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L133).*

### Lemma 3.7 (the same supporting hallways; Baek, Lemma 2.3.5)

The support functions of $S$, $\mathcal{I}(S)$ and $\mathcal{C}(S)$ agree on $J_\omega$. Hence, for
every $t \in [0, \omega]$, the supporting hallways $L_S(t)$, $L_{\mathcal{I}(S)}(t)$ and
$L_{\mathcal{C}(S)}(t)$ are the same.

*Proof.* By Proposition 3.6 and
[Lemma 2.7](02-preliminaries.md#lemma-27-the-support-function),
$h_S \le h_{\mathcal{I}(S)} \le h_{\mathcal{C}(S)}$. Conversely, for $s \in J_\omega$ the set
$\mathcal{C}(S)$ lies in $H_S(s)$, so $h_{\mathcal{C}(S)}(s) \le h_S(s)$. The supporting hallway
$L_X(t)$ depends only on $h_X(t)$ and $h_X(t + \pi/2)$, and both $t$ and $t + \pi/2$ lie in
$J_\omega$ when $t \in [0, \omega]$. $\square$

*Lean: [`lemma2_3_5_supp`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L231), [`lemma2_3_5_hallway`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L260).*

### Theorem 3.8 (the monotonization is connected; Baek, Theorem 2.3.6)

$\mathcal{I}(S)$ is connected.

*Proof.* We join every point $p \in \mathcal{I}(S)$ to the connected set $S \subseteq \mathcal{I}(S)$
by a segment inside $\mathcal{I}(S)$; then $\mathcal{I}(S)$ is a union of connected sets that all
contain $S$, and so it is connected.

**Step 1. Segments in the directions $u_\theta$, $\theta \in [\omega, \pi/2]$.** Let
$p, q \in \mathcal{I}(S)$ with $q - p$ parallel to $u_\theta$. Then the segment $[p, q]$ lies in
$\mathcal{I}(S)$. Indeed, it lies in the convex set $P_\omega \cap \bigcap_t Q_S^+(t)$. Suppose a
point $z$ of the segment lay in $Q_S^-(t)$ for some $t \in [0, \omega]$. Since
$\theta - t \in [0, \pi/2]$,

```math
\langle u_\theta, u_t \rangle = \cos(\theta - t) \ge 0, \qquad \langle u_\theta, v_t \rangle = \sin(\theta - t) \ge 0 ,
```

so the open quarter-plane $Q_S^-(t)$, defined by $\langle \cdot, u_t \rangle < h_S(t) - 1$ and
$\langle \cdot, v_t \rangle < h_S(t + \pi/2) - 1$, is closed in the direction $-u_\theta$. One of
the endpoints $p$, $q$ is $z - \lambda u_\theta$ with $\lambda \ge 0$; it would lie in $Q_S^-(t)$,
which $L_S(t)$ avoids. So no point of the segment lies in any $Q_S^-(t)$.

**Step 2. A segment that reaches $S$.** Fix $p \in \mathcal{I}(S)$, and consider the continuous
function $F(q, \theta) = \langle q - p, v_\theta \rangle$ on the connected set
$S \times [\omega, \pi/2]$; $F(q, \theta) = 0$ says that $q$ lies on the line through $p$ in the
direction $u_\theta$. Take points $a, b \in S$ with $a_1 = h_S(0)$ and
$\langle b, v_\omega \rangle = h_S(\omega + \pi/2)$. As $v_{\pi/2} = (-1, 0)$ and $p \in Q_S^+(0)$,

```math
F(a, \pi/2) = p_1 - a_1 = p_1 - h_S(0) \le 0 ,
```

and as $v_\omega = u_{\omega + \pi/2}$ and $p \in Q_S^+(\omega)$,

```math
F(b, \omega) = h_S(\omega + \pi/2) - \langle p, v_\omega \rangle \ge 0 .
```

By the intermediate value theorem on the connected set $S \times [\omega, \pi/2]$, $F(q, \theta) = 0$
for some $q \in S$ and $\theta \in [\omega, \pi/2]$. By step 1, $[p, q] \subseteq \mathcal{I}(S)$,
and $S \cup [p, q]$ is a connected subset of $\mathcal{I}(S)$ that contains $p$ and $S$
(Figure 3.2). $\square$

*Lean: [`theorem2_3_6`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L323), [`ms_segment_subset_monotonization`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L291), [`ms_qMinus_sub`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L271).*

![A disk S of diameter 1, between the dashed lines y = 0 and y = 1, inside its monotonization I(S): the upper half of the disk on top of a rectangle of width 1 and height one half, bounded by the outer walls of the supporting hallways, three of which are drawn as grey lines tangent to the disk; the orange dashed arc of the inner corners x(t) runs below the line y = 0; a short vertical black segment joins a point p in the lower right corner of I(S), outside the disk, to the point q of the disk above it](figures/03-monotone/monotonization.svg)

*Figure 3.2.* The disk $S$ of diameter 1 centred at $(0, \frac12)$ is a moving sofa with rotation
angle $\pi/2$, in standard position. Its supporting hallways have the outer walls tangent to the
disk (three are drawn) and the inner corners $\mathbf{x}_S(t) = (0, \frac12) - \frac12(u_t + v_t)$,
which lie on or below the line $y = 0$. So $\mathcal{I}(S)$ is the upper half of the disk on top of
the rectangle $[-\frac12, \frac12] \times [0, \frac12]$, of area $\frac12 + \frac\pi8 = 0.8927$,
against $\frac\pi4 = 0.7854$ for the disk. For $\omega = \pi/2$ the segment of step 2 is vertical.

Baek proves step 2 by contradiction: if no line through $p$ in a direction $u_\theta$,
$\theta \in [\omega, \pi/2]$, met $S$, these lines would split $S$ into a part on their left and a
part on their right, both nonempty. The left and right sides of a line are those of Baek's
Definition 2.3.9, which should read "not parallel to the $x$-axis" where it says "$y$-axis"
(REPORT.md, E1; the Lean definitions [`leftSide`](../../MovingSofaOptimality/Sofa/Defs.lean#L153) and [`rightSide`](../../MovingSofaOptimality/Sofa/Defs.lean#L156) follow the intended reading). The
formalization replaces the contradiction by the intermediate value theorem above.

*Proof of Theorem 3.3.* For $s \in [0, 1]$ let $\theta(s) = -s\omega$ and
$\Phi_s(p) = R_{-s\omega}(p - \mathbf{x}_S(s\omega))$, a rigid motion of the form
$R_{\theta(s)}\, p + c(s)$ that maps $L_S(s\omega) = \mathbf{x}_S(s\omega) + R_{s\omega}(L)$ onto
$L$. The functions $\theta$ and $c$ are continuous, because $h_S$ is
([Lemma 2.7](02-preliminaries.md#lemma-27-the-support-function)), and $\theta(1) = -\omega$. In the
coordinates $(X, Y)$ of the hallway $L_S(s\omega)$, $\Phi_s(p) = (X, Y)$. For
$p \in \mathcal{I}(S)$:

- at $s = 0$, $\mathbf{x}_S(0) = (h_S(0) - 1, 0)$ because $h_S(\pi/2) = 1$, so
  $\Phi_0(p) = (p_1 - h_S(0) + 1, p_2)$; here $p_1 \le h_S(0)$, as $p \in Q_S^+(0)$, and
  $0 \le p_2 \le 1$, as $p \in H$; so $\Phi_0(p) \in H_L$;
- for every $s$, $p \in L_S(s\omega)$, so $\Phi_s(p) \in L$;
- at $s = 1$, $\Phi_1(p) = (\langle p, u_\omega \rangle, \langle p, v_\omega \rangle - h_S(\omega + \pi/2) + 1)$
  because $h_S(\omega) = 1$; here $0 \le \langle p, u_\omega \rangle \le 1$, as $p \in V_\omega$, and
  $\langle p, v_\omega \rangle \le h_S(\omega + \pi/2)$, as $p \in Q_S^+(\omega)$; so
  $\Phi_1(p) \in V_L$.

So $\theta, c$ is a movement of $\mathcal{I}(S)$ with rotation angle $\omega$. The set
$\mathcal{I}(S)$ is closed (Proposition 3.6) and connected (Theorem 3.8), so it is a moving sofa
with rotation angle $\omega$. By Lemma 3.7, $h_{\mathcal{I}(S)}(\omega) = h_S(\omega) = 1$ and
$h_{\mathcal{I}(S)}(\pi/2) = h_S(\pi/2) = 1$, since $\omega, \pi/2 \in J_\omega$: it is in standard
position. Finally $S \subseteq \mathcal{I}(S)$ by Proposition 3.4. $\square$

*Lean: [`theorem2_3_2`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L408), [`ms_isMovement_monotonization`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L370), [`ms_isClosed_monotonization`](../../MovingSofaOptimality/Monotone/MonotoneSofa.lean#L82).*

## 3.2 Caps and niches

### Definition 3.9 (cap; Baek, Definitions 2.4.1 and 2.4.2)

A *cap* with rotation angle $\omega \in (0, \pi/2]$ is a convex body $K$ such that

1. $h_K(\omega) = h_K(\pi/2) = 1$ and $h_K(\omega + \pi) = h_K(3\pi/2) = 0$;
2. $K$ is an intersection of closed half-planes whose normal angles lie in
   $J_\omega \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$.

The caps with rotation angle $\omega$ form the *space of caps* $\mathcal{K}^{\mathrm c}_\omega$.

*Lean: [`IsCap`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L26), [`capSpace`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L32), [`IsHalfPlaneInter`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L20).*

Condition (1) says that the four sides of $P_\omega$ are supporting lines of $K$: $K$ lies in
$P_\omega$ and touches each of its sides. Condition (2) says that the boundary of $K$ has outer
normals only in $J_\omega$ and at the two lower sides, the normals of the outer walls of the
supporting hallways $L_K(t)$, $t \in [0, \omega]$, and of the floor.

### Theorem 3.10 (the cap of a moving sofa; Baek, Theorem 2.4.1)

For a moving sofa $S$ with rotation angle $\omega \in (0, \pi/2]$ in standard position,
$\mathcal{C}(S)$ is a cap with rotation angle $\omega$, the *cap of* $S$ (Baek's
Definition 2.4.3).

*Proof.* By Proposition 3.6, $K = \mathcal{C}(S)$ is a convex body, and by Lemma 3.7 and the
standard position, $h_K(\omega) = h_S(\omega) = 1$ and $h_K(\pi/2) = h_S(\pi/2) = 1$. As
$K \subseteq P_\omega$, $h_K(\omega + \pi) \le 0$ and $h_K(3\pi/2) \le 0$; we find points of $K$ on
the two lower sides of $P_\omega$.

First, $K$ contains a point $o$ with $o_2 = 1$ and $\langle o, u_\omega \rangle = 1$. If
$\omega = \pi/2$, take for $o$ a point of $S$ with $o_2 = h_S(\pi/2) = 1$. If $\omega < \pi/2$, take
$o = o_\omega$: let $q_\omega, q_{\pi/2} \in S$ with $\langle q_\omega, u_\omega \rangle = 1$ and
$(q_{\pi/2})_2 = 1$. For $t \in [0, \omega]$,

```math
\cos\omega\, \bigl(\langle o_\omega, u_t \rangle - \langle q_\omega, u_t \rangle\bigr) = \bigl(1 - (q_\omega)_2\bigr) \sin(t - \omega) \le 0 ,
```

and $(q_{\pi/2})_1 \le (o_\omega)_1$ because $q_{\pi/2} \in V_\omega$ lies on $y = 1$; with
$\sin t \ge 0$ this gives $\langle o_\omega, v_t \rangle \le \langle q_{\pi/2}, v_t \rangle$. So
$o_\omega$ is in $Q_S^+(t)$, below both outer walls, for every $t \in [0, \omega]$; it is a
vertex of $P_\omega$, so $o_\omega \in K$.

Second, each $Q_S^+(t)$, $t \in [0, \omega]$, is closed in the directions $-u_{\pi/2}$ and
$-u_\omega$, since $\pi/2 - t$ and $\omega - t$ lie in $[0, \pi/2]$ (as in step 1 of Theorem 3.8).
The points $o - u_{\pi/2}$, on the line $y = 0$, and $o - u_\omega$, on the line
$\langle p, u_\omega \rangle = 0$, also lie in $P_\omega$, so they lie in $K$; hence
$h_K(3\pi/2) = h_K(\omega + \pi) = 0$.

For (2): $K$ lies in its supporting half-planes, and conversely a point $p$ with
$\langle p, u_s \rangle \le h_K(s)$ for all $s \in J_\omega \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$
lies in $P_\omega$ (the four sides, with the values just found) and in every $Q_S^+(t)$, because
$h_K = h_S$ on $J_\omega$. So $K$ is the intersection of its supporting half-planes with normal
angles in $J_\omega \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$. $\square$

*Lean: [`theorem2_4_1`](../../MovingSofaOptimality/Monotone/CapNiche.lean#L84).*

In the paper's proof, the directions $v_0$ and $u_\omega$ in which $Q_S^+(t)$ is closed should be
$-v_0$ and $-u_\omega$ (REPORT.md, E26).

### Definition 3.11 (fan and niche; Baek, Definitions 2.4.4 and 2.4.5)

For $\omega \in (0, \pi/2]$, the *fan* is

```math
F_\omega = H_+(\omega, 0) \cap H_+(\pi/2, 0) = \lbrace p : \langle p, u_\omega \rangle \ge 0,\ y \ge 0 \rbrace ,
```

and the *niche* of a cap $K \in \mathcal{K}^{\mathrm c}_\omega$ is

```math
\mathcal{N}(K) = F_\omega \cap \bigcup_{t \in (0, \omega)} Q_K^-(t) .
```

*Lean: [`MovingSofaOptimality.fan`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L35), [`niche`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L38).*

![A cap K with rotation angle 1.2, light blue, with a flat top, a slanted right side and rounded upper corners, inside the dashed parallelogram P_omega; the fan F_omega, the region above the x-axis and to the right of the line through O in the direction v_omega, is shaded green; the niche N(K), orange, is a hump on the lower side of K near O, under the inner corners x_K(t), three of which are marked with the dashed walls of their quarter-planes, which continue below the fan](figures/03-monotone/fan.svg)

*Figure 3.3.* The fan $F_\omega$ (green) for $\omega = 1.2$, bounded by the rays from $O$ in the
directions $u_0$ and $v_\omega$. It contains the parallelogram $P_\omega$ (dashed), and with it the
cap $K$ (blue). The niche $\mathcal{N}(K)$ (orange) is the part of the fan covered by the open
quarter-planes $Q_K^-(t)$ below the inner corners $\mathbf{x}_K(t)$, $t \in (0, \omega)$; three of
them are drawn.

The fan contains $P_\omega$, and the bottom of a cap is the bottom of the fan: by condition (2),
a cap is cut out of the fan by its supporting half-planes with normal angles in $J_\omega$,

```math
K = F_\omega \cap \bigcap_{s \in J_\omega} H_K(s) . \tag{3.1}
```

Indeed, $K$ lies in the right-hand side, as $h_K(\omega + \pi) = h_K(3\pi/2) = 0$. Conversely, each
of the half-planes $H_-(s, c)$ of condition (2) contains $K$, so $c \ge h_K(s)$; for
$s \in J_\omega$ it contains $H_K(s)$, and for $s = \omega + \pi$ or $3\pi/2$ it contains the
half-plane $H_-(s, 0)$ of the fan, because $c \ge h_K(s) = 0$. So the right-hand side lies in all
of them, and in $K$. The angles $s \in J_\omega$ lie in
$[0, \omega + \pi/2] \subseteq [0, \pi]$, so $\sin s \ge 0$: raising a point of $F_\omega$ never
decreases $\langle \cdot, u_s \rangle$, and the set $F_\omega \setminus K$ is closed in the
direction $v_0 = (0, 1)$. In the formalization, (3.1) is a private lemma of
[`MovingSofaOptimality/Monotone/CapContainsNiche.lean`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean), used in the proofs of §3.4.

Each quarter-plane $Q_K^-(t)$, $t \in [0, \pi/2]$, is closed in the direction $-v_0 = (0, -1)$,
because $\langle v_0, u_t \rangle = \sin t$ and $\langle v_0, v_t \rangle = \cos t$ are nonnegative.
So the niche is the region of the fan below a roof, the supremum of the tops of the quarter-planes.
The fan, not the parallelogram, cuts the niche: for a cap that does not contain its niche, the
quarter-planes can reach above $P_\omega$ (Example 3.27). Baek's Definition 3.2.5 of the niche of a
polygon cap writes $P_\omega$ where $F_\omega$ is meant, which makes two later results false as
printed (REPORT.md, E6); [Chapter 4](04-balanced.md) uses the fan.

*Example (Hammersley's sofa).* Let $K$ be the union of the rectangle
$[-\frac2\pi, \frac2\pi] \times [0, 1]$ and the quarter-disks of radius 1 centred at
$(\pm\frac2\pi, 0)$ that continue it to the right and to the left, and $\omega = \pi/2$. Then
$h_K(t) = 1 + \frac2\pi \lvert \cos t \rvert$ for $t \in [0, \pi]$, $K$ is a cap, and its inner
corners are

```math
\mathbf{x}_K(t) = \tfrac2\pi \cos t\, u_t + \tfrac2\pi \sin t\, v_t = \tfrac2\pi\, u_{2t}, \qquad t \in [0, \pi/2] ,
```

on the half-circle of radius $\frac2\pi$ about $O$. The inner walls $b_K(t)$ and $d_K(t)$ pass
through $(\frac2\pi, 0)$ and $(-\frac2\pi, 0)$, so $F_{\pi/2} \cap Q_K^-(t)$ is the triangle with
these two vertices and the right angle $\mathbf{x}_K(t)$, and the niche is the half-disk of radius
$\frac2\pi$. So $K \setminus \mathcal{N}(K)$ is Hammersley's sofa (§1.3 of
[Chapter 1](README.md#13-background)), of area $\frac\pi2 + \frac2\pi = 2.2074$.

### Theorem 3.12 (the monotonization is the cap minus the niche; Baek, Theorem 2.4.2)

For a moving sofa $S$ with rotation angle $\omega \in (0, \pi/2]$ in standard position, with cap
$K = \mathcal{C}(S)$,

```math
\mathcal{I}(S) = K \setminus \mathcal{N}(K) .
```

*Proof.* Since $L_S(t) = Q_S^+(t) \setminus Q_S^-(t)$,

```math
\mathcal{I}(S) = \Bigl(P_\omega \cap \bigcap_{t \in [0, \omega]} Q_S^+(t)\Bigr) \setminus \bigcup_{t \in [0, \omega]} Q_S^-(t) = K \setminus \bigcup_{t \in [0, \omega]} Q_S^-(t) .
```

The two end angles remove nothing from $P_\omega$: $Q_S^-(0)$ lies below the line
$y = h_S(\pi/2) - 1 = 0$, and $Q_S^-(\omega)$ lies where
$\langle p, u_\omega \rangle < h_S(\omega) - 1 = 0$. As $K \subseteq P_\omega \subseteq F_\omega$,
removing $\bigcup_{t \in (0, \omega)} Q_S^-(t)$ from $K$ is the same as removing its intersection
with $F_\omega$. Finally $Q_S^-(t) = Q_K^-(t)$ for $t \in [0, \omega]$ by Lemma 3.7. $\square$

*Lean: [`theorem2_4_2`](../../MovingSofaOptimality/Monotone/CapNiche.lean#L177).*

The paper's proof takes the union over $[0, \omega]$ while the niche is a union over $(0, \omega)$;
the end angles contribute nothing, as shown above (REPORT.md, E2).

![Three panels for Gerver's sofa. (a) The cap K, light blue, below the grey outer walls of nine supporting hallways, whose envelope is the top and the rounded ends of K. (b) The niche N(K), orange, an arch on the floor below the orange rotation path x(t), with nine inner corners marked and the dashed walls of their quarter-planes; the cap is outlined dashed around it. (c) The sofa S, the cap minus the niche, with its upper boundary drawn thick and a vertical segment from a point of S just above the niche up to the upper boundary](figures/03-monotone/cap-niche.svg)

*Figure 3.4.* Theorem 3.12 for Gerver's sofa. (a) The cap $K$ is the part of the strip below the
outer walls of the supporting hallways. (b) The niche $\mathcal{N}(K)$ is the part of the half-plane
$y \ge 0$ covered by the open quarter-planes below the inner corners $\mathbf{x}(t)$, whose path
bounds the niche in the middle; at its two ends the niche is bounded by the inner walls. (c) The sofa
$S = K \setminus \mathcal{N}(K)$, its upper boundary $\delta K$ (thick, Definition 3.15), and a
vertical segment from a point of $S$ to $\delta K$, as in the proof of Theorem 3.25.

### Theorem 3.13 (a monotone sofa is its cap minus its niche; Baek, Theorem 2.4.3)

Let $S$ be a monotone sofa with rotation angle $\omega$, and $K = \mathcal{C}(S)$. Then
$S = K \setminus \mathcal{N}(K)$.

*Proof.* Let $S = \mathcal{I}(S')$ for a moving sofa $S'$ with rotation angle $\omega$ in standard
position. By Lemma 3.7, $h_S = h_{S'}$ on $J_\omega$, and $\mathcal{C}$ depends only on the support
function on $J_\omega$, so $\mathcal{C}(S) = \mathcal{C}(S')$. Theorem 3.12 for $S'$ gives
$S = \mathcal{I}(S') = K \setminus \mathcal{N}(K)$. $\square$

*Lean: [`theorem2_4_3`](../../MovingSofaOptimality/Monotone/CapNiche.lean#L216).*

So a monotone sofa is determined by its cap. Unlike Theorem 3.12, Theorem 3.13 needs no other sofa:
$\mathcal{C}(S)$ is defined for any set, and the formalization reads it so.

### Theorem 3.14 (monotonization is idempotent; Baek, Theorem 2.4.4)

Let $S'$ be a moving sofa with rotation angle $\omega \in (0, \pi/2]$ in standard position. Then
$\mathcal{I}(\mathcal{I}(S')) = \mathcal{I}(S')$. Consequently, such a moving sofa $S$ satisfies
$S = \mathcal{I}(S)$ if and only if it is a monotone sofa.

*Proof.* $\mathcal{I}(X)$ depends only on the supporting hallways $L_X(t)$, $t \in [0, \omega]$, which
are the same for $X = S'$ and $X = \mathcal{I}(S')$ by Lemma 3.7. If $S = \mathcal{I}(S)$, then $S$ is
a monotone sofa, with $S' = S$; conversely, if $S = \mathcal{I}(S')$, then
$\mathcal{I}(S) = \mathcal{I}(\mathcal{I}(S')) = S$. $\square$

*Lean: [`theorem2_4_4`](../../MovingSofaOptimality/Monotone/CapNiche.lean#L223), [`theorem2_4_4_iff`](../../MovingSofaOptimality/Monotone/CapNiche.lean#L230).*

The paper derives the first claim from Theorems 3.12 and 3.13; the formalization uses Lemma 3.7
directly.

## 3.3 The parts of a cap

In this section and the next, $K$ is a cap with rotation angle $\omega \in (0, \pi/2]$, and
$\mathbf{x}_K(t)$, $a_K(t)$, … are the parts of its supporting hallways
([Definition 2.17](02-preliminaries.md#definition-217-supporting-hallway-baek-definitions-222-and-223)).

### Definition 3.15 (vertices and upper boundary; Baek, Definitions 2.5.1 and 2.5.2)

For $t \in [0, \omega]$, the *vertices* of $K$ are

```math
A_K^\pm(t) = v_K^\pm(t), \qquad C_K^\pm(t) = v_K^\pm(t + \pi/2) ,
```

the ends of the edges along which the outer walls $a_K(t)$ and $c_K(t)$ touch $K$. The *upper
boundary* of $K$ is $\delta K = \bigcup_{t \in [0, \omega + \pi/2]} e_K(t)$.

*Lean: [`aPlus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L41), [`aMinus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L43), [`cPlus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L45), [`cMinus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L47), [`upperBoundary`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L51).*

The upper boundary runs from $A_K^-(0)$ to $C_K^+(\omega)$, and these two points lie on the lower
sides of the fan: $A_K^-(0) = (h_K(0), 0)$ and $C_K^+(\omega) = h_K(\omega + \pi/2)\, v_\omega$. For
the second, let $C = h_K(\omega + \pi/2)\, v_\omega$, a point of the line $l(\omega, 0)$. If
$\omega < \pi/2$, $K$ meets $l(\omega, 0)$, as $h_K(\omega + \pi) = 0$, at a point
$\lambda v_\omega$ with $\lambda \ge 0$, as $y \ge 0$ on $K$; so $h_K(\omega + \pi/2) \ge 0$, and
$C \in F_\omega$ (for $\omega = \pi/2$, $C$ lies on the line $y = 0$). For $s \in J_\omega$ and a
point $q \in e_K(\omega + \pi/2)$, writing $u_s = \cos(s - \omega)\, u_\omega + \sin(s - \omega)\, v_\omega$
gives $\langle C, u_s \rangle \le \langle q, u_s \rangle \le h_K(s)$, since $\cos(s - \omega) \ge 0$
and $\langle q, u_\omega \rangle \ge 0$. By (3.1), $C \in K$; it lies on $l_K(\omega + \pi/2)$, and
it is the point of that edge farthest in the direction $v_{\omega + \pi/2} = -u_\omega$, that is,
$C_K^+(\omega)$. The first claim is the mirror image of the second (Proposition 3.21 (4)). Baek's
proofs use both facts without stating them (REPORT.md, E4 (a)).

### Proposition 3.16 (the upper boundary; Baek, Proposition 2.5.1)

$\delta K$ is the boundary of $K$ relative to the fan: $\delta K = K \cap \overline{F_\omega \setminus K}$.

*Proof.* Let $z \in e_K(s)$, $s \in [0, \omega + \pi/2]$. For $\varepsilon > 0$, the point
$z + \varepsilon u_s$ lies in $F_\omega$, because $\langle u_s, u_\omega \rangle = \cos(s - \omega) \ge 0$
and $\langle u_s, u_{\pi/2} \rangle = \sin s \ge 0$, and not in $K$, because
$\langle z + \varepsilon u_s, u_s \rangle = h_K(s) + \varepsilon$. So $z$ is a limit of points of
$F_\omega \setminus K$. Conversely, let $z \in K \setminus \delta K$. Then
$\langle z, u_s \rangle < h_K(s)$ for every $s \in [0, \omega + \pi/2]$, and by continuity and
compactness the difference is at least some $m > 0$. A point $p \in F_\omega$ within distance
$m/2$ of $z$ satisfies $\langle p, u_s \rangle < h_K(s)$ for $s \in J_\omega$, so $p \in K$ by (3.1).
Hence $z \notin \overline{F_\omega \setminus K}$. $\square$

*Lean: [`proposition2_5_1`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L256).*

### Proposition 3.17 (the upper boundary is connected; Baek, Proposition 2.5.2)

$\delta K$ is connected.

*Proof.* Let $I = [0, \omega + \pi/2]$, and suppose that two disjoint open sets $U$, $V$ cover
$\delta K$. Each edge $e_K(t)$, $t \in I$, is a segment, hence connected, so it lies in $U$ or in
$V$. By [Theorem 2.9](02-preliminaries.md#theorem-29-limits-of-vertices-baek-theorem-213), the
vertex $v_K^+(r)$ tends to $v_K^+(t)$ as $r \to t^+$ and to $v_K^-(t)$ as $r \to t^-$, both points
of $e_K(t)$; so if $e_K(t)$ lies in the open set $U$, then $v_K^+(r) \in U$ for $r \in I$ near
$t$, and then $e_K(r) \subseteq U$. So $\lbrace t \in I : e_K(t) \subseteq U \rbrace$ and
$\lbrace t \in I : e_K(t) \subseteq V \rbrace$ are disjoint, open in $I$, and cover $I$. As $I$ is
connected, one of them is all of $I$, and $\delta K$ lies in $U$ or in $V$. $\square$

*Lean: [`proposition2_5_2`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L296).*

### Definition 3.18 (wedges, their ends and gaps; Baek, Definitions 2.5.3–2.5.5)

For $t \in (0, \omega)$, the *wedge* of $K$ with angle $t$ is $T_K(t) = F_\omega \cap Q_K^-(t)$. Its
*ends* $W_K(t)$ and $Z_K(t)$ are the points where the inner walls $b_K(t)$ and $d_K(t)$ meet the
lower sides $l(\pi/2, 0)$ and $l(\omega, 0)$ of the fan (Figure 3.5):

```math
W_K(t) = \Bigl(\frac{h_K(t) - 1}{\cos t},\ 0\Bigr), \qquad Z_K(t) = \frac{h_K(t + \pi/2) - 1}{\cos(\omega - t)}\, v_\omega .
```

The *right* and *left wedge gaps* are the signed distances along these sides from the ends of the
wedge to the ends of the upper boundary:

```math
w_K(t) = \langle A_K^-(0) - W_K(t), u_0 \rangle = h_K(0) - \frac{h_K(t) - 1}{\cos t}, \qquad z_K(t) = \langle C_K^+(\omega) - Z_K(t), v_\omega \rangle = h_K(\omega + \pi/2) - \frac{h_K(t + \pi/2) - 1}{\cos(\omega - t)} .
```

*Lean: [`wedge`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L54), [`wedgeW`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L58), [`wedgeZ`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L62), [`wedgeGapW`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L67), [`wedgeGapZ`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L70).*

![The cap K of Figure 3.3 in the fan, shaded green, and for the angle t = 0.55 the inner walls b_K(t) and d_K(t), orange lines through the inner corner x_K(t); the wedge T_K(t), shaded orange, is the quadrilateral with vertices O, W_K(t) on the x-axis, x_K(t) and Z_K(t) on the lower left side of the fan; the gaps w_K(t), from W_K(t) to A_K minus of 0 on the x-axis, and z_K(t), from Z_K(t) to C_K plus of omega on the lower left side, are thick purple segments](figures/03-monotone/wedge.svg)

*Figure 3.5.* The wedge $T_K(t)$ of the cap of Figure 3.3 for $t = 0.55$. The origin lies below
both inner walls, so the wedge is the quadrilateral $O\, W_K(t)\, \mathbf{x}_K(t)\, Z_K(t)$. Its
ends stop short of the ends $A_K^-(0)$ and $C_K^+(\omega)$ of the upper boundary by the gaps
$w_K(t)$ and $z_K(t)$ (purple), which are positive (Theorem 3.22).

### Proposition 3.19 (the niche is the union of the wedges; Baek, Proposition 2.5.3)

$\mathcal{N}(K) = \bigcup_{t \in (0, \omega)} T_K(t)$.

*Proof.* Distribute the intersection with $F_\omega$ over the union. $\square$

*Lean: [`proposition2_5_3`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L373).*

### Definition 3.20 (mirror reflection; Baek, Definition 2.5.6)

$M_\omega$ is the reflection of the plane in the line through $O$ and $o_\omega$, the line with
angle $\pi/4 + \omega/2$:

```math
M_\omega(x, y) = (-x \sin\omega + y \cos\omega,\ x \cos\omega + y \sin\omega) .
```

The *mirror reflection* of $K$ is $K^{\mathrm m} = M_\omega(K)$.

*Lean: [`mirror`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L75), [`mirrorCap`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L79).*

The reflection is a linear isometry, an involution, and $M_\omega u_t = u_{\omega + \pi/2 - t}$,
$M_\omega v_t = u_{\omega - t}$. It maps $P_\omega$ and $F_\omega$ onto themselves, exchanging the
two upper sides and the two lower sides.

### Proposition 3.21 (mirror symmetry; Baek, Proposition 2.5.4)

Let $t \in \mathbb{R}$.

1. If $K$ is a cap with rotation angle $\omega$, so is $K^{\mathrm m}$.
2. $h_{K^{\mathrm m}}(t) = h_K(\omega + \pi/2 - t)$.
3. $L_{K^{\mathrm m}}(t) = M_\omega(L_K(\omega - t))$, and likewise for the corners $\mathbf{x}$ and
   $\mathbf{y}$; the walls are exchanged:
   $a_{K^{\mathrm m}}(t) = M_\omega(c_K(\omega - t))$, $b_{K^{\mathrm m}}(t) = M_\omega(d_K(\omega - t))$,
   $c_{K^{\mathrm m}}(t) = M_\omega(a_K(\omega - t))$, $d_{K^{\mathrm m}}(t) = M_\omega(b_K(\omega - t))$,
   and so are the ends of the wedges:
   $W_{K^{\mathrm m}}(t) = M_\omega(Z_K(\omega - t))$, $Z_{K^{\mathrm m}}(t) = M_\omega(W_K(\omega - t))$.
4. $A^\pm_{K^{\mathrm m}}(t) = M_\omega(C^\mp_K(\omega - t))$,
   $C^\pm_{K^{\mathrm m}}(t) = M_\omega(A^\mp_K(\omega - t))$, $w_{K^{\mathrm m}}(t) = z_K(\omega - t)$ and
   $z_{K^{\mathrm m}}(t) = w_K(\omega - t)$.
5. $\delta K^{\mathrm m} = M_\omega(\delta K)$, $T_{K^{\mathrm m}}(t) = M_\omega(T_K(\omega - t))$ and
   $\mathcal{N}(K^{\mathrm m}) = M_\omega(\mathcal{N}(K))$.
6. If $K$ is a cap, $\sigma_{K^{\mathrm m}}(E) = \sigma_K(\omega + \pi/2 - E)$ for every Borel set $E$
   of angles.

*Lean: [`proposition2_5_4_isCap`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L574), [`proposition2_5_4_supp`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L620), [`proposition2_5_4_hallway`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L624),
[`proposition2_5_4_vertices`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L650), [`proposition2_5_4_gaps`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L659), [`proposition2_5_4_sets`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L671),
[`proposition2_5_4_sigma`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L718).*

The paper's first item claims $?_{K^{\mathrm m}}(t) = M_\omega(?_K(\omega - t))$ also for the walls
$a, b, c, d$ and the ends $W, Z$, and its second item has $K^{\mathrm m}$ on the right; the
reflection exchanges the two arms of the hallway, so the walls and the ends are exchanged as above,
and the right side involves $K$ (REPORT.md, E3). Items (2)–(5) hold for every set $K$, and the
formalization states them so (REPORT.md, §5). Figure 3.6 shows the exchange.

![Two panels. Left: the cap K of Figure 3.3 in blue with its supporting hallway at the angle s = 0.3, whose outer walls are labelled a on the right and c on the left and whose inner walls b and d, and the purple dashed mirror line through O and o_omega. Right: the reflected cap K^m in green with its supporting hallway at the angle omega minus s, the reflection of the left hallway, again with a on the right and c on the left; the reflection carries the wall labelled a on the left to the wall labelled c on the right, and b to d](figures/03-monotone/mirror.svg)

*Figure 3.6.* Proposition 3.21 (3). The reflection $M_\omega$ in the dashed line maps the cap $K$ and
its supporting hallway $L_K(s)$ (left) to $K^{\mathrm m}$ and $L_{K^{\mathrm m}}(\omega - s)$
(right). It maps the right outer wall $a_K(s)$ to the left outer wall $c_{K^{\mathrm m}}(\omega - s)$,
and the inner wall $b_K(s)$ to $d_{K^{\mathrm m}}(\omega - s)$.

*Proof.* (2) $\langle M_\omega p, u_t \rangle = \langle p, M_\omega u_t \rangle = \langle p, u_{\omega + \pi/2 - t} \rangle$.
(1) By (2), $h_{K^{\mathrm m}}$ takes at $\omega$, $\pi/2$, $\omega + \pi$, $3\pi/2$ the values of $h_K$ at
$\pi/2$, $\omega$, $3\pi/2 - 2\pi$, $\omega + \pi - 2\pi$, which are $1, 1, 0, 0$; and $M_\omega$ maps a
half-plane $H_-(s, c)$ onto $H_-(\omega + \pi/2 - s, c)$, and the map $s \mapsto \omega + \pi/2 - s$
maps $J_\omega$ onto itself and $\lbrace \omega + \pi, 3\pi/2 \rbrace$ onto itself modulo $2\pi$.
(3) Let $\varsigma(x, y) = (y, x)$, the reflection of $L$ in its diagonal, which fixes $L$, its
corners and its quarter-planes and exchanges $a_L \leftrightarrow c_L$, $b_L \leftrightarrow d_L$,
$\vec b_L \leftrightarrow \vec d_L$. From (2) and $M_\omega u_{\omega - t} = v_t$,
$M_\omega v_{\omega - t} = u_t$, the two rigid motions of Definition 2.17 satisfy
$f_{K^{\mathrm m}, t} = M_\omega \circ f_{K, \omega - t} \circ \varsigma$, which gives the hallways,
corners and walls; the ends of the wedges follow from their formulas. (4) $M_\omega$ maps the edge
$e_K(s)$ onto $e_{K^{\mathrm m}}(\omega + \pi/2 - s)$ and reverses the direction of $v_s$, so it
exchanges the two vertices; the gaps follow. (5) follows from (3), (4) and
$M_\omega(F_\omega) = F_\omega$. (6) is a computation with the distribution function of $\sigma_K$
([Chapter 6](06-surface-area.md)), the identity that Baek cites from Schneider's Equation (4.14).
$\square$

*Remark* (Baek, Remark 2.5.1). With Proposition 3.21, every statement about the right side of a
cap (the walls $a$ and $b$, the end $W$, the gap $w$, the vertex $A_K^-(0)$) gives one about the
left side (the walls $c$ and $d$, the end $Z$, the gap $z$, the vertex $C_K^+(\omega)$), by applying
it to $K^{\mathrm m}$ at the angle $\omega - t$. The paper proves one side of each statement below
and appeals to the mirror for the other; the formalization proves both sides directly.

## 3.4 The cap contains its niche

A point $p_1$ is *further* than $p_2$ in the direction of a nonzero vector $w$ if
$\langle p_1, w \rangle \ge \langle p_2, w \rangle$, and *strictly further* if the inequality is
strict (Baek's Definition 2.5.7; [`IsFurther`](../../MovingSofaOptimality/Basic/Plane.lean#L71), [`IsStrictlyFurther`](../../MovingSofaOptimality/Basic/Plane.lean#L74)). In these terms, the next theorem
says that $A_K^-(0)$ is strictly further than $W_K(t)$ in the direction $u_0$, and $C_K^+(\omega)$
strictly further than $Z_K(t)$ in the direction $v_\omega$.

### Theorem 3.22 (the wedge gaps are positive; Baek, Theorem 2.5.5)

For every $t \in (0, \omega)$, $w_K(t) > 0$ and $z_K(t) > 0$. Equivalently,

```math
h_K(t) - 1 < h_K(0) \cos t, \qquad h_K(t + \pi/2) - 1 < h_K(\omega + \pi/2) \cos(\omega - t) . \tag{3.2}
```

*Proof.* Let $q \in e_K(t)$. As $K$ lies in $H$ and in $H_K(0)$, $q_1 \le h_K(0)$ and
$0 \le q_2 \le 1$; and $0 < t < \omega \le \pi/2$ gives $\cos t > 0$ and $\sin t < 1$. So

```math
h_K(t) = q_1 \cos t + q_2 \sin t \le h_K(0) \cos t + \sin t < h_K(0) \cos t + 1 .
```

For the second inequality let $q \in e_K(t + \pi/2)$, and write
$u_{t + \pi/2} = \cos(\omega - t)\, v_\omega + \sin(\omega - t)\, u_\omega$. As
$\langle q, v_\omega \rangle \le h_K(\omega + \pi/2)$ and $0 \le \langle q, u_\omega \rangle \le 1$,
with $\cos(\omega - t) > 0$ and $\sin(\omega - t) < 1$,

```math
h_K(t + \pi/2) \le h_K(\omega + \pi/2) \cos(\omega - t) + \sin(\omega - t) < h_K(\omega + \pi/2) \cos(\omega - t) + 1 .
```

Dividing by $\cos t$ and $\cos(\omega - t)$ gives $w_K(t) > 0$ and $z_K(t) > 0$. $\square$

*Lean: [`theorem2_5_5`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L751).*

Baek argues geometrically: the outer wall $a_K(t)$ meets the line $y = 1$ strictly further than
$W_K(t)$ in the direction $u_0$, since $a_K(t)$ and $b_K(t)$ bound a strip of width 1 turned by $t$,
and convexity carries this to $A_K^-(t)$ and then to $A_K^-(0)$.

### Lemma 3.23 (a wedge at a corner inside the cap; Baek, Lemma 2.5.6)

Let $t \in (0, \omega)$. If the inner corner $\mathbf{x}_K(t)$ lies in $K$, then the wedge $T_K(t)$
lies in $K$.

*Proof.* We use a fact about directions: if $0 < b - a < \pi$ and $s \in [a, b]$, then

```math
\sin(b - a)\, u_s = \sin(b - s)\, u_a + \sin(s - a)\, u_b
```

with nonnegative coefficients, so a point that is not further than $q$ in the directions $u_a$ and
$u_b$ is not further than $q$ in any direction $u_s$ between them. Let $p \in T_K(t)$. By (3.1) it
suffices to show $\langle p, u_s \rangle \le h_K(s)$ for $s \in J_\omega$, and
$J_\omega \subseteq [0, t] \cup [t, t + \pi/2] \cup [t + \pi/2, \omega + \pi/2]$.

- *$s \in [0, t]$.* Let $q \in e_K(0)$, so that $q_1 = h_K(0)$ and $q_2 \ge 0$. Since
  $p \in Q_K^-(t)$, (3.2) gives
  $\langle p, u_t \rangle < h_K(t) - 1 < h_K(0) \cos t \le \langle q, u_t \rangle$; and since
  $p_2 \ge 0$, $p_1 \cos t \le \langle p, u_t \rangle < h_K(0) \cos t$, so
  $\langle p, u_0 \rangle < \langle q, u_0 \rangle$. Hence
  $\langle p, u_s \rangle \le \langle q, u_s \rangle \le h_K(s)$.
- *$s \in [t, t + \pi/2]$.* The corner $\mathbf{x} = \mathbf{x}_K(t)$ has
  $\langle \mathbf{x}, u_t \rangle = h_K(t) - 1$ and $\langle \mathbf{x}, v_t \rangle = h_K(t + \pi/2) - 1$,
  and $p \in Q_K^-(t)$ is not further than $\mathbf{x}$ in the directions $u_t$ and
  $u_{t + \pi/2} = v_t$. Hence $\langle p, u_s \rangle \le \langle \mathbf{x}, u_s \rangle \le h_K(s)$,
  because $\mathbf{x} \in K$.
- *$s \in [t + \pi/2, \omega + \pi/2]$.* The same argument in the frame $(u_\omega, v_\omega)$, with
  a point $q \in e_K(\omega + \pi/2)$ and the second inequality of (3.2). $\square$

*Lean: [`lemma2_5_6`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L836).*

Only the middle range uses the hypothesis $\mathbf{x}_K(t) \in K$; the gaps take care of the
normal angles near $0$ and $\omega + \pi/2$. Baek's proof instead splits into four cases by the
position of $O$ relative to the inner walls, and uses without proof that $O \in K$ when
$\omega < \pi/2$ and that $A_K^-(0)$ and $C_K^+(\omega)$ lie on the lower sides of the fan; both
hold (REPORT.md, E4). In its first case, $\mathbf{x}_K(t) \in K$ forces $\mathbf{x}_K(t) = O$ and
$T_K(t) = \emptyset$, rather than a contradiction (E26).

### Lemma 3.24 (the ends of the upper boundary; Baek, Lemma 2.5.7)

$A_K^-(0)$ and $C_K^+(\omega)$ lie in $K \setminus \mathcal{N}(K)$.

*Proof.* Both are points of $K$. For $t \in (0, \omega)$, the point $A = A_K^-(0)$ has
$A_1 = h_K(0)$ and $A_2 \ge 0$, so $\langle A, u_t \rangle \ge h_K(0) \cos t > h_K(t) - 1$ by (3.2),
and $A \notin Q_K^-(t)$. In the same way
$\langle C_K^+(\omega), u_{t + \pi/2} \rangle \ge h_K(\omega + \pi/2) \cos(\omega - t) > h_K(t + \pi/2) - 1$.
$\square$

*Lean: [`lemma2_5_7`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L860).*

### Theorem 3.25 (when the cap contains its niche; Baek, Theorem 2.5.8)

The following are equivalent:

1. $\mathcal{N}(K) \subseteq K$;
2. $\mathcal{N}(K) \subseteq K \setminus \delta K$;
3. for every $t \in (0, \omega)$, the inner corner $\mathbf{x}_K(t)$ lies outside the interior
   $F_\omega^\circ$ of the fan, or in $K$;
4. $K \setminus \mathcal{N}(K)$ is connected.

*Lean: [`theorem2_5_8`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L1006).*

*Proof.* (1 ⇒ 2) Suppose $p \in \mathcal{N}(K) \cap \delta K$, with $p \in Q_K^-(t)$ and
$p \in e_K(s)$, $s \in [0, \omega + \pi/2]$. The quarter-plane is open, so
$p + \varepsilon u_s \in Q_K^-(t)$ for small $\varepsilon > 0$, and $p + \varepsilon u_s \in F_\omega$
as in Proposition 3.16. So $p + \varepsilon u_s \in \mathcal{N}(K) \subseteq K$, against
$\langle p + \varepsilon u_s, u_s \rangle = h_K(s) + \varepsilon$. (2 ⇒ 1) is clear.

(1 ⇒ 3) If $\mathbf{x} = \mathbf{x}_K(t) \in F_\omega^\circ \setminus K$, an open set, then the points
$\mathbf{x} - \varepsilon v_0$ just below $\mathbf{x}$ lie in $F_\omega^\circ \setminus K$ and in
$Q_K^-(t)$, as $\langle v_0, u_t \rangle = \sin t > 0$ and $\langle v_0, v_t \rangle = \cos t > 0$;
so they lie in $\mathcal{N}(K) \setminus K$.

(3 ⇒ 1) Let $p \in F_\omega \cap Q_K^-(t)$. The angles $\omega$ and $\pi/2$ lie strictly between $t$
and $t + \pi/2$, so by the strict form of the fact about directions in Lemma 3.23,
$0 \le \langle p, u_\omega \rangle < \langle \mathbf{x}_K(t), u_\omega \rangle$ and
$0 \le p_2 < \mathbf{x}_K(t)_2$: the corner lies in $F_\omega^\circ$. By (3) it lies in $K$, and
Lemma 3.23 gives $p \in T_K(t) \subseteq K$.

(2 ⇒ 4) By (2), $\delta K \subseteq K \setminus \mathcal{N}(K)$, and $\delta K$ is connected
(Proposition 3.17). Let $y \in K \setminus \mathcal{N}(K)$, and let $q$ be the highest point of $K$
on the vertical line through $y$. The points $q + \varepsilon v_0$ lie in $F_\omega \setminus K$, so
$q \in \delta K$ by Proposition 3.16. The segment $[y, q]$ lies in $K$, and avoids $\mathcal{N}(K)$:
if a point $z$ above $y$ lay in $Q_K^-(t)$, so would $y$, since $Q_K^-(t)$ is closed in the direction
$-v_0$, and $y \in F_\omega$. So every point of $K \setminus \mathcal{N}(K)$ is joined to the
connected set $\delta K$ inside $K \setminus \mathcal{N}(K)$ (Figure 3.4 (c)).

(4 ⇒ 3) Suppose $\mathbf{x} = \mathbf{x}_K(t) \in F_\omega^\circ \setminus K$ for some
$t \in (0, \omega)$. The vertical line through $\mathbf{x}$ misses $K \setminus \mathcal{N}(K)$:
the points above $\mathbf{x}$ are in $F_\omega \setminus K$, which is closed in the direction $v_0$;
$\mathbf{x}$ is not in $K$; and the points below $\mathbf{x}$ are in $Q_K^-(t)$, hence in the niche
if they lie in $F_\omega$, and outside $K$ otherwise. But $A_K^-(0)$ lies strictly to the right of
this line, since $\mathbf{x}_1 \cos t < \langle \mathbf{x}, u_t \rangle = h_K(t) - 1 < h_K(0)\cos t$
by (3.2) and $\mathbf{x}_2 > 0$; and $C_K^+(\omega)$ lies strictly to its left, by the mirror
computation. Both lie in $K \setminus \mathcal{N}(K)$ by Lemma 3.24, so this set is not connected
(Figure 3.7). $\square$

### Theorem 3.26 (the caps of monotone sofas; Baek, Theorem 2.5.9)

A cap $K$ with rotation angle $\omega$ is the cap $\mathcal{C}(S)$ of a monotone sofa $S$ with
rotation angle $\omega$ if and only if $\mathcal{N}(K) \subseteq K$.

*Proof.* If $K = \mathcal{C}(S)$ for a monotone sofa $S = \mathcal{I}(S')$, then
$S = K \setminus \mathcal{N}(K)$ by Theorem 3.13, and $S$ is connected, being a moving sofa by
Theorem 3.3. So (4) ⇒ (1) of Theorem 3.25 gives $\mathcal{N}(K) \subseteq K$.

Conversely, suppose $\mathcal{N}(K) \subseteq K$, and let $S = K \setminus \mathcal{N}(K)$.

1. $S$ is connected by Theorem 3.25 (1 ⇒ 4), and closed: since $K \subseteq F_\omega$,
   $S = K \setminus \bigcup_{t \in (0, \omega)} Q_K^-(t)$, a closed set minus an open one.
2. $\delta K \subseteq S \subseteq K$ by Theorem 3.25 (2). Every edge $e_K(s)$, $s \in J_\omega$,
   lies in $\delta K$, so $h_S = h_K$ on $J_\omega$, and $L_S(t) = L_K(t)$ for $t \in [0, \omega]$.
3. $S \subseteq L_K(t)$ for $t \in [0, \omega]$: $S \subseteq K \subseteq Q_K^+(t)$, and $S$ avoids
   $Q_K^-(t)$, by definition of the niche for $t \in (0, \omega)$, and because $Q_K^-(0)$ and
   $Q_K^-(\omega)$ lie outside $P_\omega$ (as in Theorem 3.12).
4. The motion $\Phi_s(p) = R_{-\omega s}(p - \mathbf{x}_K(\omega s))$ moves $S$ through $L$ from
   $H_L$ to $V_L$, exactly as in the proof of Theorem 3.3. So $S$ is a moving sofa with rotation
   angle $\omega$, in standard position by (2).
5. $\mathcal{C}(S) = \mathcal{C}(K) = K$: $\mathcal{C}$ depends only on the support function on
   $J_\omega$, and $\mathcal{C}(K) = K$ by (3.1). By Theorem 3.12,
   $\mathcal{I}(S) = K \setminus \mathcal{N}(K) = S$, so $S$ is a monotone sofa, with cap $K$.
   $\square$

*Lean: [`theorem2_5_9`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L1309).*

In the paper's proof, "$\mathcal{N}(K)$ contains $K$" should read "$K$ contains $\mathcal{N}(K)$"
(REPORT.md, E26).

### Example 3.27 (a cap that does not contain its niche; Baek, Remark 2.5.2)

The rectangle $K = [0, 100] \times [0, 1]$ is a cap with rotation angle $\pi/2$, and it does not
contain its niche: the point $(50, 2)$ lies in the wedge $T_K(\pi/4)$ but not in $K$. By
Theorem 3.26, $K$ is not the cap of any monotone sofa with rotation angle $\pi/2$.

*Proof.* $K$ is the intersection of the half-planes with normal angles $0$, $\pi/2$, $\pi$, $3\pi/2$
through its sides, which lie in $J_{\pi/2} \cup \lbrace 3\pi/2 \rbrace = [0, \pi] \cup \lbrace 3\pi/2 \rbrace$,
and $h_K(\pi/2) = 1$, $h_K(3\pi/2) = 0$. At $t = \pi/4$, $h_K(\pi/4) = 101/\sqrt2$ (at the corner
$(100, 1)$) and $h_K(3\pi/4) = 1/\sqrt2$ (at $(0, 1)$), so the inner corner is
$\mathbf{x}_K(\pi/4) = (50, 51 - \sqrt2) = (50, 49.586\ldots)$, and the point $(50, 2)$, directly
below it, satisfies $\langle (50, 2), u_{\pi/4} \rangle = 52/\sqrt2 < 101/\sqrt2 - 1$ and
$\langle (50, 2), v_{\pi/4} \rangle = -48/\sqrt2 < 1/\sqrt2 - 1$. It lies in $F_{\pi/2}$, so in
$T_K(\pi/4)$, and not in $K$, as $2 > 1$. $\square$

*Lean: [`remark2_5_2`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L1371).*

![The rectangle K with corners (0, 0) and (6, 1), outlined dashed blue, whose niche, shaded orange, rises far above it as a dome with its top at the inner corner x_K(pi/4) = (3, 2.59); the wedge T_K(pi/4), a large triangle on the x-axis with its apex at that corner, is outlined orange; what remains of K, two small blue pieces labelled S at the left and right ends, is separated by the dashed vertical line through x_K(pi/4); the ends C_K plus of omega at the origin and A_K minus of 0 at (6, 0) are marked](figures/03-monotone/wide-cap.svg)

*Figure 3.7.* The same phenomenon for the shorter cap $K = [0, 6] \times [0, 1]$, with
$\mathbf{x}_K(\pi/4) = (3, 4 - \sqrt2) = (3, 2.586)$. The niche (orange) leaves $K$ and $P_{\pi/2}$,
and $K \setminus \mathcal{N}(K)$ falls into two pieces, separated by the vertical line through
$\mathbf{x}_K(\pi/4)$, as in the proof of Theorem 3.25 (4 ⇒ 3).

## 3.5 The sofa area functional

By Theorems 3.13 and 3.26, the map $S \mapsto \mathcal{C}(S)$ is a bijection from the monotone sofas
with rotation angle $\omega$ onto the caps in $\mathcal{K}^{\mathrm c}_\omega$ that contain their
niche, with inverse $K \mapsto K \setminus \mathcal{N}(K)$. The space of caps extends the space of
monotone sofas, and the area extends to it as follows.

### Definition 3.28 (sofa area functional; Baek, Definition 2.5.8)

For $\omega \in (0, \pi/2]$, the *sofa area functional* on $\mathcal{K}^{\mathrm c}_\omega$ is

```math
\mathcal{A}_\omega(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert .
```

*Lean: [`sofaArea`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L82).*

### Theorem 3.29 (the area of a monotone sofa; Baek, Theorem 2.5.10)

For a monotone sofa $S$ with rotation angle $\omega$ and its cap $K = \mathcal{C}(S)$,
$\mathcal{A}_\omega(K) = \lvert S \rvert$.

*Proof.* $K$ is a cap (Theorem 3.10, applied to the moving sofa $S$, which is in standard position
by Theorem 3.3), $S = K \setminus \mathcal{N}(K)$ (Theorem 3.13), and $\mathcal{N}(K) \subseteq K$
(Theorem 3.26). The niche is measurable, the intersection of a closed set and an open one, and $K$
is compact, so $\lvert S \rvert = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$. $\square$

*Lean: [`theorem2_5_10`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L1457).*

For Gerver's sofa (Figure 3.4), numerically $\lvert K \rvert = 2.861$ and
$\lvert \mathcal{N}(K) \rvert = 0.641$, and their difference is $\lvert G \rvert = 2.2195\ldots$.

*Table 3.1.* The reduction of this chapter, for a rotation angle $\omega \in (0, \pi/2]$.

| Step | Statement | Result |
| --- | --- | --- |
| standard position | a moving sofa has a translate in standard position, inside $P_\omega$ | Proposition 3.1 |
| monotonization | $\mathcal{I}(S) \supseteq S$ is a moving sofa in standard position | Theorem 3.3 |
| cap and niche | a monotone sofa is $K \setminus \mathcal{N}(K)$, $K = \mathcal{C}(S)$ a cap | Theorems 3.10, 3.13 |
| sofa caps | a cap is the cap of a monotone sofa if and only if $\mathcal{N}(K) \subseteq K$ | Theorem 3.26 |
| area | $\lvert S \rvert = \mathcal{A}_\omega(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$ | Theorem 3.29 |

So the largest area of a moving sofa with rotation angle $\omega$ is the supremum of
$\mathcal{A}_\omega$ over the caps that contain their niche, which is at most its supremum over all
of $\mathcal{K}^{\mathrm c}_\omega$. Not every cap contains its niche (Example 3.27), so it is not
yet clear that a maximizer of $\mathcal{A}_\omega$ is the cap of a sofa. [Chapter 4](04-balanced.md)
shows that $\mathcal{A}_\omega$ attains its supremum at a limit of maximum polygon caps, and that
this limit contains its niche, so that its monotone sofa, a *balanced maximum sofa*, has the largest
area among all moving sofas with rotation angle $\omega$ (Baek's Theorem 3.5.5).
