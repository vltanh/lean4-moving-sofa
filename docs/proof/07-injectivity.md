# 7. The injectivity condition

[Contents](README.md) · [← 6. The surface area measure](06-surface-area.md) · [8. Convex curves and Mamikon's theorem →](08-convex-curves.md)

From this chapter on the rotation angle is $\omega = \pi/2$. A balanced maximum sofa $S$ with this
rotation angle is cut out by its supporting hallways $L_t$, $t \in [0, \pi/2]$, and Romik calls the
curve $\mathbf{x}(t)$ of their inner corners the rotation path of $S$. Baek's key property of $S$,
the *injectivity condition*, says that the rotation path is continuously differentiable and that its
velocity has a negative component along $u_t$ and a positive component along $v_t$ for
$0 < t < \pi/2$. Then the first coordinate of $\mathbf{x}(t)$ decreases strictly, the path does not
cross itself (Figure 7.2), and the areas that it bounds can be computed; the upper bound of
[Chapter 9](09-optimality.md) lives on the caps with this property. This chapter proves that every
balanced maximum cap has it ([Theorem 7.2](#theorem-72-injectivity-condition-baek-theorems-611-and-171);
Baek, Theorems 6.1.1 and 1.7.1), and that the cap of Gerver's sofa has it
([Theorem 7.3](#theorem-73-gervers-sofa-baek-theorem-612); Baek, Theorem 6.1.2). It covers Baek's
Chapter 6 and its overview, §1.7 of the paper.

The proof starts from the balancing equations by which Romik derived Gerver's sofa. Where the
hallway $L_t$ touches the sofa at the points $\mathbf{A}(t)$, $\mathbf{B}(t)$ and $\mathbf{x}(t)$
(Figure 7.1), the differential side lengths of the sofa at these points balance:
$\langle \mathbf{A}'(t), v_t\rangle = \langle -\mathbf{B}'(t), v_t\rangle + \langle \mathbf{x}'(t), v_t\rangle$
(Romik's Equation (20)). For a general balanced maximum sofa Baek proves an inequality instead,
which needs no assumption on the contacts:

```math
\langle \mathbf{A}'(t), v_t\rangle \le \max\bigl(\langle -\mathbf{B}'(t), v_t\rangle, 0\bigr) + \bigl\lvert \langle \mathbf{x}'(t), v_t\rangle \bigr\rvert .
```

The proof expresses it through the *arm lengths* $f$ and $g$, the distances from the outer corner of
the hallway to its contacts with the outer walls (Figure 7.3). The velocity of the rotation path is
$\mathbf{x}' = -(f - 1)\,u_t + (g - 1)\,v_t$, so the injectivity condition says $f, g > 1$. With
$\mathbf{B} = \mathbf{A} - u_t$, the speed $\rho = \langle \mathbf{A}', v_t\rangle$ satisfies
$\langle -\mathbf{B}', v_t\rangle = 1 - \rho$, and $\langle \mathbf{x}', v_t\rangle = g - 1$; the
inequality gives $\rho \le (\lvert g - 1\rvert + 1)/2$ if $\rho < 1$ and
$\rho \le \lvert g - 1\rvert$ otherwise. Since $\rho$ is the density of the surface area measure of
the cap $K$, this reads
$\sigma_K \le k_0(g)\,\mathrm{d}t$, with the explicit function $k_0$ of
[Definition 7.14](#definition-714-balancing-functions-baek-definition-634); and
since $f' = g - (\text{density of } \sigma_K)$, it becomes the differential inequality
$f' \ge m_0(g)$, $m_0(x) = x - k_0(x)$. Starting from the trivial bound $f \ge 0$, eleven rounds of
its integrated form, applied to the cap and to its mirror image, raise the lower bounds of $f$ and $g$
above $1$ (Figure 7.7).

Throughout, $\mathcal{K}^\mathrm{c}$ is the space of caps with rotation angle $\pi/2$, and
$\mathcal{A} = \mathcal{A}_{\pi/2}$ (Baek, Definition 6.1.1). For a cap $K$ and an angle $t$, the
supporting hallway $L_K(t)$ ([Chapter 3](03-monotone.md)) has the outer corner and the inner corner

```math
\mathbf{y}_K(t) = h_K(t)\,u_t + h_K(t + \pi/2)\,v_t , \qquad \mathbf{x}_K(t) = \mathbf{y}_K(t) - u_t - v_t
```

(Baek, Proposition 2.2.2), the outer walls $a_K(t) = l_K(t)$ and $c_K(t) = l_K(t + \pi/2)$ through
$\mathbf{y}_K(t)$, the inner walls $b_K(t)$ and $d_K(t)$ parallel to them at distance $1$ through
$\mathbf{x}_K(t)$, and the inner half-walls $\vec b_K(t)$ and $\vec d_K(t)$, which leave
$\mathbf{x}_K(t)$ in the directions $-v_t$ and $-u_t$. The vertices
$A_K^\pm(t) = v_K^\pm(t)$ and $C_K^\pm(t) = v_K^\pm(t + \pi/2)$ (Baek, Definition 2.5.1) are the ends
of the contacts of $K$ with the outer walls $a_K(t)$ and $c_K(t)$.

## 7.1 The statement

### Definition 7.1 (injectivity condition; Baek, Definition 6.1.2)

A cap $K \in \mathcal{K}^\mathrm{c}$ satisfies the *injectivity condition* if

1. there are measurable functions $r_K, s_K \ge 0$ with $\sigma_K = r_K(t)\,\mathrm{d}t$ on
   $[0, \pi/2)$ and $\sigma_K = s_K(t - \pi/2)\,\mathrm{d}t$ on $(\pi/2, \pi]$;
2. the inner corner $\mathbf{x}_K$ is continuously differentiable on $[0, \pi/2]$;
3. $\langle \mathbf{x}_K'(t), u_t\rangle < 0$ and $\langle \mathbf{x}_K'(t), v_t\rangle > 0$ for
   every $t \in (0, \pi/2)$.

*Lean: [`InjCond1`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L32), [`InjCond2`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L40), [`InjCond3`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L43), [`SatisfiesInjectivity`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L48).*

Condition (1) leaves $\sigma_K$ free at $\pi/2$, the top edge of the cap. The domain of the upper bound
of [Chapter 9](09-optimality.md) is the space $\mathcal{K}^\mathrm{i}$ of the caps with the
injectivity condition and area at least $2.2$.

### Theorem 7.2 (injectivity condition; Baek, Theorems 6.1.1 and 1.7.1)

Every balanced maximum cap $K \in \mathcal{K}^\mathrm{c}$ satisfies the injectivity condition. In
particular, the rotation path $\mathbf{x}$ of a balanced maximum sofa with rotation angle $\pi/2$ is
continuously differentiable on $[0, \pi/2]$, with
$\langle \mathbf{x}'(t), u_t\rangle < 0 < \langle \mathbf{x}'(t), v_t\rangle$ for
$t \in (0, \pi/2)$.

*Lean: [`theorem6_1_1`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L468), [`theorem1_7_1`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L485), [`IsBalancedMaxCap`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L133), [`IsBalancedMaxSofa`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L646).*

A balanced maximum cap is a Hausdorff limit of maximum polygon caps with the uniform angle sets
$\Theta_{n_i}$, where $n_1 < n_2 < \dots$ are powers of two (Baek, Definition 3.5.2;
[Chapter 4](04-balanced.md)), and a balanced maximum sofa is the monotone sofa of such a cap. The
rotation path of the sofa is the inner corner $\mathbf{x}_K$ of its cap $K$.

Theorem 7.2 implies that the rotation path does not cross itself, which gives the condition its name
(Figure 7.2). Indeed, $(1, 0) = \cos t\,u_t - \sin t\,v_t$, so for $t \in (0, \pi/2)$

```math
\langle \mathbf{x}'(t), (1, 0)\rangle = \cos t\,\langle \mathbf{x}'(t), u_t\rangle - \sin t\,\langle \mathbf{x}'(t), v_t\rangle < 0 ,
```

and the first coordinate of $\mathbf{x}(t)$ decreases strictly on $[0, \pi/2]$: $\mathbf{x}$ is a
Jordan arc.

### Theorem 7.3 (Gerver's sofa; Baek, Theorem 6.1.2)

For every solution of Romik's system with $\varphi \in [0.039, 0.04]$ and
$\theta \in [0.68, 0.69]$, the cap $K = \mathcal{C}(G)$ of Gerver's sofa $G$ satisfies the
injectivity condition.

*Lean: [`theorem6_1_2`](../../MovingSofaOptimality/Gerver/Properties.lean#L140), [`GerverParams.gv_injectivity`](../../MovingSofaOptimality/Gerver/Structure.lean#L143).*

The proof is in §7.6. The box contains exactly one solution of Romik's system
([Chapter 10](10-gerver.md)). Baek deduces Theorem 7.3 from Theorem 7.2 and Gerver's Theorem 2, read
as saying that maximum polygon sofas converge to $G$; Gerver's theorem says something else, and the
formalization proves Theorem 7.3 from Romik's equations instead (§7.6; REPORT.md, E12).

Baek's overview introduces the contact points of a sofa with its hallways (Baek, Definition 1.7.1):
when the wall $a(t)$, $b(t)$, $c(t)$ or $d(t)$ of $L_t$ touches $S$, the point of contact is
$\mathbf{A}(t)$, $\mathbf{B}(t)$, $\mathbf{C}(t)$ or $\mathbf{D}(t)$. For Gerver's sofa Romik writes
them through the rotation path (Figure 7.1):

```math
\begin{aligned}
\mathbf{A} &= \mathbf{x} + u_t + \langle \mathbf{x}', u_t\rangle\,v_t , & \mathbf{B} &= \mathbf{x} + \langle \mathbf{x}', u_t\rangle\,v_t , \\
\mathbf{C} &= \mathbf{x} + v_t - \langle \mathbf{x}', v_t\rangle\,u_t , & \mathbf{D} &= \mathbf{x} - \langle \mathbf{x}', v_t\rangle\,u_t .
\end{aligned}
```

The outer walls touch the sofa at $\mathbf{A}(t)$ and $\mathbf{C}(t)$ for every $t$; the wall $d(t)$
touches it at $\mathbf{D}(t)$ only for $t \in [0, \theta]$, and the wall $b(t)$ at $\mathbf{B}(t)$
only for $t \in [\pi/2 - \theta, \pi/2]$. The formulas give $\mathbf{B} = \mathbf{A} - u_t$ and
$\mathbf{D} = \mathbf{C} - v_t$: a contact with an inner wall lies at distance $1$ from the contact
with the parallel outer wall. Romik's balancing equations relate the speeds of these points along the
walls (Baek, Theorem 8.4.2; [Chapter 10](10-gerver.md)).

![Two panels showing Gerver's sofa, fixed, with its supporting hallway at the angle t = 0.45 (left) and at π/2 − 0.45 (right), drawn as a grey floor with dark walls. In each panel the outer walls a(t) and c(t) meet at the outer corner y(t) and touch the sofa at the blue points A(t) and C(t); the inner walls b(t) and d(t) meet at the orange inner corner x(t), which touches the niche of the sofa. On the left the wall d(t) also touches the sofa at the green point D(t), on the right the wall b(t) touches it at the green point B(t). The curves traced by A and C (blue) bound the cap, those traced by B and D (green) and the dashed rotation path x (orange) bound the niche](figures/07-injectivity/contacts.svg)

*Figure 7.1.* Gerver's sofa and its supporting hallways at $t = 0.45$ and at $t = \pi/2 - 0.45$,
computed from Romik's formulas. The contact points lie on their walls, and the curves they trace
bound the sofa: $\mathbf{A}$ and $\mathbf{C}$ (blue) bound the cap, and $\mathbf{D}$ on
$[0, \theta]$, $\mathbf{B}$ on $[\pi/2 - \theta, \pi/2]$ (green) and $\mathbf{x}$ on
$[\varphi, \pi/2 - \varphi]$ (orange) bound the niche.

![The cap K of Gerver's sofa, with its niche shaded orange under an arch, and the rotation path x drawn thick in orange from x(0) on the right to x(π/2) on the left, along the top of the niche. At three points of the path, t = π/8, π/4 and 3π/8, a small green quadrant is shaded between the directions −u_t and v_t, and the velocity x'(t), drawn as a black arrow, points into it; at π/4 it points straight to the left](figures/07-injectivity/rotation-path.svg)

*Figure 7.2.* The injectivity condition for Gerver's sofa. The velocity $\mathbf{x}'(t)$ (scaled by
$0.3$) lies in the open quadrant between $-u_t$ and $v_t$ (green) for $0 < t < \pi/2$, so the first
coordinate of $\mathbf{x}$ decreases from $\mathbf{x}(0) = (0, 0)$ to
$\mathbf{x}(\pi/2) \approx (-1.228, 0)$ and the path does not cross itself. The niche
$\mathcal{N}(K)$ lies under the path, between the green end curves of Figure 7.1.

*Outline of the proof of Theorem 7.2.*

1. *Arm lengths* (§7.2). The corners of the hallway move with the velocities
   $\mathbf{y}' = -f\,u_t + g\,v_t$ and $\mathbf{x}' = -(f - 1)\,u_t + (g - 1)\,v_t$
   ([Theorem 7.7](#theorem-77-derivatives-of-the-corners-baek-theorem-623)), and
   $\mathrm{d}f^+ = g^+\,\mathrm{d}t - \sigma_K$
   ([Theorem 7.9](#theorem-79-derivative-of-the-arm-f-baek-theorem-625)).
2. *Maximum polygon caps* (§7.3). Balancedness bounds the side of a maximum polygon cap with step
   size $\delta$: $\sigma_K(t) \le k_0(g^+(t))\,\delta + C\delta^2$
   ([Theorem 7.15](#theorem-715-discrete-inequality-baek-theorem-633)).
3. *Balanced maximum caps* (§7.4). In the limit, $\sigma_K \le k_0(g)\,\mathrm{d}t$ on $[0, \pi/2)$
   ([Theorem 7.18](#theorem-718-limit-inequality-baek-theorem-643)), which gives condition (1)
   ([Corollary 7.19](#corollary-719-condition-1-baek-corollary-644)), single contact points, and
   condition (2) ([Proposition 7.22](#proposition-722-regularity-of-the-corners-baek-proposition-646)).
4. *Bounding the arms* (§7.5). Then $f' \ge m_0(g)$
   ([Theorem 7.23](#theorem-723-differential-inequality-baek-theorem-651)); iterating its integral
   form gives $f, g > 1$ ([Theorem 7.29](#theorem-729-arms-longer-than-one-baek-theorem-656)),
   which is condition (3).

## 7.2 Arm lengths

### Definition 7.4 (arm lengths; Baek, Definition 6.2.1)

For a cap $K \in \mathcal{K}^\mathrm{c}$ and an angle $t$, the *arm lengths* are

```math
f_K^\pm(t) = \langle \mathbf{y}_K(t) - A_K^\pm(t), v_t\rangle , \qquad g_K^\pm(t) = \langle \mathbf{y}_K(t) - C_K^\pm(t), u_t\rangle .
```

*Lean: [`fPlus`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L51), [`fMinus`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L53), [`gPlus`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L55), [`gMinus`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L57), [`aPlus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L41), [`aMinus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L43), [`cPlus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L45), [`cMinus`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L47).*

In terms of the support function,
$f_K^\pm(t) = h_K(t + \pi/2) - \langle v_K^\pm(t), v_t\rangle$ and
$g_K^\pm(t) = h_K(t) + \langle v_K^\pm(t + \pi/2), v_{t + \pi/2}\rangle$, since
$v_{t + \pi/2} = -u_t$. The arm lengths are nonnegative, because $A_K^\pm(t)$ and $C_K^\pm(t)$ lie in
$K$, and $g_K^-(t) \le g_K^+(t)$, with difference $\sigma_K(t + \pi/2)$ by
[Proposition 6.10](06-surface-area.md#proposition-610-atoms-baek-proposition-212).

*Lean: [`inj_fPlus_eq`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L95), [`inj_gPlus_eq`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L105), [`inj_arm_nonneg`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L449).*

### Proposition 7.5 (the arms; Baek, Proposition 6.2.1)

For every cap $K$ and every angle $t$,

```math
\mathbf{y}_K(t) = A_K^\pm(t) + f_K^\pm(t)\,v_t = C_K^\pm(t) + g_K^\pm(t)\,u_t .
```

So $f_K^\pm(t)$ and $g_K^\pm(t)$ are the distances from the outer corner to the ends of the contacts
of $K$ with the outer walls.

*Lean: [`proposition6_2_1`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L118).*

*Proof.* The points $\mathbf{y}_K(t)$ and $A_K^\pm(t)$ lie on the line $a_K(t)$, which has the
direction $v_t$, so their difference is its own $v_t$-component $f_K^\pm(t)\,v_t$. Likewise
$\mathbf{y}_K(t)$ and $C_K^\pm(t)$ lie on $c_K(t)$, which has the direction $u_t$. $\square$

The identity holds for every convex body and every $t$; Baek's hypotheses that $K$ is a cap and
$t \in [0, \pi/2]$ are not used (REPORT.md, Section 5).

### Proposition 7.6 (mirror image; Baek, Proposition 6.2.2)

Let $K^\mathrm{m}$ be the image of a cap $K$ under the reflection $(x, y) \mapsto (-x, y)$, the
mirror reflection $M_{\pi/2}$ of Baek's Definition 2.5.6. Then for every $t$

```math
f_{K^\mathrm{m}}^\pm(t) = g_K^\mp(\pi/2 - t) , \qquad g_{K^\mathrm{m}}^\pm(t) = f_K^\mp(\pi/2 - t) .
```

*Lean: [`proposition6_2_2`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L150), [`mirrorCap`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L79).*

Baek's statement omits the change of angle and writes $g_K^\mp(t)$; the reflection reverses the
angle, and Lemma 6.5.2 of the paper uses the corrected form (REPORT.md, E13).

*Proof.* The reflection $M$ maps the hallway of $K$ at $\pi/2 - t$ to the hallway of $K^\mathrm{m}$
at $t$, exchanging the two outer walls: $\mathbf{y}_{K^\mathrm{m}}(t) = M\,\mathbf{y}_K(\pi/2 - t)$,
$A_{K^\mathrm{m}}^\pm(t) = M\,C_K^\mp(\pi/2 - t)$ and $C_{K^\mathrm{m}}^\pm(t) = M\,A_K^\mp(\pi/2 - t)$
(Baek, Proposition 2.5.4; [Chapter 3](03-monotone.md)). Moreover
$\langle Mw, v_t\rangle = \langle w, u_{\pi/2 - t}\rangle$ and
$\langle Mw, u_t\rangle = \langle w, v_{\pi/2 - t}\rangle$ for every vector $w$. Substitute both into
Definition 7.4. $\square$

### Theorem 7.7 (derivatives of the corners; Baek, Theorem 6.2.3)

Let $K \in \mathcal{K}^\mathrm{c}$. At every angle $t$, the corners of the hallway have the right
derivatives

```math
\begin{aligned}
\partial^+ \mathbf{y}_K(t) &= -f_K^+(t)\,u_t + g_K^+(t)\,v_t , \\
\partial^+ \mathbf{x}_K(t) &= -\bigl(f_K^+(t) - 1\bigr)\,u_t + \bigl(g_K^+(t) - 1\bigr)\,v_t ,
\end{aligned}
```

and the left derivatives given by the same formulas with $f_K^-$ and $g_K^-$.

*Lean: [`theorem6_2_3_right`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L201), [`theorem6_2_3_left`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L226).*

Baek's Definition 6.2.2 calls $\partial^+$ the left derivative while Theorem 6.2.3 uses it as the
right one, and the second display of the theorem writes $\partial^+\mathbf{x}_K$ for
$\partial^-\mathbf{x}_K$ (REPORT.md, E14). Baek restricts $t$ to $[0, \pi/2)$ and $(0, \pi/2]$; the
formulas hold for every $t$.

*Proof.* By [Lemma 6.7](06-surface-area.md#lemma-67-one-sided-derivatives-of-the-support-function),
$h_K$ has the right derivative $\langle v_K^+(t), v_t\rangle$ at $t$, and $h_K(\cdot + \pi/2)$ has
the right derivative $\langle v_K^+(t + \pi/2), v_{t + \pi/2}\rangle$. Differentiate
$\mathbf{y}_K(t) = h_K(t)\,u_t + h_K(t + \pi/2)\,v_t$ with $u_t' = v_t$ and $v_t' = -u_t$:

```math
\begin{aligned}
\partial^+\mathbf{y}_K(t) &= \bigl(\langle v_K^+(t), v_t\rangle - h_K(t + \pi/2)\bigr)\,u_t + \bigl(h_K(t) + \langle v_K^+(t + \pi/2), v_{t + \pi/2}\rangle\bigr)\,v_t \\
&= -f_K^+(t)\,u_t + g_K^+(t)\,v_t ,
\end{aligned}
```

by the support-function forms of the arms. Since $\mathbf{x}_K(t) = \mathbf{y}_K(t) - u_t - v_t$, its
right derivative is $\partial^+\mathbf{y}_K(t) - v_t + u_t$. The left derivatives come in the same way
from the left derivatives of Lemma 6.7. $\square$

The formula has a mechanical reading (Baek, Remark 6.2.1; Figure 7.3). When the hallway turns by
$\mathrm{d}t$, the outer wall $a_K(t)$ pivots about $A_K^+(t)$ and the wall $c_K(t)$ about
$C_K^+(t)$. The outer corner lies at the distances $f$ and $g$ from the pivots along the two walls,
so it moves by $-f\,u_t\,\mathrm{d}t$ and $g\,v_t\,\mathrm{d}t$; the inner corner lies at the distances
$f - 1$ and $g - 1$ from them, measured along the walls.

![Gerver's cap and its supporting hallway at t = 0.6. The outer walls a(t) and c(t), dark lines, meet at the outer corner y(t) at the top; the segment of a(t) from y(t) down to the contact point A(t) is drawn thick in purple and labelled f(t), the segment of c(t) from y(t) down to the contact point C(t) is drawn thick in green and labelled g(t). The inner walls, dashed, meet at the orange inner corner x(t), from which a black arrow x'(t) is drawn together with its two components: a purple arrow −(f − 1)u_t pointing down-left and a green arrow (g − 1)v_t pointing up-left](figures/07-injectivity/arms.svg)

*Figure 7.3.* The arm lengths of Gerver's cap at $t = 0.6$: $f(t) \approx 1.655$ (purple) and
$g(t) \approx 2.014$ (green), the distances from $\mathbf{y}(t)$ to $\mathbf{A}(t)$ and
$\mathbf{C}(t)$. The velocity $\mathbf{x}'(t)$ of the inner corner, drawn at half scale, is the sum
of $-(f(t) - 1)\,u_t$ and $(g(t) - 1)\,v_t$.

### Lemma 7.8 (the arm as an integral; Baek, Lemma 6.2.4)

For every cap $K \in \mathcal{K}^\mathrm{c}$ and every angle $t$,

```math
g_K^+(t) = \int_{(t, t + \pi/2]} \sin(s - t)\,\mathrm{d}\sigma_K(s) .
```

*Lean: [`lemma6_2_4`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L251).*

*Proof.* The points $\mathbf{y}_K(t)$ and $A_K^+(t) = v_K^+(t)$ lie on $l_K(t)$, so
$g_K^+(t) = \langle A_K^+(t) - C_K^+(t), u_t\rangle = -\langle v_K^+(t + \pi/2) - v_K^+(t), u_t\rangle$.
By [Theorem 6.12](06-surface-area.md#theorem-612-differential-gaussminkowski-theorem-baek-theorem-522),
$v_K^+(t + \pi/2) - v_K^+(t) = \int_{(t, t + \pi/2]} v_s\,\mathrm{d}\sigma_K(s)$, and
$-\langle v_s, u_t\rangle = \sin(s - t)$. $\square$

### Theorem 7.9 (derivative of the arm f; Baek, Theorem 6.2.5)

For every convex body $K$, the arm length $f_K^+$ is right-continuous and of bounded variation on
$[0, \pi/2]$, and

```math
\mathrm{d}f_K^+(t) = g_K^+(t)\,\mathrm{d}t - \sigma_K \qquad \text{as measures on } (0, \pi/2] .
```

Equivalently, $f_K^+(b) - f_K^+(a) = \int_a^b g_K^+ - \sigma_K((a, b])$ for $a \le b$.

*Lean: [`theorem6_2_5_regular`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L365), [`theorem6_2_5`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L409), [`fPlus_sub_fPlus`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L471).*

*Proof.* With the distribution function $G_K$ of
[Definition 6.8](06-surface-area.md#definition-68-surface-area-measure),

```math
f_K^+(t) = h_K(t + \pi/2) - \langle v_K^+(t), v_t\rangle = \Bigl(h_K(t + \pi/2) + \int_0^t h_K\Bigr) - G_K(t) .
```

By Lemma 6.7, $h_K$ is a Lipschitz function with the right derivative
$\langle v_K^+(s), v_s\rangle$ everywhere, so it is the integral of it, and the bracket equals
$h_K(\pi/2) + \int_0^t \bigl(h_K(s) + \langle v_K^+(s + \pi/2), v_{s + \pi/2}\rangle\bigr)\,\mathrm{d}s = h_K(\pi/2) + \int_0^t g_K^+$.
It is absolutely continuous, and $G_K(b) - G_K(a) = \sigma_K((a, b])$. This gives the integrated
form. So $f_K^+$ is an absolutely continuous function minus a nondecreasing right-continuous one,
hence right-continuous and of bounded variation, and the two measures agree on every interval
$(a, b] \subseteq (0, \pi/2]$, so they are equal. $\square$

Baek computes $\mathrm{d}f_K^+$ with the product rule
([Lemma 6.4](06-surface-area.md#lemma-64-product-rule-baek-lemma-513)) and Theorem 6.12; the
formalization reads it off the definition of $\sigma_K$.

## 7.3 The inequality on maximum polygon caps

This section uses the polygon caps of [Chapter 4](04-balanced.md). For $\omega = \pi/2$, a polygon cap
with angle set $\Theta$ is a cap that is an intersection of closed half-planes with normal angles in
$\Theta \cup (\Theta + \pi/2) \cup \lbrace \pi/2, 3\pi/2\rbrace$; its polygon niche is
$\mathcal{N}_\Theta(K) = \lbrace y \ge 0\rbrace \cap \bigcup_{t \in \Theta} Q_K^-(t)$, the union of the
open inner quadrants $Q_K^-(t)$ of its hallways above the $x$-axis; and a maximum polygon cap
maximizes $\mathcal{A}_\Theta$. Two results of that chapter are used here: a maximum polygon cap is
*balanced*, that is, for $t \in \Theta$ the side length $\sigma_K(t)$ equals the length $\tau_K(t)$
of the side of the niche on the inner wall $\vec b_K(t)$ (Baek, Theorem 3.4.9 and Lemma 3.4.5); and
it contains its niche (Baek, Theorem 3.4.10).

*Lean: [`IsPolygonCap`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L43), [`polyNiche`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L53), [`IsMaxPolygonCap`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L1864), [`MovingSofaOptimality.tau`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L3240), [`theorem3_4_9`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4683),
[`lemma3_4_5_one`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L3981), [`theorem3_4_10`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L4717).*

### Definition 7.10 (steps; Baek, Definitions 6.3.1 and 6.3.2)

For $n = 2^{k + 1}$, $k \ge 0$, let $\Theta_n = \lbrace (\pi/2)\,j/n : 0 < j < n\rbrace$ and
$\delta = (\pi/2)/n$. A *maximum polygon cap with $n$ steps* of step size $\delta$ is a maximum
polygon cap with the angle set $\Theta_n$.

*Lean: [`rightAngleSet`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L27), [`stepSize`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L30).*

The edges of such a cap $K$ have normal angles in $\delta\mathbb{Z}$; in particular $K$ has no edge
with normal angle $0$, and between two consecutive multiples $m\delta < (m + 1)\delta$ in $[0, \pi]$
the vertices $v_K^\pm(s)$ are one point, the intersection of the two supporting lines.

*Lean: [`inj_polygon_consecutive`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L258), [`inj_polygon_vplus_zero`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L302).*

### Lemma 7.11 (diameter; Baek, Lemma 6.3.1)

A maximum polygon cap $K$ with $n$ steps has diameter at most $5$. Consequently its arm lengths
$f_K^\pm(t)$ and $g_K^\pm(t)$ are at most $5$ for $t \in [0, \pi/2]$.

*Lean: [`lemma6_3_1`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L487).*

*Proof.* Since $n \ge 2$ is even, $\pi/4 \in \Theta_n$. The inner corner $\mathbf{x}_K(\pi/4)$ has
height at most $1$: otherwise a point just below it would lie in the quadrant $Q_K^-(\pi/4)$ and
above the $x$-axis, hence in the polygon niche, hence in $K$ (Theorem 3.4.10), while $K$ lies in the
strip $0 \le y \le 1$. Every point $p$ of $K$ satisfies
$\langle p, u_{\pi/4}\rangle \le \langle \mathbf{x}_K(\pi/4), u_{\pi/4}\rangle + 1$ and
$\langle p, v_{\pi/4}\rangle \le \langle \mathbf{x}_K(\pi/4), v_{\pi/4}\rangle + 1$, the two outer
walls, and $0 \le p_y \le 1$. With $u_{\pi/4} = (1, 1)/\sqrt2$ and $v_{\pi/4} = (-1, 1)/\sqrt2$,
adding the first inequality for $p \in K$ to the second for $q \in K$ gives
$p_x - q_x \le 2 + 2\sqrt2$, since the height of $\mathbf{x}_K(\pi/4)$ is at most $1$ and
$p_y + q_y \ge 0$. So $\lvert p_x - q_x\rvert \le 2 + 2\sqrt2$, and
$\lvert p - q\rvert^2 \le (2 + 2\sqrt2)^2 + 1 = 13 + 8\sqrt2 < 25$. For the arms, Proposition 7.5
gives $A_K^\pm(t) - C_K^\pm(t) = g_K^\pm(t)\,u_t - f_K^\pm(t)\,v_t$, a vector between two points of
$K$; so the nonnegative numbers $f_K^\pm(t)$ and $g_K^\pm(t)$ are at most $5$. $\square$

Baek's proof cites Theorem 3.5.4, about balanced maximum caps, for the bound on the height of the
inner corner; Theorem 3.4.10 is the result that applies to maximum polygon caps (REPORT.md, E15).

### Definition 7.12 (half-planes above the inner walls; Baek, Definition 6.3.3)

For a cap $K$ and an angle $t$, let

```math
H_K^\mathrm{b}(t) = \lbrace p : \langle p, u_t\rangle \ge h_K(t) - 1\rbrace , \qquad H_K^\mathrm{d}(t) = \lbrace p : \langle p, v_t\rangle \ge h_K(t + \pi/2) - 1\rbrace ,
```

the closed half-planes bounded by the inner walls $b_K(t)$ and $d_K(t)$ on the side of the outer
walls.

*Lean: [`halfB`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L410), [`halfD`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L414).*

The open quadrant $Q_K^-(t)$ is the complement of $H_K^\mathrm{b}(t) \cup H_K^\mathrm{d}(t)$.

### Lemma 7.13 (the inner wall near the corner; Baek, Lemma 6.3.2)

Let $K$ be a maximum polygon cap with step size $\delta$, and let $t \in \Theta_n$. Then the lengths
of the parts of the inner half-wall $\vec b_K(t)$ in the half-planes of the neighbouring angles are

1. $\mathcal{H}^1\bigl(\vec b_K(t) \cap H_K^\mathrm{d}(t - \delta)\bigr) = \tan\delta \cdot \max\bigl(0,\ g_K^-(t) - 1 + \tan(\delta/2)\bigr)$;
2. $\mathcal{H}^1\bigl(\vec b_K(t) \cap H_K^\mathrm{d}(t + \delta)\bigr) = \tan\delta \cdot \max\bigl(0,\ 1 - g_K^+(t) + \tan(\delta/2)\bigr)$.

*Lean: [`lemma6_3_2`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L738), [`lineLength`](../../MovingSofaOptimality/Basic/Plane.lean#L64).*

Here $\mathcal{H}^1$ is the length of a subset of a line. In Baek's proof of (1), two occurrences of
$t + \delta$ should read $t - \delta$ (REPORT.md, E26).

![The supporting hallway L(t) of a polygon cap K drawn upright as the standard hallway, with the cap shaded blue. The dashed purple lines c(t − δ) and d(t − δ) are the outer and inner walls of the hallway at the previous angle, tilted by δ. The line d(t − δ) meets the wall d(t) at q, to the left of the inner corner x(t), and the inner wall b(t) at p, below x(t); the right triangle p q x(t) is shaded orange, with the angle δ marked at q and the segment from p to x(t) drawn thick. The line c(t − δ) meets the top wall c(t) at the vertex r = C⁻(t) of the cap, and the segment of c(t) from r to the outer corner y(t) is drawn thick in green and labelled g⁻(t)](figures/07-injectivity/leg-computation.svg)

*Figure 7.4.* Lemma 7.13 (1), for the polygon cap with the angle set $\Theta_4$ whose support values
at its normal angles are those of Gerver's cap, at $t = \pi/4$ and $\delta = \pi/8$. The part of
$\vec b_K(t)$ above $d_K(t - \delta)$ is the side $[p, \mathbf{x}_K(t)]$ of the right triangle
$p\,q\,\mathbf{x}_K(t)$, of length $\tan\delta \cdot \lvert q - \mathbf{x}_K(t)\rvert$; here
$g_K^-(t) \approx 1.680$ and the side has length $0.364$. The computation uses only that $t - \delta$
and $t$ are consecutive normal angles, so it applies to this cap, which is not a maximum polygon
cap.

*Proof.* (1) Let $p$ be the intersection of $d_K(t - \delta)$ with $b_K(t)$, and write
$p = \mathbf{x}_K(t) - \alpha\,v_t$ (Figure 7.4). Moving down $\vec b_K(t)$ from $\mathbf{x}_K(t)$
decreases $\langle \cdot, v_{t - \delta}\rangle$, so the part of $\vec b_K(t)$ in
$H_K^\mathrm{d}(t - \delta)$ is the segment from $\mathbf{x}_K(t)$ to $p$ if $\alpha \ge 0$ and is
empty otherwise: its length is $\max(\alpha, 0)$. Let $q$ be the intersection of $d_K(t - \delta)$
with $d_K(t)$, and write $q = \mathbf{x}_K(t) - \beta\,u_t$. The triangle $p\,q\,\mathbf{x}_K(t)$ has
a right angle at $\mathbf{x}_K(t)$ and the angle $\delta$ at $q$, so $\alpha = \beta\tan\delta$.

To compute $\beta$, let $r$ be the intersection of $c_K(t - \delta)$ with $c_K(t)$. The walls
$c_K(t)$, $d_K(t)$ are parallel at distance $1$, and so are $c_K(t - \delta)$, $d_K(t - \delta)$; the
two pairs meet at the angle $\delta$, so $r = q + v_t + \tan(\delta/2)\,u_t$. The lines
$c_K(t - \delta) = l_K(t - \delta + \pi/2)$ and $c_K(t) = l_K(t + \pi/2)$ support $K$ at consecutive
normal angles, so $r$ is the vertex $v_K^-(t + \pi/2) = C_K^-(t)$, and
$\mathbf{y}_K(t) = r + g_K^-(t)\,u_t$ by Proposition 7.5. Hence

```math
\beta = \langle \mathbf{x}_K(t) - q, u_t\rangle = \langle \mathbf{y}_K(t) - u_t - v_t - r + v_t + \tan(\delta/2)\,u_t,\ u_t\rangle = g_K^-(t) - 1 + \tan(\delta/2) .
```

(2) is the same computation at $t + \delta$, with $q = \mathbf{x}_K(t) + \beta\,u_t$ and
$r = C_K^+(t)$, which gives $\beta = 1 - g_K^+(t) + \tan(\delta/2)$. $\square$

### Definition 7.14 (balancing functions; Baek, Definition 6.3.4)

For real $x$, let

```math
k_0(x) = \max\Bigl(\lvert x - 1\rvert,\ \frac{\lvert x - 1\rvert + 1}{2}\Bigr) , \qquad m_0(x) = x - k_0(x) .
```

*Lean: [`MovingSofaOptimality.k0`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L752), [`MovingSofaOptimality.m0`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L755).*

Baek defines them for $x \ge 0$; the formalization for all real $x$. The function $k_0$ is
$1$-Lipschitz, with its minimum $\frac12$ at $x = 1$, and $m_0$ is nondecreasing and piecewise
linear: $m_0(x) = \frac32 x - 1$ on $[0, 1]$, $\frac x2$ on $[1, 2]$, and $1$ on $[2, \infty)$
(Figure 7.5). In particular $m_0(0) = -1$, $m_0(2/3) = 0$ and $m_0(3/4) = \frac18$.

![The graphs of k₀ and m₀ for x from 0 to 3, with the diagonal dashed. The graph of k₀, purple, falls from 1 at x = 0 to 1/2 at x = 1 and then rises, with slope 1/2 up to x = 2 and slope 1 after. The graph of m₀, orange, rises from −1 at 0 through 0 at 2/3 to 1/2 at 1, where it meets k₀, then with slope 1/2 to 1 at 2, where it meets k₀ again, and stays at 1](figures/07-injectivity/k0-m0.svg)

*Figure 7.5.* The functions $k_0$ (purple) and $m_0$ (orange). The bound
$\sigma_K \le k_0(g)\,\mathrm{d}t$ allows the largest density, $\lvert g - 1\rvert$ or
$(\lvert g - 1\rvert + 1)/2$, when the arm $g$ is far from $1$, and $m_0(g) = g - k_0(g)$ is then the
least slope of $f$.

### Theorem 7.15 (discrete inequality; Baek, Theorem 6.3.3)

There is an absolute constant $C$ such that for every maximum polygon cap $K$ with $n$ steps of step
size $\delta$ and every $t \in \lbrace 0\rbrace \cup \Theta_n$,

```math
\sigma_K(t) \le k_0\bigl(g_K^+(t)\bigr)\,\delta + C\,\delta^2 .
```

*Lean: [`theorem6_3_3`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L961).*

The formalization proves it with $C = 7$.

*Proof.* For $t = 0$: $K$ has no edge with normal angle $0$, so $\sigma_K(0) = 0$. Let now
$t \in \Theta_n$, and let $s = \sigma_K(t)$ and $X = \vec b_K(t) \cap \partial\mathcal{N}_\Theta(K)$,
the side of the polygon niche on the inner wall. By balancedness, $s = \tau_K(t) = \mathcal{H}^1(X)$.
Let $U = \lbrace t - \delta, t, t + \delta\rbrace$,

```math
R = \bigcup_{u \in U} H_K^\mathrm{d}(u) , \qquad S = \bigcap_{u \in U} H_K^\mathrm{b}(u) .
```

**Step 1. $X$ lies in $R \cup S$, up to one point.** A point of $X$ lies in the closure of the open
niche but, except possibly the point where $b_K(t)$ meets the $x$-axis, not in the niche itself. So
it lies outside $Q_K^-(u)$ for every $u \in U$: for $u \in \Theta_n$ because
$Q_K^-(u) \cap \lbrace y \ge 0\rbrace$ is part of the niche, and for $u \in \lbrace 0, \pi/2\rbrace$
because $Q_K^-(u)$ lies below the $x$-axis. Since $Q_K^-(u)$ is the complement of
$H_K^\mathrm{b}(u) \cup H_K^\mathrm{d}(u)$, the point lies in $H_K^\mathrm{d}(u)$ for some $u$, that
is in $R$, or in $H_K^\mathrm{b}(u)$ for every $u$, that is in $S$ (Figure 7.6).

**Step 2. The part in $R$.** Each set $\vec b_K(t) \cap H_K^\mathrm{d}(u)$ is empty or a segment
from $\mathbf{x}_K(t)$ (for $u = t$, the point itself), so $\vec b_K(t) \cap R$ is the longest of
them. By Lemma 7.13, Lemma 7.11 and $\tan\delta = \delta + O(\delta^3)$,

```math
\mathcal{H}^1(X \cap R) \le \delta \cdot \max\bigl(0,\ g_K^-(t) - 1,\ 1 - g_K^+(t)\bigr) + O(\delta^2) \le \delta\,\bigl\lvert g_K^+(t) - 1\bigr\rvert + O(\delta^2) .
```

The second inequality uses $g_K^-(t) \le g_K^+(t)$: if $g_K^-(t) \le 1$, the maximum is
$\max(0, 1 - g_K^+(t))$, and otherwise it is $g_K^-(t) - 1 \le g_K^+(t) - 1$.

**Step 3. The part in $S$.** The inner walls $b_K(u)$ are the supporting lines $a_K(u) = l_K(u)$
moved inward by $1$. The edge $e_K(t)$ runs from $l_K(t) \cap l_K(t - \delta)$ to
$l_K(t) \cap l_K(t + \delta)$, a length $s$ in the direction $v_t$. Moving the three lines inward
moves these two ends to $B_- = b_K(t) \cap b_K(t - \delta)$ and $B_+ = b_K(t) \cap b_K(t + \delta)$,
each by $\tan(\delta/2)$ towards the other along $v_t$, so $B_+ - B_- = (s - 2\tan(\delta/2))\,v_t$.
On the line $b_K(t)$, the half-plane $H_K^\mathrm{b}(t - \delta)$ is the ray from $B_-$ in the
direction $-v_t$ and $H_K^\mathrm{b}(t + \delta)$ the ray from $B_+$ in the direction $v_t$. So
$b_K(t) \cap S$ is the segment $[B_+, B_-]$ of length $2\tan(\delta/2) - s$ when this is positive,
and empty otherwise, and

```math
\mathcal{H}^1(X \setminus R) \le \max\bigl(0,\ 2\tan(\delta/2) - s\bigr) \le \max(0,\ \delta - s) + O(\delta^3) .
```

**Step 4. The two cases.** Adding steps 2 and 3,
$s \le \delta\,\lvert g_K^+(t) - 1\rvert + \max(0, \delta - s) + O(\delta^2)$. If $s \le \delta$, this
gives $2s \le \delta\,(\lvert g_K^+(t) - 1\rvert + 1) + O(\delta^2)$; if $s > \delta$, it gives
$s \le \delta\,\lvert g_K^+(t) - 1\rvert + O(\delta^2)$. In both cases
$s \le k_0(g_K^+(t))\,\delta + O(\delta^2)$, and the error terms are bounded by an absolute constant
times $\delta^2$ because the arms are at most $5$ (Lemma 7.11). $\square$

In Baek's proof one $\mathcal{H}^1$ is missing inside a maximum and $\nu_K$ stands for $\tau_K$
(REPORT.md, E26).

![The supporting hallway L(t) of the polygon cap drawn upright, with the cap shaded light blue and the polygon niche, the union of three open quadrants above the x-axis of the sofa (a grey line at 45 degrees), shaded orange. Dashed lines d(t − δ) (purple) and d(t + δ) (green) cross the hallway near the corner, and dotted lines b(t − δ) (purple) and b(t + δ) (green) cross the inner wall b(t) further down. On b(t), two thick orange segments form the side of the niche: one from the corner x(t) down to the point p where d(t − δ) crosses, labelled in R, and a short one between the crossing points B₋ and B₊ of b(t − δ) and b(t + δ), labelled in S](figures/07-injectivity/discrete-inequality.svg)

*Figure 7.6.* Step 1 of the proof of Theorem 7.15, for the polygon cap of Figure 7.4. The side $X$
of the polygon niche on $\vec b_K(t)$ (thick) consists of the segment $[p, \mathbf{x}_K(t)]$, above
$d_K(t - \delta)$ and hence in $R$, and the segment $[B_+, B_-]$ between $b_K(t - \delta)$ and
$b_K(t + \delta)$, in $S$; in between, $\vec b_K(t)$ runs inside the quadrant $Q_K^-(t - \delta)$.
Here $\sigma_K(t) \approx 0.352$ and $\lvert B_- - B_+\rvert = 2\tan(\delta/2) - \sigma_K(t) \approx 0.046$.
This cap is not a maximum polygon cap, so $\mathcal{H}^1(X)$ need not equal $\sigma_K(t)$; the
inclusion of Step 1 holds for every polygon cap.

## 7.4 The inequality on balanced maximum caps

### Lemma 7.16 (arms between two steps; Baek, Lemma 6.4.1)

Let $K$ be a maximum polygon cap with $n$ steps of step size $\delta$, and let
$t \in \lbrace 0\rbrace \cup \Theta_n$. Then

1. $g_K^+(t) \ge g_K^+(t') = g_K^-(t') \ge g_K^-(t + \delta)$ for every $t' \in (t, t + \delta)$;
2. $g_K^+(t) - g_K^-(t + \delta) \le 5\delta$.

*Lean: [`lemma6_4_1`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L53).*

*Proof.* On $[t, t + \delta]$ the cap has a single vertex $A$ on the lines $l_K(s)$ and a single
vertex $C$ on the lines $l_K(s + \pi/2)$ (Definition 7.10): $h_K(s) = \langle A, u_s\rangle$, and the
arms at $t$ from the right, at $t + \delta$ from the left and at $t'$ from both sides are values of
$g(s) = \langle A - C, u_s\rangle$. Its derivative $\langle A - C, v_s\rangle$ lies in $[-5, 0]$: it is
at most $0$ because $\langle A, v_s\rangle \le h_K(s + \pi/2) = \langle C, v_s\rangle$, and at least
$-5$ because $\lvert A - C\rvert \le 5$ (Lemma 7.11). So $g$ is nonincreasing and $g(s) + 5s$ is
nondecreasing on $[t, t + \delta]$. $\square$

Baek's proof follows the outer corner along the circle with diameter $AC$, on which it moves by
Thales' theorem.

### Lemma 7.17 (convergence of the arms; Baek, Lemma 6.4.2)

If polygon caps $K_n$ converge to a cap $K \in \mathcal{K}^\mathrm{c}$ in the Hausdorff distance,
then $\int_0^{\pi/2} \lvert g_{K_n}^+ - g_K^+\rvert \to 0$.

*Lean: [`lemma6_4_2`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L312).*

*Proof.* The arms are nonnegative and at most the widths $h(t) + h(t + \pi)$, which are bounded
uniformly in $n$, so by dominated convergence it suffices to show $g_{K_n}^+(t) \to g_K^+(t)$ for
almost every $t$. Let $t$ be an angle with $\sigma_K(t + \pi/2) = 0$, which excludes only countably
many $t$, and put $s = t + \pi/2$. Since
$g_L^+(t) = h_L(t) + \langle v_L^+(s), v_s\rangle$ and $h_{K_n} \to h_K$ uniformly, it suffices that
$\langle v_{K_n}^+(s), v_s\rangle \to \langle v_K^+(s), v_s\rangle$. For every convex body $L$ and
$\varepsilon \in (0, \pi)$,

```math
\langle v_L(s - \varepsilon, s), v_s\rangle \le \langle v_L^-(s), v_s\rangle \le \langle v_L^+(s), v_s\rangle \le \langle v_L(s, s + \varepsilon), v_s\rangle ,
```

because $v_L^-(s) \in L$ lies in the supporting half-plane at $s - \varepsilon$ and $v_L^+(s)$ in the
one at $s + \varepsilon$. The intersection
points $v_L(a, b)$ are explicit in the support values, so the outer terms for $L = K_n$ converge to
those for $K$ as $n \to \infty$; as $\varepsilon \to 0^+$ these tend to
$\langle v_K^-(s), v_s\rangle$ and $\langle v_K^+(s), v_s\rangle$ (Baek, Theorem 2.1.3), which are
equal because $\sigma_K(s) = 0$. $\square$

Baek's proof writes $g^\pm$ as integrals against $\sigma$ (Lemma 7.8) and applies the Portmanteau
theorem to the weak convergence $\sigma_{K_n} \to \sigma_K$; the formalization uses the sandwich
above instead. The polygon caps need not have rotation angle $\pi/2$ (REPORT.md, Section 5), and in
Baek's proof $\sigma(\lbrace t\rbrace) = 0$ should read $\sigma(\lbrace t + \pi/2\rbrace) = 0$
(REPORT.md, E26).

### Theorem 7.18 (limit inequality; Baek, Theorem 6.4.3)

For every balanced maximum cap $K \in \mathcal{K}^\mathrm{c}$,
$\sigma_K \le k_0(g_K^+(t))\,\mathrm{d}t$ on $[0, \pi/2)$: for every Borel set
$X \subseteq [0, \pi/2)$,

```math
\sigma_K(X) \le \int_X k_0\bigl(g_K^+(t)\bigr)\,\mathrm{d}t .
```

*Lean: [`theorem6_4_3`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L815).*

*Proof sketch.* Let $K_i \to K$ be maximum polygon caps with $n_i$ steps of size $\delta_i \to 0$.

1. *Summing the steps.* For $t \in \lbrace 0\rbrace \cup \Theta_{n_i}$, Theorem 7.15 and
   Lemma 7.16, with the $1$-Lipschitz $k_0$, give
   $\sigma_{K_i}(t) \le \int_t^{t + \delta_i} k_0(g_{K_i}^+) + (C + 5)\,\delta_i^2$. The measure
   $\sigma_{K_i}$ is concentrated on the multiples of $\delta_i$, and an interval of $[0, \pi/2]$
   contains at most $n_i = \pi/(2\delta_i)$ of them, so for $0 \le a \le b \le \pi/2$
   ```math
   \sigma_{K_i}\bigl([a, b)\bigr) \le \int_a^b k_0\bigl(g_{K_i}^+\bigr) + C'\,\delta_i , \qquad C' = 8 + \frac\pi2\,(C + 5) .
   ```
   A cap has no edge with normal angle in $(-\pi/2, 0)$, so the same bound holds for $\sigma_{K_i}$ of
   an open interval $(a, b)$ with $-\pi/2 \le a$, with $\max(a, 0)$ as the lower limit of the integral.
2. *The right side.* By Lemma 7.17 and the $1$-Lipschitz $k_0$,
   $\int_a^b k_0(g_{K_i}^+) \to \int_a^b k_0(g_K^+)$.
3. *The left side.* From Definition 6.8 and Baek's Theorem 2.1.3,
   $\sigma_L((a, b)) = \langle v_L^-(b), v_b\rangle - \langle v_L^+(a), v_a\rangle + \int_a^b h_L$
   for every convex body $L$. The sandwich of Lemma 7.17 bounds it below by
   $\langle v_L(b - \varepsilon, b), v_b\rangle - \langle v_L(a, a + \varepsilon), v_a\rangle + \int_a^b h_L$,
   which for $L = K_i$ converges to the same expression for $K$, and that tends to
   $\sigma_K((a, b))$ as $\varepsilon \to 0^+$. So
   $\sigma_K((a, b)) \le \int_{\max(a, 0)}^b k_0(g_K^+)$ for every open interval $(a, b)$ with
   $-\pi/2 \le a < b \le \pi/2$.
4. *All Borel sets.* Two finite measures on $\mathbb{R}$ that compare on all open intervals compare on
   all Borel sets. $\square$

*Lean: [`inj_step_bound`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L539), [`inj_polygon_Ico_bound`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L567), [`inj_sigma_Ioo_toReal`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L451), [`inj_measure_le_of_Ioo`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L368).*

Baek takes the limit of the left side with the Portmanteau theorem: $\sigma_{K_i} \to \sigma_K$ weakly
([Theorem 6.14](06-surface-area.md#theorem-614-weak-convergence-baek-theorem-413)), so
$\sigma_K(I) \le \liminf \sigma_{K_i}(I)$ for open $I$. In the paper the difference
$g_{K_n}^+ - g_{K_n}^+$ should read $g_{K_n}^+ - g_K^+$ (REPORT.md, E26).

### Corollary 7.19 (condition (1); Baek, Corollary 6.4.4)

Every balanced maximum cap satisfies condition (1) of the injectivity condition.

*Lean: [`corollary6_4_4`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L900).*

*Proof.* By Theorem 7.18, $\sigma_K$ restricted to $[0, \pi/2)$ is absolutely continuous with respect
to $\mathrm{d}t$, so by the Radon–Nikodym theorem it is $r_K(t)\,\mathrm{d}t$ for a measurable
$r_K \ge 0$. The mirror image $K^\mathrm{m}$ is a balanced maximum cap (Baek, Proposition 3.5.1), and
$\sigma_{K^\mathrm{m}}(E) = \sigma_K(\pi - E)$ (Baek, Proposition 2.5.4). So $\sigma_K$ restricted to
$(\pi/2, \pi]$ is absolutely continuous too, with a density $s_K(t - \pi/2)$. $\square$

*Lean: [`proposition3_5_1`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L182), [`proposition2_5_4_sigma`](../../MovingSofaOptimality/Monotone/CapContainsNiche.lean#L718).*

### Proposition 7.20 (single contact points; Baek, Proposition 6.4.5)

Let $K \in \mathcal{K}^\mathrm{c}$ satisfy condition (1). Then $A_K^+(t) = A_K^-(t)$ and
$f_K^+(t) = f_K^-(t)$ for $t \in [0, \pi/2)$, and $C_K^+(t) = C_K^-(t)$ and
$g_K^+(t) = g_K^-(t)$ for $t \in (0, \pi/2]$.

*Lean: [`proposition6_4_5`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L986).*

*Proof.* Condition (1) gives $\sigma_K(t) = 0$ for $t \in [0, \pi/2) \cup (\pi/2, \pi]$, and
$v_K^+(t) = v_K^-(t) + \sigma_K(t)\,v_t$ by Proposition 6.10. $\square$

### Definition 7.21 (contacts and arms of a cap; Baek, Definition 6.4.1)

For $K \in \mathcal{K}^\mathrm{c}$ satisfying condition (1), let $A_K = A_K^-$, $f_K = f_K^-$,
$C_K = C_K^+$ and $g_K = g_K^+$ on $[0, \pi/2]$. By Proposition 7.20 these are the common values of
$A_K^\pm$ and $f_K^\pm$ on $[0, \pi/2)$, and of $C_K^\pm$ and $g_K^\pm$ on $(0, \pi/2]$.

*Lean: [`MovingSofaOptimality.aK`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L999), [`MovingSofaOptimality.fK`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L1001), [`MovingSofaOptimality.cK`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L1004),
[`MovingSofaOptimality.gK`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L1006).*

Baek's definition gives $f_K$ and $g_K$ the values $\mathbb{R}^2$ by a slip (REPORT.md, E16).

### Proposition 7.22 (regularity of the corners; Baek, Proposition 6.4.6)

Let $K \in \mathcal{K}^\mathrm{c}$ satisfy condition (1).

1. $A_K$, $C_K$, $f_K$ and $g_K$ are continuous on $[0, \pi/2]$.
2. $\mathbf{x}_K$ and $\mathbf{y}_K$ are continuously differentiable on $[0, \pi/2]$, with
   ```math
   \mathbf{x}_K'(t) = -\bigl(f_K(t) - 1\bigr)\,u_t + \bigl(g_K(t) - 1\bigr)\,v_t , \qquad \mathbf{y}_K'(t) = -f_K(t)\,u_t + g_K(t)\,v_t .
   ```

*Lean: [`proposition6_4_6_continuous`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L1010), [`proposition6_4_6_deriv`](../../MovingSofaOptimality/Injectivity/LimitIneq.lean#L1070).*

*Proof.* (1) By Baek's Theorem 2.1.3, $v_K^-$ is left-continuous, and as $s \to t^+$ it tends to
$v_K^+(t)$, which is $v_K^-(t)$ for $t \in [0, \pi/2)$ by Proposition 7.20; so $A_K = v_K^-$ is
continuous on $[0, \pi/2]$. In the same way $C_K = v_K^+(\cdot + \pi/2)$ is continuous, and so are the
arms, since $\mathbf{y}_K$ is. (2) By Proposition 7.20 the right and left derivatives of Theorem 7.7
agree at every $t \in (0, \pi/2)$, so $\mathbf{x}_K$ and $\mathbf{y}_K$ are differentiable with the
stated derivatives (one-sided at the ends), which are continuous by (1). $\square$

## 7.5 Bounding the arm lengths

### Theorem 7.23 (differential inequality; Baek, Theorem 6.5.1)

For every balanced maximum cap $K$, the arm length $f_K$ is absolutely continuous on $[0, \pi/2]$, and
$f_K'(t) \ge m_0(g_K(t))$ for almost every $t \in [0, \pi/2]$.

*Lean: [`theorem6_5_1`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L84).*

*Proof.* By Corollary 7.19, $\sigma_K = r_K(t)\,\mathrm{d}t$ on $[0, \pi/2)$, and by Theorem 7.18,
$r_K \le k_0(g_K)$ almost everywhere on $[0, \pi/2)$. On $[0, \pi/2)$ we have $f_K = f_K^+$ and
$g_K = g_K^+$ (Proposition 7.20), so by Theorem 7.9

```math
f_K(t) - f_K(0) = \int_0^t g_K - \sigma_K\bigl((0, t]\bigr) = \int_0^t \bigl(g_K - r_K\bigr) \qquad \text{for } t \in [0, \pi/2) ,
```

and at $t = \pi/2$ by continuity (Proposition 7.22). So $f_K$ is absolutely continuous
([Proposition 6.5](06-surface-area.md#proposition-65-absolutely-continuous-functions-baek-proposition-514)),
and $f_K' = g_K - r_K \ge g_K - k_0(g_K) = m_0(g_K)$ almost everywhere. $\square$

### Definition 7.24 (the iteration; Baek, Definitions 6.5.1 and 6.5.2)

For a continuous function $f$ on $[0, \pi/2]$, let

```math
\mathcal{F}f(x) = 1 + \int_0^x m_0\bigl(f(\pi/2 - u)\bigr)\,\mathrm{d}u ,
```

and define the continuous functions $f_0 = 0$ and $f_{n + 1} = \max(f_n, \mathcal{F}f_n)$ on
$[0, \pi/2]$.

*Lean: [`lowerOp`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L199), [`lowerSeq`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L202).*

Since $m_0(0) = -1$, $f_1(x) = \max(0, 1 - x)$.

### Lemma 7.25 (lower bounds; Baek, Lemma 6.5.2)

For every $n \ge 0$ and every balanced maximum cap $K$, $f_K(t) \ge f_n(t)$ for $t \in [0, \pi/2)$,
and $g_K(t) \ge f_n(\pi/2 - t)$ for $t \in (0, \pi/2]$.

*Lean: [`lemma6_5_2`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L239).*

*Proof.* By induction on $n$, for all balanced maximum caps at once. For $n = 0$ the arms are
nonnegative. Assume the claim for $n$, and let $K$ be a balanced maximum cap. Its mirror image
$K^\mathrm{m}$ is one too (Baek, Proposition 3.5.1), and $g_K(u) = f_{K^\mathrm{m}}(\pi/2 - u)$ for
$u \in (0, \pi/2]$ (Propositions 7.6 and 7.20), so the claim for $K^\mathrm{m}$ gives
$g_K(u) \ge f_n(\pi/2 - u)$. The vertex $A_K(0)$ is the right end $(h_K(0), 0)$ of the bottom edge,
so $f_K(0) = h_K(\pi/2) - 0 = 1$. By Theorem 7.23 and since $m_0$ is nondecreasing, for
$t \in [0, \pi/2)$

```math
f_K(t) = 1 + \int_0^t f_K' \ \ge\ 1 + \int_0^t m_0\bigl(g_K(u)\bigr)\,\mathrm{d}u \ \ge\ 1 + \int_0^t m_0\bigl(f_n(\pi/2 - u)\bigr)\,\mathrm{d}u = \mathcal{F}f_n(t) .
```

With $f_K \ge f_n$, this gives $f_K \ge f_{n + 1}$ on $[0, \pi/2)$. The bound on $g_K$ is the bound on
$f_{K^\mathrm{m}}$. $\square$

*Lean: [`inj_fK_zero`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L29), [`inj_gK_eq_fK_mirror`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L71).*

The paper uses $f_K(0) = 1$ without stating it (REPORT.md, E17), and writes
$m_0(f_K(\pi/2 - u))$ for $m_0(f_n(\pi/2 - u))$ in the last integral (E26).

### Lemma 7.26 (one round of the iteration; Baek, Lemma 6.5.3)

For $c \in [0, 1]$ let $j_c(x) = \max(1 - x, c)$ (Baek, Definition 6.5.3). If $c \in [0, 2/3]$, then
$\mathcal{F}j_c(x) \ge j_{c + 1/12}(x)$ for every $x \in [0, \pi/2]$.

*Lean: [`jFun`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L273), [`lemma6_5_3`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L277).*

Baek states the conclusion on $[0, 1]$; the proof gives it on $[0, \pi/2]$, which Lemma 7.28 needs
(REPORT.md, E17).

*Proof.* On $[0, \pi/2]$ the function $j_c$ takes values in $[0, 1]$, where
$m_0(y) = \frac32 y - 1$, so

```math
\mathcal{F}j_c(x) = 1 - x + \frac32 \int_0^x j_c(\pi/2 - u)\,\mathrm{d}u \ \ge\ 1 - x .
```

It remains to show $\mathcal{F}j_c(x) \ge c + \frac1{12}$. Let $x_0 = \pi/2 - 1 + c$; then
$j_c(\pi/2 - u) = c$ for $u \le x_0$ and $= u + 1 - \pi/2$ for $u \ge x_0$.

*Case $x \le x_0$.* Then $\mathcal{F}j_c(x) = 1 - (1 - \frac32 c)\,x \ge 1 - (1 - \frac32 c)\,x_0$,
and

```math
1 - \Bigl(1 - \frac32 c\Bigr)\Bigl(\frac\pi2 - 1 + c\Bigr) - c - \frac1{12} = \frac32 c^2 + \Bigl(\frac{3\pi}4 - \frac72\Bigr) c + \frac{23}{12} - \frac\pi2 .
```

This quadratic is least at $c = \frac76 - \frac\pi4 \in [0, \frac23]$, where it equals
$-\frac18 + \frac{3\pi}8 - \frac{3\pi^2}{32} = 0.12782\ldots > 0$.

*Case $x > x_0$.* Then

```math
\mathcal{F}j_c(x) = 1 - x + \frac32\,c\,x_0 + \frac34\Bigl(\bigl(x - \frac\pi2 + 1\bigr)^2 - c^2\Bigr) \ \ge\ \frac53 - \frac\pi2 + \frac34\,c\,(c + \pi - 2) ,
```

the minimum over all real $x$, attained at $x = \pi/2 - 1/3$. The difference
$\frac34 c^2 + (\frac{3\pi}4 - \frac52)\,c + \frac{19}{12} - \frac\pi2$ with $c + \frac1{12}$ is least
at $c = \frac53 - \frac\pi2 \in [0, \frac23]$, where it equals
$-\frac12 + \frac{3\pi}4 - \frac{3\pi^2}{16} = 0.005644\ldots > 0$. $\square$

### Lemma 7.27 (monotonicity; Baek, Lemma 6.5.4)

If $f$ and $g$ are continuous on $[0, \pi/2]$ and $f \le g$ there, then $\mathcal{F}f \le \mathcal{F}g$
on $[0, \pi/2]$.

*Lean: [`lemma6_5_4`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L344).*

*Proof.* $m_0$ is nondecreasing, so the integrand of $\mathcal{F}f$ is at most that of
$\mathcal{F}g$. $\square$

Baek assumes $f, g \ge 0$; since $m_0$ is nondecreasing on all of $\mathbb{R}$, the formalization
needs neither sign.

### Lemma 7.28 (the eleventh bound; Baek, Lemma 6.5.5)

$f_{11}(x) > 1$ for every $x \in (0, \pi/2]$.

*Lean: [`lemma6_5_5`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L364).*

Baek states it on $(0, 1]$; Theorem 7.29 needs $(0, \pi/2]$, which the proof gives (REPORT.md, E17).

*Proof.* First $f_1 = \max(0, 1 - x) = j_0$. If $f_m \ge j_{(m - 1)/12}$ for some
$1 \le m \le 9$, then $(m - 1)/12 \le 2/3$, and by Lemmas 7.27 and 7.26

```math
f_{m + 1} \ \ge\ \mathcal{F}f_m \ \ge\ \mathcal{F}j_{(m - 1)/12} \ \ge\ j_{m/12} .
```

So $f_{10} \ge j_{3/4} \ge \frac34$. Since $m_0(3/4) = \frac18$ and $m_0$ is nondecreasing,
$f_{11}(x) \ge \mathcal{F}f_{10}(x) \ge 1 + x/8 > 1$ for $x > 0$. $\square$

![The lower bounds f₁ to f₁₁ on the interval from 0 to π/2, drawn in orange, lighter for small n, together with the dashed line at height 1 and, in blue on top, the arm length f of Gerver's sofa. The first five bounds dip below 1; f₆ and all later bounds start at 1 and stay above 1, rising towards the blue curve; f₆ and f₁₁ are drawn thick, and f₁₁ ends at about 2.31, just below Gerver's 2.42](figures/07-injectivity/lower-bounds.svg)

*Figure 7.7.* The lower bounds $f_1, \dots, f_{11}$ of Definition 7.24, computed numerically, with
$f_6$ and $f_{11}$ thick, and the arm length $f(t) = 1 - \langle \mathbf{x}'(t), u_t\rangle$ of
Gerver's sofa (blue), which lies above all of them. Numerically, $f_6$ is the first bound that exceeds $1$ on all of $(0, \pi/2]$; the
proof of Lemma 7.28 takes eleven rounds so that each round is a short computation.

### Theorem 7.29 (arms longer than one; Baek, Theorem 6.5.6)

For every balanced maximum cap $K$, $f_K(t) > 1$ for $t \in (0, \pi/2]$ and $g_K(t) > 1$ for
$t \in [0, \pi/2)$.

*Lean: [`theorem6_5_6`](../../MovingSofaOptimality/Injectivity/BoundingArms.lean#L422).*

*Proof.* For $t \in (0, \pi/2)$, $f_K(t) \ge f_{11}(t) > 1$ by Lemmas 7.25 and 7.28. At
$t = \pi/2$, Lemma 7.25 gives no bound, but $f_K$ and $f_{11}$ are continuous
(Proposition 7.22), so $f_K(\pi/2) \ge f_{11}(\pi/2) > 1$. Likewise
$g_K(t) \ge f_{11}(\pi/2 - t) > 1$ for $t \in (0, \pi/2)$, and at $t = 0$ by continuity. $\square$

The paper deduces the endpoint values from Lemma 6.5.2 directly, which covers only the open interval
there; continuity closes the gap (REPORT.md, E17).

*Proof of Theorem 7.2.* Let $K$ be a balanced maximum cap. Condition (1) is Corollary 7.19, and
condition (2) is Proposition 7.22 (2). By the same proposition,
$\mathbf{x}_K'(t) = -(f_K(t) - 1)\,u_t + (g_K(t) - 1)\,v_t$, so
$\langle \mathbf{x}_K'(t), u_t\rangle = 1 - f_K(t) < 0$ and
$\langle \mathbf{x}_K'(t), v_t\rangle = g_K(t) - 1 > 0$ for $t \in (0, \pi/2)$ by Theorem 7.29: this
is condition (3). The statement about a balanced maximum sofa is the case of its cap. $\square$

The uniqueness proof shows more: every cap that maximizes $\mathcal{A}$, balanced or not, satisfies
the injectivity condition, by the same differential inequality and an analytic form of the
iteration (note 20, Proposition 3; [`MovingSofaUniqueness.isKi_of_maximal_area`](../../MovingSofaUniqueness/Main.lean#L88);
[Chapter 11](11-selection.md) and [Chapter 12](12-uniqueness.md)).

## 7.6 Gerver's sofa

*Proof of Theorem 7.3.* Baek's proof reads Gerver's Theorem 2 as constructing maximum polygon sofas
that converge to $G$, so that $G$ would be a balanced maximum sofa and Theorem 7.2 would apply. That
cannot be right: the cap of $G$ would then maximize $\mathcal{A}$ (Baek, Theorem 3.5.5), and with
Theorems 1.5.1 and 1.5.2 ([Chapter 5](05-rotation-angle.md)) this would already prove the optimality
of $G$, which Gerver only conjectured. Gerver's Theorem 2 shows that $G$ satisfies the balancing
condition (REPORT.md, E12). Baek's Remark 6.1.1 observes that the statement can be checked on
Romik's equations, and the formalization does so. The full proof is in
[`MovingSofaOptimality/Gerver/StructureCap.lean`](../../MovingSofaOptimality/Gerver/StructureCap.lean) and [`MovingSofaOptimality/Gerver/Frame.lean`](../../MovingSofaOptimality/Gerver/Frame.lean);
[Chapter 10](10-gerver.md) describes Romik's description of $G$.

Romik's rotation path is glued from five phases, on $[0, \varphi]$, $[\varphi, \theta]$,
$[\theta, \pi/2 - \theta]$, $[\pi/2 - \theta, \pi/2 - \varphi]$ and $[\pi/2 - \varphi, \pi/2]$. On
each, $\mathbf{x}(t) = R_t\,(w_1(t), w_2(t)) + \kappa$ with explicit functions $w_1$, $w_2$ and a
constant $\kappa$. Differentiating in the rotating frame,

```math
\mathbf{x}' = \alpha\,u_t + \beta\,v_t , \qquad \alpha = w_1' - w_2 , \qquad \beta = w_2' + w_1 ,
```

and the contact points $\mathbf{A} = \mathbf{x} + u_t + \alpha\,v_t$ and
$\mathbf{C} = \mathbf{x} + v_t - \beta\,u_t$ move with the velocities $\mathbf{A}' = \rho_A\,v_t$ and
$\mathbf{C}' = -\rho_C\,u_t$, where $\rho_A = w_1'' + w_1 + 1$ and $\rho_C = w_2'' + w_2 + 1$.

1. *The cap.* The cap of $G$ is the convex body
   $K = \lbrace y \ge 0\rbrace \cap \bigcap_{\sigma \in [0, \pi]} \lbrace p : \langle p, u_\sigma\rangle \le H(\sigma)\rbrace$
   with $H(\sigma) = \langle \mathbf{x}(\sigma), u_\sigma\rangle + 1$ for $\sigma \le \pi/2$ and
   $H(\sigma) = \langle \mathbf{x}(\sigma - \pi/2), v_{\sigma - \pi/2}\rangle + 1$ for
   $\sigma > \pi/2$. Its support function is $H$ on $[0, \pi]$, its inner corner is $\mathbf{x}$, and
   its vertices are $v_K^-(t) = \mathbf{A}(t)$ for $t \in [0, \pi/2]$, $v_K^+(t) = \mathbf{A}(t)$ for
   $t \in [0, \pi/2)$ and $v_K^+(t + \pi/2) = \mathbf{C}(t)$ for $t \in [0, \pi/2]$.
2. *Condition (1).* On $[0, \pi/2)$ the distribution function is
   $G_K(t) = \langle \mathbf{A}(t), v_t\rangle + \int_0^t H$, whose right derivative is
   $\langle \mathbf{A}'(t), v_t\rangle - \langle \mathbf{A}(t), u_t\rangle + H(t) = \rho_A(t)$, since
   $\langle \mathbf{A}(t), u_t\rangle = H(t)$. So $\sigma_K = \rho_A(t)\,\mathrm{d}t$ there, and in the
   same way $\sigma_K = \rho_C(t - \pi/2)\,\mathrm{d}t$ on $(\pi/2, \pi]$; on each phase $\rho_A$ and
   $\rho_C$ are explicit and nonnegative.
3. *Condition (2).* The phases match with their first derivatives at the four junctions, by Romik's
   equations (35)–(42), so $\mathbf{x}$ is continuously differentiable.
4. *Condition (3).* $\alpha(t) < 0$ for $t \in (0, \pi/2]$ and $\beta(t) > 0$ for $t \in [0, \pi/2)$,
   phase by phase, from the explicit formulas and the enclosures of the parameters. On the middle
   phase, for example, $w_1 = c_1 - t$ and $w_2 = c_2 + t$, so $\alpha = -1 - c_2 - t$ and
   $\beta = 1 + c_1 - t$ with $c_1 \approx 0.626$ and $c_2 = c_1 - \pi/2$; at $t = \pi/4$,
   $\alpha \approx -0.841$ and $\beta \approx 0.841$. $\square$

*Lean: [`GerverParams.gs_monotone_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L579), [`GerverParams.gs_supp_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L421), [`GerverParams.gs_innerCorner_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L476),
[`GerverParams.gs_InjCond1`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L1058), [`GerverParams.gs_InjCond2`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L745), [`GerverParams.gs_InjCond3`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L748),
[`GerverParams.gs_contDiff_path`](../../MovingSofaOptimality/Gerver/Frame.lean#L631).*

In terms of the arms, $f = 1 - \alpha$ and $g = 1 + \beta$ (Figure 7.3), and Figure 7.7 shows $f$.
Romik derives $G$ under the weaker assumption $\alpha \le 0 \le \beta$ (Baek, Remark 6.1.1); the
strict inequalities hold for the solution.
