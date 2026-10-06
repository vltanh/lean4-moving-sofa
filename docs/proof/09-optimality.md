# 9. The upper bound and the optimality of Gerver's sofa

[Contents](README.md) · [← 8. Convex curves and Mamikon's theorem](08-convex-curves.md) · [10. Gerver's sofa →](10-gerver.md)

This chapter proves Baek's main theorem, Theorem 1.1.1: Gerver's sofa $G$ is a moving sofa, and
every moving sofa has area at most $\lvert G \rvert = 2.2195\ldots$ (Theorem 9.33). The earlier
chapters reduce the problem to caps with rotation angle $\pi/2$. The area of a moving sofa is at
most the sofa area functional $\mathcal{A}(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$ of a
balanced maximum cap $K$ with rotation angle $\pi/2$ ([Chapter 4](04-balanced.md),
[Chapter 5](05-rotation-angle.md)), and such a cap satisfies the injectivity condition
([Chapter 7](07-injectivity.md)). Following Baek's Chapter 8, this chapter bounds $\mathcal{A}(K)$
for all such caps at once.

The bound replaces the niche $\mathcal{N}(K)$ by a smaller region $N'$ with the shape of the niche
of Gerver's sofa. It has a *core*, traced by the inner corner $\mathbf{x}_K(t)$ for
$t \in [\varphi, \pi/2 - \varphi]$, where $\varphi = 0.0391\ldots$ is one of Romik's angles, and two
*tails*, the lower boundaries of two convex bodies $B_K, D_K \subseteq K$. The area of
$K \setminus N'$ is a quadratic functional $\mathcal{Q}(K, B_K, D_K)$ of the triple, on a convex
domain $\mathcal{L}$ of triples that satisfy linear constraints. A concave quadratic functional is
maximal where its directional derivatives are nonpositive
([Theorem 8.7](08-convex-curves.md#theorem-87-maximum-of-a-concave-quadratic-functional-baek-theorem-715)),
and the outline below follows this. Figure 9.1 shows the chain of inequalities.

![A column of five boxes joined by relation signs: the area of S, at most A(K) = |K| - |N(K)|, at most Q(K, B_K, D_K), at most Q(K_G, B_G, D_G), equal to |G| = 2.2195...; beside each sign, the property that gives it: K is a balanced maximum cap with rotation angle pi/2 (Chapters 3 to 5); K satisfies the injectivity condition (Chapter 7) and Q bounds the sofa area functional (Section 9.2); Q is concave (Section 9.3) and its directional derivatives at Gerver's triple are at most 0 (Section 9.4); the bound is attained at Gerver's sofa (Chapter 10)](figures/09-optimality/chain.svg)

*Figure 9.1.* The proof of Theorem 9.33 for a moving sofa $S$ with $\lvert S \rvert \ge 2.2$. Here
$K_G$ is the cap of Gerver's sofa, and $B_G = B_{K_G}$, $D_G = D_{K_G}$.

*Outline.*

1. *The domain* (§9.1). The caps $\mathcal{K}^\mathrm{i}$ with the injectivity condition and area at
   least $2.2$ form a convex domain (Theorem 9.2). To each $K \in \mathcal{K}^\mathrm{i}$ belong the
   bodies $B_K$ and $D_K$, the parts of $K$ beyond the inner walls of the hallways, and the triple
   $(K, B_K, D_K)$ lies in the convex domain $\mathcal{L}$ (Theorem 9.12).
2. *The bound* (§9.2). $\mathcal{A}(K) \le \mathcal{Q}(K, B_K, D_K)$ (Theorem 9.18), by bounding
   from below the three parts into which two lines cut the niche.
3. *Concavity* (§9.3). $\mathcal{Q}$ is a linear functional minus Mamikon areas, which are convex
   (Theorem 9.27).
4. *The derivative* (§9.4). At Gerver's triple every directional derivative of $\mathcal{Q}$ is
   nonpositive (Theorem 9.31), by Romik's equations. So Gerver's triple maximizes $\mathcal{Q}$
   (Corollary 9.32).
5. *The theorem* (§9.5). The chain of Figure 9.1.

The formalization follows the paper with three main changes of route. Theorem 9.2 (1) is proved by
slicing instead of the Brunn–Minkowski inequality. Lemmas 9.15 and 9.16 compute areas directly
instead of with Jordan curves (§8.2). Lemma 9.11 and Theorem 9.18 avoid the inclusion
$\mathcal{N}(K) \subseteq K$, which the paper uses but which $\mathcal{K}^\mathrm{i}$ does not
provide (REPORT.md, E21). Smaller departures, in Lemmas 9.9 and 9.24 and Theorems 9.29 and 9.33,
are noted where they occur.

*Notation*, as in Chapters 2, 3 and 7. The hallway $L_K(t)$ supporting a cap $K$ has the inner
corner $\mathbf{x}_K(t) = (h_K(t) - 1)\, u_t + (h_K(t + \pi/2) - 1)\, v_t$, the outer corner
$\mathbf{y}_K(t) = h_K(t)\, u_t + h_K(t + \pi/2)\, v_t$, the outer walls $a_K(t) = l_K(t)$ and
$c_K(t) = l_K(t + \pi/2)$, and the inner walls $b_K(t)$ through $\mathbf{x}_K(t)$ parallel to
$a_K(t)$ and $d_K(t)$ parallel to $c_K(t)$. The quadrant $Q_K^-(t)$ is the open quadrant below the
inner corner, bounded by $b_K(t)$ and $d_K(t)$:
$Q_K^-(t) = \lbrace \mathbf{x}_K(t) + \lambda u_t + \mu v_t : \lambda, \mu < 0 \rbrace$. With
$H_+(t, h) = \lbrace p : \langle p, u_t \rangle \ge h \rbrace$, the fan of rotation angle $\pi/2$ is
$H_+(\pi/2, 0) = \lbrace y \ge 0 \rbrace$, the wedge is $T_K(t) = H_+(\pi/2, 0) \cap Q_K^-(t)$, and
the niche is $\mathcal{N}(K) = \bigcup_{t \in (0, \pi/2)} T_K(t)$. For a cap with the injectivity
condition and $t \in [0, \pi/2]$, the vertices $A_K(t) = v_K^-(t)$ and $C_K(t) = v_K^+(t + \pi/2)$
and the arm lengths $f_K(t) = h_K(t + \pi/2) - \langle A_K(t), v_t \rangle$ and
$g_K(t) = h_K(t) - \langle C_K(t), u_t \rangle$ are those of
[Definition 7.21](07-injectivity.md#definition-721-contacts-and-arms-of-a-cap-baek-definition-641).
The curve area functional $\mathcal{J}$, the convex curves $\mathbf{u}_K^{a,b}$ and the Mamikon areas
$\mathcal{M}_K$ are those of [Chapter 8](08-convex-curves.md).

## 9.1 The domain of the upper bound

### Definition 9.1 (caps with the injectivity condition; Baek, Definition 8.1.1)

$\mathcal{K}^\mathrm{i}$ is the set of caps $K$ with rotation angle $\pi/2$ that satisfy the
injectivity condition and have area $\lvert K \rvert \ge 2.2$. Recall that the injectivity condition
([Definition 7.1](07-injectivity.md#definition-71-injectivity-condition-baek-definition-612)) asks
that (1) $\sigma_K$ has a density on $[0, \pi/2)$ and on $(\pi/2, \pi]$, (2) the inner corner
$\mathbf{x}_K$ is continuously differentiable on $[0, \pi/2]$, and (3)
$\langle \mathbf{x}_K'(t), u_t \rangle < 0 < \langle \mathbf{x}_K'(t), v_t \rangle$ for
$t \in (0, \pi/2)$.

*Lean: [`IsKi`](../../MovingSofaOptimality/Optimality/Domain.lean#L205),
[`KiSet`](../../MovingSofaOptimality/Optimality/Concavity.lean#L286),
[`SatisfiesInjectivity`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L49),
[`InjCond1`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L32),
[`InjCond2`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L40),
[`InjCond3`](../../MovingSofaOptimality/Injectivity/ArmLengths.lean#L43).*

Condition (3) says that the arm lengths exceed 1. Indeed
$\mathbf{x}_K'(t) = -(f_K(t) - 1)\, u_t + (g_K(t) - 1)\, v_t$
([Proposition 7.22](07-injectivity.md#proposition-722-regularity-of-the-corners-baek-proposition-646)),
so (3) gives $f_K(t) > 1$ and $g_K(t) > 1$ on $(0, \pi/2)$
([`opt_arm_gt_one`](../../MovingSofaOptimality/Optimality/Domain.lean#L1046)).

### Theorem 9.2 (these caps form a convex domain; Baek, Theorem 8.1.1)

1. $\mathcal{K}^\mathrm{i}$ is closed under Minkowski combinations; it is a convex domain.
2. Every balanced maximum cap with rotation angle $\pi/2$ lies in $\mathcal{K}^\mathrm{i}$.
3. The cap of Gerver's sofa lies in $\mathcal{K}^\mathrm{i}$.

*Proof.* (1) Caps with rotation angle $\pi/2$ are closed under Minkowski combinations
([`opt_comb_isCap`](../../MovingSofaOptimality/Optimality/Domain.lean#L232)). So is the
injectivity condition. The measure $\sigma_K$ and the inner corner $\mathbf{x}_K$ are convex-linear
in $K$
([Theorem 8.3](08-convex-curves.md#theorem-83-convex-linear-quantities-baek-theorem-712)), so the
densities of (1) combine, (2) is preserved, and the strict inequalities of (3) survive convex
combinations. For the area, Baek uses the Brunn–Minkowski inequality. The formalization slices
instead. A cap $K$ with rotation angle $\pi/2$ lies in the strip $0 \le y \le 1$ and meets every
line $y = c$, $0 \le c \le 1$, in a segment. The slice of $(1 - \lambda) K_1 + \lambda K_2$ at
height $c$ contains the combination of the slices of $K_1$ and $K_2$, whose length is the
combination of their lengths. By Fubini's theorem,

```math
\lvert (1 - \lambda) K_1 + \lambda K_2 \rvert \ \ge\ (1 - \lambda) \lvert K_1 \rvert + \lambda \lvert K_2 \rvert \ \ge\ 2.2 .
```

(2) A balanced maximum cap $K$ satisfies the injectivity condition
([Theorem 7.2](07-injectivity.md#theorem-72-injectivity-condition-baek-theorems-611-and-171)). It
maximizes the sofa area functional among caps with rotation angle $\pi/2$
([Theorem 4.38](04-balanced.md#theorem-438-maximality-baek-theorem-355)). So, with $K_G$ the cap
of Gerver's sofa,
$\lvert K \rvert \ge \mathcal{A}(K) \ge \mathcal{A}(K_G) = \lvert G \rvert = 2.2195\ldots \ge 2.2$.
(3) $K_G$ satisfies the injectivity condition
([Theorem 10.13](10-gerver.md#theorem-1013-injectivity-baek-theorem-612), which the formalization
proves from Romik's equations), and
$\lvert K_G \rvert \ge \mathcal{A}(K_G) = \lvert G \rvert \ge 2.2$. $\square$

*Lean: [`theorem8_1_1_convex`](../../MovingSofaOptimality/Optimality/Domain.lean#L476),
[`theorem8_1_1_balanced`](../../MovingSofaOptimality/Main.lean#L43),
[`theorem8_1_1_gerver`](../../MovingSofaOptimality/Main.lean#L56),
[`opt_comb_area`](../../MovingSofaOptimality/Optimality/Domain.lean#L396),
[`opt_comb_isCap`](../../MovingSofaOptimality/Optimality/Domain.lean#L232),
[`opt_comb_injectivity`](../../MovingSofaOptimality/Optimality/Domain.lean#L337),
[`kiDomain`](../../MovingSofaOptimality/Optimality/Concavity.lean#L306).*

### Definition 9.3 (Gerver's angles; Baek, Definition 8.1.2)

Romik's system of equations (27)–(44) has exactly one solution with $\varphi \in [0.039, 0.04]$ and
$\theta \in [0.68, 0.69]$, with $\varphi = 0.0391773\ldots$ and $\theta = 0.6813015\ldots$, and
Gerver's sofa $G$ is the shape of its rotation path ([Chapter 10](10-gerver.md)). Put
$\varphi^\mathrm{R} = \varphi$ and $\varphi^\mathrm{L} = \pi/2 - \varphi$.

*Lean: [`definition8_1_2_exists`](../../MovingSofaOptimality/Main.lean#L32),
[`definition8_1_2_unique`](../../MovingSofaOptimality/Main.lean#L37),
[`GerverParams.IsSolution`](../../MovingSofaOptimality/Gerver/Defs.lean#L93),
[`GerverParams.InBox`](../../MovingSofaOptimality/Gerver/Defs.lean#L109),
[`gerverSofa`](../../MovingSofaOptimality/Gerver/Defs.lean#L120).*

The rotation path of $G$ traces the core of its niche on $[\varphi^\mathrm{R}, \varphi^\mathrm{L}]$.
The formalization states §9.1 to §9.4 for an arbitrary parameter $\varphi \in [0.039, 0.04]$ in
place of $\varphi^\mathrm{R}$, with $\varphi^\mathrm{L} = \pi/2 - \varphi$; this range contains
Gerver's angle. The numerical facts the paper takes from Gerver's angle, such as
$\sec \varphi < 1.1$ and $2 \sec \varphi + 2 \tan \varphi = 2.08\ldots < 2.2$, hold on this range
(REPORT.md, Section 6). The statements about $\mathcal{Q}$ alone need only $0 < \varphi < \pi/4$.

### Definition 9.4 (the domain of triples; Baek, Definition 8.1.3)

$\mathcal{L}$ is the set of triples $(K, B, D)$ of convex bodies such that

1. $K \in \mathcal{K}^\mathrm{i}$, $B \subseteq K$ and $D \subseteq K$;
2. $h_K(t) + h_B(\pi + t) \le 1$ for $t \in [\varphi^\mathrm{R}, \pi/2]$;
3. equality holds in (2) at $t = \varphi^\mathrm{R}$ and $t = \pi/2$;
4. $h_K(\pi/2 + t) + h_D(3\pi/2 + t) \le 1$ for $t \in [0, \varphi^\mathrm{L}]$;
5. equality holds in (4) at $t = 0$ and $t = \varphi^\mathrm{L}$.

*Lean: [`MovingSofaOptimality.InL`](../../MovingSofaOptimality/Optimality/Domain.lean#L485),
[`LTriple`](../../MovingSofaOptimality/Optimality/Domain.lean#L532).*

Condition (2) says that $B$ lies on the far side of the inner wall $b_K(t)$, the line at distance 1
from $l_K(t)$; (4) is the same for $D$ and $d_K(t)$.

### Proposition 9.5 (the triples form a convex domain; Baek, Proposition 8.1.2)

$\mathcal{L}$ is closed under componentwise Minkowski combinations, so it is a convex domain.

*Proof.* $\mathcal{K}^\mathrm{i}$ is closed under combinations by Theorem 9.2 (1). Inclusions are
preserved, and conditions (2) to (5) are linear in the support functions
([Theorem 8.3](08-convex-curves.md#theorem-83-convex-linear-quantities-baek-theorem-712) (1)).
$\square$

*Lean: [`proposition8_1_2`](../../MovingSofaOptimality/Optimality/Domain.lean#L507),
[`lDomain`](../../MovingSofaOptimality/Optimality/Domain.lean#L562),
[`lTriple_embeds`](../../MovingSofaOptimality/Optimality/Domain.lean#L545).*

### Definition 9.6 (the right and left bodies; Baek, Definitions 8.1.4–8.1.6)

For a cap $K$ with rotation angle $\pi/2$, let

```math
H_K^\mathrm{b}(t) = \lbrace p : \langle p, u_t \rangle \ge h_K(t) - 1 \rbrace , \qquad H_K^\mathrm{d}(t) = \lbrace p : \langle p, v_t \rangle \ge h_K(t + \pi/2) - 1 \rbrace ,
```

the closed half-planes bounded by the inner walls $b_K(t)$ and $d_K(t)$ on the side of the sofa, and

```math
B_K = K \cap \bigcap_{t \in [\varphi^\mathrm{R}, \pi/2]} H_K^\mathrm{b}(t) , \qquad D_K = K \cap \bigcap_{t \in [0, \varphi^\mathrm{L}]} H_K^\mathrm{d}(t) .
```

The two cut lines are $b_K^\mathrm{R} = b_K(\varphi^\mathrm{R})$ and
$d_K^\mathrm{L} = d_K(\varphi^\mathrm{L})$, with the half-planes
$\breve H_K^\mathrm{R} = H_K^\mathrm{b}(\varphi^\mathrm{R})$ and
$\breve H_K^\mathrm{L} = H_K^\mathrm{d}(\varphi^\mathrm{L})$, bounded from below by them. They meet
the $x$-axis at

```math
W_K^\mathrm{R} = \Bigl(\frac{h_K(\varphi) - 1}{\cos \varphi}, 0\Bigr) , \qquad Z_K^\mathrm{L} = \Bigl(\frac{1 - h_K(\pi - \varphi)}{\cos \varphi}, 0\Bigr) ,
```

and pass through $\mathbf{x}_K^\mathrm{R} = \mathbf{x}_K(\varphi^\mathrm{R})$ and
$\mathbf{x}_K^\mathrm{L} = \mathbf{x}_K(\varphi^\mathrm{L})$. Finally, with $H$ the strip
$0 \le y \le 1$, $P_K^\mathrm{R} = H \cap H_K(\varphi^\mathrm{R}) \cap \breve H_K^\mathrm{R}$ and
$P_K^\mathrm{L} = H \cap H_K(\pi/2 + \varphi^\mathrm{L}) \cap \breve H_K^\mathrm{L}$.

*Lean: [`halfB`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L350),
[`halfD`](../../MovingSofaOptimality/Injectivity/DiscreteIneq.lean#L354),
[`rightBody`](../../MovingSofaOptimality/Optimality/Domain.lean#L567),
[`leftBody`](../../MovingSofaOptimality/Optimality/Domain.lean#L570),
[`hRight`](../../MovingSofaOptimality/Optimality/Domain.lean#L574),
[`hLeft`](../../MovingSofaOptimality/Optimality/Domain.lean#L577),
[`wRight`](../../MovingSofaOptimality/Optimality/Domain.lean#L579),
[`zLeft`](../../MovingSofaOptimality/Optimality/Domain.lean#L583),
[`xRight`](../../MovingSofaOptimality/Optimality/Domain.lean#L581),
[`xLeft`](../../MovingSofaOptimality/Optimality/Domain.lean#L585),
[`paraR`](../../MovingSofaOptimality/Optimality/Domain.lean#L588),
[`paraL`](../../MovingSofaOptimality/Optimality/Domain.lean#L590).*

![Gerver's cap K, light blue, between the x-axis and the line y = 1, with its niche shaded light orange under an orange arch, the core x_K. Two green bodies B and D fill the parts of the cap to the right of the dashed, nearly vertical line b_K^R and to the left of the dashed line d_K^L. The lower boundaries of B and D near the x-axis are short green curves, the tails b_B and d_D; the tail b_B runs from the end x_K^R = X_B of the core down to W_B on the x-axis, and d_D from Z_D on the axis up to the other end x_K^L = Y_D. The lines b_K^R and d_K^L meet the x-axis at W_K^R and Z_K^L](figures/09-optimality/bodies.svg)

*Figure 9.2.* The objects of Definitions 9.6 and 9.13 for the cap $K$ of Gerver's sofa. The bodies
$B = B_K$ and $D = D_K$ (green) are the parts of $K$ beyond all the inner walls $b_K(t)$,
$t \in [\varphi^\mathrm{R}, \pi/2]$, and $d_K(t)$, $t \in [0, \varphi^\mathrm{L}]$; their lower
boundaries are the tails $\mathbf{b}_B$ and $\mathbf{d}_D$. The core $\mathbf{x}_K$ on
$[\varphi^\mathrm{R}, \varphi^\mathrm{L}]$ (orange) runs between the dashed lines $b_K^\mathrm{R}$
and $d_K^\mathrm{L}$. For Gerver's sofa the tails end exactly where the core begins:
$X_B = \mathbf{x}_K^\mathrm{R}$ and $Y_D = \mathbf{x}_K^\mathrm{L}$.

### Lemma 9.7 (the parallelogram; Baek, Lemma 8.1.3)

For $0 < \varphi < \pi/4$, $P_K^\mathrm{R}$ is the parallelogram
$\lbrace p : 0 \le p_y \le 1,\ h_K(\varphi) - 1 \le \langle p, u_\varphi \rangle \le h_K(\varphi) \rbrace$,
bounded by the $x$-axis, the line $y = 1$, $a_K(\varphi^\mathrm{R})$ and $b_K^\mathrm{R}$. Its base
on the $x$-axis is the segment from $W_K^\mathrm{R}$ to $W_K^\mathrm{R} + (\sec \varphi, 0)$.

*Proof.* The description is the definition. A point $(x, 0)$ lies in it if and only if
$h_K(\varphi) - 1 \le x \cos \varphi \le h_K(\varphi)$. $\square$

*Lean: [`lemma8_1_3`](../../MovingSofaOptimality/Optimality/Domain.lean#L643).*

### Lemma 9.8 (the cut half-planes are disjoint in the cap; Baek, Lemma 8.1.4)

For $K \in \mathcal{K}^\mathrm{i}$, the sets $K \cap \breve H_K^\mathrm{R}$ and
$K \cap \breve H_K^\mathrm{L}$ are disjoint.

*Proof.* A common point would make $K$ too narrow to have area $2.2$. Every point $q$ of $K$ has
$0 \le q_y \le 1$ and $\langle q, u_\varphi \rangle \le h_K(\varphi)$, so
$q_x \le h_K(\varphi) / \cos \varphi$; likewise $q_x \ge -h_K(\pi - \varphi) / \cos \varphi$. Hence
$\lvert K \rvert \le (h_K(\varphi) + h_K(\pi - \varphi)) / \cos \varphi$. A common point $p$ of the
two half-planes satisfies $\langle p, u_\varphi \rangle \ge h_K(\varphi) - 1$ and
$\langle p, u_{\pi - \varphi} \rangle \ge h_K(\pi - \varphi) - 1$. Since
$u_\varphi + u_{\pi - \varphi} = (0, 2 \sin \varphi)$, adding gives

```math
h_K(\varphi) + h_K(\pi - \varphi) \le 2 + 2 p_y \sin \varphi \le 2 + 2 \sin \varphi
```

if $p \in K$. Then $\lvert K \rvert \le 2 \sec \varphi + 2 \tan \varphi = 2.08\ldots < 2.2$, a
contradiction. $\square$

*Lean: [`lemma8_1_4`](../../MovingSofaOptimality/Optimality/Domain.lean#L677).*

### Lemma 9.9 (the feet of the cut lines; Baek, Lemma 8.1.5)

For $K \in \mathcal{K}^\mathrm{i}$, the points $W_K^\mathrm{R}$ and $Z_K^\mathrm{L}$ lie on the
bottom edge $e_K(3\pi/2)$, and differ from its end points $A_K(0) = (h_K(0), 0)$ and
$C_K(\pi/2) = (-h_K(\pi), 0)$.

*Proof.* The bottom edge is the segment from $C_K(\pi/2)$ to $A_K(0)$. The right wedge gap of $K$ is
positive
([Theorem 3.22](03-monotone.md#theorem-322-the-wedge-gaps-are-positive-baek-theorem-255)), which
says $h_K(\varphi) - 1 < h_K(0) \cos \varphi$: $W_K^\mathrm{R}$ lies strictly to the left of
$A_K(0)$. If $W_K^\mathrm{R}$ were not strictly to the right of $C_K(\pi/2)$, then $K$ would lie in
$[-h_K(\pi), h_K(\varphi)/\cos \varphi] \times [0, 1]$, a rectangle of width
$h_K(\pi) + h_K(\varphi)/\cos \varphi \le \sec \varphi < 2.2$, against $\lvert K \rvert \ge 2.2$.
The point $Z_K^\mathrm{L}$ is the mirror case. $\square$

*Lean: [`lemma8_1_5`](../../MovingSofaOptimality/Optimality/Domain.lean#L797).*

The paper argues that the bottom edge has length at least $\lvert K \rvert \ge 2.2$ without
justification. This holds because the width of a cap with rotation angle $\pi/2$ does not increase
with the height (REPORT.md, E19). The proof above avoids it.

### Lemma 9.10 (the core leaves the cut half-planes; Baek, Lemma 8.1.6)

Let $K \in \mathcal{K}^\mathrm{i}$.

1. For $t \in (\varphi^\mathrm{R}, \pi/2]$, $\mathbf{x}_K(t) \notin \breve H_K^\mathrm{R}$, and
   $\breve H_K^\mathrm{R} \cap Q_K^-(t) = \breve H_K^\mathrm{R} \setminus H_K^\mathrm{b}(t)$; hence
   $\breve H_K^\mathrm{R} \cap T_K(t) = (\breve H_K^\mathrm{R} \cap H_+(\pi/2, 0)) \setminus H_K^\mathrm{b}(t)$.
2. For $t \in [0, \varphi^\mathrm{L})$, $\mathbf{x}_K(t) \notin \breve H_K^\mathrm{L}$, and
   $\breve H_K^\mathrm{L} \cap Q_K^-(t) = \breve H_K^\mathrm{L} \setminus H_K^\mathrm{d}(t)$; hence
   $\breve H_K^\mathrm{L} \cap T_K(t) = (\breve H_K^\mathrm{L} \cap H_+(\pi/2, 0)) \setminus H_K^\mathrm{d}(t)$.

*Proof.* (1) First, the inner corner moves away from $\breve H_K^\mathrm{R}$. For
$s \in (\varphi, \pi/2)$, write $u_\varphi$ in the frame $(u_s, v_s)$:

```math
\frac{d}{ds} \langle \mathbf{x}_K(s), u_\varphi \rangle = \cos(s - \varphi) \langle \mathbf{x}_K'(s), u_s \rangle - \sin(s - \varphi) \langle \mathbf{x}_K'(s), v_s \rangle < 0
```

by the injectivity condition (3). So
$\langle \mathbf{x}_K(t), u_\varphi \rangle < \langle \mathbf{x}_K(\varphi), u_\varphi \rangle = h_K(\varphi) - 1$,
that is, $\mathbf{x}_K(t) \notin \breve H_K^\mathrm{R}$.

Next, the quadrant is
$Q_K^-(t) = \lbrace p : \langle p - \mathbf{x}_K(t), u_t \rangle < 0,\ \langle p - \mathbf{x}_K(t), v_t \rangle < 0 \rbrace$,
and its first condition says $p \notin H_K^\mathrm{b}(t)$. So it remains to show that a point
$p \in \breve H_K^\mathrm{R}$ with $\langle p - \mathbf{x}_K(t), u_t \rangle < 0$ also satisfies
the second condition. Suppose instead that $\langle p - \mathbf{x}_K(t), v_t \rangle \ge 0$. As
$\cos(\varphi - t) > 0 \ge \sin(\varphi - t)$,

```math
\langle p - \mathbf{x}_K(t), u_\varphi \rangle = \cos(\varphi - t) \langle p - \mathbf{x}_K(t), u_t \rangle + \sin(\varphi - t) \langle p - \mathbf{x}_K(t), v_t \rangle < 0 ,
```

so $\langle p, u_\varphi \rangle < \langle \mathbf{x}_K(t), u_\varphi \rangle < h_K(\varphi) - 1$,
against $p \in \breve H_K^\mathrm{R}$. The statement on wedges follows by intersecting with
$H_+(\pi/2, 0)$. (2) is the mirror argument. $\square$

*Lean: [`lemma8_1_6_right`](../../MovingSofaOptimality/Optimality/Domain.lean#L881),
[`lemma8_1_6_left`](../../MovingSofaOptimality/Optimality/Domain.lean#L916).*

### Lemma 9.11 (the constraints for the right and left bodies; Baek, Lemma 8.1.7)

Let $K \in \mathcal{K}^\mathrm{i}$, $B = B_K$ and $D = D_K$.

1. $h_K(t) + h_B(\pi + t) \le 1$ for $t \in [\varphi^\mathrm{R}, \pi/2]$.
2. Equality holds in (1) at $t = \varphi^\mathrm{R}$ and $t = \pi/2$; so $l_B(3\pi/2)$ is the
   $x$-axis and $l_B(\pi + \varphi^\mathrm{R}) = b_K^\mathrm{R}$.
3. $h_K(\pi/2 + t) + h_D(3\pi/2 + t) \le 1$ for $t \in [0, \varphi^\mathrm{L}]$.
4. Equality holds in (3) at $t = 0$ and $t = \varphi^\mathrm{L}$; so $l_D(3\pi/2)$ is the $x$-axis
   and $l_D(3\pi/2 + \varphi^\mathrm{L}) = d_K^\mathrm{L}$.

*Lean: [`lemma8_1_7_one`](../../MovingSofaOptimality/Optimality/Domain.lean#L956),
[`lemma8_1_7_two`](../../MovingSofaOptimality/Optimality/Domain.lean#L1147),
[`lemma8_1_7_three`](../../MovingSofaOptimality/Optimality/Domain.lean#L1184),
[`lemma8_1_7_four`](../../MovingSofaOptimality/Optimality/Domain.lean#L1310),
[`opt_exists_rightBody_on_line`](../../MovingSofaOptimality/Optimality/Domain.lean#L1063),
[`opt_exists_normal_of_isMax`](../../MovingSofaOptimality/Optimality/Domain.lean#L971),
[`opt_supp_interp`](../../MovingSofaOptimality/Optimality/Domain.lean#L1034),
[`opt_arm_gt_one`](../../MovingSofaOptimality/Optimality/Domain.lean#L1046).*

The paper writes "$t = 0, \varphi^\mathrm{R}$" in (4); $\varphi^\mathrm{L}$ is meant. Its proof of
(2) and (4) uses $\mathcal{N}(K) \subseteq K$, which caps in $\mathcal{K}^\mathrm{i}$ need not
satisfy. For example, the union of $[1, 4] \times [0, 1]$ and the quarter discs of radius 1 about
$(1, 0)$ and $(4, 0)$ is in $\mathcal{K}^\mathrm{i}$, but its inner corner
$\mathbf{x}_K(\pi/4) = (2.5, 1.5)$ lies outside it. The statements hold nevertheless, by the
argument below (REPORT.md, E21).

*Proof.* (1) The body $B$ contains $A_K(0) = (h_K(0), 0)$, so it is not empty. Indeed, for
$t \in [0, \pi/2]$, $u_t = \cos t\, u_0 + \sin t\, u_{\pi/2}$ gives
$h_K(t) \le h_K(0) \cos t + h_K(\pi/2) \sin t \le \langle A_K(0), u_t \rangle + 1$, that is,
$A_K(0) \in H_K^\mathrm{b}(t)$. Now
$B \subseteq H_K^\mathrm{b}(t)$ says $\langle p, u_{\pi + t} \rangle \le 1 - h_K(t)$ for $p \in B$,
so $h_B(\pi + t) \le 1 - h_K(t)$.

(2) By (1), it suffices to find a point of $B$ on each of the two lines. At $t = \pi/2$, the point
$A_K(0) \in B$ lies on the $x$-axis, so $h_B(3\pi/2) \ge 0 = 1 - h_K(\pi/2)$.

At $t = \varphi$ we need a point $p \in B$ on $b_K^\mathrm{R}$; then
$h_B(\pi + \varphi) \ge \langle p, u_{\pi + \varphi} \rangle = 1 - h_K(\varphi)$. The line
$b_K^\mathrm{R}$ meets $K$, at $W_K^\mathrm{R}$ for instance (Lemma 9.9). Let $p$ be the highest
point of $K$ on it, the one with the largest $\langle p, v_\varphi \rangle$. Then $K$ has a
supporting line through $p$ with a normal angle $\vartheta \in [\varphi, \varphi + \pi]$. Put
$d(s) = h_K(s) - \langle p, u_s \rangle \ge 0$, so that $d(\varphi) = 1$, $d(\vartheta) = 0$ and
$d(\pi/2) = 1 - p_y \le 1$. The point $p$ lies in $B$ if $d \le 1$ on $[\varphi, \pi/2]$.

- *The case $\vartheta > \varphi + \pi/2$ is impossible.* Let $C = C_K(\varphi)$, which lies on
  $l_K(\varphi + \pi/2)$, while $p$ lies on $l_K(\vartheta)$. So
  $\langle p - C, u_{\varphi + \pi/2} \rangle \le 0 \le \langle p - C, u_\vartheta \rangle$. Write
  $u_\vartheta = \cos(\vartheta - \varphi)\, u_\varphi + \sin(\vartheta - \varphi)\, u_{\varphi + \pi/2}$,
  with $\cos(\vartheta - \varphi) < 0 \le \sin(\vartheta - \varphi)$. This gives
  $\langle p - C, u_\varphi \rangle \le 0$, and then
  $g_K(\varphi) = h_K(\varphi) - \langle C, u_\varphi \rangle \le h_K(\varphi) - \langle p, u_\varphi \rangle = 1$,
  against $g_K(\varphi) > 1$ (Definition 9.1).
- *The case $\vartheta \le \varphi + \pi/2$.* Here $\vartheta > \varphi$, since $d(\varphi) \ne 0$.
  The support function satisfies the interpolation inequality

  ```math
  \sin(\beta - \alpha)\, h_K(s) \le \sin(\beta - s)\, h_K(\alpha) + \sin(s - \alpha)\, h_K(\beta) \qquad (\alpha \le s \le \beta \le \alpha + \pi) ,
  ```

  because $\sin(\beta - \alpha)\, u_s = \sin(\beta - s)\, u_\alpha + \sin(s - \alpha)\, u_\beta$ with
  nonnegative coefficients. The function $s \mapsto \langle p, u_s \rangle$ satisfies this with
  equality, so $d$ satisfies the inequality too. With $(\alpha, \beta) = (\varphi, \vartheta)$ it
  gives $d(s) \le \sin(\vartheta - s) / \sin(\vartheta - \varphi) \le 1$ for
  $s \in [\varphi, \vartheta]$, as $0 \le \vartheta - s \le \vartheta - \varphi \le \pi/2$. If
  $\vartheta < \pi/2$, then $(\alpha, \beta) = (\vartheta, \pi/2)$ gives
  $d(s) \le \sin(s - \vartheta)\, d(\pi/2) / \sin(\pi/2 - \vartheta) \le 1$ for
  $s \in [\vartheta, \pi/2]$.

So $d \le 1$ on $[\varphi, \pi/2]$, and $p \in B$.

(3) and (4) are the mirror images, with $f_K(\varphi^\mathrm{L}) > 1$ in place of
$g_K(\varphi^\mathrm{R}) > 1$. $\square$

### Theorem 9.12 (the triple of a cap; Baek, Theorem 8.1.8)

For $K \in \mathcal{K}^\mathrm{i}$, $(K, B_K, D_K) \in \mathcal{L}$.

*Proof.* $B_K$ and $D_K$ are closed convex subsets of $K$. They are nonempty, since they contain
$A_K(0)$ and $C_K(\pi/2)$ (proof of Lemma 9.11). So they are convex bodies, and Definition 9.4 (1)
holds. Conditions (2) to (5) are Lemma 9.11. $\square$

*Lean: [`theorem8_1_8`](../../MovingSofaOptimality/Optimality/Domain.lean#L1349).*

The map $K \mapsto (K, B_K, D_K)$ is not convex-linear. Near its tail, $B_K$ is cut out by the
half-planes $\langle p, u_{\pi + t} \rangle \le 1 - h_K(t)$: it is the Wulff shape (Aleksandrov
body) of these values, and its support function depends on $K$ in a complicated way (Baek, Remark
8.1.2). In the larger domain $\mathcal{L}$, $B$ and $D$ vary freely under linear constraints. This
is what turns the sofa area functional into a quadratic functional.

## 9.2 The upper bound

### Definition 9.13 (the tails and the upper bound; Baek, Definitions 8.2.1, 8.2.2)

For convex bodies $B$ and $D$, the *right tail*
$\mathbf{b}_B = \mathbf{u}_B^{\pi + \varphi^\mathrm{R}, 3\pi/2}$ runs from
$X_B = v_B^+(\pi + \varphi^\mathrm{R})$ to $W_B = v_B^-(3\pi/2)$, and the *left tail*
$\mathbf{d}_D = \mathbf{u}_D^{3\pi/2, 3\pi/2 + \varphi^\mathrm{L}}$ runs from $Z_D = v_D^+(3\pi/2)$
to $Y_D = v_D^-(3\pi/2 + \varphi^\mathrm{L})$. For $(K, B, D) \in \mathcal{L}$,

```math
\mathcal{Q}(K, B, D) = \lvert K \rvert + \mathcal{J}(\mathbf{d}_D) + \mathcal{J}(Y_D, \mathbf{x}_K^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K|_{[\varphi^\mathrm{R}, \varphi^\mathrm{L}]}) + \mathcal{J}(\mathbf{x}_K^\mathrm{R}, X_B) + \mathcal{J}(\mathbf{b}_B) .
```

*Lean: [`tailB`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L343),
[`MovingSofaOptimality.xB`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L345),
[`MovingSofaOptimality.wB`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L347),
[`tailD`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L349),
[`MovingSofaOptimality.zD`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L352),
[`MovingSofaOptimality.yD`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L354),
[`upperQ`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L359),
[`upperQL`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L365).*

Consider the closed curve $\gamma$ made of six pieces: the core from $\mathbf{x}_K^\mathrm{R}$ to
$\mathbf{x}_K^\mathrm{L}$, the segment to $Y_D$, the left tail backwards to $Z_D$, the $x$-axis to
$W_B$, the right tail backwards to $X_B$, and the segment back to $\mathbf{x}_K^\mathrm{R}$. The
piece on the $x$-axis has $\mathcal{J} = 0$
([Proposition 8.12](08-convex-curves.md#proposition-812-segments-baek-propositions-724-725) (3)),
and the five curve terms of $\mathcal{Q}$ are, up to sign, $\mathcal{J}$ of the other five pieces.
So $\mathcal{Q}(K, B, D) = \lvert K \rvert - \mathcal{J}(\gamma)$: the area of $K$ minus the area of
the region $N'$ that $\gamma$ encloses when it is a Jordan curve. For Gerver's sofa the two segments
are single points (Figure 9.2).

### Proposition 9.14 (the upper bound is quadratic; Baek, Proposition 8.2.1)

For $0 < \varphi < \pi/4$, $\mathcal{Q}$ is a quadratic functional on $\mathcal{L}$.

*Proof.* The projections of $\mathcal{L}$ onto its three factors are convex-linear, and a sum of
quadratic functionals is quadratic. So it suffices to check each term.

- $\lvert K \rvert$ is quadratic in $K$
  ([Theorem 8.4](08-convex-curves.md#theorem-84-the-area-is-quadratic-baek-theorem-713)), and
  $\mathcal{J}(\mathbf{d}_D)$, $\mathcal{J}(\mathbf{b}_B)$ are quadratic in $D$, $B$
  ([Theorem 8.16](08-convex-curves.md#theorem-816-the-curve-area-functional-of-a-convex-arc-baek-theorem-732)).
- The inner corner $\mathbf{x}_K$ is a continuous curve of bounded variation, convex-linear in $K$
  by its formula and
  [Theorem 8.3](08-convex-curves.md#theorem-83-convex-linear-quantities-baek-theorem-712) (1). So
  $\mathcal{J}(\mathbf{x}_K|_{[\varphi^\mathrm{R}, \varphi^\mathrm{L}]})$ is quadratic
  ([Proposition 8.11](08-convex-curves.md#proposition-811-quadratic-baek-proposition-722)).
- The segment terms are bilinear in points that are convex-linear in the triple, by Theorem 8.3 (1)
  and (2). $\square$

*Lean: [`proposition8_2_1`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L368),
[`opt_innerCBV`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L222),
[`opt_innerCBV_linear`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L226).*

### Lemma 9.15 (the tails of the niche; Baek, Lemma 8.2.2)

For $K \in \mathcal{K}^\mathrm{i}$, $B = B_K$ and $D = D_K$,

```math
\lvert \mathcal{N}(K) \cap \breve H_K^\mathrm{R} \rvert \ \ge\ \mathcal{J}(X_B, W_K^\mathrm{R}) - \mathcal{J}(\mathbf{b}_B) , \qquad \lvert \mathcal{N}(K) \cap \breve H_K^\mathrm{L} \rvert \ \ge\ \mathcal{J}(Z_K^\mathrm{L}, Y_D) - \mathcal{J}(\mathbf{d}_D) .
```

*Lean: [`lemma8_2_2`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L529).*

![A close-up of the right end of the niche of Gerver's sofa, near the x-axis. The green body B fills the upper right; its lower boundary, the green tail b_B, curves from x_K^R = X_B down to W_B on the x-axis. The dashed, nearly vertical line b_K^R passes through X_B and meets the axis at W_K^R. A dashed triangle has the vertices X_B, W_K^R and W_B; the orange region inside it and below the tail is swept by orange tangent segments, a fan at X_B followed by segments from the tail down to the axis. The orange core leaves X_B to the upper left](figures/09-optimality/tail.svg)

*Figure 9.3.* Lemma 9.15 for Gerver's sofa, enlarged about nine times from Figure 9.2. The part of
the niche in $\breve H_K^\mathrm{R}$, to the right of $b_K^\mathrm{R}$, is the dashed triangle
$X_B W_K^\mathrm{R} W_B$ minus the body $B$: the region of
[Lemma 8.19](08-convex-curves.md#lemma-819-the-region-between-an-arc-and-its-tangents-baek-lemma-735)
for $B$ and the normal angles $(\pi + \varphi^\mathrm{R}, 3\pi/2)$, whose area is
$\mathcal{J}(X_B, W_K^\mathrm{R}) - \mathcal{J}(\mathbf{b}_B)$. The tangent segments of $B$ that
sweep it are those of the Mamikon area $\mathcal{R}_B$ of Definition 9.21.

*Proof.* We prove the first inequality; the second is the mirror image. The idea is that the region
between the tail and its two end tangents, whose area Lemma 8.19 gives, lies in the niche (Figure
9.3). By Lemma 9.11 (2), $l_B(\pi + \varphi) = b_K^\mathrm{R}$ and $l_B(3\pi/2)$ is the $x$-axis,
so $v_B(\pi + \varphi, 3\pi/2) = W_K^\mathrm{R}$. The points $W_K^\mathrm{R}$, $W_B$ and $O$ lie on
the $x$-axis, so $\mathcal{J}(W_K^\mathrm{R}, W_B) = 0$.

If $X_B = W_B$, the tail is a single point and $X_B = W_K^\mathrm{R}$
([Lemma 8.15](08-convex-curves.md#lemma-815-cutting-a-convex-body-along-a-chord-baek-lemma-731)),
so $\mathcal{J}(X_B, W_K^\mathrm{R}) = 0$. Also $\mathcal{J}(\mathbf{b}_B) = 0$, since by Theorem
8.16 it is $\mathcal{J}$ of a constant curve. The right side is 0.

Otherwise let $R$ be the region of
[Lemma 8.19](08-convex-curves.md#lemma-819-the-region-between-an-arc-and-its-tangents-baek-lemma-735)
for $B$ and the angles $(\pi + \varphi, 3\pi/2)$: the interior of the triangle
$X_B W_K^\mathrm{R} W_B$ outside $\bigcap_{s \in [\pi + \varphi, 3\pi/2]} H_B(s)$. Its area is
$\mathcal{J}(X_B, W_K^\mathrm{R}) + \mathcal{J}(W_K^\mathrm{R}, W_B) - \mathcal{J}(\mathbf{b}_B) = \mathcal{J}(X_B, W_K^\mathrm{R}) - \mathcal{J}(\mathbf{b}_B)$.
It remains to show $R \subseteq \mathcal{N}(K) \cap \breve H_K^\mathrm{R}$. Let $p \in R$.

- By Lemma 8.19, $p$ lies in the interior of
  $H_B(\pi + \varphi) \cap H_B(3\pi/2) = \breve H_K^\mathrm{R} \cap \lbrace y \ge 0 \rbrace$. So
  $p \in \breve H_K^\mathrm{R}$ and $p_y > 0$.
- The vertices of the triangle lie in $K$: $X_B, W_B \in B \subseteq K$, and $W_K^\mathrm{R} \in K$
  by Lemma 9.9. So $p \in K$.
- By Lemma 8.19, $p \notin B$. As $p \in K$, some $s \in [\varphi, \pi/2]$ has
  $p \notin H_K^\mathrm{b}(s)$. Here $s \ne \varphi$, since $p \in \breve H_K^\mathrm{R}$, and
  $s \ne \pi/2$, since $H_K^\mathrm{b}(\pi/2) = \lbrace y \ge 0 \rbrace$.

By Lemma 9.10 (1), $p \in \breve H_K^\mathrm{R} \cap T_K(s) \subseteq \mathcal{N}(K)$. $\square$

The paper encloses $R$ by a Jordan curve and applies Green's theorem. The formalization uses the
region $R$ of Lemma 8.19 directly.

### Lemma 9.16 (the core of the niche; Baek, Lemma 8.2.3)

For $K \in \mathcal{K}^\mathrm{i}$,

```math
\lvert \mathcal{N}(K) \setminus \breve H_K^\mathrm{R} \setminus \breve H_K^\mathrm{L} \rvert \ \ge\ \mathcal{J}(W_K^\mathrm{R}, \mathbf{x}_K^\mathrm{R}) + \mathcal{J}(\mathbf{x}_K|_{[\varphi^\mathrm{R}, \varphi^\mathrm{L}]}) + \mathcal{J}(\mathbf{x}_K^\mathrm{L}, Z_K^\mathrm{L}) .
```

*Lean: [`lemma8_2_3`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L876),
[`opt_inj_X'_neg`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L810),
[`opt_volume_under_curve`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L262),
[`opt_curveArea_inner_eq`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L744),
[`opt_integral_under_inner`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L785).*

![The core part of the niche of Gerver's sofa: the region under the orange core x_K, an arch from x_K^R on the right to x_K^L on the left, between the dashed lines b_K^R and d_K^L, shaded light orange down to the line y = -H, with dotted vertical segments from the line y = -H up to the core. The part below the x-axis, between the two dashed lines, is a grey trapezoid with the corners W_K^R and Z_K^L on the axis. Short green tails continue the core outward along the axis](figures/09-optimality/core.svg)

*Figure 9.4.* The proof of Lemma 9.16 for Gerver's sofa. The first coordinate of the core decreases,
so the region between the core and the line $y = -H$, between $d_K^\mathrm{L}$ and $b_K^\mathrm{R}$,
meets each vertical line in one segment (dotted), and Fubini's theorem gives its area. Removing the
grey trapezoid below the $x$-axis leaves the core part of the niche.

*Proof sketch.* The core part of the niche contains the region below the core, above the $x$-axis
and between the two cut lines. The core is a graph, so Fubini's theorem gives the area of this
region.

Write $\mathbf{x}_K(t) = (X(t), Y(t))$. By the injectivity condition (3),
$X'(t) = \cos t\, \langle \mathbf{x}_K', u_t \rangle - \sin t\, \langle \mathbf{x}_K', v_t \rangle < 0$
on $(0, \pi/2)$, so the core is the graph of a function over
$[X(\varphi^\mathrm{L}), X(\varphi^\mathrm{R})]$. Choose $H > 0$ with the core above the line
$y = -H$. Let $G$ be the open region bounded by the core, the cut lines $d_K^\mathrm{L}$ and
$b_K^\mathrm{R}$ below its ends, and the line $y = -H$. It is the union of $G_0$, the points
vertically below the core, and two thin triangles $T^\mathrm{R}$ and $T^\mathrm{L}$ between the
vertical lines through $\mathbf{x}_K^\mathrm{R}$, $\mathbf{x}_K^\mathrm{L}$ and the cut lines below
them. Let $R$ be the trapezoid of the points strictly between the cut lines with $-H < y < 0$
(Figure 9.4). It is a trapezoid because $Z_K^\mathrm{L}$ lies left of $W_K^\mathrm{R}$, that is,
$h_K(\varphi) + h_K(\pi - \varphi) > 2$, which follows from $\lvert K \rvert \ge 2.2$ as in the
proof of Lemma 9.8.

- *Areas.* $G_0$ is the image of
  $\lbrace (t, s) : t \in (\varphi^\mathrm{R}, \varphi^\mathrm{L}),\ 0 < s < Y(t) + H \rbrace$ under
  $(t, s) \mapsto (X(t), Y(t) - s)$, which has area
  $\int_{\varphi^\mathrm{R}}^{\varphi^\mathrm{L}} -X'(t)\,(Y(t) + H)\, dt$. The triangles and $R$
  are elementary. With
  $\mathcal{J}(\mathbf{x}_K|_{[\varphi^\mathrm{R}, \varphi^\mathrm{L}]}) = \frac12 \int (X Y' - Y X')\, dt$
  and an integration by parts, $\lvert G \rvert - \lvert R \rvert$ is the right side of the lemma.
- *$G$ lies outside $\breve H_K^\mathrm{R}$ and $\breve H_K^\mathrm{L}$.* Their inner normals
  $u_\varphi = (\cos \varphi, \sin \varphi)$ and $u_{\pi - \varphi} = (-\cos \varphi, \sin \varphi)$
  point upwards, the first to the right and the second to the left. The core lies outside both
  half-planes, except that its ends lie on the cut lines (Lemma 9.10). Moving down leaves both
  half-planes, so $G_0$ lies outside them. $T^\mathrm{R}$ lies left of $b_K^\mathrm{R}$, and right
  of and below $\mathbf{x}_K^\mathrm{R} \notin \breve H_K^\mathrm{L}$, so it lies outside both.
  Likewise for $T^\mathrm{L}$.
- *$G \setminus R$ lies in the niche.* A point $p \in G_0$ lies below some $\mathbf{x}_K(t)$,
  $t \in (\varphi^\mathrm{R}, \varphi^\mathrm{L})$, and then in $Q_K^-(t)$, since
  $-(0, 1) = -\sin t\, u_t - \cos t\, v_t$. A point of $T^\mathrm{R}$ lies left of
  $b_K(\varphi^\mathrm{R})$, and below $d_K(\varphi^\mathrm{R})$ since it is right of and below
  $\mathbf{x}_K^\mathrm{R}$; so it lies in $Q_K^-(\varphi^\mathrm{R})$. Likewise
  $T^\mathrm{L} \subseteq Q_K^-(\varphi^\mathrm{L})$. Finally, the points of $G$ below the $x$-axis
  lie in $R$, so the points of $G \setminus R$ lie in the fan.

So
$\lvert \mathcal{N}(K) \setminus \breve H_K^\mathrm{R} \setminus \breve H_K^\mathrm{L} \rvert \ge \lvert G \setminus R \rvert \ge \lvert G \rvert - \lvert R \rvert$.
The full computation is in
[`MovingSofaOptimality/Optimality/UpperBound.lean`](../../MovingSofaOptimality/Optimality/UpperBound.lean).
$\square$

The paper encloses $G$ by a Jordan curve. The formalization describes it as a region between graphs,
which needs the monotonicity of $X$ (REPORT.md, Section 7).

### Lemma 9.17 (the niche avoids the overlap of the cut half-planes)

For $K \in \mathcal{K}^\mathrm{i}$,
$\mathcal{N}(K) \cap \breve H_K^\mathrm{R} \cap \breve H_K^\mathrm{L} = \emptyset$.

*Proof.* The overlap of the two half-planes lies high above the $x$-axis, and the niche lies low.
As in Lemma 9.8, a point $p$ of both half-planes has
$2 p_y \sin \varphi \ge h_K(\varphi) + h_K(\pi - \varphi) - 2$. Let $W_0 = h_K(0) + h_K(\pi)$. The
bottom corners $(h_K(0), 0)$ and $(-h_K(\pi), 0)$ of $K$ give
$h_K(\varphi) + h_K(\pi - \varphi) \ge W_0 \cos \varphi$. And $W_0 \ge \lvert K \rvert \ge 2.2$,
because $K$ lies in $[-h_K(\pi), h_K(0)] \times [0, 1]$. So
$p_y \ge (W_0 \cos \varphi - 2) / (2 \sin \varphi)$.

A point of $\mathcal{N}(K)$ lies in some $Q_K^-(t)$, $t \in (0, \pi/2)$, below the inner corner
$\mathbf{x}_K(t)$. The bounds $h_K(t) \le h_K(0) \cos t + \sin t$ and
$h_K(t + \pi/2) \le h_K(\pi) \sin t + \cos t$, from the same rectangle, bound the height of
$\mathbf{x}_K(t)$ by $W_0 \sin t \cos t + 1 - \sin t - \cos t \le W_0 / 2$. Since
$W_0 (\cos \varphi - \sin \varphi) \ge 2.2 \cdot 0.959 > 2$, we have
$W_0 / 2 < (W_0 \cos \varphi - 2) / (2 \sin \varphi)$, and the two sets are disjoint. $\square$

*Lean: [`opt_niche_hRight_hLeft`](../../MovingSofaOptimality/Optimality/Domain.lean#L707).*

This lemma is not in the paper, which obtains the disjointness from Lemma 9.8 and
$\mathcal{N}(K) \subseteq K$; the latter may fail on $\mathcal{K}^\mathrm{i}$ (Lemma 9.11,
REPORT.md, E21).

### Theorem 9.18 (the upper bound; Baek, Theorem 8.2.4)

For $K \in \mathcal{K}^\mathrm{i}$, $\mathcal{A}(K) \le \mathcal{Q}(K, B_K, D_K)$.

*Proof.* By Lemma 9.17 the niche splits into three disjoint parts:

```math
\lvert \mathcal{N}(K) \rvert = \lvert \mathcal{N}(K) \cap \breve H_K^\mathrm{R} \rvert + \lvert \mathcal{N}(K) \cap \breve H_K^\mathrm{L} \rvert + \lvert \mathcal{N}(K) \setminus \breve H_K^\mathrm{R} \setminus \breve H_K^\mathrm{L} \rvert .
```

Bound each from below by Lemmas 9.15 and 9.16, and subtract from $\lvert K \rvert$. For three points
$p, q, r$ on a line, $\mathcal{J}(p, q) + \mathcal{J}(q, r) = \mathcal{J}(p, r)$, since the
difference is the signed area of the triangle $pqr$. The points $X_B$, $W_K^\mathrm{R}$,
$\mathbf{x}_K^\mathrm{R}$ lie on $b_K^\mathrm{R}$ (for $X_B$ by Lemma 9.11 (2)), so
$\mathcal{J}(X_B, W_K^\mathrm{R}) + \mathcal{J}(W_K^\mathrm{R}, \mathbf{x}_K^\mathrm{R}) = -\mathcal{J}(\mathbf{x}_K^\mathrm{R}, X_B)$.
Likewise $Y_D$, $Z_K^\mathrm{L}$, $\mathbf{x}_K^\mathrm{L}$ lie on $d_K^\mathrm{L}$, and
$\mathcal{J}(\mathbf{x}_K^\mathrm{L}, Z_K^\mathrm{L}) + \mathcal{J}(Z_K^\mathrm{L}, Y_D) = -\mathcal{J}(Y_D, \mathbf{x}_K^\mathrm{L})$.
What remains is

```math
\mathcal{A}(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert \ \le\ \lvert K \rvert + \mathcal{J}(\mathbf{d}_D) + \mathcal{J}(Y_D, \mathbf{x}_K^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K|_{[\varphi^\mathrm{R}, \varphi^\mathrm{L}]}) + \mathcal{J}(\mathbf{x}_K^\mathrm{R}, X_B) + \mathcal{J}(\mathbf{b}_B) ,
```

which is $\mathcal{Q}(K, B_K, D_K)$. $\square$

The paper obtains the disjointness of the three parts from $\mathcal{N}(K) \subseteq K$, which may
fail on $\mathcal{K}^\mathrm{i}$; Lemma 9.17 replaces it (REPORT.md, E21 and Section 7).

*Lean: [`theorem8_2_4`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L1089),
[`segArea_add_of_mem_line`](../../MovingSofaOptimality/Convex/CurveArea.lean#L767).*

## 9.3 Concavity of the upper bound

The plan is to write $\mathcal{Q}(K, B, D) = \mathcal{P}_K - \mathcal{R}_B - \mathcal{L}_D$, where
$\mathcal{R}_B$ and $\mathcal{L}_D$ are Mamikon areas (Lemma 9.23), and to show that $\mathcal{P}_K$
differs from $-\mathcal{S}_K$, a sum of Mamikon areas of $K$, by a convex-linear functional (Lemma
9.26). Mamikon areas are convex (Lemma 9.22), so $\mathcal{Q}$ is a convex-linear functional minus
convex ones. The tangent segments of these Mamikon areas end on curves of two kinds: the outer corner
$\mathbf{y}_K$, and points running along a fixed supporting line.

### Definition 9.19 (tangent line parametrization; Baek, Definition 8.3.1)

For a convex body $K$ and an angle $t$, let $\mathbf{l}_K^t(s) = v_K(s, t)$ for $s < t$ and
$\mathbf{l}_K^t(t) = v_K^-(t)$: the point where $l_K(s)$ meets $l_K(t)$.

*Lean: [`tangentParam`](../../MovingSofaOptimality/Optimality/Concavity.lean#L112).*

### Theorem 9.20 (tangent line parametrization; Baek, Theorems 8.3.1, 8.3.2)

Let $t - \pi < a \le b \le t$.

1. $\mathbf{l}_K^t|_{[a, b]}$ is a continuous curve of bounded variation that runs monotonically
   along $l_K(t)$, its image is the segment from $\mathbf{l}_K^t(a)$ to $\mathbf{l}_K^t(b)$, and
   $\mathcal{J}(\mathbf{l}_K^t|_{[a, b]}) = \mathcal{J}(\mathbf{l}_K^t(a), \mathbf{l}_K^t(b))$.
2. For $s \in [a, b]$, $\mathbf{l}_K^t(s)$ is convex-linear in $K$; this holds for every $s \le t$.

*Proof.* (1) The position $\langle \mathbf{l}_K^t(s), v_t \rangle$ of the point along $l_K(t)$ is
nondecreasing in $s$
([`opt_tangentParam_mono`](../../MovingSofaOptimality/Optimality/Concavity.lean#L142)). Indeed, let
$t - \pi < s_1 < s_2 \le t$. On $l_K(t)$, the half-plane $H_K(s_1)$ is the set of points at or beyond
$\mathbf{l}_K^t(s_1)$ in the direction $v_t$, since $\langle v_t, u_{s_1} \rangle < 0$. And
$\mathbf{l}_K^t(s_2) \in H_K(s_1)$: for $s_2 = t$ because $v_K^-(t) \in K$, and for $s_2 < t$ by the
interpolation inequality of the proof of Lemma 9.11, applied to $s_1 < s_2 < t$. So
$\mathbf{l}_K^t(s_2)$ lies at or beyond $\mathbf{l}_K^t(s_1)$. The position is also continuous,
with limit $\langle v_K^-(t), v_t \rangle$ as $s \to t$ from below
([Theorem 2.9](02-preliminaries.md#theorem-29-limits-of-vertices-baek-theorem-213)). A continuous
monotone curve along a line has the image and the curve area functional of the segment between its
ends. (2) is
[Theorem 8.3](08-convex-curves.md#theorem-83-convex-linear-quantities-baek-theorem-712) (2).
$\square$

*Lean: [`theorem8_3_1`](../../MovingSofaOptimality/Optimality/Concavity.lean#L212),
[`theorem8_3_2`](../../MovingSofaOptimality/Optimality/Concavity.lean#L256).*

Baek's Theorem 8.3.2 also assumes $a > t - \pi$, which (2) does not need (REPORT.md, Section 5).

### Definition 9.21 (the Mamikon terms; Baek, Definitions 8.3.2–8.3.4)

For $K \in \mathcal{K}^\mathrm{i}$ and convex bodies $B, D$:

```math
\mathcal{S}_K = \mathcal{M}_K(0, \varphi^\mathrm{R}; \mathbf{l}_K^{\pi/2}) + \mathcal{M}_K(\varphi^\mathrm{R}, \varphi^\mathrm{L}; \mathbf{y}_K) + \mathcal{M}_K(\varphi^\mathrm{L}, \pi/2; \mathbf{l}_K^{\pi/2 + \varphi^\mathrm{L}}) + \mathcal{M}_K(\pi/2, \pi; \mathbf{l}_K^{\pi}) ,
```

```math
\mathcal{R}_B = \mathcal{M}_B(\pi + \varphi^\mathrm{R}, 3\pi/2; \mathbf{l}_B^{3\pi/2}) , \qquad \mathcal{L}_D = \mathcal{M}_D(3\pi/2, 3\pi/2 + \varphi^\mathrm{L}; \mathbf{l}_D^{3\pi/2 + \varphi^\mathrm{L}}) ,
```

```math
\mathcal{P}_K = \lvert K \rvert + \mathcal{J}(Z_K^\mathrm{L}, \mathbf{x}_K^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K|_{[\varphi^\mathrm{R}, \varphi^\mathrm{L}]}) + \mathcal{J}(\mathbf{x}_K^\mathrm{R}, W_K^\mathrm{R}) .
```

*Lean: [`mamikonS`](../../MovingSofaOptimality/Optimality/Concavity.lean#L271),
[`mamikonR`](../../MovingSofaOptimality/Optimality/Concavity.lean#L278),
[`mamikonL`](../../MovingSofaOptimality/Optimality/Concavity.lean#L282),
[`upperP`](../../MovingSofaOptimality/Optimality/Concavity.lean#L400),
[`outerCorner`](../../MovingSofaOptimality/Sofa/Defs.lean#L116).*

The paper writes $\pi/2 + \varphi^\mathrm{R}$ for the first angle of $\mathcal{R}_B$. The tail
$\mathbf{b}_B$ and Lemma 9.23 need $\pi + \varphi^\mathrm{R}$, which the formalization uses
(REPORT.md, E27). The term $\mathcal{P}_K$ is $\lvert K \rvert$ minus the lower bound of Lemma 9.16
for the core part of the niche. $\mathcal{R}_B$ and $\mathcal{L}_D$ are the lower bounds of Lemma
9.15 for the two tails (Lemma 9.23). $\mathcal{S}_K$ is the area swept by tangent segments of $K$
above the cap (Figure 9.5).

![Gerver's cap K, light blue, with the core part of its niche white under the orange core, and four purple regions swept by tangent segments: region 1, a thin fan at the bottom right corner (1, 0) reaching up to the line y = 1; region 2, a large fan of segments from the right side and top of the cap up to a purple arch, the outer corner curve y_K from y_K(phi^R) on the right to y_K(phi^L) on the left; region 3, a thin wedge just above the top edge; region 4, segments from the left side of the cap to the vertical line x = -h_K(pi). A bold black outline encloses the cap and the four regions, minus the core part of the niche](figures/09-optimality/mamikon-cap.svg)

*Figure 9.5.* The Mamikon regions of $\mathcal{S}_K$ for Gerver's cap, numbered as the four terms of
Definition 9.21. Their areas are convex in $K$ (Lemma 9.22). The region inside the bold outline,
which consists of $K$ and the four regions minus the core part of the niche, has area
$\mathcal{S}_K + \mathcal{P}_K$. Its boundary is made of segments on lines that depend linearly on
$K$, the curve $\mathbf{y}_K$ and the core, which is why $\mathcal{S}_K + \mathcal{P}_K$ is
convex-linear in $K$ (Lemma 9.26).

### Lemma 9.22 (the Mamikon terms are convex; Baek, Lemma 8.3.3)

For $0 < \varphi < \pi/4$, $\mathcal{S}_K$ is a convex quadratic functional of
$K \in \mathcal{K}^\mathrm{i}$, and $\mathcal{R}_B$ and $\mathcal{L}_D$ are convex quadratic
functionals of $B, D \in \mathcal{K}$.

*Proof.* Each of the six terms is a Mamikon area $\mathcal{M}_K(a, b; \mathbf{z}_K)$ with
$0 < b - a < \pi$, where $\mathbf{z}_K$ is a continuous curve of bounded variation with
$\mathbf{z}_K(s) \in l_K(s)$, convex-linear in $K$. For the tangent line parametrizations this is
Theorem 9.20, as $t - \pi < a \le b \le t$ in each case. For
$\mathbf{y}_K(s) = h_K(s)\, u_s + h_K(s + \pi/2)\, v_s$ it follows from
[Theorem 8.3](08-convex-curves.md#theorem-83-convex-linear-quantities-baek-theorem-712) (1).
[Theorem 8.22](08-convex-curves.md#theorem-822-mamikon-areas-are-convex-baek-theorem-742) applies to
each term, and a sum of convex quadratic functionals is convex and quadratic. $\square$

*Lean: [`lemma8_3_3`](../../MovingSofaOptimality/Optimality/Concavity.lean#L372).*

### Lemma 9.23 (decomposition of the upper bound; Baek, Lemma 8.3.4)

For $0 < \varphi < \pi/4$ and $(K, B, D) \in \mathcal{L}$,
$\mathcal{Q}(K, B, D) = \mathcal{P}_K - \mathcal{R}_B - \mathcal{L}_D$.

*Proof.* By Definition 9.4 (3), $h_B(\pi + \varphi) = 1 - h_K(\varphi)$ and $h_B(3\pi/2) = 0$. So
$l_B(\pi + \varphi) = b_K^\mathrm{R}$, $l_B(3\pi/2)$ is the $x$-axis, and
$v_B(\pi + \varphi, 3\pi/2) = W_K^\mathrm{R}$. By Theorem 9.20 (1), the curve
$\mathbf{l}_B^{3\pi/2}$ runs along the $x$-axis from $W_K^\mathrm{R}$ to $W_B$, so its
$\mathcal{J}$ vanishes, and

```math
\mathcal{R}_B = \mathcal{J}(X_B, W_K^\mathrm{R}) + 0 + \mathcal{J}(W_B, W_B) - \mathcal{J}(\mathbf{b}_B) = \mathcal{J}(X_B, W_K^\mathrm{R}) - \mathcal{J}(\mathbf{b}_B) .
```

In the same way, by Definition 9.4 (5), $\mathbf{l}_D^{3\pi/2 + \varphi^\mathrm{L}}$ runs along
$d_K^\mathrm{L}$ from $Z_K^\mathrm{L}$ to $Y_D$. As $Z_D$ and $Z_K^\mathrm{L}$ lie on the $x$-axis,
$\mathcal{L}_D = \mathcal{J}(Z_D, Z_K^\mathrm{L}) + \mathcal{J}(Z_K^\mathrm{L}, Y_D) - \mathcal{J}(\mathbf{d}_D) = \mathcal{J}(Z_K^\mathrm{L}, Y_D) - \mathcal{J}(\mathbf{d}_D)$.
Then $\mathcal{P}_K - \mathcal{R}_B - \mathcal{L}_D = \mathcal{Q}(K, B, D)$ by the collinear
identities of the proof of Theorem 9.18. $\square$

*Lean: [`lemma8_3_4`](../../MovingSofaOptimality/Optimality/Concavity.lean#L405).*

### Lemma 9.24 (the area as a sum over arcs; Baek, Lemma 8.3.5)

For $0 < \varphi < \pi/4$, on $\mathcal{K}^\mathrm{i}$,

```math
\lvert K \rvert \equiv_K \mathcal{J}(\mathbf{u}_K^{0, \varphi^\mathrm{R}}) + \mathcal{J}(\mathbf{u}_K^{\varphi^\mathrm{R}, \varphi^\mathrm{L}}) + \mathcal{J}(\mathbf{u}_K^{\varphi^\mathrm{L}, \pi/2}) + \mathcal{J}(\mathbf{u}_K^{\pi/2, \pi}) .
```

*Proof.* By [Theorem 8.4](08-convex-curves.md#theorem-84-the-area-is-quadratic-baek-theorem-713),
$\lvert K \rvert = \frac12 \int_{[0, 2\pi)} h_K \, d\sigma_K$. A cap with rotation angle $\pi/2$ is
an intersection of half-planes with normal angles in $[0, \pi] \cup \lbrace 3\pi/2 \rbrace$, so
$\sigma_K$ is carried by this set, and $h_K(3\pi/2) = 0$. By the injectivity condition (1),
$\sigma_K$ has no atoms at $0$, $\varphi^\mathrm{R}$, $\varphi^\mathrm{L}$ and $\pi$. Splitting
$(0, \pi)$ at $\varphi^\mathrm{R}$, $\varphi^\mathrm{L}$ and $\pi/2$ leaves the integrals over the
four arcs, which are their curve area functionals by definition, and the atom at $\pi/2$. The atom
contributes $\frac12 h_K(\pi/2)\, \sigma_K(\lbrace \pi/2 \rbrace) = \frac12 \sigma_K(\lbrace \pi/2 \rbrace)$,
which is convex-linear in $K$ by
[Theorem 8.3](08-convex-curves.md#theorem-83-convex-linear-quantities-baek-theorem-712) (3).
$\square$

*Lean: [`lemma8_3_5`](../../MovingSofaOptimality/Optimality/Concavity.lean#L854).*

The paper applies its Theorem 7.3.2 to the arc $\mathbf{u}_K^{0, \pi}$, outside its range
$b < a + \pi$. The splitting above avoids this (REPORT.md, E20).

### Lemma 9.25 (linear differences; Baek, Lemma 8.3.6)

For $0 < \varphi < \pi/4$, on $\mathcal{K}^\mathrm{i}$, with
$I = [\varphi^\mathrm{R}, \varphi^\mathrm{L}]$:

1. $\mathcal{J}(\mathbf{y}_K|_I) \equiv_K \mathcal{J}(\mathbf{x}_K|_I)$;
2. $\mathcal{J}(\mathbf{l}_K^{\pi/2}(\varphi^\mathrm{R}), \mathbf{y}_K(\varphi^\mathrm{R})) \equiv_K \mathcal{J}(W_K^\mathrm{R}, \mathbf{x}_K^\mathrm{R})$;
3. $\mathcal{J}(\mathbf{l}_K^{\pi/2 + \varphi^\mathrm{L}}(\pi/2), \mathbf{y}_K(\varphi^\mathrm{L})) \equiv_K \mathcal{J}(Z_K^\mathrm{L}, \mathbf{x}_K^\mathrm{L})$.

*Lean: [`lemma8_3_6`](../../MovingSofaOptimality/Optimality/Concavity.lean#L889).*

In (3) the paper evaluates $\mathbf{l}_K^{\pi/2 + \varphi^\mathrm{L}}$ at $\varphi^\mathrm{L}$,
where it equals $\mathbf{y}_K(\varphi^\mathrm{L})$. The left side would then vanish, and the
statement would be false, since $\mathcal{J}(Z_K^\mathrm{L}, \mathbf{x}_K^\mathrm{L})$ is not linear
in $K$. The value at $\pi/2$, which Lemma 8.3.7 uses, is meant (REPORT.md, E23).

*Proof.* In each item, the two sides differ by shifts that do not depend on $K$. (1)
$\mathbf{y}_K(t) = \mathbf{x}_K(t) + c_t$ with $c_t = u_t + v_t$, and
$\mathcal{J}(\mathbf{x} + c) - \mathcal{J}(\mathbf{x}) = \frac12 \int c \times d\mathbf{x} + \frac12 \int \mathbf{x} \times dc + \mathcal{J}(c)$
is affine in $\mathbf{x}$, which is convex-linear in $K$. (2) The differences
$\mathbf{y}_K(\varphi) - \mathbf{x}_K^\mathrm{R} = u_\varphi + v_\varphi$ and
$\mathbf{l}_K^{\pi/2}(\varphi) - W_K^\mathrm{R} = (\sec \varphi\, (1 - \sin \varphi), 1)$, a
diagonal of the parallelogram $P_K^\mathrm{R}$ (Lemma 9.7), are constant. For constant vectors
$c, c'$, the difference
$\mathcal{J}(p + c, q + c') - \mathcal{J}(p, q) = \frac12 (p \times c' + c \times q + c \times c')$
is affine in $(p, q)$, as in
[Lemma 8.9](08-convex-curves.md#lemma-89-shifting-the-arguments-of-a-convex-bilinear-map-baek-lemma-716),
and $W_K^\mathrm{R}$, $\mathbf{x}_K^\mathrm{R}$ are convex-linear in $K$. (3) is the same with
$P_K^\mathrm{L}$. $\square$

### Lemma 9.26 (the Mamikon regions above the cap; Baek, Lemma 8.3.7)

For $0 < \varphi < \pi/4$, on $\mathcal{K}^\mathrm{i}$, $\mathcal{S}_K \equiv_K -\mathcal{P}_K$.

*Proof.* Expand the four Mamikon areas of $\mathcal{S}_K$ by
[Definition 8.20](08-convex-curves.md#definition-820-mamikon-region-and-its-area-baek-definitions-741-742),
and replace the $\mathcal{J}$ of each tangent line parametrization by that of its segment (Theorem
9.20 (1)). Only the vertices at the ends of the four intervals enter. By the injectivity condition
(1), $\sigma_K$ has no atoms at $0$, $\varphi^\mathrm{R}$, $\varphi^\mathrm{L}$ and $\pi$, so
$v_K^+ = v_K^-$ there: these vertices are $A_K(0) = (h_K(0), 0)$, $A_K(\varphi^\mathrm{R})$,
$A_K(\varphi^\mathrm{L})$ and $C_K(\pi/2) = (-h_K(\pi), 0)$. At $\pi/2$ they are
$v_K^-(\pi/2) = A_K(\pi/2)$ and $v_K^+(\pi/2) = C_K(0)$, the ends of the top edge. Writing
$\mathbf{l}^{\pi/2}$, $\mathbf{l}^{\pi - \varphi}$, $\mathbf{l}^{\pi}$ for the tangent line
parametrizations of $K$, the sixteen terms are:

| Term of $\mathcal{S}_K$ | out | along $\mathbf{z}$ | back | arc |
| --- | --- | --- | --- | --- |
| $\mathcal{M}_K(0, \varphi^\mathrm{R}; \mathbf{l}^{\pi/2})$ | $\mathcal{J}(A_K(0), \mathbf{l}^{\pi/2}(0))$ | $\mathcal{J}(\mathbf{l}^{\pi/2}(0), \mathbf{l}^{\pi/2}(\varphi^\mathrm{R}))$ | $\mathcal{J}(\mathbf{l}^{\pi/2}(\varphi^\mathrm{R}), A_K(\varphi^\mathrm{R}))$ | $-\mathcal{J}(\mathbf{u}_K^{0, \varphi^\mathrm{R}})$ |
| $\mathcal{M}_K(\varphi^\mathrm{R}, \varphi^\mathrm{L}; \mathbf{y}_K)$ | $\mathcal{J}(A_K(\varphi^\mathrm{R}), \mathbf{y}_K(\varphi^\mathrm{R}))$ | $\mathcal{J}(\mathbf{y}_K\vert_I)$ | $\mathcal{J}(\mathbf{y}_K(\varphi^\mathrm{L}), A_K(\varphi^\mathrm{L}))$ | $-\mathcal{J}(\mathbf{u}_K^{\varphi^\mathrm{R}, \varphi^\mathrm{L}})$ |
| $\mathcal{M}_K(\varphi^\mathrm{L}, \pi/2; \mathbf{l}^{\pi - \varphi})$ | $\mathcal{J}(A_K(\varphi^\mathrm{L}), \mathbf{y}_K(\varphi^\mathrm{L}))$ | $\mathcal{J}(\mathbf{y}_K(\varphi^\mathrm{L}), \mathbf{l}^{\pi - \varphi}(\pi/2))$ | $\mathcal{J}(\mathbf{l}^{\pi - \varphi}(\pi/2), A_K(\pi/2))$ | $-\mathcal{J}(\mathbf{u}_K^{\varphi^\mathrm{L}, \pi/2})$ |
| $\mathcal{M}_K(\pi/2, \pi; \mathbf{l}^{\pi})$ | $\mathcal{J}(C_K(0), \mathbf{l}^{\pi}(\pi/2))$ | $\mathcal{J}(\mathbf{l}^{\pi}(\pi/2), C_K(\pi/2))$ | $\mathcal{J}(C_K(\pi/2), C_K(\pi/2)) = 0$ | $-\mathcal{J}(\mathbf{u}_K^{\pi/2, \pi})$ |

Here $\mathbf{l}^{\pi - \varphi}(\varphi^\mathrm{L}) = \mathbf{y}_K(\varphi^\mathrm{L})$, the outer
corner being the meeting point of $l_K(\varphi^\mathrm{L})$ and $l_K(\pi - \varphi)$. Now regroup:

- the arc column sums to $-\lvert K \rvert$ modulo linear terms (Lemma 9.24);
- the third term of the first row and the first of the second join along $l_K(\varphi^\mathrm{R})$
  into
  $\mathcal{J}(\mathbf{l}^{\pi/2}(\varphi^\mathrm{R}), \mathbf{y}_K(\varphi^\mathrm{R})) \equiv \mathcal{J}(W_K^\mathrm{R}, \mathbf{x}_K^\mathrm{R})$
  (Lemma 9.25 (2));
- $\mathcal{J}(\mathbf{y}_K|_I) \equiv \mathcal{J}(\mathbf{x}_K|_I)$ (Lemma 9.25 (1));
- the third term of the second row and the first of the third cancel;
- $\mathcal{J}(\mathbf{y}_K(\varphi^\mathrm{L}), \mathbf{l}^{\pi - \varphi}(\pi/2)) \equiv \mathcal{J}(\mathbf{x}_K^\mathrm{L}, Z_K^\mathrm{L})$
  (Lemma 9.25 (3));
- the remaining terms are linear. Two points $(x_1, 1)$, $(x_2, 1)$ of the line $y = 1$ give
  $\mathcal{J} = \frac12 (x_1 - x_2)$
  ([Proposition 8.12](08-convex-curves.md#proposition-812-segments-baek-propositions-724-725) (2)),
  linear in $K$ by Theorem 8.3 (2).
  This covers the second term of the first row and the remaining terms of the last two rows except
  $\mathcal{J}(\mathbf{l}^{\pi}(\pi/2), C_K(\pi/2)) = \mathcal{J}((-h_K(\pi), 1), (-h_K(\pi), 0)) = \frac12 h_K(\pi)$.
  Finally $\mathcal{J}(A_K(0), \mathbf{l}^{\pi/2}(0)) = \mathcal{J}((h_K(0), 0), (h_K(0), 1)) = \frac12 h_K(0)$.

Altogether
$\mathcal{S}_K \equiv_K -\lvert K \rvert + \mathcal{J}(W_K^\mathrm{R}, \mathbf{x}_K^\mathrm{R}) + \mathcal{J}(\mathbf{x}_K|_I) + \mathcal{J}(\mathbf{x}_K^\mathrm{L}, Z_K^\mathrm{L}) = -\mathcal{P}_K$.
$\square$

*Lean: [`lemma8_3_7`](../../MovingSofaOptimality/Optimality/Concavity.lean#L1113).*

In the paper's proof the last regrouping reads $\frac12 h_K(\pi/2)$ for $\frac12 h_K(\pi)$, and a
factor $\frac12$ is missing in the second term of the first row. Both terms are linear anyway
(REPORT.md, E27).

### Theorem 9.27 (concavity; Baek, Theorem 8.3.8)

For $0 < \varphi < \pi/4$, $\mathcal{Q}$ is concave on $\mathcal{L}$.

*Proof.* By Lemma 9.23,

```math
\mathcal{Q}(K, B, D) = \bigl(\mathcal{P}_K + \mathcal{S}_K\bigr) - \mathcal{S}_K - \mathcal{R}_B - \mathcal{L}_D .
```

The bracket is convex-linear in $K$ (Lemma 9.26), and $\mathcal{S}_K$, $\mathcal{R}_B$,
$\mathcal{L}_D$ are convex (Lemma 9.22). The projections of $\mathcal{L}$ onto $K$, $B$ and $D$ are
convex-linear. So $\mathcal{Q}$ is a convex-linear functional minus convex ones, hence concave.
$\square$

*Lean: [`theorem8_3_8`](../../MovingSofaOptimality/Optimality/Concavity.lean#L1131),
[`kiDomain`](../../MovingSofaOptimality/Optimality/Concavity.lean#L306).*

## 9.4 The directional derivative at Gerver's sofa

### Definition 9.28 (reflected measures and the measure of the core; Baek, Definitions 8.4.5, 8.4.6)

For a convex body $C$, $\breve\sigma_C(X) = \sigma_C(X + \pi)$ and $\breve h_C(t) = h_C(t + \pi)$.
For a cap $K \in \mathcal{K}^\mathrm{i}$, let

```math
i_K(t) = \langle \mathbf{x}_K'(t), v_t \rangle , \qquad i_K(t + \pi/2) = -\langle \mathbf{x}_K'(t), u_t \rangle \qquad (t \in (0, \pi/2]) ,
```

and $\iota_K = i_K(t)\, dt$ on $[0, \pi]$. By the injectivity condition (3), $i_K > 0$ on
$(0, \pi) \setminus \lbrace \pi/2 \rbrace$.

*Lean: [`sigmaBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L68),
[`suppBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L71),
[`iFun`](../../MovingSofaOptimality/Optimality/Variation.lean#L75),
[`iota`](../../MovingSofaOptimality/Optimality/Variation.lean#L81).*

The density $i_K$ splits the velocity of the inner corner into its components along $v_t$ and
$-u_t$, the directions of the inner walls $b_K(t)$ and $d_K(t)$. In Theorem 9.29 (5), the measure
$\iota_K$ plays for the core the role that $\sigma_K$ plays for the boundary of $K$.

### Theorem 9.29 (directional derivatives of the pieces; Baek, Theorems 8.5.1–8.5.5)

Let $I = [\varphi^\mathrm{R}, \varphi^\mathrm{L}]$ with $0 < \varphi < \pi/4$.

1. For $K, K^* \in \mathcal{K}^\mathrm{i}$:
   $D\lvert \cdot \rvert(K; K^*) = \int_{[0, \pi]} (h_{K^*} - h_K)\, d\sigma_K$.
2. For convex bodies $K, K^*$ and $a < b < a + \pi$:

   ```math
   D\mathcal{J}(\mathbf{u}^{a,b})(K; K^*) = \int_{(a, b)} (h_{K^*} - h_K)\, d\sigma_K + \bigl[\mathcal{J}(v_K^-(b), v_{K^*}^-(b)) - \mathcal{J}(v_K^+(a), v_{K^*}^+(a))\bigr] .
   ```

3. For points $(p, q), (p^*, q^*) \in \mathbb{R}^2 \times \mathbb{R}^2$:

   ```math
   D\mathcal{J}(p, q; p^*, q^*) = \tfrac12 \bigl((p^* + q^*) \times (q - p) - 2\, p \times q\bigr) + \bigl[\mathcal{J}(q, q^*) - \mathcal{J}(p, p^*)\bigr] .
   ```

4. For $\mathbf{x}, \mathbf{x}^* \in C^\mathrm{BV}[a, b]$:

   ```math
   D\mathcal{J}(\mathbf{x}; \mathbf{x}^*) = \int_a^b (\mathbf{x}^* - \mathbf{x}) \times d\mathbf{x} + \bigl[\mathcal{J}(\mathbf{x}(b), \mathbf{x}^*(b)) - \mathcal{J}(\mathbf{x}(a), \mathbf{x}^*(a))\bigr] .
   ```

5. For $K, K^* \in \mathcal{K}^\mathrm{i}$:

   ```math
   D\mathcal{J}(\mathbf{x}_\cdot|_I)(K; K^*) = \int_{I \cup (I + \pi/2)} (h_{K^*} - h_K)\, i_K \, dt + \bigl[\mathcal{J}(\mathbf{x}_K^\mathrm{L}, \mathbf{x}_{K^*}^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K^\mathrm{R}, \mathbf{x}_{K^*}^\mathrm{R})\bigr] .
   ```

*Lean: [`theorem8_5_1`](../../MovingSofaOptimality/Optimality/Variation.lean#L445),
[`theorem8_5_2`](../../MovingSofaOptimality/Optimality/Variation.lean#L479),
[`theorem8_5_3`](../../MovingSofaOptimality/Optimality/Variation.lean#L501),
[`theorem8_5_4`](../../MovingSofaOptimality/Optimality/Variation.lean#L551),
[`theorem8_5_5`](../../MovingSofaOptimality/Optimality/Variation.lean#L611).*

*Proof.* Each functional is quadratic, $f(K) = \beta(K, K)$, so by
[Lemma 8.6](08-convex-curves.md#lemma-86-derivative-of-a-quadratic-functional-baek-lemma-714)
$Df(K; K^*) = \beta(K, K^*) + \beta(K^*, K) - 2 \beta(K, K)$. If $\beta$ is symmetric, this is
$2\beta(K^*, K) - 2\beta(K, K)$. In general, it remains to compute the asymmetry
$\beta(K, K^*) - \beta(K^*, K)$, which gives the bracketed end point terms.

(1): $\beta(K_1, K_2) = \frac12 \int h_{K_1}\, d\sigma_{K_2}$. Write
$h_K'(t) = \langle v_K^+(t), v_t \rangle$, the right derivative of $h_K$. Since $\sigma_K$ is the
Stieltjes measure of $h_K' + \int_0^t h_K$, integration by parts gives

```math
\int_{(a, b]} h_{K_1}\, d\sigma_{K_2} = \bigl[h_{K_1} h_{K_2}'\bigr]_a^b - \int_a^b h_{K_1}' h_{K_2}'\, dt + \int_a^b h_{K_1} h_{K_2}\, dt ,
```

whose integrals are symmetric in $K_1, K_2$. Over a full period the boundary terms cancel, so
$\beta$ is symmetric (it is the mixed area), and
$D\lvert \cdot \rvert(K; K^*) = \int_{[0, 2\pi)} (h_{K^*} - h_K)\, d\sigma_K$. For two caps,
$\sigma_K$ is carried by $[0, \pi] \cup \lbrace 3\pi/2 \rbrace$ and both support functions vanish
at $3\pi/2$, which gives (1).

(2), as in the paper: $\beta(K_1, K_2) = \frac12 \int_{(a, b)} h_{K_1}\, d\sigma_{K_2}$. Lemma 6.3 for
the cross product $v_{K_1}^+ \times v_{K_2}^+$, whose left limits are $v_{K_1}^-$ and $v_{K_2}^-$
(Theorem 2.9), gives, once the atoms at $b$ are removed,

```math
\int_{(a, b)} dv_{K_1}^+ \times v_{K_2}^+ + \int_{(a, b)} v_{K_1}^- \times dv_{K_2}^+ = v_{K_1}^-(b) \times v_{K_2}^-(b) - v_{K_1}^+(a) \times v_{K_2}^+(a) .
```

By [Lemma 8.17](08-convex-curves.md#lemma-817-the-bilinear-form-along-the-vertices-baek-lemma-733),
which needs $b < a + \pi$, the two integrals are $-2\beta(K_2, K_1)$ and $2\beta(K_1, K_2)$, so
$\beta(K_1, K_2) - \beta(K_2, K_1) = \mathcal{J}(v_{K_1}^-(b), v_{K_2}^-(b)) - \mathcal{J}(v_{K_1}^+(a), v_{K_2}^+(a))$,
which is (2).

(3) $\beta((p_1, q_1), (p_2, q_2)) = \mathcal{J}(p_1, q_2)$, and the formula is algebra. (4)
$\beta = \mathcal{B}$, and integration by parts (Lemma 6.3 for the cross product) gives
$\int_a^b \mathbf{x} \times d\mathbf{x}^* = \mathbf{x}(b) \times \mathbf{x}^*(b) - \mathbf{x}(a) \times \mathbf{x}^*(a) + \int_a^b \mathbf{x}^* \times d\mathbf{x}$.

(5) Apply (4) to $\mathbf{x} = \mathbf{x}_K|_I$ and $\mathbf{x}^* = \mathbf{x}_{K^*}|_I$. The inner
corner is continuously differentiable, with
$\mathbf{x}^* - \mathbf{x} = (h_{K^*} - h_K)(t)\, u_t + (h_{K^*} - h_K)(t + \pi/2)\, v_t$ and
$\mathbf{x}' = \langle \mathbf{x}', u_t \rangle u_t + \langle \mathbf{x}', v_t \rangle v_t$, so

```math
(\mathbf{x}^* - \mathbf{x}) \times \mathbf{x}' = (h_{K^*} - h_K)(t)\, i_K(t) + (h_{K^*} - h_K)(t + \pi/2)\, i_K(t + \pi/2) .
```

Integrating over $I$ gives the integral over $I \cup (I + \pi/2)$. $\square$

The paper proves (1) with Schneider's formula for the mixed area, which Mathlib lacks; the
formalization proves the symmetry of $\beta$ by the integration by parts above ([`opt_Bs_symm`](../../MovingSofaOptimality/Optimality/Variation.lean#L408);
REPORT.md, Section 7). The proofs of (2) and (4) are the paper's ([`opt_curveBilin_antisymm`](../../MovingSofaOptimality/Optimality/Variation.lean#L527)).

### Theorem 9.30 (the directional derivative of the upper bound; Baek, Theorem 8.5.6)

Let $0 < \varphi < \pi/4$, and let $(K, B, D) \in \mathcal{L}$ satisfy
$X_B = \mathbf{x}_K^\mathrm{R}$ and $Y_D = \mathbf{x}_K^\mathrm{L}$. For every
$(K^*, B^*, D^*) \in \mathcal{L}$, the directional derivative of $\mathcal{Q}$ at $(K, B, D)$
towards $(K^*, B^*, D^*)$ is

```math
\int_{[0, \pi]} (h_{K^*} - h_K)\, d\sigma_K - \int_{I \cup (I + \pi/2)} (h_{K^*} - h_K)\, i_K\, dt + \int_{(\varphi^\mathrm{R}, \pi/2)} (\breve h_{B^*} - \breve h_B)\, d\breve\sigma_B + \int_{(\pi/2, \pi/2 + \varphi^\mathrm{L})} (\breve h_{D^*} - \breve h_D)\, d\breve\sigma_D .
```

*Proof.* Differentiate the six terms of $\mathcal{Q}$ with Theorem 9.29. The integrals give the four
terms above; those of the tails are shifted by $\pi$. The bracketed end point terms telescope along
the closed curve of Definition 9.13:

```math
\begin{aligned}
&\bigl[\mathcal{J}(Y_D, Y_{D^*}) - \mathcal{J}(Z_D, Z_{D^*})\bigr] + \bigl[\mathcal{J}(\mathbf{x}_K^\mathrm{L}, \mathbf{x}_{K^*}^\mathrm{L}) - \mathcal{J}(Y_D, Y_{D^*})\bigr] - \bigl[\mathcal{J}(\mathbf{x}_K^\mathrm{L}, \mathbf{x}_{K^*}^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K^\mathrm{R}, \mathbf{x}_{K^*}^\mathrm{R})\bigr] \\
&\quad + \bigl[\mathcal{J}(X_B, X_{B^*}) - \mathcal{J}(\mathbf{x}_K^\mathrm{R}, \mathbf{x}_{K^*}^\mathrm{R})\bigr] + \bigl[\mathcal{J}(W_B, W_{B^*}) - \mathcal{J}(X_B, X_{B^*})\bigr] .
\end{aligned}
```

This leaves $\mathcal{J}(W_B, W_{B^*}) - \mathcal{J}(Z_D, Z_{D^*})$. These points lie on the
$x$-axis, so both terms vanish. The other part of Theorem 9.29 (3) for the two segments,
$\frac12 ((p^* + q^*) \times (q - p) - 2\, p \times q)$, vanishes because the segments have equal
end points, $p = q$. $\square$

*Lean: [`theorem8_5_6`](../../MovingSofaOptimality/Optimality/Variation.lean#L680).*

### Theorem 9.31 (Gerver's triple is a critical point; Baek, Theorem 8.5.7)

Let $K = K_G$ be the cap of Gerver's sofa, $B = B_K$ and $D = D_K$. For every
$(K^*, B^*, D^*) \in \mathcal{L}$, the directional derivative of $\mathcal{Q}$ at $(K, B, D)$
towards $(K^*, B^*, D^*)$ is at most 0.

*Lean: [`theorem8_5_7`](../../MovingSofaOptimality/Main.lean#L136),
[`gm_sigma_decomp`](../../MovingSofaOptimality/Main.lean#L91),
[`theorem8_4_5`](../../MovingSofaOptimality/Gerver/Properties.lean#L1356),
[`theorem8_4_3_two`](../../MovingSofaOptimality/Gerver/Properties.lean#L1693),
[`theorem8_4_3_three`](../../MovingSofaOptimality/Gerver/Properties.lean#L992),
[`gm_sigmaBreve_B_restrict`](../../MovingSofaOptimality/Gerver/Properties.lean#L1568).*

*Proof.* Romik's equations say that, at Gerver's triple, $\sigma_K$ is the sum of $\iota_K$ and the
reflected measures of the tails. Substituting this into Theorem 9.30 cancels the core term, and what
remains is controlled by the constraints of $\mathcal{L}$.

By [Theorem 10.22](10-gerver.md#theorem-1022-left-middle-and-right-parts-baek-theorem-843) (2),
$X_B = \mathbf{x}_K^\mathrm{R}$ and $Y_D = \mathbf{x}_K^\mathrm{L}$, so Theorem 9.30 applies. Its
four integrals live on $[0, \pi]$, which Gerver's angles $0 < \varphi < \theta$ cut into the
intervals $J_1 = [0, \varphi)$, $J_2 \cup J_3 = [\varphi, \pi/2 - \theta)$,
$J_4 = [\pi/2 - \theta, \pi/2 - \varphi)$, $J_5 = [\pi/2 - \varphi, \pi/2)$, the point $\pi/2$, and
their mirror images $J_{11 - i} = \pi - J_i$. Romik's equations become identities of measures on
these intervals
([Theorem 10.25](10-gerver.md#theorem-1025-romiks-equations-as-measures-baek-theorem-845)):

| Interval | $\sigma_K$ | Integrand of the derivative there |
| --- | --- | --- |
| $J_1 = [0, \varphi)$ | $0$ | none |
| $J_2 \cup J_3 = [\varphi, \pi/2 - \theta)$ | $\iota_K$ | none: the first two integrals cancel |
| $J_4 = [\pi/2 - \theta, \pi/2 - \varphi)$ | $\breve\sigma_B + \iota_K$ | $(h_{K^*} + \breve h_{B^*}) - (h_K + \breve h_B)$ against $\breve\sigma_B$ |
| $J_5 = [\pi/2 - \varphi, \pi/2)$ | $\breve\sigma_B$ | $(h_{K^*} + \breve h_{B^*}) - (h_K + \breve h_B)$ against $\breve\sigma_B$ |
| $\lbrace \pi/2 \rbrace$ | the atom of the top edge | $h_{K^*}(\pi/2) - h_K(\pi/2) = 0$ |
| $J_6 = (\pi/2, \pi/2 + \varphi]$ | $\breve\sigma_D$ | $(h_{K^*} + \breve h_{D^*}) - (h_K + \breve h_D)$ against $\breve\sigma_D$ |
| $J_7 = (\pi/2 + \varphi, \pi/2 + \theta]$ | $\breve\sigma_D + \iota_K$ | $(h_{K^*} + \breve h_{D^*}) - (h_K + \breve h_D)$ against $\breve\sigma_D$ |
| $J_8 \cup J_9 = (\pi/2 + \theta, \pi - \varphi]$ | $\iota_K$ | none: the first two integrals cancel |
| $J_{10} = (\pi - \varphi, \pi]$ | $0$ | none |

In one formula, $\sigma_K$ on $[0, \pi]$ is $\iota_K$ on $I \cup (I + \pi/2)$, plus
$\breve\sigma_B$ on $[\pi/2 - \theta, \pi/2)$, plus $\breve\sigma_D$ on
$(\pi/2, \pi/2 + \theta]$, plus the atom at $\pi/2$
([`gm_sigma_decomp`](../../MovingSofaOptimality/Main.lean#L91)). Moreover $\breve\sigma_B$ vanishes
on $(\varphi, \pi/2 - \theta)$, where $B$ has the single vertex $\mathbf{x}_K^\mathrm{R}$, and
likewise $\breve\sigma_D$ on $(\pi/2 + \theta, \pi - \varphi)$. Substituting, the derivative of
Theorem 9.30 becomes

```math
\int_{[\pi/2 - \theta, \pi/2)} \bigl[(h_{K^*} + \breve h_{B^*}) - (h_K + \breve h_B)\bigr]\, d\breve\sigma_B + \int_{(\pi/2, \pi/2 + \theta]} \bigl[(h_{K^*} + \breve h_{D^*}) - (h_K + \breve h_D)\bigr]\, d\breve\sigma_D .
```

On $[\pi/2 - \theta, \pi/2]$, $h_K(t) + h_B(\pi + t) = 1$: the inner wall $b_K(t)$ touches $B$
along the tail (Theorem 10.22 (3)). And $h_{K^*}(t) + h_{B^*}(\pi + t) \le 1$ by Definition 9.4 (2).
So the first integrand is at most 0, and $\breve\sigma_B \ge 0$. The second integral is the mirror
case, with Definition 9.4 (4). $\square$

In the paper's proof, "nonnegative" should read "nonpositive" (twice), and $J_1$ should read
$J_{10}$ in the last case. The constraints on an arbitrary $(K^*, B^*, D^*)$ are Definition 8.1.3
(2)–(5), not Lemma 8.1.7 (1), (3), which concerns $(K, B_K, D_K)$ (REPORT.md, E27).

The table is the measure-theoretic form of the balancing argument of Gerver and Romik. On each
interval, Romik's equations balance the pieces of the boundary of $G$ that change when the
supporting lines of the triple move. Where $B$ or $D$ takes part, the constraints of $\mathcal{L}$
allow only moves that lose area.

### Corollary 9.32 (Gerver's triple is the maximum; Baek, Corollary 8.5.8)

With $K_G$ the cap of Gerver's sofa, for every $(K, B, D) \in \mathcal{L}$,

```math
\mathcal{Q}(K, B, D) \le \mathcal{Q}(K_G, B_{K_G}, D_{K_G}) .
```

*Proof.* Gerver's triple lies in $\mathcal{L}$ by Theorems 9.2 (3) and 9.12. $\mathcal{Q}$ is a
concave quadratic functional on $\mathcal{L}$ (Proposition 9.14, Theorem 9.27), and its directional
derivatives at Gerver's triple are at most 0 (Theorem 9.31).
[Theorem 8.7](08-convex-curves.md#theorem-87-maximum-of-a-concave-quadratic-functional-baek-theorem-715)
concludes. $\square$

*Lean: [`corollary8_5_8`](../../MovingSofaOptimality/Main.lean#L259),
[`gerverTriple`](../../MovingSofaOptimality/Main.lean#L65),
[`gerver_inL`](../../MovingSofaOptimality/Main.lean#L60).*

## 9.5 The optimality of Gerver's sofa

### Theorem 9.33 (optimality of Gerver's sofa; Baek, Theorem 1.1.1)

Gerver's sofa $G$ is a moving sofa, and every moving sofa $S$ has
$\lvert S \rvert \le \lvert G \rvert$.

*Lean: [`theorem1_1_1`](../../MovingSofaOptimality/Main.lean#L302),
[`gm_area_le`](../../MovingSofaOptimality/Main.lean#L269),
[`Baek.gerver_sofa_optimal`](../../Challenge.lean#L384).*

*Proof.* $G$ is a monotone sofa with rotation angle $\pi/2$
([Theorem 10.11](10-gerver.md#theorem-1011-the-structure-of-gervers-sofa-baek-theorem-841-1-3-4)),
hence a moving sofa. Let $S$ be a moving sofa. Since $\lvert G \rvert \ge 2.2$, we may assume
$\lvert S \rvert \ge 2.2$. Then (Figure 9.1):

1. $S$ moves with a rotation angle $\omega \in [\sec^{-1}(2.2), \pi/2]$
   ([Theorem 5.1](05-rotation-angle.md#theorem-51-a-first-bound-on-the-rotation-angle-baek-theorem-151)).
2. A balanced maximum cap $K_\omega$ with rotation angle $\omega$ exists, and its sofa
   $K_\omega \setminus \mathcal{N}(K_\omega)$ has the largest area among the moving sofas with
   rotation angle $\omega$
   ([Theorem 4.40](04-balanced.md#theorem-440-balanced-maximum-sofas-baek-theorem-356)). So
   $\lvert S \rvert \le \lvert K_\omega \setminus \mathcal{N}(K_\omega) \rvert$.
3. A rotated copy of that sofa moves with rotation angle $\pi/2$
   ([Theorem 5.2](05-rotation-angle.md#theorem-52-the-right-angle-baek-theorem-152)), and rotations
   preserve area.
4. Let $K$ be a balanced maximum cap with rotation angle $\pi/2$ (Theorem 4.40 again). Its sofa has
   the largest area among the moving sofas with rotation angle $\pi/2$, and this area is
   $\mathcal{A}(K)$
   ([Theorem 3.29](03-monotone.md#theorem-329-the-area-of-a-monotone-sofa-baek-theorem-2510)). So
   $\lvert S \rvert \le \mathcal{A}(K)$.
5. $K \in \mathcal{K}^\mathrm{i}$ by Theorem 9.2 (2), so
   $\mathcal{A}(K) \le \mathcal{Q}(K, B_K, D_K)$ by Theorem 9.18, and
   $(K, B_K, D_K) \in \mathcal{L}$ by Theorem 9.12.
6. $\mathcal{Q}(K, B_K, D_K) \le \mathcal{Q}(K_G, B_{K_G}, D_{K_G})$ by Corollary 9.32.
7. $\mathcal{Q}(K_G, B_{K_G}, D_{K_G}) = \mathcal{A}(K_G)$
   ([Theorem 10.26](10-gerver.md#theorem-1026-the-upper-bound-is-attained-baek-theorem-846)): for
   Gerver's sofa the tails end where the core begins, the two segments of $\mathcal{Q}$ vanish, and
   the niche is exactly the region enclosed by the core and the tails. Finally
   $\mathcal{A}(K_G) = \lvert G \rvert$ (Theorem 3.29).

So $\lvert S \rvert \le \lvert G \rvert$. $\square$

The paper's proof first picks a balanced maximum sofa that attains the maximum area. The Lean proof
compares each moving sofa with Gerver's directly, as above. In
[`Challenge.lean`](../../Challenge.lean), Theorem 9.33 is the statement
[`Baek.gerver_sofa_optimal`](../../Challenge.lean#L384), written with Mathlib's definitions only,
for the parameters whose existence and uniqueness are
[`Baek.gerver_params_exists`](../../Challenge.lean#L368) and
[`Baek.gerver_params_unique`](../../Challenge.lean#L372) (Definition 9.3);
[`Solution.lean`](../../Solution.lean) derives it from
[`theorem1_1_1`](../../MovingSofaOptimality/Main.lean#L302). The area of $G$ lies in
$[2.2192, 2.2199]$ ([`gerverSofa_area_mem`](../../MovingSofaOptimality/Main.lean#L291),
[Appendix B](appendix-b.md)).

The choice of the angles matters only at the end (Baek, Remark 8.5.1). Other cut angles
$(\varphi^\mathrm{R}, \varphi^\mathrm{L})$ also give a concave upper bound, but its maximizer need
not come from a sofa, because the ends of the core and the tails need not match. With Gerver's
angles they match at Gerver's triple, and the bound is attained.
