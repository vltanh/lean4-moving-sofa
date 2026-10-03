# 10. Gerver's sofa

[Contents](README.md) · [← 9. The upper bound and the optimality of Gerver's sofa](09-optimality.md) · [11. Uniqueness I: approximating a maximizing cap →](11-selection.md)

This chapter defines Gerver's sofa $G$ as the formalization does, following Romik [4], and proves
the facts about it that the optimality proof of [Chapter 9](09-optimality.md) and the uniqueness
proof of Chapters [11](11-selection.md) and [12](12-uniqueness.md) use. The rotation path
$\mathbf{x}$ of $G$ is glued from five explicit curves, one for each phase of the motion, whose 22
parameters solve Romik's equations (27)–(44) (§10.1). Theorem 10.8 shows that these equations have
exactly one solution with $\varphi \in [0.039, 0.04]$ and $\theta \in [0.68, 0.69]$, so that $G$ is
well defined, and Theorem 10.21 that $2.2192 \le \lvert G \rvert \le 2.2199$. The rest of the
chapter proves Section 8.4 of Baek's paper: $G$ is a monotone sofa whose cap $K$ has the vertices
$\mathbf{A}(t)$, $\mathbf{C}(t)$ and the inner corner $\mathbf{x}(t)$, and whose niche is the region
below the curves $\mathbf{D}$, $\mathbf{x}$ and $\mathbf{B}$ (Theorems 10.11 and 10.19, together
Baek's Theorem 8.4.1, which the paper states without proof); Romik's balancing equations hold
(Theorem 10.12); $K$ satisfies the injectivity condition (Theorem 10.13); and the identities of
measures and areas that Chapter 9 uses hold (Theorems 10.22 to 10.26).

Everything rests on one computation. On each phase the rotation path is
$\mathbf{x}(t) = R_t\, w(t) + \kappa$ for an explicit curve $w$, so that $\mathbf{x}'$, the contact
curves and their derivatives are explicit in the rotating frame $u_t, v_t$ (Lemma 10.5 and
Table 10.1). The geometric statements then reduce to the signs of four explicit functions and to a
few inequalities in one variable, which follow from enclosures of the parameters. The numerical
work, the existence and uniqueness of the solution, its enclosures and the area bounds, is done by
interval arithmetic, explained in [Appendix B](appendix-b.md). Every formal statement about $G$ is
made for every solution of Romik's equations in the box; by Theorem 10.8 there is exactly one.

## 10.1 Romik's description

### Definition 10.1 (the shape of a rotation path; Romik, Equation (8))

Let $\mathbf{x} : [0, \pi/2] \to \mathbb{R}^2$. The *shape* of the rotation path $\mathbf{x}$ is the set

```math
S_{\mathbf{x}} = H_L \cap \bigcap_{t \in [0, \pi/2]} \bigl(\mathbf{x}(t) + R_t L\bigr) \cap \bigl(\mathbf{x}(\pi/2) + R_{\pi/2} V_L\bigr) .
```

*Lean: [`Baek.shapeOfPath`](../../Challenge.lean#L192), [`MovingSofaOptimality.shapeOfPath`](../../MovingSofaOptimality/Gerver/Defs.lean#L111).*

Seen from the sofa, at the moment the sofa has turned by $t$ the hallway occupies
$\mathbf{x}(t) + R_t L$ ([Section 1.2](README.md#12-the-main-theorems)). A point $q$ lies in this
copy of $L$ when its *hallway coordinates*

```math
X = \langle q - \mathbf{x}(t), u_t \rangle , \qquad Y = \langle q - \mathbf{x}(t), v_t \rangle
```

satisfy $X \le 1$, $Y \le 1$, and $X \ge 0$ or $Y \ge 0$. The hallway at time $t$ has the outer
walls $a(t) = \lbrace X = 1 \rbrace$ and $c(t) = \lbrace Y = 1 \rbrace$, the inner walls
$\vec b(t) = \lbrace X = 0,\ Y \le 0 \rbrace$ and $\vec d(t) = \lbrace Y = 0,\ X \le 0 \rbrace$ on
the lines $b(t)$ and $d(t)$, and the inner corner $\mathbf{x}(t)$.

### Definition 10.2 (contact paths; Romik, Equations (9)–(12))

For a differentiable $\mathbf{x}$ let $\alpha(t) = \langle \mathbf{x}'(t), u_t \rangle$ and
$\beta(t) = \langle \mathbf{x}'(t), v_t \rangle$, and

```math
\mathbf{A} = \mathbf{x} + \alpha\, v_t + u_t , \qquad \mathbf{B} = \mathbf{x} + \alpha\, v_t , \qquad \mathbf{C} = \mathbf{x} - \beta\, u_t + v_t , \qquad \mathbf{D} = \mathbf{x} - \beta\, u_t .
```

*Lean: [`MovingSofaOptimality.GerverParams.contactA`](../../MovingSofaOptimality/Gerver/Defs.lean#L77), [`MovingSofaOptimality.GerverParams.contactB`](../../MovingSofaOptimality/Gerver/Defs.lean#L80),
[`MovingSofaOptimality.GerverParams.contactC`](../../MovingSofaOptimality/Gerver/Defs.lean#L82), [`MovingSofaOptimality.GerverParams.contactD`](../../MovingSofaOptimality/Gerver/Defs.lean#L85),
[`Baek.GerverParams.contactB`](../../Challenge.lean#L169), [`Baek.GerverParams.contactD`](../../Challenge.lean#L172).*

In hallway coordinates $\mathbf{A}(t) = (1, \alpha(t))$, $\mathbf{B}(t) = (0, \alpha(t))$,
$\mathbf{C}(t) = (-\beta(t), 1)$ and $\mathbf{D}(t) = (-\beta(t), 0)$, so the four points lie on the
lines $a(t)$, $b(t)$, $c(t)$, $d(t)$. They are the points where these lines touch their envelopes:
$a(t)$ is the line $\langle q - \mathbf{x}(t), u_t \rangle = 1$, the derivative in $t$ of the left
side is $-\alpha(t) + \langle q - \mathbf{x}(t), v_t \rangle$, and it vanishes on $a(t)$ exactly at
$\mathbf{A}(t)$; the other three are alike. Romik's derivation rests on this: a sofa that moves along
$\mathbf{x}$ and stays in contact with the wall $a(t)$ during an interval of times touches it at
$\mathbf{A}(t)$.

### Definition 10.3 (Romik's parameters and the five phases)

A *parameter tuple* consists of the two angles $\varphi$ and $\theta$, the ten numbers
$a_1, a_2, b_1, b_2, c_1, c_2, d_1, d_2, e_1, e_2$ and five points
$\kappa_1, \dots, \kappa_5 \in \mathbb{R}^2$: 22 real parameters. Its five curves, Romik's general
solutions (SOL1)–(SOL5) of Romik's differential equations on the five phases, are

```math
\begin{aligned}
\mathbf{x}_1(t) &= R_t \bigl(a_1 \cos t + a_2 \sin t - 1,\ -a_2 \cos t + a_1 \sin t - \tfrac12\bigr) + \kappa_1 , \\
\mathbf{x}_2(t) &= R_t \bigl(-\tfrac{t^2}{4} + b_1 t + b_2,\ \tfrac t2 - b_1 - 1\bigr) + \kappa_2 , \\
\mathbf{x}_3(t) &= R_t \bigl(c_1 - t,\ c_2 + t\bigr) + \kappa_3 , \\
\mathbf{x}_4(t) &= R_t \bigl(-\tfrac t2 + d_1 - 1,\ -\tfrac{t^2}{4} + d_1 t + d_2\bigr) + \kappa_4 , \\
\mathbf{x}_5(t) &= R_t \bigl(e_1 \cos t + e_2 \sin t - \tfrac12,\ -e_2 \cos t + e_1 \sin t - 1\bigr) + \kappa_5 .
\end{aligned}
```

With the angles $t_0 = 0 < t_1 = \varphi < t_2 = \theta < t_3 = \frac\pi2 - \theta < t_4 = \frac\pi2 - \varphi < t_5 = \frac\pi2$
(Baek's Definition 8.4.1), the rotation path (Romik's Equation (25)) is $\mathbf{x}(t) = \mathbf{x}_i(t)$
on the $i$th phase: on $[t_0, t_1)$, $[t_1, t_2)$, $[t_2, t_3]$, $(t_3, t_4]$ and $(t_4, t_5]$
for $i = 1, \dots, 5$, and its contact paths are written $\mathbf{A}, \mathbf{B}, \mathbf{C},
\mathbf{D}$ (Baek's Definitions 8.4.2 and 8.4.3).

*Lean: [`Baek.GerverParams`](../../Challenge.lean#L122), [`MovingSofaOptimality.GerverParams`](../../MovingSofaOptimality/Gerver/Defs.lean#L30), [`MovingSofaOptimality.GerverParams.x₁`](../../MovingSofaOptimality/Gerver/Defs.lean#L54),
[`MovingSofaOptimality.GerverParams.x₂`](../../MovingSofaOptimality/Gerver/Defs.lean#L57), [`MovingSofaOptimality.GerverParams.x₃`](../../MovingSofaOptimality/Gerver/Defs.lean#L60),
[`MovingSofaOptimality.GerverParams.x₄`](../../MovingSofaOptimality/Gerver/Defs.lean#L62), [`MovingSofaOptimality.GerverParams.x₅`](../../MovingSofaOptimality/Gerver/Defs.lean#L65),
[`MovingSofaOptimality.GerverParams.path`](../../MovingSofaOptimality/Gerver/Defs.lean#L69), [`MovingSofaOptimality.GerverParams.tPt`](../../MovingSofaOptimality/Gerver/Properties.lean#L48),
[`MovingSofaOptimality.GerverParams.curveA`](../../MovingSofaOptimality/Gerver/Properties.lean#L60).*

### Definition 10.4 (Romik's equations; Gerver's sofa)

A parameter tuple *solves Romik's equations* if $0 < \varphi < \theta < \pi/4$ and

1. (27)–(31), left-right symmetry: $e_1 = a_1$, $e_2 = -a_2$, $d_1 = \frac\pi4 - b_1$,
   $d_2 = b_2 + \frac\pi4\bigl(2b_1 - \frac\pi4\bigr)$ and $c_2 = c_1 - \frac\pi2$;
2. (32)–(34), the start: $\kappa_1 = (1 - a_1, \frac14)$ and $a_2 = -\frac14$, which say that
   $\mathbf{x}(0) = 0$ and $\mathbf{A}(0) = (1, 0)$;
3. (35)–(42), continuous differentiability: $\mathbf{x}_i(t_i) = \mathbf{x}_{i+1}(t_i)$ and
   $\mathbf{x}_i'(t_i) = \mathbf{x}_{i+1}'(t_i)$ for $i = 1, 2, 3, 4$;
4. (43)–(44), the transitions between the contact phases: $\mathbf{x}_1(t_1) = \mathbf{B}_4(t_3)$
   and $\mathbf{x}_5(t_4) = \mathbf{D}_2(t_2)$, where $\mathbf{B}_4$ and $\mathbf{D}_2$ are the
   contact paths of $\mathbf{x}_4$ and $\mathbf{x}_2$.

The tuple *lies in the box* if $\varphi \in [0.039, 0.04]$ and $\theta \in [0.68, 0.69]$.
*Gerver's sofa* is the shape $G = S_{\mathbf{x}}$ of its rotation path.

*Lean: [`Baek.GerverParams.IsSolution`](../../Challenge.lean#L175), [`Baek.GerverParams.InBox`](../../Challenge.lean#L187), [`Baek.gerverSofa`](../../Challenge.lean#L197),
[`MovingSofaOptimality.GerverParams.IsSolution`](../../MovingSofaOptimality/Gerver/Defs.lean#L89), [`MovingSofaOptimality.GerverParams.InBox`](../../MovingSofaOptimality/Gerver/Defs.lean#L105),
[`MovingSofaOptimality.gerverSofa`](../../MovingSofaOptimality/Gerver/Defs.lean#L116).*

The Challenge states Definitions 10.1, 10.3 and 10.4, with the contact paths $\mathbf{B}$ and
$\mathbf{D}$ that (43)–(44) use, in Mathlib's vocabulary, in the namespace `Baek` of
[`Challenge.lean`](../../Challenge.lean); they are copied verbatim from
[`ChallengeDefs.lean`](../../ChallengeDefs.lean), and they agree field by field with the library's
definitions in [`Defs.lean`](../../MovingSofaOptimality/Gerver/Defs.lean)
([`Baek.GerverParams.toLib`](../../Solution.lean#L41); [`Baek.gerverSofa_eq_lib`](../../Solution.lean#L54) holds by `rfl`). The paper defines $G$ from
"the" solution of Romik's equations (its Definition 8.1.2) and notes that $\varphi \in [0.039, 0.040]$;
the formalization proves that the box contains exactly one solution (Theorem 10.8) and states every
result about $G$ for every solution in the box.

Romik derived the five phases from the contacts of the sofa with the moving hallway. On each phase
the sofa touches the walls at a fixed set of contact points, and on the walls of each direction the
differential side lengths at these points balance (Theorem 10.12):

| Phase | Interval | Contact points |
| --- | --- | --- |
| 1 | $[t_0, t_1)$ | $\mathbf{A}$, $\mathbf{C}$, $\mathbf{D}$ |
| 2 | $[t_1, t_2)$ | $\mathbf{A}$, $\mathbf{C}$, $\mathbf{D}$, $\mathbf{x}$ |
| 3 | $[t_2, t_3]$ | $\mathbf{A}$, $\mathbf{C}$, $\mathbf{x}$ |
| 4 | $(t_3, t_4]$ | $\mathbf{A}$, $\mathbf{B}$, $\mathbf{C}$, $\mathbf{x}$ |
| 5 | $(t_4, t_5]$ | $\mathbf{A}$, $\mathbf{B}$, $\mathbf{C}$ |

Figure 10.1 shows the rotation path of the solution on Gerver's sofa, and Figure 10.2 the contact
points in each phase.

![Gerver's sofa, a light blue region between y = 0 and y = 1 with a niche in the middle of its lower side, and its rotation path drawn in five colours: a short first phase from x(0) at the origin up to x(phi) at the right foot of the niche, the second phase up the right side of the niche to x(theta), a short third phase over the top to x(pi/2 - theta), the fourth phase down the left side to x(pi/2 - phi), and a short fifth phase down to x(pi/2) on the x-axis; a legend gives the five intervals of t](figures/10-gerver/phases.svg)

*Figure 10.1.* Gerver's sofa $G$ and its rotation path $\mathbf{x}$, coloured by phase. The path
starts at $\mathbf{x}(0) = 0$, runs along the top of the niche from $\mathbf{x}(\varphi)$ to
$\mathbf{x}(\frac\pi2 - \varphi)$, and ends at $\mathbf{x}(\frac\pi2)$ on the $x$-axis. The first
and the last phase are short: $\varphi = 0.0392$.

![Five panels, one per phase, each showing the fixed L-shaped hallway with Gerver's sofa placed at a time of that phase. Phase 1: the sofa lies in the horizontal arm and touches the top wall at C, the right wall at A and the inner wall at D. Phase 2: it also touches the inner corner x. Phase 3: at t = pi/4 it touches the outer walls at C and A and the inner corner x. Phase 4: it touches A, C, x and the inner vertical wall at B. Phase 5: the sofa lies in the vertical arm and touches A, B and C](figures/10-gerver/contacts.svg)

*Figure 10.2.* The sofa in the hallway at one time of each phase, moved by
$q \mapsto R_{-t}(q - \mathbf{x}(t))$, which maps the copy $\mathbf{x}(t) + R_t L$ to $L$. The
contact points are the outer ones $\mathbf{A}, \mathbf{C}$ (blue), the inner ones
$\mathbf{B}, \mathbf{D}$ (green) and the inner corner $\mathbf{x}$ (orange). Phases 4 and 5 are the
mirror images of phases 2 and 1.

## 10.2 The rotating frame

### Lemma 10.5 (the phases in the rotating frame)

Let $w = (w_1, w_2) : \mathbb{R} \to \mathbb{R}^2$ be twice differentiable, $\kappa \in \mathbb{R}^2$,
and $\mathbf{x}(t) = R_t\, w(t) + \kappa$. Then $\mathbf{x}' = \alpha\, u_t + \beta\, v_t$ with
$\alpha = w_1' - w_2$ and $\beta = w_2' + w_1$; the contact paths are

```math
\mathbf{A} = R_t(w_1 + 1,\, w_1') + \kappa , \quad \mathbf{B} = R_t(w_1,\, w_1') + \kappa , \quad \mathbf{C} = R_t(-w_2',\, w_2 + 1) + \kappa , \quad \mathbf{D} = R_t(-w_2',\, w_2) + \kappa ;
```

and, with $\rho_A = w_1'' + w_1 + 1$ and $\rho_C = w_2'' + w_2 + 1$,

```math
\mathbf{A}' = \rho_A\, v_t , \qquad \mathbf{B}' = (\rho_A - 1)\, v_t , \qquad \mathbf{C}' = -\rho_C\, u_t , \qquad \mathbf{D}' = (1 - \rho_C)\, u_t .
```

*Lean: [`gs_Phase`](../../MovingSofaOptimality/Gerver/Frame.lean#L60), [`gs_Phase.hasDerivAt_X`](../../MovingSofaOptimality/Gerver/Frame.lean#L120), [`gs_Phase.A_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L151), [`gs_Phase.contactA_X`](../../MovingSofaOptimality/Gerver/Frame.lean#L1139),
[`gs_Phase.hasDerivAt_A`](../../MovingSofaOptimality/Gerver/Frame.lean#L123), [`gs_Phase.hasDerivAt_B`](../../MovingSofaOptimality/Gerver/Frame.lean#L128), [`gs_Phase.hasDerivAt_C`](../../MovingSofaOptimality/Gerver/Frame.lean#L133), [`gs_Phase.hasDerivAt_D`](../../MovingSofaOptimality/Gerver/Frame.lean#L138),
[`rom_hasDerivAt_rot`](../../MovingSofaOptimality/External/Romik.lean#L46).*

*Proof.* Write $R_t(a, b) = a\, u_t + b\, v_t$. Since $u_t' = v_t$ and $v_t' = -u_t$, the curve
$t \mapsto R_t(a(t), b(t))$ has derivative $R_t(a' - b,\ b' + a)$; for $(a, b) = (w_1, w_2)$ this is
the formula for $\mathbf{x}'$. Next,
$\mathbf{x} + \alpha\, v_t + u_t = R_t(w_1 + 1,\ w_2 + w_1' - w_2) + \kappa = R_t(w_1 + 1, w_1') + \kappa$,
and $\mathbf{B}$, $\mathbf{C}$, $\mathbf{D}$ are alike. Finally, the rule with
$(a, b) = (w_1 + 1, w_1')$ gives $\mathbf{A}' = R_t(0,\ w_1'' + w_1 + 1) = \rho_A\, v_t$, and the
other three derivatives are alike. $\square$

The phase $\mathbf{x}_i$ of Definition 10.3 is $R_t\, w_i(t) + \kappa_i$ for the explicit $w_i$
displayed there. Lemma 10.5 makes the four functions $\alpha$, $\beta$, $\rho_A$, $\rho_C$ of each
phase explicit (Table 10.1), and with them the derivative of $\mathbf{x}$ and of its contact paths.
The equations (27)–(34) make the last two phases mirror images of the first two.

| Phase | $\alpha(t)$ | $\beta(t)$ | $\rho_A(t)$ | $\rho_C(t)$ |
| --- | --- | --- | --- | --- |
| 1 | $\frac12(1 - \cos t) - 2a_1 \sin t$ | $2a_1 \cos t - \frac12 \sin t - 1$ | $0$ | $\frac12$ |
| 2 | $2b_1 + 1 - t$ | $\frac12 - \frac{t^2}4 + b_1 t + b_2$ | $\frac12 - \frac{t^2}4 + b_1 t + b_2$ | $\frac t2 - b_1$ |
| 3 | $\frac\pi2 - 1 - c_1 - t$ | $1 + c_1 - t$ | $1 + c_1 - t$ | $1 + c_1 + t - \frac\pi2$ |
| 4 | $-\beta_2(\frac\pi2 - t)$ | $-\alpha_2(\frac\pi2 - t)$ | $\rho_{C,2}(\frac\pi2 - t)$ | $\rho_{A,2}(\frac\pi2 - t)$ |
| 5 | $-\beta_1(\frac\pi2 - t)$ | $-\alpha_1(\frac\pi2 - t)$ | $\frac12$ | $0$ |

*Table 10.1.* The rotating frame of the five phases, for a parameter tuple that satisfies
(27)–(34); $\alpha_i$, $\beta_i$, $\rho_{A,i}$, $\rho_{C,i}$ denote the entries of phase $i$
([`gs_ph1`](../../MovingSofaOptimality/Gerver/Frame.lean#L361) to [`gs_ph5`](../../MovingSofaOptimality/Gerver/Frame.lean#L401), [`gs_α₁_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L975) to [`gs_β₅_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L1012), [`gs_ρA₁_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L1085) to [`gs_ρC₅_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L1104)). On the first phase
$\rho_A = 0$: the curve $\mathbf{A}$ stays at the corner $\mathbf{A}(0) = (1, 0)$; on the last,
$\mathbf{C}$ stays at $\mathbf{C}(\pi/2)$.

### Lemma 10.6 (signs and junctions)

Let the parameters solve Romik's equations and lie in the box. Then:

1. $\mathbf{x}$ is continuously differentiable, $\mathbf{x}(0) = 0$, and $\mathbf{x}(\pi/2)$ lies on
   the $x$-axis;
2. $\alpha(0) = 0$ and $\alpha(t) < 0$ for $t \in (0, \pi/2]$; $\beta(t) > 0$ for $t \in [0, \pi/2)$
   and $\beta(\pi/2) = 0$;
3. $\rho_A \ge 0$ and $\rho_C \ge 0$ on $[0, \pi/2]$; $\rho_A < 1$ on $[t_3, t_5]$ and $\rho_C < 1$ on
   $[t_0, t_2]$;
4. $\mathbf{B}(t_3) = \mathbf{x}(t_1)$ and $\mathbf{D}(t_2) = \mathbf{x}(t_4)$, and $\mathbf{B}(t_5)$
   and $\mathbf{D}(t_0)$ lie on the $x$-axis.

*Lean: [`gs_contDiff_path`](../../MovingSofaOptimality/Gerver/Frame.lean#L631), [`gs_path_zero`](../../MovingSofaOptimality/Gerver/Frame.lean#L1158), [`gs_path_pi_div_two_snd`](../../MovingSofaOptimality/Gerver/Frame.lean#L1166), [`gs_α_zero`](../../MovingSofaOptimality/Gerver/Frame.lean#L1054), [`gs_α_neg`](../../MovingSofaOptimality/Gerver/Frame.lean#L1025),
[`gs_β_pos`](../../MovingSofaOptimality/Gerver/Frame.lean#L1040), [`gs_β_pi_div_two`](../../MovingSofaOptimality/Gerver/Frame.lean#L1057), [`gs_ρ_nonneg`](../../MovingSofaOptimality/Gerver/Frame.lean#L1108), [`gb_rhoA_lt`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L443), [`gb_rhoC_lt`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L485), [`gs_contactB_t₃`](../../MovingSofaOptimality/Gerver/Frame.lean#L1185),
[`gs_contactD_t₂`](../../MovingSofaOptimality/Gerver/Frame.lean#L1194), [`gs_contactB_pi_div_two_snd`](../../MovingSofaOptimality/Gerver/Frame.lean#L1203), [`gs_contactD_zero_snd`](../../MovingSofaOptimality/Gerver/Frame.lean#L1208).*

*Proof.* (1) The equations (35)–(42) glue the five smooth curves into a continuously differentiable
one. The start equations give $\mathbf{x}(0) = 0$, and the second coordinates of the four continuity
equations, combined with the symmetry equations, add up to $\mathbf{x}(\pi/2)_y = 0$.

(2), (3) By Table 10.1 the claims for phases 4 and 5 are those for phases 2 and 1 at
$\frac\pi2 - t$, so it suffices to look at phases 1 to 3, where they follow from the enclosures of
the parameters given by Theorem 10.8: with $b_1 = -0.52762$, $b_2 = 0.92026$, $c_1 = 0.62605$ and
$a_1 = 1.21032$ (to five decimals),
$\alpha_2 = 2b_1 + 1 - t < 0$, $\beta_2 = \rho_{A,2}$ decreases on $[0, \theta]$ to
$\beta_2(\theta) = 0.94474$, $0 < \rho_{C,2} = \frac t2 - b_1 < 0.869$ on $[0, \theta]$,
$\alpha_3 \le \frac\pi2 - 1 - c_1 - \theta < 0$ and $\beta_3 = \rho_{A,3} \ge 1 + c_1 - t_3 > 0.73$.
On the first phase $\beta_1 \ge 2a_1 \cos 0.04 - \frac12 \sin 0.04 - 1 > 1.39$, and
$\alpha_1(t) < 0$ for $0 < t \le \varphi$ because $\frac12(1 - \cos t) \le \frac{t^2}4$ and
$2a_1 \sin t > 2a_1 (t - \frac{t^3}6)$. The ends follow from the formulas:
$\alpha_1(0) = 0$ and $\beta_5(\frac\pi2) = -\alpha_1(0) = 0$.

(4) The transition equations say $\mathbf{x}_1(t_1) = \mathbf{B}_4(t_3)$ and
$\mathbf{x}_5(t_4) = \mathbf{D}_2(t_2)$. The path agrees with $\mathbf{x}_1$ at $t_1$ and with
$\mathbf{x}_5$ at $t_4$, and its contact paths agree with those of $\mathbf{x}_4$ at $t_3$ and of
$\mathbf{x}_2$ at $t_2$, because $\mathbf{x}$ and $\mathbf{x}'$ are continuous at the junctions.
Finally $\mathbf{B}(\frac\pi2) = \mathbf{x}(\frac\pi2) + \alpha\, v_{\pi/2}$ and
$\mathbf{D}(0) = \mathbf{x}(0) - \beta\, u_0$ differ from points of the $x$-axis by horizontal
vectors. $\square$

In terms of Gerver's four constants of [Appendix A](appendix-a.md),
$A = -\alpha(\varphi) = 0.0944$ and $B = \beta(\varphi) = 1.3992$.

## 10.3 Existence and uniqueness of the parameters

Romik's equations are 18 equations, ten of them between vectors, in 22 unknowns. All unknowns but
the two angles enter linearly, and eliminating them leaves two equations in the two angles.

### Proposition 10.7 (reduction to two equations)

For angles $\varphi$ and $\theta$ write $c = \cos\varphi$, $s = \sin\varphi$, $C = \cos\theta$,
$S = \sin\theta$, and let

```math
K = \tfrac\pi2 - \tfrac32 - \theta + \tfrac{\theta^2}4 , \qquad D = 2c - (2 + \theta - \varphi)\, s , \qquad \beta_0 = \tfrac12\bigl(\varphi - \tfrac12 - \tfrac c2\bigr) , \qquad N = \tfrac s2 - \tfrac{\varphi^2}4 + K + \tfrac32 - (2 + \theta - \varphi)\, \beta_0 ,
```

```math
a_1 = \frac ND , \qquad b_1 = \beta_0 - s\, a_1 , \qquad b_2 = K - (2 + \theta)\, b_1 , \qquad c_1 = \tfrac\pi2 - 2 - 2b_1 ,
```

```math
U = \Bigl(-c\,\bigl(K - \tfrac{\varphi^2}4\bigr) + s\,\bigl(\tfrac\varphi2 - 1\bigr) + \tfrac32 C + S\,\bigl(\tfrac{3\theta}2 - 3\bigr),\ \ -s\,\bigl(K - \tfrac{\varphi^2}4\bigr) - c\,\bigl(\tfrac\varphi2 - 1\bigr) - \tfrac S2 + C\,\bigl(\tfrac\theta2 - 1\bigr)\Bigr) ,
```

```math
V = \bigl(c\,(2 + \theta - \varphi) - s - 3S,\ \ s\,(2 + \theta - \varphi) + c - C\bigr) , \qquad H(\varphi, \theta) = D\,\bigl(U + b_1 V\bigr) \in \mathbb{R}^2 .
```

Let $P(\varphi, \theta)$ be the parameter tuple with these $a_1, b_1, b_2, c_1$, the other coefficients
given by (27)–(34), $\kappa_1 = (1 - a_1, \frac14)$, $\kappa_2$ and $\kappa_3$ given by the
continuity equations at $t_1$ and $t_2$, $\kappa_4 = (2\kappa_{3,1} - \kappa_{2,1}, \kappa_{2,2})$ and
$\kappa_5 = (2\kappa_{3,1} - 1 + a_1, \frac14)$. Then:

1. $D > 0$ on the box;
2. a solution of Romik's equations in the box is the tuple $P(\varphi, \theta)$ of its angles, and
   $H(\varphi, \theta) = 0$;
3. if $(\varphi, \theta)$ lies in the box and $H(\varphi, \theta) = 0$, then $P(\varphi, \theta)$ solves
   Romik's equations.

*Lean: [`rom_mk`](../../MovingSofaOptimality/External/Romik.lean#L156), [`rom_Hz`](../../MovingSofaOptimality/External/Romik/Fix.lean#L26), [`rom_D_pos`](../../MovingSofaOptimality/External/Romik.lean#L177), [`rom_eq_mk`](../../MovingSofaOptimality/External/Romik.lean#L183), [`rom_Hz_of_solution`](../../MovingSofaOptimality/External/Romik.lean#L372), [`rom_mk_isSolution`](../../MovingSofaOptimality/External/Romik.lean#L300),
[`rom_mk_contact1_iff`](../../MovingSofaOptimality/External/Romik.lean#L267), [`rom_mk_contact2`](../../MovingSofaOptimality/External/Romik.lean#L286), [`rom_H_eq`](../../MovingSofaOptimality/External/Romik.lean#L253).*

*Proof sketch.* (1) $D \ge 1.8923$ on the box, by interval arithmetic ([`rom_D_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L455);
[Figure B.1](appendix-b.md)).

(2) By Lemma 10.5, $\mathbf{x}_i' = R_t(w_i' + J w_i)$ with $J(a, b) = (-b, a)$, and $R_t$ is
injective, so each derivative condition among (35)–(42) is an equation between the frame vectors
$(\alpha, \beta)$ of two phases (Table 10.1). At $t_2 = \theta$ the two coordinates read
$2b_1 + 1 - \theta = \frac\pi2 - 1 - c_1 - \theta$ and
$\frac12 - \frac{\theta^2}4 + b_1\theta + b_2 = 1 + c_1 - \theta$, which give $c_1$ and $b_2$ as
displayed. At $t_1 = \varphi$ the first coordinate gives $b_1 = \beta_0 - s\, a_1$, and the second,
after substituting $b_1$ and $b_2$, is the linear equation $a_1 D = N$. So $a_1, b_1, b_2, c_1$ are
those of $P(\varphi, \theta)$, and the remaining coefficients follow from (27)–(34). The continuity
conditions at $t_1, \dots, t_4$ then determine $\kappa_2, \dots, \kappa_5$, and with the symmetry
those at $t_3$ and $t_4$ take the displayed form. Substituting all of this into the transition
equation (43) turns it into $U + b_1 V = 0$; multiplied by $D > 0$, this is $H(\varphi, \theta) = 0$
(and $D\, b_1 = c\,(\varphi - \frac12 - \frac c2) - s\,(\frac s2 - \frac{\varphi^2}4 + K + \frac32)$,
which is how [`Num.lean`](../../MovingSofaOptimality/External/Romik/Num.lean) writes $H$).

(3) Conversely, $P(\varphi, \theta)$ satisfies (27)–(34) and the continuity and derivative conditions
at $t_1$ and $t_2$ by construction, and (43) because $H = 0$ and $D \ne 0$. The derivative
conditions at $t_3$ and $t_4$, the continuity conditions there, and the second transition equation
(44) follow from these by the left-right symmetry, as Romik says: each is a polynomial identity in
$\varphi, \theta, c, s, C, S, \pi$ and the coefficients, which Lean checks with `ring` and
`linear_combination`. $\square$

### Theorem 10.8 (Gerver's sofa is well defined; Romik, Section 4)

Romik's equations have exactly one solution in the box. Its angles satisfy

```math
\lvert \varphi - 0.0391773648 \rvert \le 10^{-10} , \qquad \lvert \theta - 0.6813015094 \rvert \le 10^{-10} ,
```

and its other parameters lie in explicit intervals of width at most $1.5 \cdot 10^{-8}$ around the
values of Table 10.2.

*Lean: [`Baek.gerver_params_exists`](../../Challenge.lean#L328), [`Baek.gerver_params_unique`](../../Challenge.lean#L332), [`romik_exists`](../../MovingSofaOptimality/External/Romik.lean#L387), [`romik_unique`](../../MovingSofaOptimality/External/Romik.lean#L393),
[`rom_angles_mem`](../../MovingSofaOptimality/External/Romik.lean#L405), [`romik_bounds`](../../MovingSofaOptimality/External/Romik.lean#L577), [`definition8_1_2_exists`](../../MovingSofaOptimality/Main.lean#L24), [`definition8_1_2_unique`](../../MovingSofaOptimality/Main.lean#L28).*

*Proof sketch.* By Proposition 10.7, $(\varphi, \theta) \mapsto P(\varphi, \theta)$ is a bijection from
the zeros of $H$ in the box onto the solutions in the box, so it suffices to show that $H$ has
exactly one zero in the box, near $z_0 = (0.0391773648, 0.6813015094)$. Let $M$ be the rational
matrix with rows $(-0.1481, -0.2886)$ and $(-2.7218, 0.6267)$, a four-digit approximation of the
inverse of the Jacobian of $H$ at its zero, and let $G(z) = z - M H(z)$ be the Newton-type map.
As $M$ is invertible, the zeros of $H$ are the fixed points of $G$.

1. *Uniqueness.* Interval arithmetic on the whole box gives
   $\lvert \partial G_1/\partial\varphi \rvert \le 0.03$, $\lvert \partial G_1/\partial\theta \rvert \le 0.012$,
   $\lvert \partial G_2/\partial\varphi \rvert \le 0.3$ and $\lvert \partial G_2/\partial\theta \rvert \le 0.16$.
   By the mean value theorem along the two coordinates, $G$ is a $\frac12$-contraction of the box in
   the maximum norm ($0.03 + 0.012 \le \frac12$ and $0.3 + 0.16 \le \frac12$). Two fixed points $z$,
   $z'$ in the box then satisfy $\lVert z - z' \rVert \le \frac12 \lVert z - z' \rVert$, so $z = z'$.
2. *Existence.* At $z_0$, interval arithmetic gives
   $G(z_0) - z_0 \in [-9.9160, -9.9155] \cdot 10^{-12} \times [-1.72761, -1.72726] \cdot 10^{-11}$.
   For $z$ in the square $T$ of radius $r = 10^{-10}$ about $z_0$, the contraction gives
   $\lvert G(z)_1 - z_{0,1} \rvert \le 0.042\, r + 0.0992\, r < r$ and
   $\lvert G(z)_2 - z_{0,2} \rvert \le 0.46\, r + 0.1728\, r < r$, so $G$ maps $T$ to itself, and
   Banach's fixed point theorem on the complete set $T$ gives a fixed point there
   ([Figure B.3](appendix-b.md)).
3. *Enclosures.* On $T$, interval arithmetic encloses $a_1, b_1, b_2, c_1$ and the points
   $\kappa_i$, as functions of $\varphi$, $\theta$, their cosines and sines, and $\pi$.

[Appendix B](appendix-b.md) explains how each bound is proved. $\square$

| Parameter | Value | Parameter | Value |
| --- | --- | --- | --- |
| $\varphi$ | $0.039177364790$ | $\kappa_1$ | $(-0.21032242207, \frac14)$ |
| $\theta$ | $0.68130150938$ | $\kappa_2$ | $(-0.91917929277, 0.47240661975)$ |
| $a_1 = e_1$ | $1.21032242207$ | $\kappa_3$ | $(-0.61376322943, 0.88962647900)$ |
| $b_1$ | $-0.52762459803$ | $\kappa_4$ | $(-0.30834716609, 0.47240661975)$ |
| $b_2$ | $0.92025838516$ | $\kappa_5$ | $(-1.01720403679, \frac14)$ |
| $c_1$ | $0.62604552285$ | $c_2 = c_1 - \frac\pi2$ | $-0.94475080395$ |
| $d_1 = \frac\pi4 - b_1$ | $1.31302276142$ | $d_2$ | $-0.52538267041$ |

*Table 10.2.* The parameters of Gerver's sofa, recomputed in 40-digit arithmetic and rounded; also
$a_2 = -\frac14$ and $e_2 = \frac14$. The structure [`GerverParams.Bounds`](../../MovingSofaOptimality/Gerver/Bounds.lean#L23) keeps enclosures of width
about $2 \cdot 10^{-7}$ around these values, which are what the numerical verifications of
§§10.4–10.6 use ([`romik_bounds`](../../MovingSofaOptimality/External/Romik.lean#L577)).

Romik solves the equations numerically and states without proof that the solution with
$0 < \varphi < \theta < \pi/4$ is unique; the paper relies on this uniqueness in its Definition 8.1.2
(REPORT.md, Section 2). The formalization proves uniqueness in the box, which is all that the
definition of $G$ needs, and states the theorems about $G$ for the solutions in the box.
Figure 10.3 shows the zero sets of $H_1$ and $H_2$ in the box.

![A square box with phi from 0.039 to 0.04 on the horizontal axis and theta from 0.68 to 0.69 on the vertical axis, drawn with different scales; the green arc where H1 = 0 runs from the left side down to the bottom side, the purple arc where H2 = 0 runs steeply from the bottom to the top side, and they cross once, near the lower left corner, at the orange point (phi, theta)](figures/10-gerver/box.svg)

*Figure 10.3.* The box of the parameters, with the zero sets of $H_1$ (green) and $H_2$ (purple).
They cross once in the box, at Romik's solution $(\varphi, \theta) = (0.03918, 0.68130)$
(orange); Theorem 10.8 proves this crossing to be the only zero of $H$ in the box.

## 10.4 The cap of Gerver's sofa

From now on the parameters solve Romik's equations and lie in the box. The convex body that will be
the cap of $G$ is defined by its support function, read off the rotation path.

### Definition 10.9 (the cap $K_G$)

For $\sigma \in [0, \pi]$ let $h(\sigma) = \langle \mathbf{x}(\sigma), u_\sigma \rangle + 1$ if
$\sigma \le \pi/2$ and $h(\sigma) = \langle \mathbf{x}(\sigma - \frac\pi2), v_{\sigma - \pi/2} \rangle + 1$
if $\sigma > \pi/2$, and

```math
K_G = \lbrace p : p_y \ge 0 \rbrace \cap \bigcap_{\sigma \in [0, \pi]} \lbrace p : \langle p, u_\sigma \rangle \le h(\sigma) \rbrace .
```

*Lean: [`gs_H`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L138), [`gs_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L144).*

### Lemma 10.10 (the cap $K_G$)

1. For all $\tau \in [0, \pi/2]$ and $\sigma \in [0, \pi]$,
   $\langle \mathbf{A}(\tau), u_\sigma \rangle \le h(\sigma)$ and
   $\langle \mathbf{C}(\tau), u_\sigma \rangle \le h(\sigma)$, with equality for $\mathbf{A}$ at
   $\tau = \sigma \le \pi/2$ and for $\mathbf{C}$ at $\tau = \sigma - \pi/2 \ge 0$.
2. $K_G$ is a cap with rotation angle $\pi/2$, its support function is $h$ on $[0, \pi]$, and its
   inner corner is $\mathbf{x}_{K_G}(t) = \mathbf{x}(t)$ for $t \in [0, \pi/2]$.
3. Every point $\mathbf{x}(s)$, $s \in [0, \pi/2]$, with $\mathbf{x}(s)_y \ge 0$ lies in $K_G$.

*Lean: [`gs_A_le_H`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L222), [`gs_C_le_H`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L246), [`gs_H_eq_A`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L146), [`gs_H_eq_C`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L155), [`gs_isCap_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L440), [`gs_supp_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L421),
[`gs_innerCorner_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L476), [`gs_path_mem_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L484).*

*Proof.* (1) For $\sigma \le \pi/2$, $\langle \mathbf{A}(\sigma), u_\sigma \rangle = \langle \mathbf{x}(\sigma), u_\sigma \rangle + 1 = h(\sigma)$,
and by Lemma 10.5 the function $\tau \mapsto \langle \mathbf{A}(\tau), u_\sigma \rangle$ has right
derivative $\rho_A(\tau) \langle v_\tau, u_\sigma \rangle = \rho_A(\tau) \sin(\sigma - \tau)$. As
$\rho_A \ge 0$ (Lemma 10.6), it increases up to $\tau = \sigma$ and decreases after, so its maximum is
$h(\sigma)$. For $\sigma > \pi/2$ it increases on all of $[0, \pi/2]$; the top edge from
$\mathbf{A}(\frac\pi2) = (\mathbf{x}(\frac\pi2)_x + 2a_1 - 1, 1)$ to $\mathbf{C}(0) = (1 - 2a_1, 1)$
is horizontal and points left, so $\langle \cdot, u_\sigma \rangle$ increases along it as
$\cos\sigma \le 0$; and $\tau \mapsto \langle \mathbf{C}(\tau), u_\sigma \rangle$, with right derivative
$-\rho_C(\tau) \cos(\tau - \sigma)$, increases up to $\tau = \sigma - \pi/2$, where it equals
$h(\sigma)$. The bounds for $\mathbf{C}$ are the same argument run backwards.

(2) $K_G$ is closed and convex, and bounded since $0 \le p_y \le h(\frac\pi2) = 1$ and $p_x$ is
bounded by $h(0)$ and $h(\pi)$. By (1) the points $\mathbf{A}(\tau)$, $\mathbf{C}(\tau)$ lie in $K_G$ and
attain $h(\sigma)$ in every direction $\sigma \in [0, \pi]$, so $h_{K_G} = h$ there; and
$h_{K_G}(\frac{3\pi}2) = 0$ as $\mathbf{A}(0) = (1, 0)$. So $K_G$ is the intersection of the
half-planes of a cap of rotation angle $\pi/2$, with normal angles in
$[0, \pi] \cup \lbrace 3\pi/2 \rbrace$ (Baek's Definition 2.4.1, [Chapter 3](03-monotone.md)). The
inner corner of a cap is $\mathbf{x}_K(t) = (h_K(t) - 1)\, u_t + (h_K(t + \frac\pi2) - 1)\, v_t$
(Baek's Proposition 2.2.2), and here $h(t) - 1 = \langle \mathbf{x}(t), u_t \rangle$ and
$h(t + \frac\pi2) - 1 = \langle \mathbf{x}(t), v_t \rangle$.

(3) On $[0, \pi/2]$ the abscissa of $\mathbf{x}$ has derivative $\alpha \cos t - \beta \sin t < 0$
(Lemma 10.6), so it decreases from $0$ to $\mathbf{x}(\frac\pi2)_x = -1.2275$; and
$\mathbf{x}(s)_y \le 1$ phase by phase. So $\mathbf{x}(s)$ lies in the rectangle
$[1 - 2a_1, \mathbf{x}(\frac\pi2)_x + 2a_1 - 1] \times [0, 1]$, whose upper corners $\mathbf{C}(0)$,
$\mathbf{A}(\frac\pi2)$ and lower corners lie in the convex set $K_G$. $\square$

### Theorem 10.11 (the structure of Gerver's sofa; Baek, Theorem 8.4.1 (1), (3), (4))

Gerver's sofa $G$ is a monotone sofa with rotation angle $\pi/2$, its cap is $K = K_G$, and
$G = K \setminus \mathcal{N}(K)$. Moreover:

1. $A_K(t) = \mathbf{A}(t)$, $C_K(t) = \mathbf{C}(t)$ and $\mathbf{x}_K(t) = \mathbf{x}(t)$ for
   $t \in [0, \pi/2]$;
3. the inner wall $\vec b_K(t)$ passes through $\mathbf{B}(t)$ for $t \in [t_3, t_5]$, and
   $\vec d_K(t)$ through $\mathbf{D}(t)$ for $t \in [t_0, t_2]$;
4. $\mathbf{B}'(t)$ is a negative multiple of $v_t$ for $t \in (t_3, t_5)$, $t \ne t_4$, and
   $\mathbf{D}'(t)$ a positive multiple of $u_t$ for $t \in (t_0, t_2)$, $t \ne t_1$.

*Lean: [`theorem8_4_1_monotone`](../../MovingSofaOptimality/Gerver/Properties.lean#L74), [`theorem8_4_1_walls`](../../MovingSofaOptimality/Gerver/Properties.lean#L99), [`theorem8_4_1_tangents`](../../MovingSofaOptimality/Gerver/Properties.lean#L108), [`gv_monotone`](../../MovingSofaOptimality/Gerver/Structure.lean#L34),
[`gv_walls`](../../MovingSofaOptimality/Gerver/Structure.lean#L46), [`gv_tangents`](../../MovingSofaOptimality/Gerver/Structure.lean#L64), [`gs_monotone_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L579), [`gs_gerverSofa_eq`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L530), [`gs_niche_subset`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L507), [`gs_vminus_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L665),
[`gs_vplus_K'`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L699).*

Baek's paper states Theorem 8.4.1 without proof; its Remark 8.4.1 notes that the properties are
easy to verify numerically and are assumed in the earlier literature (REPORT.md, E23). Part (2), the
niche, is Theorem 10.19. In (4) the curves $\mathbf{B}$ and $\mathbf{D}$ have corners at $t_4$ and
$t_1$, where $\rho_A$ and $\rho_C$ jump, and the statement is made on the open phases. Figure 10.4
shows the cap with its supporting hallway at a time of phase 2.

![The cap K of Gerver's sofa, a blue-outlined region with a flat bottom on the x-axis, with its niche shaded orange, inside the grey supporting hallway at a time t of phase 2, turned by t: the outer wall c(t) touches the cap at C(t) on its left shoulder, the outer wall a(t) at A(t) on its right shoulder, the inner wall d(t) passes through D(t) at the left foot of the niche, and the inner corner x(t) lies on the arch of the niche, from where the inner wall b(t) runs down to the right](figures/10-gerver/cap.svg)

*Figure 10.4.* The cap $K$ (blue outline), its niche (orange), and the supporting hallway
$L_K(t) = \mathbf{x}(t) + R_t L$ at $t = 0.3$, in phase 2. The outer walls touch $K$ at the vertices
$\mathbf{A}(t)$ and $\mathbf{C}(t)$, the inner corner is $\mathbf{x}(t)$, and the inner wall
$\vec d(t)$ passes through $\mathbf{D}(t)$ on the boundary of the niche: the four contact points of
phase 2.

*Proof.* *The sofa.* By Lemma 10.10 (2) and Baek's Proposition 2.2.2, the supporting hallway of $K_G$
at $t \in [0, \pi/2]$ is $L_{K_G}(t) = \mathbf{x}(t) + R_t L = Q^+_{K_G}(t) \setminus Q^-_{K_G}(t)$.
A point $p$ with $p_y \ge 0$ lies in every $Q^+_{K_G}(t)$, $t \in [0, \pi/2]$, exactly when it lies
in $K_G$, since the half-planes of these quarter-planes are those of $K_G$ with normals in
$[0, \pi]$. A point of $K_G$ lies in $H_L$ and in $\mathbf{x}(\pi/2) + R_{\pi/2} V_L$, and not in
$Q^-_{K_G}(0)$ or $Q^-_{K_G}(\pi/2)$, which lie below the $x$-axis because $\mathbf{x}(0)$ and
$\mathbf{x}(\pi/2)$ lie on it. Unwinding Definition 10.1, $G$ is therefore the set of points of
$K_G$ in no quadrant $Q^-_{K_G}(t)$, $t \in (0, \pi/2)$, that is,
$G = K_G \setminus \mathcal{N}(K_G)$, as the fan $F_{\pi/2}$ is the upper half-plane. For
$t \in (0, \pi/2)$ the inner corner $\mathbf{x}(t)$ either lies below the $x$-axis or lies in $K_G$
(Lemma 10.10 (3)), so $K_G$ contains its niche by Baek's Theorem 2.5.8, (3) ⇒ (1); a cap that
contains its niche is the cap of the monotone sofa $K_G \setminus \mathcal{N}(K_G)$ (Theorems 2.5.9
and 2.4.3, [Chapter 3](03-monotone.md)). This is $G$.

(1) For $\sigma \le \pi/2$, $h_K(\sigma) = \langle \mathbf{A}(\sigma), u_\sigma \rangle$, whose
derivative is $\langle \mathbf{A}(\sigma), v_\sigma \rangle$ because $\mathbf{A}'$ is parallel to
$v_\sigma$. The left derivative of a support function at $t$ is $\langle v_K^-(t), v_t \rangle$, and
$v_K^-(t)$ also has the component $h_K(t)$ along $u_t$, like $\mathbf{A}(t)$; so
$A_K(t) = v_K^-(t) = \mathbf{A}(t)$ for $t \in [0, \pi/2]$. In the same way, with right derivatives,
$C_K(t) = v_K^+(t + \frac\pi2) = \mathbf{C}(t)$. The inner corner is Lemma 10.10 (2).

(3) In hallway coordinates $\mathbf{B}(t) = (0, \alpha(t))$ and $\mathbf{D}(t) = (-\beta(t), 0)$, with
$\alpha \le 0 \le \beta$ (Lemma 10.6): the points lie on the half-lines $\vec b_K(t)$ and
$\vec d_K(t)$.

(4) By Lemma 10.5, $\mathbf{B}' = (\rho_A - 1)\, v_t$ and $\mathbf{D}' = (1 - \rho_C)\, u_t$ on the
open phases, and $\rho_A < 1$ on $[t_3, t_5]$, $\rho_C < 1$ on $[t_0, t_2]$ (Lemma 10.6). $\square$

### Theorem 10.12 (Romik's balancing equations; Baek, Theorem 8.4.2)

On the open phases, the contact curves satisfy:

| Phase | Equations |
| --- | --- |
| 1 | $\langle \mathbf{A}', v_t \rangle = 0$, $\ \langle -\mathbf{C}', u_t \rangle = \langle \mathbf{D}', u_t \rangle$ |
| 2 | $\langle \mathbf{A}', v_t \rangle = \langle \mathbf{x}', v_t \rangle$, $\ \langle -\mathbf{C}', u_t \rangle = \langle \mathbf{D}' - \mathbf{x}', u_t \rangle$ |
| 3 | $\langle \mathbf{A}', v_t \rangle = \langle \mathbf{x}', v_t \rangle$, $\ \langle -\mathbf{C}', u_t \rangle = \langle -\mathbf{x}', u_t \rangle$ |
| 4 | $\langle \mathbf{A}', v_t \rangle = \langle -\mathbf{B}' + \mathbf{x}', v_t \rangle$, $\ \langle -\mathbf{C}', u_t \rangle = \langle -\mathbf{x}', u_t \rangle$ |
| 5 | $\langle \mathbf{A}', v_t \rangle = \langle -\mathbf{B}', v_t \rangle$, $\ \langle -\mathbf{C}', u_t \rangle = 0$ |

*Lean: [`theorem8_4_2`](../../MovingSofaOptimality/Gerver/Properties.lean#L118), [`gv_odes`](../../MovingSofaOptimality/Gerver/Structure.lean#L90).*

Each equation balances the differential side lengths at the contact points of the phase: the first
of each pair on the walls $a(t)$, $b(t)$ with normal $u_t$, the second on the walls $c(t)$, $d(t)$
with normal $v_t$. Romik derived them as the conditions of local optimality, and the paper cites
Romik's proof; here they are checked on the explicit solution.

*Proof.* By Lemma 10.5, $\langle \mathbf{A}', v_t \rangle = \rho_A$,
$\langle -\mathbf{B}', v_t \rangle = 1 - \rho_A$, $\langle -\mathbf{C}', u_t \rangle = \rho_C$,
$\langle \mathbf{D}', u_t \rangle = 1 - \rho_C$, $\langle \mathbf{x}', u_t \rangle = \alpha$ and
$\langle \mathbf{x}', v_t \rangle = \beta$. The ten equations become: on phase 1, $\rho_A = 0$ and
$\rho_C = 1 - \rho_C$; on phase 2, $\rho_A = \beta$ and $\rho_C = 1 - \rho_C - \alpha$; on phase 3,
$\rho_A = \beta$ and $\rho_C = -\alpha$; on phase 4, $\rho_A = 1 - \rho_A + \beta$ and
$\rho_C = -\alpha$; on phase 5, $\rho_A = 1 - \rho_A$ and $\rho_C = 0$. Each is read off Table 10.1;
for instance on phase 2, $1 - (\frac t2 - b_1) - (2b_1 + 1 - t) = \frac t2 - b_1$, and on phase 4,
with $s = \frac\pi2 - t$, $1 - (\frac s2 - b_1) + (s - 2b_1 - 1) = \frac s2 - b_1$. $\square$

### Theorem 10.13 (injectivity; Baek, Theorem 6.1.2)

The cap $K$ of Gerver's sofa satisfies the injectivity condition
([Chapter 7](07-injectivity.md)): $\sigma_K = \rho_A(t)\, dt$ on $[0, \pi/2)$ and
$\sigma_K = \rho_C(t - \frac\pi2)\, dt$ on $(\pi/2, \pi]$, with $\rho_A, \rho_C \ge 0$; the inner
corner $\mathbf{x}_K$ is continuously differentiable on $[0, \pi/2]$; and
$\langle \mathbf{x}_K'(t), u_t \rangle < 0 < \langle \mathbf{x}_K'(t), v_t \rangle$ for
$t \in (0, \pi/2)$.

*Lean: [`theorem6_1_2`](../../MovingSofaOptimality/Gerver/Properties.lean#L140), [`gv_injectivity`](../../MovingSofaOptimality/Gerver/Structure.lean#L143), [`gs_InjCond1`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L1058), [`gs_InjCond2`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L745), [`gs_InjCond3`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L748).*

The paper derives this theorem from Gerver's Theorem 2, read as constructing maximum polygon sofas
that converge to $G$; Gerver's theorem does not say this, and the proof is invalid as written
(REPORT.md, E12). The statement is true, and the formalization proves it from Romik's equations, as
the paper's Remark 6.1.1 suggests.

*Proof.* By Theorem 10.11 (1), $\mathbf{x}_K = \mathbf{x}$, which is continuously differentiable, with
$\langle \mathbf{x}', u_t \rangle = \alpha < 0 < \beta = \langle \mathbf{x}', v_t \rangle$ on
$(0, \pi/2)$ (Lemma 10.6). The surface area measure $\sigma_K$ is the Lebesgue–Stieltjes measure of
$F(t) = \langle v_K^+(t), v_t \rangle + \int_0^t h_K$ ([Chapter 6](06-surface-area.md)). On
$[0, \pi/2)$, $v_K^+ = \mathbf{A}$ and $h_K(t) = \langle \mathbf{A}(t), u_t \rangle$, so
$F' = \langle \mathbf{A}', v_t \rangle - \langle \mathbf{A}, u_t \rangle + h_K = \rho_A$ off the
phase boundaries, and $F$ is continuous there; there is no atom at $0$, where
$v_K^-(0) = v_K^+(0) = \mathbf{A}(0)$. On $(\pi/2, \pi]$ the same computation with
$v_K^+(t) = \mathbf{C}(t - \frac\pi2)$ gives $\rho_C(t - \frac\pi2)$. $\square$

## 10.5 The niche of Gerver's sofa

The niche of $K$ is $\mathcal{N}(K) = F_{\pi/2} \cap \bigcup_{s \in (0, \pi/2)} Q^-_K(s)$, where the
fan $F_{\pi/2}$ is the closed upper half-plane. Since $L_K(s) = \mathbf{x}(s) + R_s L$
(Theorem 10.11), the quadrant $Q^-_K(s)$ is

```math
Q^-(s) = \lbrace q : f_s(q) < 0,\ g_s(q) < 0 \rbrace , \qquad f_s(q) = \langle q - \mathbf{x}(s), u_s \rangle , \quad g_s(q) = \langle q - \mathbf{x}(s), v_s \rangle ,
```

the open quarter-plane between the inner walls $\vec b(s)$ and $\vec d(s)$, below the inner corner.
The niche is the union of these quarter-planes over $s \in (0, \pi/2)$, cut at the $x$-axis
([`gn_niche_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L93)).

### Definition 10.14 (the curve $\Gamma$)

Let $\Gamma = \mathbf{B}([t_3, t_5]) \cup \mathbf{x}([t_1, t_4]) \cup \mathbf{D}([t_0, t_2])$, and let
$R$ be the set of points $q$ with $q_y \ge 0$ that lie strictly below a point of $\Gamma$: some
$\gamma \in \Gamma$ has $\gamma_x = q_x$ and $q_y < \gamma_y$.

*Lean: [`envCurve`](../../MovingSofaOptimality/Gerver/Envelope.lean#L82), [`envUnderStrict`](../../MovingSofaOptimality/Gerver/Envelope.lean#L89), [`envUnder`](../../MovingSofaOptimality/Gerver/Envelope.lean#L86), [`envQuad`](../../MovingSofaOptimality/Gerver/Envelope.lean#L69), [`envNiche`](../../MovingSofaOptimality/Gerver/Envelope.lean#L73).*

The proof that $\mathcal{N}(K) = R$ must show that no point of $\Gamma$ lies in any quadrant
$Q^-(s)$: a family of inequalities in two parameters, the time $s$ of the quadrant and the time
$\tau$ of the point of $\Gamma$. Their margins are small: at $s = \pi/4$ the point
$\mathbf{x}(\varphi)$ is only $f_{\pi/4}(\mathbf{x}(\varphi)) = 0.00124$ away from the inner wall
$b(\pi/4)$, as Gerver observed (Baek's Remark 8.4.1). The proof reduces the family to inequalities in
one variable: for a fixed $s$, a monotonicity in $\tau$ reduces each inequality to its value at one
end, which depends on $s$ alone.

### Lemma 10.15 (Principle P)

If $\langle p - \mathbf{x}(s), u_\sigma \rangle \ge 0$ for some $\sigma \in [s, s + \pi/2]$, then
$p \notin Q^-(s)$.

*Lean: [`env_not_mem_of_dot`](../../MovingSofaOptimality/Gerver/Envelope.lean#L179).*

![A point x(s) with the directions u_s and v_s drawn as arrows. Below it, between the two inner walls, the orange quadrant Q-minus of s. A green arrow u_sigma between u_s and v_s, a dashed line through x(s) perpendicular to it, and beyond that line the green half-plane of the points p with p minus x(s) dotted with u_sigma at least zero, which contains a point p and does not meet the orange quadrant](figures/10-gerver/principle.svg)

*Figure 10.5.* Principle P. The quadrant $Q^-(s)$ (orange) is where both $f_s$ and $g_s$ are
negative. For $\sigma$ between $s$ and $s + \pi/2$ the direction $u_\sigma$ is a nonnegative
combination of $u_s$ and $v_s$, so the half-plane $\langle p - \mathbf{x}(s), u_\sigma \rangle \ge 0$
(green) misses the quadrant. The witnesses used below are $\sigma = s$ (the line $b(s)$),
$\sigma = s + \pi/2$ (the line $d(s)$), $\sigma = t_3$ and $\sigma = t_2 + \pi/2$.

*Proof.* (Figure 10.5.) $u_\sigma = \cos(\sigma - s)\, u_s + \sin(\sigma - s)\, v_s$ with both
coefficients nonnegative and not both zero, so $\langle p - \mathbf{x}(s), u_\sigma \rangle < 0$ whenever
$f_s(p) < 0$ and $g_s(p) < 0$. $\square$

### Lemma 10.16 (the one-variable facts)

Let $s_A = 0.62$ and $s_C = 0.95$, so that $t_1 \le s_A \le t_3$ and $t_2 \le s_C \le t_4$. Then:

1. $\alpha < 0 < \beta$ on $(0, \pi/2)$, and $\lvert\alpha\rvert / \beta$ is nondecreasing there;
2. $\rho_A \le 1$ on $[s_A, \pi/2]$, and $\rho_C \le 1$ on $[0, s_C]$;
3. $I(s) = \langle \mathbf{x}(t_1) - \mathbf{x}(s), u_s \rangle \ge 0$ for $s \in [t_1, s_A]$, and
   $J(s) = \langle \mathbf{x}(t_4) - \mathbf{x}(s), v_s \rangle \ge 0$ for $s \in [s_C, t_4]$;
4. $\langle \mathbf{x}(t_1) - \mathbf{x}(s), u_{t_3} \rangle \ge 0$ for $s \in [0, t_1]$, and
   $\langle \mathbf{x}(t_4) - \mathbf{x}(s), v_{t_2} \rangle \ge 0$ for $s \in [t_4, \pi/2]$;
5. $\mathbf{x}(t)_y > 0$ for $t \in [t_1, t_4]$.

*Lean: [`gn_envHyp`](../../MovingSofaOptimality/Gerver/Niche.lean#L57), [`EnvHyp`](../../MovingSofaOptimality/Gerver/Envelope.lean#L94), [`gb_ratio_mono`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L404), [`gb_α_antitoneOn`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L340), [`gb_β_antitoneOn`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L373), [`gb_rhoA_le`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L421),
[`gb_rhoC_le`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L461), [`gb_I_nonneg`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L535), [`gb_I'_nonneg`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L555), [`gb_core`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L145), [`gb_corner_B`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L621), [`gb_corner_D`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L641), [`gb_x_pos`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L695).*

*Proof sketch.* Each fact is checked phase by phase from Table 10.1 and the enclosures of the
parameters; the mirror symmetry halves the work. (1) The signs are Lemma 10.6. By Table 10.1,
$\alpha$ and $\beta$ are both nonincreasing on $[0, \pi/2]$, so $\lvert\alpha\rvert = -\alpha$
increases while $\beta > 0$ decreases. (2) $\rho_A$ is at most $\rho_{A,2}(0.62) = 0.99703$ on
$[0.62, \theta]$, $1 + c_1 - \theta = 0.9447$ on phase 3, $\frac\theta2 - b_1 = 0.8682$ on phase 4
and $\frac12$ on phase 5; $\rho_C$ is the mirror image, with $\rho_C(0.95) = 0.99636$. (3) Both
points lie on phase 2, and with $\sigma = s - \varphi$,

```math
I(s) = \sigma + \tfrac{\sigma^2}4 - W_1\,(1 - \cos\sigma) + W_2\,(\sigma + \sin\sigma) , \qquad W_1 = -\tfrac{\varphi^2}4 + b_1\varphi + b_2 = 0.89920 , \quad W_2 = \tfrac\varphi2 - b_1 - 1 = -0.45279 .
```

The bounds $1 - \cos\sigma \le \frac{\sigma^2}2 - \frac{\sigma^4}{24} + \frac{\sigma^6}{720}$ and
$\sin\sigma \le \sigma - \frac{\sigma^3}6 + \frac{\sigma^5}{120}$ bound $I(s)/\sigma$ below by a
polynomial that is positive on $[0, 0.582]$ (numerically $I(s)/\sigma \ge 0.0108$ there); $J$ is
the mirror image. (4) The derivative of $s \mapsto \langle \mathbf{x}(s), u_{t_3} \rangle$ on phase 1 is
$\alpha_1(s) \sin(\theta + s) + \beta_1(s) \cos(\theta + s) \ge -0.1 + 1.39 \cdot 0.74 > 0$. (5) The
height $\mathbf{x}_y$ increases on $[t_1, \pi/4]$ and decreases on $[\pi/4, t_4]$, and
$\mathbf{x}(t_1)_y = \mathbf{x}(t_4)_y = 0.05519$. The full proofs are in
[`NicheBounds.lean`](../../MovingSofaOptimality/Gerver/NicheBounds.lean). $\square$

### Theorem 10.17 (the niche is the region under $\Gamma$)

$\mathcal{N}(K) = R$, and the points of $\Gamma$ lie in the closure of $\mathcal{N}(K)$ but not in
$\mathcal{N}(K)$ (Figure 10.6).

*Lean: [`env_niche_eq`](../../MovingSofaOptimality/Gerver/Envelope.lean#L842), [`env_niche_subset_strict`](../../MovingSofaOptimality/Gerver/Envelope.lean#L750), [`env_subset_niche`](../../MovingSofaOptimality/Gerver/Envelope.lean#L794), [`env_not_mem`](../../MovingSofaOptimality/Gerver/Envelope.lean#L586),
[`env_not_mem_niche`](../../MovingSofaOptimality/Gerver/Envelope.lean#L600), [`env_mem_closure`](../../MovingSofaOptimality/Gerver/Envelope.lean#L866), [`env_wit_x`](../../MovingSofaOptimality/Gerver/Envelope.lean#L467), [`env_wit_B`](../../MovingSofaOptimality/Gerver/Envelope.lean#L522), [`env_wit_D`](../../MovingSofaOptimality/Gerver/Envelope.lean#L554), [`env_I_nonneg`](../../MovingSofaOptimality/Gerver/Envelope.lean#L438),
[`env_J_nonneg`](../../MovingSofaOptimality/Gerver/Envelope.lean#L453), [`env_min_le`](../../MovingSofaOptimality/Gerver/Envelope.lean#L293), [`env_sign_aux`](../../MovingSofaOptimality/Gerver/Envelope.lean#L315), [`gn_niche_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L93).*

![Close-up of the niche of Gerver's sofa, shaded orange, under the orange arch x and the two green feet D on the left and B on the right; many thin grey segments run from points x(s) of the arch down to the x-axis along the inner walls b(s) and d(s), crossing each other, and one quadrant below a point x(s0) of the arch is shaded darker](figures/10-gerver/niche.svg)

*Figure 10.6.* The niche as the union of the quadrants $Q^-(s)$. Grey segments are the inner walls
$\vec b(s)$ and $\vec d(s)$ from $\mathbf{x}(s)$ down to the $x$-axis, for 27 values of $s$; one
quadrant $Q^-(s_0)$, $s_0 = 0.45$, is shaded darker. The corners trace $\mathbf{x}$ (orange), and the
walls $\vec d(s)$ and $\vec b(s)$ envelope the curves $\mathbf{D}$ and $\mathbf{B}$ (green) at the two
feet.

*Proof.* Write $\varphi_s(r) = f_s(\mathbf{B}(r))$ and $\psi_s(r) = g_s(\mathbf{D}(r))$. Two facts make
$\mathbf{B}$ and $\mathbf{D}$ envelopes: $\varphi_s(s) = 0$ and $\psi_s(s) = 0$ by
Definition 10.2, and off the phase boundaries, by Lemma 10.5,

```math
\varphi_s'(r) = (\rho_A(r) - 1) \sin(s - r) , \qquad \psi_s'(r) = (1 - \rho_C(r)) \sin(r - s) .
```

By Lemma 10.16 (2), $\varphi_s$ decreases on $[s_A, s]$ and increases on $[\max(s, s_A), \pi/2]$, and
$\psi_s$ decreases on $[0, \min(s, s_C)]$ and increases on $[s, s_C]$.

*Step 1: $I \ge 0$ on $[t_1, \pi/2)$ and $J \ge 0$ on $(0, t_4]$.* For $s \le s_A$ this is
Lemma 10.16 (3). For $s \ge s_A$, $I(s) = f_s(\mathbf{x}(t_1)) = \varphi_s(t_3)$ since
$\mathbf{B}(t_3) = \mathbf{x}(t_1)$, and $\varphi_s(t_3) \ge \varphi_s(s) = 0$ by the monotonicity
of $\varphi_s$ on $[s_A, \pi/2]$. $J$ is the mirror image.

*Step 2: no point of $\Gamma$ lies in a quadrant.* Fix $s \in (0, \pi/2)$; in each case below a
witness angle $\sigma \in [s, s + \pi/2]$ and Lemma 10.15 exclude the point from $Q^-(s)$.

- $\mathbf{x}(\tau)$ with $t_1 \le \tau \le s$, with $\sigma = s$: the function
  $F(\tau') = f_s(\mathbf{x}(\tau'))$ on $[t_1, s]$ has derivative
  $F' = \alpha \cos(s - \tau') + \beta \sin(s - \tau')$, which has the sign of
  $\tan(s - \tau') - \lvert\alpha\rvert/\beta$. As $\tau'$ grows the tangent decreases and
  $\lvert\alpha\rvert/\beta$ increases (Lemma 10.16 (1)), so once $F'$ is negative it stays negative,
  and $F$ has no interior point below both of its end values. Hence
  $F(\tau) \ge \min(F(t_1), F(s)) = \min(I(s), 0) = 0$ by Step 1.
- $\mathbf{x}(\tau)$ with $s \le \tau \le t_4$: the mirror argument with $g_s$, $J$ and
  $\sigma = s + \pi/2$.
- $\mathbf{B}(\tau)$, $\tau \in [t_3, \pi/2]$, when $s \ge t_1$, with $\sigma = s$: if $s \le t_3$,
  $\varphi_s(\tau) \ge \varphi_s(t_3) = I(s) \ge 0$; if $s > t_3$, $\varphi_s(\tau) \ge \varphi_s(s) = 0$.
- $\mathbf{B}(\tau)$ when $s < t_1$, with $\sigma = t_3$:
  $\langle \mathbf{B}(\tau) - \mathbf{x}(s), u_{t_3} \rangle = \varphi_{t_3}(\tau) + \langle \mathbf{x}(t_1) - \mathbf{x}(s), u_{t_3} \rangle \ge 0$
  by the monotonicity of $\varphi_{t_3}$ and Lemma 10.16 (4).
- $\mathbf{D}(\tau)$: the mirror arguments, with $\sigma = s + \pi/2$, or $\sigma = t_2 + \pi/2$ when
  $s > t_4$.

*Step 3: $R \subseteq \mathcal{N}(K)$.* If $\gamma = \mathbf{x}(\tau)$, $\mathbf{B}(\tau)$ or
$\mathbf{D}(\tau)$ with $\tau \in (0, \pi/2)$ and $b > 0$, then $\gamma - b\, e_2 \in Q^-(\tau)$: the
point $\gamma$ has $f_\tau(\gamma) \le 0$ and $g_\tau(\gamma) \le 0$, and moving down by $b$ lowers
both by $b \sin\tau > 0$ and $b \cos\tau > 0$. (The ends $\mathbf{B}(\pi/2)$ and $\mathbf{D}(0)$ lie
on the $x$-axis, and no point of $R$ lies below them.)

*Step 4: $\mathcal{N}(K) \subseteq R$.* Let $q \in Q^-(s)$ with $q_y \ge 0$. If
$q_x > \mathbf{B}(\pi/2)_x$, the witness $\sigma \in [s, \pi/2]$ of $\mathbf{B}(\pi/2)$ gives
$\langle q - \mathbf{x}(s), u_\sigma \rangle \ge \langle \mathbf{B}(\pi/2) - \mathbf{x}(s), u_\sigma \rangle \ge 0$,
since both coordinates of $q - \mathbf{B}(\pi/2)$ are nonnegative and so are $\cos\sigma$ and
$\sin\sigma$: impossible by Lemma 10.15. The case $q_x < \mathbf{D}(0)_x$ is the mirror image.
Otherwise the intermediate value theorem gives $\gamma \in \Gamma$ with $\gamma_x = q_x$, and if
$q_y \ge \gamma_y$, the witness $\sigma$ of $\gamma$, which lies in $[0, \pi]$, gives
$\langle q - \mathbf{x}(s), u_\sigma \rangle = \langle \gamma - \mathbf{x}(s), u_\sigma \rangle + (q_y - \gamma_y) \sin\sigma \ge 0$,
again impossible. So $q_y < \gamma_y$ and $q \in R$.

*Step 5: closure.* A point $\gamma$ of $\Gamma$ above the $x$-axis is the limit of the points
$\gamma - b\, e_2 \in R$ as $b \to 0$, and the two ends on the axis are limits of such points.
$\square$

### Lemma 10.18 (the area under a monotone curve)

Let $z : [a, b] \to \mathbb{R}^2$ be continuous, with $z_y \ge 0$ and with a bounded derivative off a
countable set, and let $z_x$ be monotone. The set of points $q$ with $q_y \ge 0$ that lie below
$z$, that is $q_x = z_x(t)$ and $q_y \le z_y(t)$ for some $t \in [a, b]$, and the set of those that lie
strictly below $z$ both have area

```math
\tfrac12 \bigl[z_x z_y\bigr]_a^b - \mathcal{J}(z|_{[a,b]}) \quad (z_x \text{ nondecreasing}), \qquad \mathcal{J}(z|_{[a,b]}) - \tfrac12 \bigl[z_x z_y\bigr]_a^b \quad (z_x \text{ nonincreasing}),
```

where $\mathcal{J}(z) = \frac12 \int z \times dz$ is the curve area functional
([Chapter 8](08-convex-curves.md)).

*Lean: [`env_volume_region_of_monotoneOn`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L420), [`env_volume_region_of_antitoneOn`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L440),
[`env_area_region_of_monotoneOn`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L458), [`env_nullMeasurableSet_region`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L481).*

*Proof sketch.* The map $(t, \lambda) \mapsto (z_x(t), \lambda z_y(t))$ sweeps the region; it has
Jacobian $z_x'(t)\, z_y(t)$ and is injective on the parameters where $z_y > 0$ and $z_x$ takes its
value once. The change of variables formula gives the area $\int_a^b \lvert z_x' \rvert z_y$, since
off those parameters $z_x' = 0$ or $z_y = 0$, and the rest of the region (countably many vertical
lines, the $x$-axis and the curve itself) is null. Integration by parts gives
$\int_a^b z_x' z_y = \frac12 [z_x z_y]_a^b - \mathcal{J}(z|_{[a,b]})$. $\square$

### Theorem 10.19 (the niche; Baek, Theorem 8.4.1 (2))

The curves $\mathbf{B}|_{[t_3, t_5]}$, $\mathbf{x}|_{[t_1, t_4]}$ and $\mathbf{D}|_{[t_0, t_2]}$ lie in
$\overline{\mathcal{N}(K)} \setminus \mathcal{N}(K)$, with $\mathbf{B}(t_3) = \mathbf{x}(t_1)$,
$\mathbf{x}(t_4) = \mathbf{D}(t_2)$, and $\mathbf{D}(t_0)$, $\mathbf{B}(t_5)$ on the $x$-axis; and

```math
\lvert \mathcal{N}(K) \rvert = \mathcal{J}(\mathbf{x}|_{[t_1, t_4]}) - \mathcal{J}(\mathbf{B}|_{[t_3, t_5]}) - \mathcal{J}(\mathbf{D}|_{[t_0, t_2]}) .
```

*Lean: [`theorem8_4_1_niche`](../../MovingSofaOptimality/Gerver/Properties.lean#L85), [`gv_niche`](../../MovingSofaOptimality/Gerver/Niche.lean#L130), [`env_area`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L570), [`env_niche_eq_union`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L560).*

The paper states that the niche is the region enclosed counterclockwise by $\mathbf{B}$ reversed,
$\mathbf{x}|_{[t_1, t_4]}$, $\mathbf{D}$ reversed and the segment of the $x$-axis from
$\mathbf{D}(0)$ to $\mathbf{B}(\pi/2)$, a statement about a Jordan curve, which the formalization does
not use. Theorem 10.19 is what the paper uses from it, and Theorem 10.17 says more: the niche is the
region strictly under these curves (REPORT.md, Section 6).

*Proof.* The first claims are Theorem 10.17 and Lemma 10.6 (4). By Theorem 10.17 the niche is the
union of the regions strictly under $\mathbf{D}|_{[0, t_2]}$, $\mathbf{x}|_{[t_1, t_4]}$ and
$\mathbf{B}|_{[t_3, \pi/2]}$, which meet only on two vertical lines. The abscissa increases along
$\mathbf{D}$ (as $\mathbf{D}' = (1 - \rho_C)\, u_t$ with $\rho_C < 1$) and along $\mathbf{B}$ (as
$\mathbf{B}' = (\rho_A - 1)\, v_t$ with $\rho_A < 1$), and decreases along $\mathbf{x}$ (Lemma 10.10).
Lemma 10.18 gives the three areas, and the boundary terms cancel: $\mathbf{D}(t_2) = \mathbf{x}(t_4)$,
$\mathbf{B}(t_3) = \mathbf{x}(t_1)$, and $\mathbf{D}(0)$, $\mathbf{B}(\pi/2)$ have height $0$. $\square$

By Theorems 10.11 and 10.19, the boundary of $G$ consists of 18 pieces (Figure 10.7): the curve
$\mathbf{A}$ on phases 2 to 5, the top edge from $\mathbf{A}(\pi/2)$ to $\mathbf{C}(0)$, the curve
$\mathbf{C}$ on phases 1 to 4, an edge on the $x$-axis, $\mathbf{D}$ on phases 1 and 2, $\mathbf{x}$ on
phases 4, 3 and 2, $\mathbf{B}$ on phases 4 and 5, and a second edge on the $x$-axis. On phase 1 the
curve $\mathbf{A}$ rests at the corner $(1, 0)$, and on phase 5 the curve $\mathbf{C}$ at the corner
$\mathbf{C}(\pi/2) = (-2.2275, 0)$.

![The boundary of Gerver's sofa drawn in 18 pieces separated by black dots: the right shoulder in blue in four pieces labelled A2, A3, A4, A5, a black top edge, the left shoulder in blue in four pieces C1 to C4, a black bottom edge on the left, the left foot of the niche in green, D1 and D2, the orange arch in three pieces x4, x3, x2, the right foot in green, B4 and B5, and a black bottom edge on the right; the short pieces A5, C1, D1 and B5 are labelled through leader lines, and the corners are labelled A1 at the lower right and C5 at the lower left](figures/10-gerver/pieces.svg)

*Figure 10.7.* The 18 boundary pieces of $G$: the outer curves $\mathbf{A}$, $\mathbf{C}$ (blue),
the inner curves $\mathbf{B}$, $\mathbf{D}$ (green) and the rotation path $\mathbf{x}$ (orange),
indexed by phase, and three edges (black). The four pieces $\mathbf{A}_5$, $\mathbf{C}_1$,
$\mathbf{D}_1$ and $\mathbf{B}_5$ have length $\varphi/2 = 0.0196$, since $\rho_A$ or $\rho_C$ is
$\frac12$ there.

## 10.6 The area of Gerver's sofa

### Proposition 10.20 (the area of the cap)

```math
\lvert K \rvert = \mathcal{J}(\mathbf{A}|_{[0, \pi/2]}) + \mathcal{J}(\mathbf{C}|_{[0, \pi/2]}) + \mathcal{J}(\mathbf{A}(\pi/2), \mathbf{C}(0)) ,
```

where $\mathcal{J}(p, q) = \frac12\, p \times q$ is the curve area functional of the segment from $p$
to $q$.

*Lean: [`gv_cap_area`](../../MovingSofaOptimality/Gerver/Niche.lean#L404), [`gn_K_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L296), [`segArea`](../../MovingSofaOptimality/Convex/CurveArea.lean#L468).*

*Proof.* $K$ is the region between the $x$-axis and the curve made of $\mathbf{A}|_{[0, \pi/2]}$, the
top edge and $\mathbf{C}|_{[0, \pi/2]}$ ([`gn_K_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L296)): a point above the axis and below a point of
$K$ lies in $K$, because the normals $u_\sigma$, $\sigma \in [0, \pi]$, of its other half-planes have
a nonnegative second coordinate; and a point $q$ of $K$ with the abscissa of $\mathbf{A}(t)$,
$t \in (0, \pi/2]$, lies below $\mathbf{A}(t)$ by the support inequality
$\langle q, u_t \rangle \le \langle \mathbf{A}(t), u_t \rangle$, and likewise for $\mathbf{C}$.
Along all three pieces the abscissa decreases, as $\mathbf{A}' = \rho_A v_t$ and
$\mathbf{C}' = -\rho_C u_t$ with $\rho_A, \rho_C \ge 0$. Lemma 10.18 gives the three areas, and the
boundary terms cancel since $\mathbf{A}(0)_y = \mathbf{C}(\pi/2)_y = 0$ and
$\mathbf{A}(\pi/2)_y = \mathbf{C}(0)_y = 1$. $\square$

### Theorem 10.21 (the area of Gerver's sofa)

```math
\lvert G \rvert = \mathcal{J}(\mathbf{A}|_{[0, \pi/2]}) + \mathcal{J}(\mathbf{C}|_{[0, \pi/2]}) + \mathcal{J}(\mathbf{A}(\pi/2), \mathbf{C}(0)) - \mathcal{J}(\mathbf{x}|_{[t_1, t_4]}) + \mathcal{J}(\mathbf{B}|_{[t_3, t_5]}) + \mathcal{J}(\mathbf{D}|_{[t_0, t_2]}) ,
```

and $2.2192 \le \lvert G \rvert \le 2.2199$; in particular $\lvert G \rvert \ge 2.2$.

*Lean: [`Baek.gerver_sofa_area`](../../Challenge.lean#L338), [`gerverSofa_area_mem`](../../MovingSofaOptimality/Main.lean#L307), [`gv_area_mem`](../../MovingSofaOptimality/Gerver/Niche.lean#L529), [`gv_area_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L504),
[`gerverSofa_area`](../../MovingSofaOptimality/Gerver/Properties.lean#L146), [`gv_area`](../../MovingSofaOptimality/Gerver/Niche.lean#L484), [`gerverSofa_volume_ne_top`](../../MovingSofaOptimality/Main.lean#L312).*

| Term | Lean enclosure | Value |
| --- | --- | --- |
| $\mathcal{J}(\mathbf{A}\vert_{[0, \pi/2]})$ | $[0.7201, 0.7202]$ | $0.720164$ |
| $\mathcal{J}(\mathbf{C}\vert_{[0, \pi/2]})$ | $[1.3339, 1.3340]$ | $1.333927$ |
| $\mathcal{J}(\mathbf{A}(\pi/2), \mathbf{C}(0))$ | $[0.8068, 0.8069]$ | $0.806882$ |
| $\mathcal{J}(\mathbf{x}\vert_{[t_1, t_4]})$ | $[0.6013, 0.6015]$ | $0.601395$ |
| $\mathcal{J}(\mathbf{B}\vert_{[t_3, t_5]})$ | $[-0.0031, -0.0030]$ | $-0.003087$ |
| $\mathcal{J}(\mathbf{D}\vert_{[t_0, t_2]})$ | $[-0.0370, -0.0369]$ | $-0.036959$ |
| $\lvert K \rvert$ | | $2.860973$ |
| $\lvert \mathcal{N}(K) \rvert$ | | $0.641441$ |
| $\lvert G \rvert$ | $[2.2192, 2.2199]$ | $2.219532$ |

*Table 10.3.* The six curve areas, their enclosures in
[`AreaBounds.lean`](../../MovingSofaOptimality/Gerver/AreaBounds.lean) ([`ga_curveArea_A_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3135),
[`ga_curveArea_C_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3147), [`ga_segArea_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3180), [`ga_curveArea_x_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3187), [`ga_curveArea_B_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3197),
[`ga_curveArea_D_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3206)), and their values recomputed by quadrature in 25-digit arithmetic.

*Proof.* By Theorem 10.11, $G = K \setminus \mathcal{N}(K)$ with $\mathcal{N}(K) \subseteq K$; the niche
is measurable (it is the union of open quadrants cut by a closed half-plane) and $K$ is compact, so
$\lvert G \rvert = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$. Proposition 10.20 and
Theorem 10.19 give the formula. [Appendix B](appendix-b.md) encloses each term as in Table 10.3, and
adding the enclosures gives $2.2192 \le \lvert G \rvert \le 2.2199$. The Challenge states the bounds
for the Lebesgue measure, `volume (gerverSofa P)`, which is finite since $G \subseteq K$. $\square$

The value is $\lvert G \rvert = 2.21953166887\ldots$, as computed by Gerver and Romik [3, 4]. With
Theorem 10.13, the bound $\lvert K \rvert \ge \lvert G \rvert \ge 2.2$ puts the cap of Gerver's sofa in
the space $\mathcal{K}^\mathrm{i}$ of Baek's Chapter 8 (Theorem 8.1.1 (3), [`theorem8_1_1_gerver`](../../MovingSofaOptimality/Main.lean#L47);
[Chapter 9](09-optimality.md)).

## 10.7 The left and right bodies (Baek, §8.4.3–8.4.4)

[Chapter 9](09-optimality.md) attaches to a cap $K \in \mathcal{K}^\mathrm{i}$ the right and left
bodies $B_K = K \cap \bigcap_{t \in [\varphi, \pi/2]} H^\mathrm{b}_K(t)$ and
$D_K = K \cap \bigcap_{t \in [0, \pi/2 - \varphi]} H^\mathrm{d}_K(t)$, the points
$\mathbf{x}_K^\mathrm{R} = \mathbf{x}_K(\varphi)$ and $\mathbf{x}_K^\mathrm{L} = \mathbf{x}_K(\frac\pi2 - \varphi)$,
the tails $\mathbf{b}_{B} = \mathbf{u}_B^{\pi + \varphi, 3\pi/2}$ and
$\mathbf{d}_{D} = \mathbf{u}_D^{3\pi/2, 3\pi/2 + \pi/2 - \varphi}$ of their boundaries, with ends
$X_B = v_B^+(\pi + \varphi)$ and $Y_D = v_D^-(2\pi - \varphi)$, and the upper bound
$\mathcal{Q}(K, B, D)$. This section identifies these objects for the cap $K$ of Gerver's sofa.

### Theorem 10.22 (left, middle and right parts; Baek, Theorem 8.4.3)

Let $B = B_K$ and $D = D_K$.

1. $\mathbf{D}(t) = v_D^\pm(\frac{3\pi}2 + t)$ for $t \in (t_0, t_2)$, and
   $\mathbf{B}(t) = v_B^\pm(\pi + t)$ for $t \in (t_3, t_5)$.
2. $\mathbf{x}_K^\mathrm{L} = Y_D = \mathbf{D}(t_2)$, and the tail $\mathbf{d}_D$ is the curve
   $\mathbf{D}([t_0, t_2])$; $\mathbf{x}_K^\mathrm{R} = X_B = \mathbf{B}(t_3)$, and the tail
   $\mathbf{b}_B$ is the curve $\mathbf{B}([t_3, t_5])$.
3. $h_K(\frac\pi2 + t) + h_D(\frac{3\pi}2 + t) = 1$ for $t \in [t_0, t_2]$, and
   $h_K(t) + h_B(\pi + t) = 1$ for $t \in [t_3, t_5]$.

*Lean: [`theorem8_4_3_one`](../../MovingSofaOptimality/Gerver/Properties.lean#L1496), [`theorem8_4_3_two`](../../MovingSofaOptimality/Gerver/Properties.lean#L1505), [`theorem8_4_3_three`](../../MovingSofaOptimality/Gerver/Properties.lean#L1518), [`rightBody`](../../MovingSofaOptimality/Optimality/Domain.lean#L635), [`leftBody`](../../MovingSofaOptimality/Optimality/Domain.lean#L638),
[`gm_D_mem_leftBody`](../../MovingSofaOptimality/Gerver/Properties.lean#L986), [`gm_D_edge`](../../MovingSofaOptimality/Gerver/Properties.lean#L1015), [`gm_B_edge`](../../MovingSofaOptimality/Gerver/Properties.lean#L1165), [`gm_tailD`](../../MovingSofaOptimality/Gerver/Properties.lean#L1253), [`gm_tailB`](../../MovingSofaOptimality/Gerver/Properties.lean#L1281), [`lemma8_1_6_left`](../../MovingSofaOptimality/Optimality/Domain.lean#L986).*

Baek's paper writes $\mathbf{x}_K^\mathrm{R} = X_{B_K} = \mathbf{D}(t_3)$ in (2); $\mathbf{B}(t_3)$ is
meant, as $\mathbf{D}$ is defined on $[t_0, t_2]$ only (REPORT.md, E24).

*Proof sketch.* The proof follows the paper; the right body is the mirror image of the left one. By
Theorem 10.19 the curve $\mathbf{D}|_{[t_0, t_2]}$ lies in the closure of the niche, hence in $K$, but
not in the niche. Its end $\mathbf{D}(t_2) = \mathbf{x}(t_4) = \mathbf{x}_K^\mathrm{L}$ lies on the
line $d_K^\mathrm{L} = d_K(\frac\pi2 - \varphi)$, and as $\mathbf{D}'$ is a positive multiple of $u_t$
(Theorem 10.11 (4)), the whole curve lies in the closed half-plane $\breve H_K^\mathrm{L}$ above that
line. For $t \in [0, \frac\pi2 - \varphi)$, a point of $\breve H_K^\mathrm{L}$ outside the half-plane
$H^\mathrm{d}_K(t)$ above $d_K(t)$ lies in $Q^-_K(t)$ (Baek's Lemma 8.1.6 (2)), hence, being above
the axis, in the niche; so the curve lies in every $H^\mathrm{d}_K(t)$, that is, in $D$. At each
$t \in [t_0, t_2]$ the point $\mathbf{D}(t)$ lies on $d_K(t)$ (Theorem 10.11 (3)), which bounds $D$,
so $\mathbf{D}(t)$ lies on the edge $e_D(\frac{3\pi}2 + t)$; since $\mathbf{D}$ is continuous, the
edges at the angles near $\frac{3\pi}2 + t$ shrink to $\mathbf{D}(t)$, which gives (1). Letting $t \to t_2$, the point
$\mathbf{D}(t_2) = \mathbf{x}_K^\mathrm{L}$ lies on the supporting lines of $D$ at
$\frac{3\pi}2 + t_2$ and at $\frac{3\pi}2 + \pi/2 - \varphi$, so $D$ has a corner there and the
vertices at the angles between coincide: (2). For (3), $\mathbf{C}(t)$ and $\mathbf{D}(t)$ lie on
the parallel lines $c_K(t)$ and $d_K(t)$ at distance 1, and they are the vertices of $K$ at
$\frac\pi2 + t$ and of $D$ at $\frac{3\pi}2 + t$. $\square$

For a convex body $C$, let $\breve\sigma_C(X) = \sigma_C(X + \pi)$ and $\breve h_C(t) = h_C(t + \pi)$
(Baek's Definition 8.4.5; [`sigmaBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L88), [`suppBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L91)).

### Proposition 10.23 (the surface area measures; Baek, Proposition 8.4.4)

1. $\sigma_K = \langle \mathbf{A}'(t), v_t \rangle\, dt$ on $[0, \pi/2)$;
2. $\breve\sigma_B = \langle -\mathbf{B}'(t), v_t \rangle\, dt$ on $[t_3, t_5)$;
3. $\sigma_K = \langle -\mathbf{C}'(t - \frac\pi2), u_{t - \pi/2} \rangle\, dt$ on $(\pi/2, \pi]$;
4. $\breve\sigma_D = \langle \mathbf{D}'(t - \frac\pi2), u_{t - \pi/2} \rangle\, dt$ on
   $(\frac\pi2 + t_0, \frac\pi2 + t_2]$.

*Lean: [`proposition8_4_4`](../../MovingSofaOptimality/Gerver/Properties.lean#L1689), [`sigmaBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L88).*

Baek's paper states (4) on $(t_0, t_2]$ with the density $\langle \mathbf{D}'(t), u_t \rangle$. As
$\mathbf{D}(s) = v_D(\frac{3\pi}2 + s)$, the measure $\breve\sigma_D$ lives on
$(\frac\pi2 + t_0, \frac\pi2 + t_2]$, with the shifted density of item (3), which is the form that
Theorems 8.4.5 and 8.5.6 use; as printed, the left side is $\breve\sigma_D$ on $(t_0, t_2]$, which
vanishes (REPORT.md, E25).

*Proof.* Items (1) and (3) are the computation in the proof of Theorem 10.13. For (2), the vertex
$v_B^+(\pi + t) = \mathbf{B}(t)$ on $(t_3, t_5)$ (Theorem 10.22), and
$\mathbf{B}' = (\rho_A - 1)\, v_t = (1 - \rho_A)\, v_{\pi + t}$, so the distribution function of
$\sigma_B$ has derivative $1 - \rho_A = \langle -\mathbf{B}'(t), v_t \rangle$ at $\pi + t$ (Baek's
Theorem 5.2.2, $dv_B^+ = v\, d\sigma_B$; [Chapter 6](06-surface-area.md)); shifting by $\pi$ gives
$\breve\sigma_B$. There is no atom at $t_3$, where the edge of $B$ is a single point. Item (4) is the
same computation for $D$, with $\mathbf{D}' = (1 - \rho_C)\, u_t = (1 - \rho_C)\, v_{3\pi/2 + t}$ at the
angle $\frac{3\pi}2 + t$, shifted by $\pi$ to $\frac\pi2 + t$. $\square$

### Definition 10.24 (the measure $\iota_K$ and the intervals $J_i$; Baek, Definitions 8.4.6 and 8.4.7)

For a cap $K$ with the injectivity condition, $i_K(t) = \langle \mathbf{x}_K'(t), v_t \rangle$ and
$i_K(t + \frac\pi2) = \langle -\mathbf{x}_K'(t), u_t \rangle$ for $t \in (0, \pi/2]$, and
$\iota_K = i_K(t)\, dt$ on $[0, \pi]$. Let $J_i = [t_{i-1}, t_i)$ for $1 \le i \le 5$ and
$J_i = \pi - J_{11 - i}$ for $6 \le i \le 10$; the intervals $J_1, \dots, J_{10}$ and the point
$\lbrace \pi/2 \rbrace$ partition $[0, \pi]$.

*Lean: [`iFun`](../../MovingSofaOptimality/Optimality/Variation.lean#L95), [`iota`](../../MovingSofaOptimality/Optimality/Variation.lean#L101), [`MovingSofaOptimality.GerverParams.jInt`](../../MovingSofaOptimality/Gerver/Properties.lean#L1708).*

### Theorem 10.25 (Romik's equations as measures; Baek, Theorem 8.4.5)

With $B = B_K$ and $D = D_K$:

| Interval | Measure $\sigma_K$ | Interval | Measure $\sigma_K$ |
| --- | --- | --- | --- |
| $J_1$ | $0$ | $J_6$ | $\breve\sigma_D$ |
| $J_2 \cup J_3$ | $\iota_K$ | $J_7$ | $\breve\sigma_D + \iota_K$ |
| $J_4$ | $\breve\sigma_B + \iota_K$ | $J_8 \cup J_9$ | $\iota_K$ |
| $J_5$ | $\breve\sigma_B$ | $J_{10}$ | $0$ |

*Lean: [`theorem8_4_5`](../../MovingSofaOptimality/Gerver/Properties.lean#L1841), [`gm_sigma_restrict_A`](../../MovingSofaOptimality/Gerver/Properties.lean#L1758), [`gm_sigma_restrict_C`](../../MovingSofaOptimality/Gerver/Properties.lean#L1764), [`gm_iota_restrict`](../../MovingSofaOptimality/Gerver/Properties.lean#L1785).*

*Proof.* On $J_i$, $i \le 5$, translate the first equation of phase $i$ of Theorem 10.12 by
Proposition 10.23 (1), (2) and Definition 10.24: on $J_4$, for instance,
$\langle \mathbf{A}', v_t \rangle = \langle -\mathbf{B}', v_t \rangle + \langle \mathbf{x}', v_t \rangle$
says that the density of $\sigma_K$ is that of $\breve\sigma_B$ plus $i_K$. Since
$J_{5 + i} = \frac\pi2 + (t_{i-1}, t_i]$, on $J_{5+i}$ translate the second equation of phase $i$ by
Proposition 10.23 (3), (4) at $t - \frac\pi2$: on $J_7 = (\frac\pi2 + t_1, \frac\pi2 + t_2]$,
$\langle -\mathbf{C}', u \rangle = \langle \mathbf{D}', u \rangle + \langle -\mathbf{x}', u \rangle$ is
$\sigma_K = \breve\sigma_D + \iota_K$. The densities agree off the finitely many phase boundaries,
and none of the measures has an atom on these intervals. $\square$

### Theorem 10.26 (the upper bound is attained; Baek, Theorem 8.4.6)

$\mathcal{A}(K) = \mathcal{Q}(K, B_K, D_K)$.

*Lean: [`theorem8_4_6`](../../MovingSofaOptimality/Gerver/Properties.lean#L2223), [`sofaArea`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L82), [`upperQ`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L458), [`gm_convexCurveArea_B`](../../MovingSofaOptimality/Gerver/Properties.lean#L2142), [`gm_convexCurveArea_D`](../../MovingSofaOptimality/Gerver/Properties.lean#L2172).*

*Proof.* By definition ([Chapter 9](09-optimality.md)),

```math
\mathcal{Q}(K, B, D) = \lvert K \rvert + \mathcal{J}(\mathbf{d}_D) + \mathcal{J}(Y_D, \mathbf{x}_K^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K|_{[\varphi, \pi/2 - \varphi]}) + \mathcal{J}(\mathbf{x}_K^\mathrm{R}, X_B) + \mathcal{J}(\mathbf{b}_B) .
```

By Theorem 10.22 (2), $Y_D = \mathbf{x}_K^\mathrm{L}$ and $X_B = \mathbf{x}_K^\mathrm{R}$, so the two
segment terms vanish, and the curve areas of the tails are $\mathcal{J}(\mathbf{D}|_{[t_0, t_2]})$
and $\mathcal{J}(\mathbf{B}|_{[t_3, t_5]})$. With $\mathbf{x}_K = \mathbf{x}$ (Theorem 10.11),
Theorem 10.19 turns the remaining terms into
$\lvert K \rvert - \lvert \mathcal{N}(K) \rvert = \mathcal{A}(K)$. $\square$
