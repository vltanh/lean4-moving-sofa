# 10. Gerver's sofa

[Contents](README.md) · [← 9. The upper bound and the optimality of Gerver's sofa](09-optimality.md) · [11. Uniqueness I: approximating a maximizing cap →](11-selection.md)

This chapter defines Gerver's sofa $G$ as the formalization does, following Romik [4], and proves
the facts about it that the optimality proof of [Chapter 9](09-optimality.md) and the uniqueness
proof of Chapters [11](11-selection.md) and [12](12-uniqueness.md) use. The rotation path
$\mathbf{x}$ of $G$ is glued from five explicit curves, one for each phase of the motion, and their
22 parameters solve Romik's equations (27)–(44) (§10.1). These equations have exactly one solution
with $\varphi \in [0.039, 0.04]$ and $\theta \in [0.68, 0.69]$, so $G$ is well defined
(Theorem 10.8), and $2.2192 \le \lvert G \rvert \le 2.2199$ (Theorem 10.21). The rest of the chapter
proves Section 8.4 of Baek's paper:

- $G$ is a monotone sofa whose cap $K$ has the vertices $\mathbf{A}(t)$, $\mathbf{C}(t)$ and the
  inner corner $\mathbf{x}(t)$ (Theorem 10.11), and whose niche is the region below the curves
  $\mathbf{D}$, $\mathbf{x}$ and $\mathbf{B}$ (Theorem 10.19). Together these are Baek's
  Theorem 8.4.1, which the paper states without proof.
- Romik's balancing equations hold (Theorem 10.12), and $K$ satisfies the injectivity condition
  (Theorem 10.13).
- The identities of measures and areas that Chapter 9 uses hold (Theorems 10.22 to 10.26).

Everything rests on one computation. On each phase the rotation path is
$\mathbf{x}(t) = R_t\, w(t) + \kappa$ for an explicit curve $w$, so the velocity of $\mathbf{x}$, the
contact curves and their velocities are explicit in the rotating frame $u_t, v_t$ (Lemma 10.5 and
Table 10.1). The geometric statements reduce to the signs of four explicit functions and to a few
inequalities in one variable, which follow from enclosures of the parameters. The numerical work
(existence and uniqueness of the solution, its enclosures, the area bounds) is done by interval
arithmetic, explained in [Appendix B](appendix-b.md). Every formal statement about $G$ is made for
every solution of Romik's equations in the box; by Theorem 10.8 there is exactly one.

## 10.1 Romik's description

### Definition 10.1 (the shape of a rotation path; Romik, Equation (8))

Let $\mathbf{x} : [0, \pi/2] \to \mathbb{R}^2$. The *shape* of the rotation path $\mathbf{x}$ is the set

```math
S_{\mathbf{x}} = H_L \cap \bigcap_{t \in [0, \pi/2]} \bigl(\mathbf{x}(t) + R_t L\bigr) \cap \bigl(\mathbf{x}(\pi/2) + R_{\pi/2} V_L\bigr) .
```

*Lean: [`Baek.shapeOfPath`](../../Challenge.lean#L192), [`MovingSofaOptimality.shapeOfPath`](../../MovingSofaOptimality/Gerver/Defs.lean#L115).*

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

*Lean: [`MovingSofaOptimality.GerverParams.contactA`](../../MovingSofaOptimality/Gerver/Defs.lean#L79), [`MovingSofaOptimality.GerverParams.contactB`](../../MovingSofaOptimality/Gerver/Defs.lean#L82),
[`MovingSofaOptimality.GerverParams.contactC`](../../MovingSofaOptimality/Gerver/Defs.lean#L85), [`MovingSofaOptimality.GerverParams.contactD`](../../MovingSofaOptimality/Gerver/Defs.lean#L88),
[`Baek.GerverParams.contactB`](../../Challenge.lean#L169), [`Baek.GerverParams.contactD`](../../Challenge.lean#L172).*

In hallway coordinates $\mathbf{A}(t) = (1, \alpha(t))$, $\mathbf{B}(t) = (0, \alpha(t))$,
$\mathbf{C}(t) = (-\beta(t), 1)$ and $\mathbf{D}(t) = (-\beta(t), 0)$, so the four points lie on the
lines $a(t)$, $b(t)$, $c(t)$, $d(t)$. They are the points where these lines touch their envelopes.
For instance, $a(t)$ is the line $\langle q - \mathbf{x}(t), u_t \rangle = 1$; the derivative in $t$
of the left side is $-\alpha(t) + \langle q - \mathbf{x}(t), v_t \rangle$, which vanishes on $a(t)$
exactly at $\mathbf{A}(t)$. Romik's derivation rests on this: a sofa that moves along $\mathbf{x}$
and touches the wall $a(t)$ during an interval of times touches it at $\mathbf{A}(t)$.

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

Let $t_0 = 0 < t_1 = \varphi < t_2 = \theta < t_3 = \frac\pi2 - \theta < t_4 = \frac\pi2 - \varphi < t_5 = \frac\pi2$
(Baek's Definition 8.4.1). The rotation path (Romik's Equation (25)) is $\mathbf{x}(t) = \mathbf{x}_i(t)$
on the $i$th phase, where the five phases are $[t_0, t_1)$, $[t_1, t_2)$, $[t_2, t_3]$, $(t_3, t_4]$
and $(t_4, t_5]$. Its contact paths are written $\mathbf{A}, \mathbf{B}, \mathbf{C}, \mathbf{D}$
(Baek's Definitions 8.4.2 and 8.4.3).

*Lean: [`Baek.GerverParams`](../../Challenge.lean#L122), [`MovingSofaOptimality.GerverParams`](../../MovingSofaOptimality/Gerver/Defs.lean#L31), [`MovingSofaOptimality.GerverParams.x₁`](../../MovingSofaOptimality/Gerver/Defs.lean#L55),
[`MovingSofaOptimality.GerverParams.x₂`](../../MovingSofaOptimality/Gerver/Defs.lean#L58), [`MovingSofaOptimality.GerverParams.x₃`](../../MovingSofaOptimality/Gerver/Defs.lean#L61),
[`MovingSofaOptimality.GerverParams.x₄`](../../MovingSofaOptimality/Gerver/Defs.lean#L63), [`MovingSofaOptimality.GerverParams.x₅`](../../MovingSofaOptimality/Gerver/Defs.lean#L66),
[`MovingSofaOptimality.GerverParams.path`](../../MovingSofaOptimality/Gerver/Defs.lean#L70), [`MovingSofaOptimality.GerverParams.tPt`](../../MovingSofaOptimality/Gerver/Properties.lean#L58),
[`MovingSofaOptimality.GerverParams.curveA`](../../MovingSofaOptimality/Gerver/Properties.lean#L70).*

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
[`MovingSofaOptimality.GerverParams.IsSolution`](../../MovingSofaOptimality/Gerver/Defs.lean#L93), [`MovingSofaOptimality.GerverParams.InBox`](../../MovingSofaOptimality/Gerver/Defs.lean#L109),
[`MovingSofaOptimality.gerverSofa`](../../MovingSofaOptimality/Gerver/Defs.lean#L120).*

The Challenge states Definitions 10.1, 10.3 and 10.4, with the contact paths $\mathbf{B}$ and
$\mathbf{D}$ that (43)–(44) use, in Mathlib's vocabulary, in the namespace `Baek` of
[`Challenge.lean`](../../Challenge.lean). They are copied verbatim from
[`ChallengeDefs.lean`](../../ChallengeDefs.lean), and they agree field by field with the library's
definitions in [`Defs.lean`](../../MovingSofaOptimality/Gerver/Defs.lean)
([`Baek.GerverParams.toLib`](../../Solution.lean#L41); [`Baek.gerverSofa_eq_lib`](../../Solution.lean#L54) holds by `rfl`).

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

*Lean: [`gs_Phase`](../../MovingSofaOptimality/Gerver/Frame.lean#L68), [`gs_Phase.hasDerivAt_X`](../../MovingSofaOptimality/Gerver/Frame.lean#L126), [`gs_Phase.A_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L170), [`gs_Phase.contactA_X`](../../MovingSofaOptimality/Gerver/Frame.lean#L188),
[`gs_Phase.hasDerivAt_A`](../../MovingSofaOptimality/Gerver/Frame.lean#L130), [`gs_Phase.hasDerivAt_B`](../../MovingSofaOptimality/Gerver/Frame.lean#L136), [`gs_Phase.hasDerivAt_C`](../../MovingSofaOptimality/Gerver/Frame.lean#L142), [`gs_Phase.hasDerivAt_D`](../../MovingSofaOptimality/Gerver/Frame.lean#L148),
[`rom_hasDerivAt_rot`](../../MovingSofaOptimality/External/Romik.lean#L47).*

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
([`gs_ph1`](../../MovingSofaOptimality/Gerver/Frame.lean#L384) to [`gs_ph5`](../../MovingSofaOptimality/Gerver/Frame.lean#L424), [`gs_α₁_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L942) to [`gs_β₅_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L979), [`gs_ρA₁_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L1062) to [`gs_ρC₅_eq`](../../MovingSofaOptimality/Gerver/Frame.lean#L1088)). On the first phase
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

*Lean: [`gs_contDiff_path`](../../MovingSofaOptimality/Gerver/Frame.lean#L603), [`gs_path_zero`](../../MovingSofaOptimality/Gerver/Frame.lean#L1125), [`gs_path_pi_div_two_snd`](../../MovingSofaOptimality/Gerver/Frame.lean#L1133), [`gs_α_zero`](../../MovingSofaOptimality/Gerver/Frame.lean#L1038), [`gs_α_neg`](../../MovingSofaOptimality/Gerver/Frame.lean#L1012),
[`gs_β_pos`](../../MovingSofaOptimality/Gerver/Frame.lean#L1025), [`gs_β_pi_div_two`](../../MovingSofaOptimality/Gerver/Frame.lean#L1042), [`gs_ρ_nonneg`](../../MovingSofaOptimality/Gerver/Frame.lean#L1104), [`gb_rhoA_lt`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L409), [`gb_rhoC_lt`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L451), [`gs_contactB_t₃`](../../MovingSofaOptimality/Gerver/Frame.lean#L1152),
[`gs_contactD_t₂`](../../MovingSofaOptimality/Gerver/Frame.lean#L1161), [`gs_contactB_pi_div_two_snd`](../../MovingSofaOptimality/Gerver/Frame.lean#L1170), [`gs_contactD_zero_snd`](../../MovingSofaOptimality/Gerver/Frame.lean#L1175).*

*Proof.* (1) The equations (35)–(42) glue the five smooth curves into a continuously differentiable
one. The start equations give $\mathbf{x}(0) = 0$. Adding the second coordinates of the four
continuity equations and using the symmetry equations gives $\mathbf{x}(\pi/2)_y = 0$.

(2), (3) By Table 10.1, the claims on phases 4 and 5 are those on phases 2 and 1 at
$\frac\pi2 - t$, so it suffices to check phases 1 to 3. To five decimals, the enclosures of
Theorem 10.8 give $a_1 = 1.21032$, $b_1 = -0.52762$, $b_2 = 0.92026$ and $c_1 = 0.62605$.

- Phase 1: $\rho_A = 0$ and $\rho_C = \frac12$. The function $\beta$ decreases, so
  $\beta \ge 2a_1 \cos 0.04 - \frac12 \sin 0.04 - 1 > 1.39$. For $0 < t \le \varphi$,
  $1 - \cos t \le \frac{t^2}2$ and $\sin t > t - \frac{t^3}6$ give
  $\alpha(t) < \frac{t^2}4 - 2a_1 (t - \frac{t^3}6) < 0$.
- Phase 2: $\alpha = 2b_1 + 1 - t < 0$. The function $\beta = \rho_A$ decreases on $[0, \theta]$ to
  $\beta(\theta) = 0.94474 > 0$, and $0 < \rho_C = \frac t2 - b_1 < 0.869$.
- Phase 3: $\beta = \rho_A = 1 + c_1 - t$ and $-\alpha = \rho_C = 1 + c_1 + t - \frac\pi2$ both lie
  in $[0.73655, 0.94474]$.

So $\alpha < 0 < \beta$ and $\rho_A, \rho_C \ge 0$ where claimed, $\rho_C < 1$ on $[t_0, t_2]$, and,
by the mirror symmetry, $\rho_A < 1$ on $[t_3, t_5]$. At the ends, $\alpha(0) = \alpha_1(0) = 0$ and
$\beta(\frac\pi2) = -\alpha_1(0) = 0$.

(4) The transition equations say $\mathbf{x}_1(t_1) = \mathbf{B}_4(t_3)$ and
$\mathbf{x}_5(t_4) = \mathbf{D}_2(t_2)$. The path agrees with $\mathbf{x}_1$ at $t_1$ and with
$\mathbf{x}_5$ at $t_4$. Its contact paths agree with those of $\mathbf{x}_4$ at $t_3$ and of
$\mathbf{x}_2$ at $t_2$, because $\mathbf{x}$ and $\mathbf{x}'$ are continuous at the junctions.
Finally $\mathbf{B}(\frac\pi2) = \mathbf{x}(\frac\pi2) + \alpha\, v_{\pi/2}$ and
$\mathbf{D}(0) = \mathbf{x}(0) - \beta\, u_0$ differ from points of the $x$-axis by horizontal
vectors. $\square$

Gerver's four constants
([Definition 13.3](13-bridge.md#definition-133-gervers-system-and-gervers-four-constants)) include
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

*Lean: [`rom_mk`](../../MovingSofaOptimality/External/Romik.lean#L133), [`rom_Hz`](../../MovingSofaOptimality/External/Romik/Fix.lean#L28), [`rom_D_pos`](../../MovingSofaOptimality/External/Romik.lean#L154), [`rom_eq_mk`](../../MovingSofaOptimality/External/Romik.lean#L160), [`rom_Hz_of_solution`](../../MovingSofaOptimality/External/Romik.lean#L339), [`rom_mk_isSolution`](../../MovingSofaOptimality/External/Romik.lean#L268),
[`rom_mk_contact1_iff`](../../MovingSofaOptimality/External/Romik.lean#L239), [`rom_mk_contact2`](../../MovingSofaOptimality/External/Romik.lean#L254), [`rom_H_eq`](../../MovingSofaOptimality/External/Romik.lean#L225).*

*Proof sketch.* (1) $D \ge 1.8923$ on the box, by interval arithmetic ([`rom_D_box`](../../MovingSofaOptimality/External/Romik/Num.lean#L454);
[Figure B.1](appendix-b.md)).

(2) By Lemma 10.5, $\mathbf{x}_i' = R_t(w_i' + J w_i)$ with $J(a, b) = (-b, a)$, and $R_t$ is
injective. So each derivative condition among (35)–(42) equates the frame vectors $(\alpha, \beta)$
of two phases (Table 10.1). At $t_2 = \theta$ the two coordinates read
$2b_1 + 1 - \theta = \frac\pi2 - 1 - c_1 - \theta$ and
$\frac12 - \frac{\theta^2}4 + b_1\theta + b_2 = 1 + c_1 - \theta$, which give $c_1$ and $b_2$ as
displayed. At $t_1 = \varphi$ the first coordinate gives $b_1 = \beta_0 - s\, a_1$. The second,
after substituting $b_1$ and $b_2$, is the linear equation $a_1 D = N$. So $a_1, b_1, b_2, c_1$ are
those of $P(\varphi, \theta)$, and the remaining coefficients follow from (27)–(34). The continuity
conditions at $t_1, \dots, t_4$ then determine $\kappa_2, \dots, \kappa_5$, and with the symmetry
those at $t_3$ and $t_4$ take the displayed form. Substituting all of this into the transition
equation (43) turns it into $U + b_1 V = 0$; multiplied by $D > 0$, this is $H(\varphi, \theta) = 0$.
[`Num.lean`](../../MovingSofaOptimality/External/Romik/Num.lean) writes $H = D\, U + N_b V$ with
$N_b = D\, b_1 = c\,(\varphi - \frac12 - \frac c2) - s\,(\frac s2 - \frac{\varphi^2}4 + K + \frac32)$.

(3) Conversely, $P(\varphi, \theta)$ satisfies (27)–(34) and the continuity and derivative conditions
at $t_1$ and $t_2$ by construction, and (43) because $H = 0$ and $D \ne 0$. The derivative
conditions at $t_3$ and $t_4$, the continuity conditions there, and the second transition equation
(44) follow from these by the left-right symmetry, as Romik says. Each is a polynomial identity in
$\varphi, \theta, c, s, C, S, \pi$ and the coefficients, which Lean checks with `ring` and
`linear_combination`. $\square$

### Theorem 10.8 (Gerver's sofa is well defined; Romik, Section 4)

Romik's equations have exactly one solution in the box. Its angles satisfy

```math
\lvert \varphi - 0.0391773648 \rvert \le 10^{-10} , \qquad \lvert \theta - 0.6813015094 \rvert \le 10^{-10} ,
```

and its other parameters lie in explicit intervals of width at most $1.5 \cdot 10^{-8}$ around the
values of Table 10.2.

*Lean: [`Baek.gerver_params_exists`](../../Challenge.lean#L328), [`Baek.gerver_params_unique`](../../Challenge.lean#L332), [`romik_exists`](../../MovingSofaOptimality/External/Romik.lean#L354), [`romik_unique`](../../MovingSofaOptimality/External/Romik.lean#L360),
[`rom_angles_mem`](../../MovingSofaOptimality/External/Romik.lean#L372), [`romik_bounds`](../../MovingSofaOptimality/External/Romik.lean#L522), [`definition8_1_2_exists`](../../MovingSofaOptimality/Main.lean#L32), [`definition8_1_2_unique`](../../MovingSofaOptimality/Main.lean#L37).*

*Proof sketch.* By Proposition 10.7, $(\varphi, \theta) \mapsto P(\varphi, \theta)$ is a bijection from
the zeros of $H$ in the box onto the solutions in the box. So it suffices to show that $H$ has
exactly one zero in the box, and to locate it. [Appendix B](appendix-b.md) does this by interval
arithmetic, with a Newton-type map. Let $M$ be the matrix with rows $(-0.1481, -0.2886)$ and
$(-2.7218, 0.6267)$, a four-digit approximation of the inverse of the Jacobian of $H$ at its zero,
and let $G(z) = z - M H(z)$. As $M$ is invertible, the zeros of $H$ are the fixed points of $G$.

1. *Uniqueness.* Bounds on the partial derivatives of $G$ make it a $\frac12$-contraction of the box
   in the maximum norm (Lemmas B.3 and B.4). Two fixed points $z$, $z'$ in the box then satisfy
   $\lVert z - z' \rVert \le \frac12 \lVert z - z' \rVert$, so $z = z'$.
2. *Existence.* At $z_0 = (0.0391773648, 0.6813015094)$ both coordinates of $G(z_0) - z_0$ are
   smaller than $2 \cdot 10^{-11}$ in absolute value (Lemma B.5). Let $T$ be the square of radius
   $r = 10^{-10}$ about $z_0$. For $z \in T$,
   $\lVert G(z) - z_0 \rVert \le \lVert G(z) - G(z_0) \rVert + \lVert G(z_0) - z_0 \rVert \le \frac12 r + 0.2\, r < r$,
   so $G$ maps $T$ into itself, and Banach's fixed point theorem on the complete set $T$ gives a
   fixed point there (Theorem B.6).
3. *Enclosures.* On $T$, interval arithmetic encloses $a_1, b_1, b_2, c_1$ and the points
   $\kappa_i$, as functions of $\varphi$, $\theta$, their cosines and sines, and $\pi$
   (Proposition B.7). $\square$

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
$a_2 = -\frac14$ and $e_2 = \frac14$. The structure [`GerverParams.Bounds`](../../MovingSofaOptimality/Gerver/Bounds.lean#L24) keeps enclosures of width
about $2 \cdot 10^{-7}$ around these values, which are what the numerical verifications of
§§10.4–10.6 use ([`romik_bounds`](../../MovingSofaOptimality/External/Romik.lean#L522)).

Romik solves the equations numerically and states without proof that the solution with
$0 < \varphi < \theta < \pi/4$ is unique. The paper relies on this uniqueness when it defines $G$
from "the" solution (its Definition 8.1.2, which notes that $\varphi \in [0.039, 0.040]$; REPORT.md,
Section 2). The formalization proves uniqueness in the box, which is all that the definition of $G$
needs. Figure 10.3 shows the zero sets of $H_1$ and $H_2$ in the box.

![A square box with phi from 0.039 to 0.04 on the horizontal axis and theta from 0.68 to 0.69 on the vertical axis, drawn with different scales; the green arc where H1 = 0 runs from the left side down to the bottom side, the purple arc where H2 = 0 runs steeply from the bottom to the top side, and they cross once, near the lower left corner, at the orange point (phi, theta)](figures/10-gerver/box.svg)

*Figure 10.3.* The box of the parameters, with the zero sets of $H_1$ (green) and $H_2$ (purple).
They cross once in the box, at Romik's solution $(\varphi, \theta) = (0.03918, 0.68130)$
(orange); Theorem 10.8 proves this crossing to be the only zero of $H$ in the box.

## 10.4 The cap of Gerver's sofa

From now on the parameters solve Romik's equations and lie in the box. The cap of $G$ is defined by
its support function, which the rotation path dictates: at time $t$ the outer walls $a(t)$ and
$c(t)$ are the lines $\langle p, u_t \rangle = \langle \mathbf{x}(t), u_t \rangle + 1$ and
$\langle p, v_t \rangle = \langle \mathbf{x}(t), v_t \rangle + 1$, with the normal angles $t$ and
$t + \frac\pi2$.

### Definition 10.9 (the cap $K_G$)

For $\sigma \in [0, \pi]$ let $h(\sigma) = \langle \mathbf{x}(\sigma), u_\sigma \rangle + 1$ if
$\sigma \le \pi/2$ and $h(\sigma) = \langle \mathbf{x}(\sigma - \frac\pi2), v_{\sigma - \pi/2} \rangle + 1$
if $\sigma > \pi/2$, and

```math
K_G = \lbrace p : p_y \ge 0 \rbrace \cap \bigcap_{\sigma \in [0, \pi]} \lbrace p : \langle p, u_\sigma \rangle \le h(\sigma) \rbrace .
```

*Lean: [`gs_H`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L105), [`gs_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L111).*

### Lemma 10.10 (the cap $K_G$)

1. For all $\tau \in [0, \pi/2]$ and $\sigma \in [0, \pi]$,
   $\langle \mathbf{A}(\tau), u_\sigma \rangle \le h(\sigma)$ and
   $\langle \mathbf{C}(\tau), u_\sigma \rangle \le h(\sigma)$, with equality for $\mathbf{A}$ at
   $\tau = \sigma \le \pi/2$ and for $\mathbf{C}$ at $\tau = \sigma - \pi/2 \ge 0$.
2. $K_G$ is a cap with rotation angle $\pi/2$, its support function is $h$ on $[0, \pi]$, and its
   inner corner is $\mathbf{x}_{K_G}(t) = \mathbf{x}(t)$ for $t \in [0, \pi/2]$.
3. Every point $\mathbf{x}(s)$, $s \in [0, \pi/2]$, with $\mathbf{x}(s)_y \ge 0$ lies in $K_G$.

*Lean: [`gs_A_le_H`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L189), [`gs_C_le_H`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L214), [`gs_H_eq_A`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L114), [`gs_H_eq_C`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L125), [`gs_isCap_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L397), [`gs_supp_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L377),
[`gs_innerCorner_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L422), [`gs_path_mem_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L430).*

*Proof.* (1) Let $\sigma \le \pi/2$. By Lemma 10.5, $\tau \mapsto \langle \mathbf{A}(\tau), u_\sigma \rangle$
has the right derivative $\rho_A(\tau) \langle v_\tau, u_\sigma \rangle = \rho_A(\tau) \sin(\sigma - \tau)$.
As $\rho_A \ge 0$ (Lemma 10.6), the function increases up to $\tau = \sigma$ and decreases after, so
its maximum is $\langle \mathbf{A}(\sigma), u_\sigma \rangle = \langle \mathbf{x}(\sigma), u_\sigma \rangle + 1 = h(\sigma)$.
Let $\sigma > \pi/2$. Then $\sin(\sigma - \tau) \ge 0$ for all $\tau \in [0, \pi/2]$, so the function
increases on all of $[0, \pi/2]$. The top edge, from
$\mathbf{A}(\frac\pi2) = (\mathbf{x}(\frac\pi2)_x + 2a_1 - 1, 1)$ to $\mathbf{C}(0) = (1 - 2a_1, 1)$, is
horizontal and points left, so $\langle \cdot, u_\sigma \rangle$ increases along it, as
$\cos\sigma \le 0$. Finally, $\tau \mapsto \langle \mathbf{C}(\tau), u_\sigma \rangle$ has the right
derivative $-\rho_C(\tau) \cos(\tau - \sigma)$, which is nonnegative for $\tau \le \sigma - \frac\pi2$.
So it increases up to $\tau = \sigma - \frac\pi2$, where it equals $h(\sigma)$. This proves the bound
for $\mathbf{A}$; the bound for $\mathbf{C}$ is the same argument run backwards.

(2) $K_G$ is closed and convex. It is bounded: its points have $0 \le p_y \le h(\frac\pi2) = 1$,
$p_x \le h(0) = 1$ and $-p_x \le h(\pi) = 1 - \mathbf{x}(\frac\pi2)_x$. The points $\mathbf{A}(\tau)$
and $\mathbf{C}(\tau)$ lie in $K_G$: they satisfy the inequalities by (1), and they lie above the
$x$-axis, since $\mathbf{A}_y$ increases from $\mathbf{A}(0)_y = 0$ and $\mathbf{C}_y$ decreases to
$\mathbf{C}(\frac\pi2)_y = 0$ (Lemma 10.5, with $\rho_A, \rho_C \ge 0$). By (1) these points attain
$h(\sigma)$ in every direction $\sigma \in [0, \pi]$, so $h_{K_G} = h$ there, and
$h_{K_G}(\frac{3\pi}2) = 0$ is attained at $\mathbf{A}(0) = (1, 0)$. As $h(\frac\pi2) = 1$ and $K_G$
is by definition an intersection of half-planes with normal angles in
$[0, \pi] \cup \lbrace 3\pi/2 \rbrace$, $K_G$ is a cap with rotation angle $\pi/2$
([Definition 3.9](03-monotone.md#definition-39-cap-baek-definitions-241-and-242)). The inner corner of
a cap is $\mathbf{x}_K(t) = (h_K(t) - 1)\, u_t + (h_K(t + \frac\pi2) - 1)\, v_t$
([Proposition 2.19](02-preliminaries.md#proposition-219-the-parts-of-the-supporting-hallway-baek-proposition-222)),
and here $h(t) - 1 = \langle \mathbf{x}(t), u_t \rangle$ and
$h(t + \frac\pi2) - 1 = \langle \mathbf{x}(t), v_t \rangle$.

(3) The abscissa of $\mathbf{x}$ has the derivative $\alpha \cos t - \beta \sin t < 0$ on
$(0, \pi/2)$ (Lemma 10.6), so it decreases from $0$ to $\mathbf{x}(\frac\pi2)_x = -1.2275$. Phase by
phase, $\mathbf{x}(s)_y \le 1$. So $\mathbf{x}(s)$ lies to the left of
$\mathbf{A}(\frac\pi2) = (0.1931, 1)$, to the right of $\mathbf{C}(0) = (-1.4206, 1)$, and not above
them. For $\sigma \le \pi/2$ both coordinates of $u_\sigma$ are nonnegative, so
$\langle \mathbf{x}(s), u_\sigma \rangle \le \langle \mathbf{A}(\frac\pi2), u_\sigma \rangle \le h(\sigma)$
by (1). For $\sigma \ge \pi/2$, $u_\sigma$ has a nonpositive first and a nonnegative second
coordinate, so $\langle \mathbf{x}(s), u_\sigma \rangle \le \langle \mathbf{C}(0), u_\sigma \rangle \le h(\sigma)$.
With $\mathbf{x}(s)_y \ge 0$, this gives $\mathbf{x}(s) \in K_G$. $\square$

### Theorem 10.11 (the structure of Gerver's sofa; Baek, Theorem 8.4.1 (1), (3), (4))

Gerver's sofa $G$ is a monotone sofa with rotation angle $\pi/2$, its cap is $K = K_G$, and
$G = K \setminus \mathcal{N}(K)$. Moreover:

- (1) $A_K(t) = \mathbf{A}(t)$, $C_K(t) = \mathbf{C}(t)$ and $\mathbf{x}_K(t) = \mathbf{x}(t)$ for
  $t \in [0, \pi/2]$;
- (3) the inner wall $\vec b_K(t)$ passes through $\mathbf{B}(t)$ for $t \in [t_3, t_5]$, and
  $\vec d_K(t)$ through $\mathbf{D}(t)$ for $t \in [t_0, t_2]$;
- (4) $\mathbf{B}'(t)$ is a negative multiple of $v_t$ for $t \in [t_3, t_5]$, and $\mathbf{D}'(t)$ a
  positive multiple of $u_t$ for $t \in [t_0, t_2]$: two-sided inside the phases, and one-sided
  within each closed phase $[t_3, t_4]$, $[t_4, t_5]$, $[t_0, t_1]$ and $[t_1, t_2]$.

*Lean: [`theorem8_4_1_monotone`](../../MovingSofaOptimality/Gerver/Properties.lean#L89), [`theorem8_4_1_walls`](../../MovingSofaOptimality/Gerver/Properties.lean#L122), [`theorem8_4_1_tangents`](../../MovingSofaOptimality/Gerver/Properties.lean#L137), [`gv_monotone`](../../MovingSofaOptimality/Gerver/Structure.lean#L34),
[`gv_walls`](../../MovingSofaOptimality/Gerver/Structure.lean#L46), [`gv_tangents`](../../MovingSofaOptimality/Gerver/Structure.lean#L65), [`gv_tangents_Icc`](../../MovingSofaOptimality/Gerver/Structure.lean#L93), [`gs_monotone_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L531), [`gs_gerverSofa_eq`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L477), [`gs_niche_subset`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L453), [`gs_vminus_K`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L564),
[`gs_vplus_K'`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L598).*

Here $A_K = A_K^- = v_K^-$ and $C_K = C_K^+ = v_K^+(\cdot + \frac\pi2)$ are the contacts of the cap
with its outer walls
([Definition 7.21](07-injectivity.md#definition-721-contacts-and-arms-of-a-cap-baek-definition-641)).
Baek's paper states Theorem 8.4.1 without proof; its Remark 8.4.1 notes that the properties are easy
to verify numerically and are assumed in the earlier literature (REPORT.md, E24). Part (2), the
niche, is Theorem 10.19. In (4) the curves $\mathbf{B}$ and $\mathbf{D}$ have corners at $t_4$ and
$t_1$, where $\rho_A$ and $\rho_C$ jump, so there, and at the ends of the phases, the derivatives are
one-sided (REPORT.md, E24). Figure 10.4
shows the cap with its supporting hallway at a time of phase 2.

![The cap K of Gerver's sofa, a blue-outlined region with a flat bottom on the x-axis, with its niche shaded orange, inside the grey supporting hallway at a time t of phase 2, turned by t: the outer wall c(t) touches the cap at C(t) on its left shoulder, the outer wall a(t) at A(t) on its right shoulder, the inner wall d(t) passes through D(t) at the left foot of the niche, and the inner corner x(t) lies on the arch of the niche, from where the inner wall b(t) runs down to the right](figures/10-gerver/cap.svg)

*Figure 10.4.* The cap $K$ (blue outline), its niche (orange), and the supporting hallway
$L_K(t) = \mathbf{x}(t) + R_t L$ at $t = 0.3$, in phase 2. The outer walls touch $K$ at the vertices
$\mathbf{A}(t)$ and $\mathbf{C}(t)$, the inner corner is $\mathbf{x}(t)$, and the inner wall
$\vec d(t)$ passes through $\mathbf{D}(t)$ on the boundary of the niche: the four contact points of
phase 2.

*Proof.* *The sofa.* By Lemma 10.10 (2) and
[Proposition 2.19](02-preliminaries.md#proposition-219-the-parts-of-the-supporting-hallway-baek-proposition-222),
for $t \in [0, \pi/2]$ the supporting hallway of $K_G$ is the hallway of Definition 10.1:
$L_{K_G}(t) = \mathbf{x}(t) + R_t L = Q^+_{K_G}(t) \setminus Q^-_{K_G}(t)$. A point $p$ with
$p_y \ge 0$ lies in every $Q^+_{K_G}(t)$, $t \in [0, \pi/2]$, exactly when it lies in $K_G$, since the
half-planes of these quarter-planes are those of $K_G$ with normal angles in $[0, \pi]$. The
quadrants $Q^-_{K_G}(0)$ and $Q^-_{K_G}(\pi/2)$ lie below the $x$-axis, because $\mathbf{x}(0)$ and
$\mathbf{x}(\pi/2)$ lie on it. By the bounds in the proof of Lemma 10.10 (2), $K_G$ lies in $H_L$ and
in $\mathbf{x}(\pi/2) + R_{\pi/2} V_L$. Unwinding Definition 10.1, $G$ is therefore the set of points
of $K_G$ in no quadrant $Q^-_{K_G}(t)$, $t \in (0, \pi/2)$. As the fan $F_{\pi/2}$ is the upper
half-plane, this set is $K_G \setminus \mathcal{N}(K_G)$
([Definition 3.11](03-monotone.md#definition-311-fan-and-niche-baek-definitions-244-and-245)).

For $t \in (0, \pi/2)$ the inner corner $\mathbf{x}(t)$ either lies below the $x$-axis or lies in
$K_G$ (Lemma 10.10 (3)). So $K_G$ contains its niche
([Theorem 3.25](03-monotone.md#theorem-325-when-the-cap-contains-its-niche-baek-theorem-258),
(3) ⇒ (1)), and it is the cap of a monotone sofa
([Theorem 3.26](03-monotone.md#theorem-326-the-caps-of-monotone-sofas-baek-theorem-259)), which is
$K_G \setminus \mathcal{N}(K_G) = G$
([Theorem 3.13](03-monotone.md#theorem-313-a-monotone-sofa-is-its-cap-minus-its-niche-baek-theorem-243)).

(1) On $[0, \pi/2]$ the support function $h_K = h$ (Lemma 10.10) is differentiable, as $\mathbf{x}$
is continuously differentiable, with derivative
$\langle \mathbf{x}'(t), u_t \rangle + \langle \mathbf{x}(t), v_t \rangle = \langle \mathbf{A}(t), v_t \rangle$.
For $t \in (0, \pi/2]$ the left derivative of $h_K$ at $t$ is $\langle v_K^-(t), v_t \rangle$
([Corollary 2.10](02-preliminaries.md#corollary-210-one-sided-derivatives-of-the-support-function)).
So $v_K^-(t)$ and $\mathbf{A}(t)$, which both lie on $l_K(t)$, have the same components along $u_t$
and $v_t$: $A_K(t) = v_K^-(t) = \mathbf{A}(t)$. With right derivatives, $v_K^+(t) = \mathbf{A}(t)$ for
$t \in [0, \pi/2)$ as well. At $t = 0$, $v_K^-(0)$ is the lowest point of the edge $e_K(0)$ on the
line $x = 1$, which is $\mathbf{A}(0) = (1, 0)$, as $K$ lies above the $x$-axis. In the same way,
$C_K(t) = v_K^+(t + \frac\pi2) = \mathbf{C}(t)$: for $t < \pi/2$ from the right derivative of
$h(\sigma) = \langle \mathbf{x}(\sigma - \frac\pi2), v_{\sigma - \pi/2} \rangle + 1$, and for
$t = \pi/2$ because $\mathbf{C}(\frac\pi2) = (\mathbf{x}(\frac\pi2)_x - 1, 0)$ is the lowest point of
the edge $e_K(\pi)$. The inner corner is Lemma 10.10 (2).

(3) In hallway coordinates $\mathbf{B}(t) = (0, \alpha(t))$ and $\mathbf{D}(t) = (-\beta(t), 0)$, with
$\alpha \le 0 \le \beta$ (Lemma 10.6). So the points lie on the half-lines $\vec b_K(t)$ and
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

*Lean: [`theorem8_4_2`](../../MovingSofaOptimality/Gerver/Properties.lean#L155), [`gv_odes`](../../MovingSofaOptimality/Gerver/Structure.lean#L124).*

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

*Lean: [`theorem6_1_2`](../../MovingSofaOptimality/Gerver/Properties.lean#L181), [`gv_injectivity`](../../MovingSofaOptimality/Gerver/Structure.lean#L175), [`gs_InjCond1`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L857), [`gs_InjCond2`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L635), [`gs_InjCond3`](../../MovingSofaOptimality/Gerver/StructureCap.lean#L639).*

This is [Theorem 7.3](07-injectivity.md#theorem-73-gervers-sofa-baek-theorem-612), and this is
where it is proved; [§7.6](07-injectivity.md#76-gervers-sofa) explains why the paper's proof does
not work and why Romik's equations are used instead.

*Proof.* By Theorem 10.11 (1), $\mathbf{x}_K = \mathbf{x}$, which is continuously differentiable,
with $\langle \mathbf{x}', u_t \rangle = \alpha < 0 < \beta = \langle \mathbf{x}', v_t \rangle$ on
$(0, \pi/2)$ (Lemma 10.6). These are conditions (2) and (3) of
[Definition 7.1](07-injectivity.md#definition-71-injectivity-condition-baek-definition-612).

For condition (1), recall that $\sigma_K$ is the Lebesgue–Stieltjes measure of the distribution
function $F(t) = \langle v_K^+(t), v_t \rangle + \int_0^t h_K$
([Definition 6.8](06-surface-area.md#definition-68-surface-area-measure)). By the proof of
Theorem 10.11 (1), $v_K^+ = \mathbf{A}$ on $[0, \pi/2)$, so $F$ is continuous there. As
$h_K(t) = \langle \mathbf{A}(t), u_t \rangle$, Lemma 10.5 gives
$F' = \langle \mathbf{A}', v_t \rangle - \langle \mathbf{A}, u_t \rangle + h_K = \rho_A$ off the
phase boundaries. Hence $\sigma_K = \rho_A\, dt$ on $(0, \pi/2)$, and there is no atom at $0$, as
$v_K^-(0) = v_K^+(0) = \mathbf{A}(0)$
([Proposition 6.10](06-surface-area.md#proposition-610-atoms-baek-proposition-212)). On
$[\pi/2, \pi]$ the same computation, with $v_K^+(t) = \mathbf{C}(t - \frac\pi2)$ and
$\mathbf{C}'(t - \frac\pi2) = -\rho_C(t - \frac\pi2)\, u_{t - \pi/2} = \rho_C(t - \frac\pi2)\, v_t$,
gives $\sigma_K = \rho_C(t - \frac\pi2)\, dt$ on $(\pi/2, \pi]$. Both densities are nonnegative
(Lemma 10.6). $\square$

## 10.5 The niche of Gerver's sofa

The niche of $K$ is $\mathcal{N}(K) = F_{\pi/2} \cap \bigcup_{s \in (0, \pi/2)} Q^-_K(s)$, where the
fan $F_{\pi/2}$ is the closed upper half-plane. Since $L_K(s) = \mathbf{x}(s) + R_s L$
(Theorem 10.11), the quadrant $Q^-_K(s)$ is

```math
Q^-(s) = \lbrace q : f_s(q) < 0,\ g_s(q) < 0 \rbrace , \qquad f_s(q) = \langle q - \mathbf{x}(s), u_s \rangle , \quad g_s(q) = \langle q - \mathbf{x}(s), v_s \rangle ,
```

the open quarter-plane below the inner corner, between the inner walls $\vec b(s)$ and $\vec d(s)$.
So the niche is the union of these quarter-planes over $s \in (0, \pi/2)$, cut at the $x$-axis
([`gn_niche_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L88)).

### Definition 10.14 (the curve $\Gamma$)

Let $\Gamma = \mathbf{B}([t_3, t_5]) \cup \mathbf{x}([t_1, t_4]) \cup \mathbf{D}([t_0, t_2])$, and let
$R$ be the set of points $q$ with $q_y \ge 0$ that lie strictly below a point of $\Gamma$: some
$\gamma \in \Gamma$ has $\gamma_x = q_x$ and $q_y < \gamma_y$.

*Lean: [`envCurve`](../../MovingSofaOptimality/Gerver/Envelope.lean#L81), [`envUnderStrict`](../../MovingSofaOptimality/Gerver/Envelope.lean#L88), [`envUnder`](../../MovingSofaOptimality/Gerver/Envelope.lean#L85), [`envQuad`](../../MovingSofaOptimality/Gerver/Envelope.lean#L68), [`envNiche`](../../MovingSofaOptimality/Gerver/Envelope.lean#L72).*

The proof that $\mathcal{N}(K) = R$ must show that no point of $\Gamma$ lies in any quadrant
$Q^-(s)$. This is a family of inequalities in two parameters: the time $s$ of the quadrant and the
time $\tau$ of the point of $\Gamma$. Their margins are small: at $s = \pi/4$ the point
$\mathbf{x}(\varphi)$ is only $f_{\pi/4}(\mathbf{x}(\varphi)) = 0.00124$ away from the inner wall
$b(\pi/4)$, as Gerver observed (Baek's Remark 8.4.1). For a fixed $s$, a monotonicity in $\tau$
reduces each inequality to its value at one end, which depends on $s$ alone; so the proof needs
only inequalities in one variable.

### Lemma 10.15 (Principle P)

If $\langle p - \mathbf{x}(s), u_\sigma \rangle \ge 0$ for some $\sigma \in [s, s + \pi/2]$, then
$p \notin Q^-(s)$.

*Lean: [`env_not_mem_of_dot`](../../MovingSofaOptimality/Gerver/Envelope.lean#L140).*

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

*Lean: [`gn_envHyp`](../../MovingSofaOptimality/Gerver/Niche.lean#L58), [`EnvHyp`](../../MovingSofaOptimality/Gerver/Envelope.lean#L93), [`gb_ratio_mono`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L370), [`gb_α_antitoneOn`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L304), [`gb_β_antitoneOn`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L338), [`gb_rhoA_le`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L387),
[`gb_rhoC_le`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L427), [`gb_I_nonneg`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L501), [`gb_I'_nonneg`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L521), [`gb_core`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L130), [`gb_corner_B`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L578), [`gb_corner_D`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L598), [`gb_x_pos`](../../MovingSofaOptimality/Gerver/NicheBounds.lean#L691).*

*Proof sketch.* Each fact is checked phase by phase from Table 10.1 and the enclosures of the
parameters; the mirror symmetry halves the work.

(1) The signs are Lemma 10.6. By Table 10.1, $\alpha$ and $\beta$ are both nonincreasing on
$[0, \pi/2]$, so $\lvert\alpha\rvert = -\alpha$ increases while $\beta > 0$ decreases.

(2) $\rho_A$ is at most $\rho_{A,2}(0.62) = 0.99703$ on $[0.62, \theta]$, at most
$1 + c_1 - \theta = 0.9447$ on phase 3, at most $\frac\theta2 - b_1 = 0.8682$ on phase 4, and
$\frac12$ on phase 5. $\rho_C$ is the mirror image, with $\rho_C(0.95) = 0.99636$.

(3) Both points lie on phase 2. With $\sigma = s - \varphi$,

```math
I(s) = \sigma + \tfrac{\sigma^2}4 - W_1\,(1 - \cos\sigma) + W_2\,(\sigma + \sin\sigma) , \qquad W_1 = -\tfrac{\varphi^2}4 + b_1\varphi + b_2 = 0.89920 , \quad W_2 = \tfrac\varphi2 - b_1 - 1 = -0.45279 .
```

As $W_1 > 0 > W_2$, the bounds $1 - \cos\sigma \le \frac{\sigma^2}2 - \frac{\sigma^4}{24} + \frac{\sigma^6}{720}$
and $\sin\sigma \le \sigma - \frac{\sigma^3}6 + \frac{\sigma^5}{120}$ bound $I(s)/\sigma$ below by a
polynomial that is positive on $[0, 0.582]$, which contains $[0, s_A - \varphi]$ (numerically,
$I(s)/\sigma > 0.0106$ there). $J$ is the mirror image.

(4) On phase 1, $s \mapsto \langle \mathbf{x}(s), u_{t_3} \rangle$ increases, with derivative
$\alpha_1(s) \sin(\theta + s) + \beta_1(s) \cos(\theta + s) \ge -0.1 + 1.39 \cdot 0.74 > 0$. The
second claim is the mirror image.

(5) The height $\mathbf{x}_y$ increases on $[t_1, \pi/4]$ and decreases on $[\pi/4, t_4]$, and
$\mathbf{x}(t_1)_y = \mathbf{x}(t_4)_y = 0.05519$.

The full proofs are in [`NicheBounds.lean`](../../MovingSofaOptimality/Gerver/NicheBounds.lean).
$\square$

### Theorem 10.17 (the niche is the region under $\Gamma$)

$\mathcal{N}(K) = R$, and the points of $\Gamma$ lie in the closure of $\mathcal{N}(K)$ but not in
$\mathcal{N}(K)$ (Figure 10.6).

*Lean: [`env_niche_eq`](../../MovingSofaOptimality/Gerver/Envelope.lean#L775), [`env_niche_subset_strict`](../../MovingSofaOptimality/Gerver/Envelope.lean#L689), [`env_subset_niche`](../../MovingSofaOptimality/Gerver/Envelope.lean#L727), [`env_not_mem`](../../MovingSofaOptimality/Gerver/Envelope.lean#L531),
[`env_not_mem_niche`](../../MovingSofaOptimality/Gerver/Envelope.lean#L545), [`env_mem_closure`](../../MovingSofaOptimality/Gerver/Envelope.lean#L797), [`env_wit_x`](../../MovingSofaOptimality/Gerver/Envelope.lean#L410), [`env_wit_B`](../../MovingSofaOptimality/Gerver/Envelope.lean#L465), [`env_wit_D`](../../MovingSofaOptimality/Gerver/Envelope.lean#L497), [`env_I_nonneg`](../../MovingSofaOptimality/Gerver/Envelope.lean#L382),
[`env_J_nonneg`](../../MovingSofaOptimality/Gerver/Envelope.lean#L396), [`env_min_le`](../../MovingSofaOptimality/Gerver/Envelope.lean#L237), [`env_sign_aux`](../../MovingSofaOptimality/Gerver/Envelope.lean#L259), [`gn_niche_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L88).*

![Close-up of the niche of Gerver's sofa, shaded orange, under the orange arch x and the two green feet D on the left and B on the right; many thin grey segments run from points x(s) of the arch down to the x-axis along the inner walls b(s) and d(s), crossing each other, and one quadrant below a point x(s0) of the arch is shaded darker](figures/10-gerver/niche.svg)

*Figure 10.6.* The niche as the union of the quadrants $Q^-(s)$. Grey segments are the inner walls
$\vec b(s)$ and $\vec d(s)$ from $\mathbf{x}(s)$ down to the $x$-axis, for 27 values of $s$; one
quadrant $Q^-(s_0)$, $s_0 = 0.45$, is shaded darker. The corners trace $\mathbf{x}$ (orange), and the
walls $\vec d(s)$ and $\vec b(s)$ envelope the curves $\mathbf{D}$ and $\mathbf{B}$ (green) at the two
feet.

*Proof.* The idea is that the curves $\mathbf{B}$ and $\mathbf{D}$ are envelopes of the inner walls,
and that every point of $\Gamma$ is separated from each quadrant by a line through its corner
(Lemma 10.15). By Definition 10.2, $f_s(\mathbf{B}(s)) = 0$ and $g_s(\mathbf{D}(s)) = 0$, and off the
phase boundaries, by Lemma 10.5,

```math
(f_s \circ \mathbf{B})'(r) = (\rho_A(r) - 1) \sin(s - r) , \qquad (g_s \circ \mathbf{D})'(r) = (1 - \rho_C(r)) \sin(r - s) .
```

By Lemma 10.16 (2), $f_s \circ \mathbf{B}$ decreases on $[s_A, s]$ and increases on
$[\max(s, s_A), \pi/2]$; and $g_s \circ \mathbf{D}$ decreases on $[0, \min(s, s_C)]$ and increases on
$[s, s_C]$.

*Step 1: $I \ge 0$ on $[t_1, \pi/2)$ and $J \ge 0$ on $(0, t_4]$.* For $s \le s_A$ this is
Lemma 10.16 (3). For $s \ge s_A$, $I(s) = f_s(\mathbf{x}(t_1)) = f_s(\mathbf{B}(t_3))$, as
$\mathbf{B}(t_3) = \mathbf{x}(t_1)$. On $[s_A, \pi/2]$, which contains $t_3$, the function
$f_s \circ \mathbf{B}$ is smallest at $s$, so $I(s) \ge f_s(\mathbf{B}(s)) = 0$. $J$ is the mirror
image.

*Step 2: no point of $\Gamma$ lies in a quadrant.* Fix $s \in (0, \pi/2)$. In each case below, a
witness angle $\sigma \in [s, s + \pi/2]$ and Lemma 10.15 exclude the point from $Q^-(s)$.

- $\mathbf{x}(\tau)$ with $t_1 \le \tau \le s$, with $\sigma = s$. The function
  $F(\tau') = f_s(\mathbf{x}(\tau'))$ on $[t_1, s]$ has derivative
  $F' = \alpha \cos(s - \tau') + \beta \sin(s - \tau')$, which has the sign of
  $\tan(s - \tau') - \lvert\alpha\rvert/\beta$. As $\tau'$ grows, the tangent decreases and
  $\lvert\alpha\rvert/\beta$ increases (Lemma 10.16 (1)). So once $F'$ is negative it stays
  negative, and $F$ attains its minimum on $[t_1, s]$ at an end. Hence
  $F(\tau) \ge \min(F(t_1), F(s)) = \min(I(s), 0) = 0$ by Step 1.
- $\mathbf{x}(\tau)$ with $s \le \tau \le t_4$: the mirror argument, with $g_s$, $J$ and
  $\sigma = s + \pi/2$.
- $\mathbf{B}(\tau)$, $\tau \in [t_3, \pi/2]$, when $s \ge t_1$, with $\sigma = s$. If $s \le t_3$,
  $f_s(\mathbf{B}(\tau)) \ge f_s(\mathbf{B}(t_3)) = I(s) \ge 0$. If $s > t_3$,
  $f_s(\mathbf{B}(\tau)) \ge f_s(\mathbf{B}(s)) = 0$.
- $\mathbf{B}(\tau)$ when $s < t_1$, with $\sigma = t_3$. Since
  $f_{t_3}(\mathbf{x}(t_1)) = f_{t_3}(\mathbf{B}(t_3)) = 0$,
  $\langle \mathbf{B}(\tau) - \mathbf{x}(s), u_{t_3} \rangle = f_{t_3}(\mathbf{B}(\tau)) + \langle \mathbf{x}(t_1) - \mathbf{x}(s), u_{t_3} \rangle$.
  The first term is nonnegative because $f_{t_3} \circ \mathbf{B}$ increases on $[t_3, \pi/2]$, the
  second by Lemma 10.16 (4).
- $\mathbf{D}(\tau)$: the mirror arguments, with $\sigma = s + \pi/2$, or $\sigma = t_2 + \pi/2$ when
  $s > t_4$.

*Step 3: $R \subseteq \mathcal{N}(K)$.* Let $\gamma = \mathbf{x}(\tau)$, $\mathbf{B}(\tau)$ or
$\mathbf{D}(\tau)$ with $\tau \in (0, \pi/2)$, and $b > 0$. Then $f_\tau(\gamma) \le 0$ and
$g_\tau(\gamma) \le 0$ (Definition 10.2 and Lemma 10.6). Moving down by $b$ lowers $f_\tau$ by
$b \sin\tau > 0$ and $g_\tau$ by $b \cos\tau > 0$, so $\gamma - (0, b) \in Q^-(\tau)$. The ends
$\mathbf{B}(\pi/2)$ and $\mathbf{D}(0)$ lie on the $x$-axis, and no point of $R$ lies below them.

*Step 4: $\mathcal{N}(K) \subseteq R$.* Let $q \in Q^-(s)$ with $q_y \ge 0$. Suppose first that
$q_x > \mathbf{B}(\pi/2)_x$, and let $\sigma \in [s, \pi/2]$ be the witness of $\mathbf{B}(\pi/2)$
from Step 2. Both coordinates of $q - \mathbf{B}(\pi/2)$ are nonnegative, and so are $\cos\sigma$
and $\sin\sigma$; so
$\langle q - \mathbf{x}(s), u_\sigma \rangle \ge \langle \mathbf{B}(\pi/2) - \mathbf{x}(s), u_\sigma \rangle \ge 0$,
which Lemma 10.15 forbids. The case $q_x < \mathbf{D}(0)_x$ is the mirror image. Otherwise, as
$\Gamma$ is a curve from $\mathbf{D}(0)$ to $\mathbf{B}(\pi/2)$, the intermediate value theorem
gives $\gamma \in \Gamma$ with $\gamma_x = q_x$. If $q_y \ge \gamma_y$, the witness $\sigma$ of
$\gamma$, which lies in $[0, \pi]$, gives
$\langle q - \mathbf{x}(s), u_\sigma \rangle = \langle \gamma - \mathbf{x}(s), u_\sigma \rangle + (q_y - \gamma_y) \sin\sigma \ge 0$,
again impossible. So $q_y < \gamma_y$ and $q \in R$.

*Step 5: closure.* A point $\gamma$ of $\Gamma$ above the $x$-axis is the limit of the points
$\gamma - (0, b) \in R$ as $b \to 0$, and the two ends on the axis are limits of such points.
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

*Lean: [`env_volume_region_of_monotoneOn`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L419), [`env_volume_region_of_antitoneOn`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L439),
[`env_nullMeasurableSet_region`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L458).*

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

*Lean: [`theorem8_4_1_niche`](../../MovingSofaOptimality/Gerver/Properties.lean#L103), [`gv_niche`](../../MovingSofaOptimality/Gerver/Niche.lean#L125), [`env_area`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L530), [`env_niche_eq_union`](../../MovingSofaOptimality/Gerver/EnvelopeArea.lean#L520).*

The paper states that the niche is the region enclosed counterclockwise by $\mathbf{B}$ reversed,
$\mathbf{x}|_{[t_1, t_4]}$, $\mathbf{D}$ reversed and the segment of the $x$-axis from
$\mathbf{D}(0)$ to $\mathbf{B}(\pi/2)$, a statement about a Jordan curve, which the formalization does
not use. Theorem 10.19 is what the paper uses from it, and Theorem 10.17 says more: the niche is the
region strictly under these curves (REPORT.md, Section 6).

*Proof.* The first claims are Theorem 10.17 and Lemma 10.6 (4). By Theorem 10.17 the niche is the
union of the regions strictly under $\mathbf{D}|_{[0, t_2]}$, $\mathbf{x}|_{[t_1, t_4]}$ and
$\mathbf{B}|_{[t_3, \pi/2]}$, which meet only on two vertical lines. The abscissa increases along
$\mathbf{D}$ (as $\mathbf{D}' = (1 - \rho_C)\, u_t$ with $\rho_C < 1$) and along $\mathbf{B}$ (as
$\mathbf{B}' = (\rho_A - 1)\, v_t$ with $\rho_A < 1$), and decreases along $\mathbf{x}$ (proof of
Lemma 10.10 (3)). Lemma 10.18 gives the three areas, and the boundary terms cancel:
$\mathbf{D}(t_2) = \mathbf{x}(t_4)$, $\mathbf{B}(t_3) = \mathbf{x}(t_1)$, and $\mathbf{D}(0)$,
$\mathbf{B}(\pi/2)$ have height $0$. $\square$

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

*Lean: [`gv_cap_area`](../../MovingSofaOptimality/Gerver/Niche.lean#L371), [`gn_K_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L354), [`segArea`](../../MovingSofaOptimality/Convex/CurveArea.lean#L668).*

*Proof.* $K$ is the region between the $x$-axis and the curve made of $\mathbf{A}|_{[0, \pi/2]}$, the
top edge and $\mathbf{C}|_{[0, \pi/2]}$ ([`gn_K_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L354)).
Indeed, this curve lies in $K$ (Lemma 10.10). A point above the axis and below a point of $K$ lies in
$K$, because the normals $u_\sigma$, $\sigma \in [0, \pi]$, of the other half-planes of $K$ have a
nonnegative second coordinate. Conversely, a point $q \in K$ with the abscissa of $\mathbf{A}(t)$,
$t \in (0, \pi/2]$, lies below $\mathbf{A}(t)$, by the support inequality
$\langle q, u_t \rangle \le \langle \mathbf{A}(t), u_t \rangle$ and $\sin t > 0$; likewise for
$\mathbf{C}$, and the top edge has height $1$. Along all three pieces the abscissa decreases, as
$\mathbf{A}' = \rho_A v_t$ and $\mathbf{C}' = -\rho_C u_t$ with $\rho_A, \rho_C \ge 0$. Lemma 10.18
gives the three areas, and the boundary terms cancel, since $\mathbf{A}(0)_y = \mathbf{C}(\pi/2)_y = 0$
and $\mathbf{A}(\pi/2)_y = \mathbf{C}(0)_y = 1$. $\square$

### Theorem 10.21 (the area of Gerver's sofa)

```math
\lvert G \rvert = \mathcal{J}(\mathbf{A}|_{[0, \pi/2]}) + \mathcal{J}(\mathbf{C}|_{[0, \pi/2]}) + \mathcal{J}(\mathbf{A}(\pi/2), \mathbf{C}(0)) - \mathcal{J}(\mathbf{x}|_{[t_1, t_4]}) + \mathcal{J}(\mathbf{B}|_{[t_3, t_5]}) + \mathcal{J}(\mathbf{D}|_{[t_0, t_2]}) ,
```

and $2.2192 \le \lvert G \rvert \le 2.2199$; in particular $\lvert G \rvert \ge 2.2$.

*Lean: [`Baek.gerver_sofa_area`](../../Challenge.lean#L338), [`gerverSofa_area_mem`](../../MovingSofaOptimality/Main.lean#L291), [`gv_area_mem`](../../MovingSofaOptimality/Gerver/Niche.lean#L467), [`gv_area_eq`](../../MovingSofaOptimality/Gerver/Niche.lean#L444),
[`gerverSofa_area`](../../MovingSofaOptimality/Gerver/Properties.lean#L187), [`gv_area`](../../MovingSofaOptimality/Gerver/Niche.lean#L461), [`gerverSofa_volume_ne_top`](../../MovingSofaOptimality/Main.lean#L296).*

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
[`AreaBounds.lean`](../../MovingSofaOptimality/Gerver/AreaBounds.lean) ([`ga_curveArea_A_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L2954),
[`ga_curveArea_C_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L2966), [`ga_segArea_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L2999), [`ga_curveArea_x_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3006), [`ga_curveArea_B_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3016),
[`ga_curveArea_D_mem`](../../MovingSofaOptimality/Gerver/AreaBounds.lean#L3025)), and their values recomputed by quadrature in 25-digit arithmetic.

*Proof.* By Theorem 10.11 and its proof, $G = K \setminus \mathcal{N}(K)$ with
$\mathcal{N}(K) \subseteq K$. The niche is measurable, the intersection of a closed half-plane with a
union of open quadrants, and $K$ is compact, so
$\lvert G \rvert = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert$. Proposition 10.20 and
Theorem 10.19 give the formula. [Appendix B](appendix-b.md) encloses each term as in Table 10.3, and
adding the enclosures gives $2.2192 \le \lvert G \rvert \le 2.2199$. The Challenge states the bounds
for the Lebesgue measure, `volume (gerverSofa P)`, which is finite since $G \subseteq K$. $\square$

The value is $\lvert G \rvert = 2.21953166887\ldots$, as computed by Gerver and Romik [3, 4]. With
Theorem 10.13, the bound $\lvert K \rvert \ge \lvert G \rvert \ge 2.2$ puts the cap of Gerver's sofa in
the space $\mathcal{K}^\mathrm{i}$ of Chapter 9
([Theorem 9.2](09-optimality.md#theorem-92-these-caps-form-a-convex-domain-baek-theorem-811) (3),
[`theorem8_1_1_gerver`](../../MovingSofaOptimality/Main.lean#L56)).

## 10.7 The left and right bodies (Baek, §8.4.3–8.4.4)

[Chapter 9](09-optimality.md) attaches to a cap $K \in \mathcal{K}^\mathrm{i}$ the right and left
bodies $B_K = K \cap \bigcap_{t \in [\varphi, \pi/2]} H^\mathrm{b}_K(t)$ and
$D_K = K \cap \bigcap_{t \in [0, \pi/2 - \varphi]} H^\mathrm{d}_K(t)$, the points
$\mathbf{x}_K^\mathrm{R} = \mathbf{x}_K(\varphi)$ and $\mathbf{x}_K^\mathrm{L} = \mathbf{x}_K(\frac\pi2 - \varphi)$
([Definition 9.6](09-optimality.md#definition-96-the-right-and-left-bodies-baek-definitions-814816)),
the tails $\mathbf{b}_{B} = \mathbf{u}_B^{\pi + \varphi, 3\pi/2}$ and
$\mathbf{d}_{D} = \mathbf{u}_D^{3\pi/2, 3\pi/2 + \pi/2 - \varphi}$ of their boundaries, with ends
$X_B = v_B^+(\pi + \varphi)$ and $Y_D = v_D^-(2\pi - \varphi)$, and the upper bound
$\mathcal{Q}(K, B, D)$
([Definition 9.13](09-optimality.md#definition-913-the-tails-and-the-upper-bound-baek-definitions-821-822)).
It also uses the reflected surface area measure $\breve\sigma_C(X) = \sigma_C(X + \pi)$ and support
function $\breve h_C(t) = h_C(t + \pi)$ of a convex body $C$
([Definition 9.28](09-optimality.md#definition-928-reflected-measures-and-the-measure-of-the-core-baek-definitions-845-846);
[`sigmaBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L68), [`suppBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L71)).
This section identifies these objects for the cap $K$ of Gerver's sofa.

### Theorem 10.22 (left, middle and right parts; Baek, Theorem 8.4.3)

Let $B = B_K$ and $D = D_K$.

1. $\mathbf{D}(t) = v_D^\pm(\frac{3\pi}2 + t)$ for $t \in (t_0, t_2)$, and
   $\mathbf{B}(t) = v_B^\pm(\pi + t)$ for $t \in (t_3, t_5)$.
2. $\mathbf{x}_K^\mathrm{L} = Y_D = \mathbf{D}(t_2)$, and the tail $\mathbf{d}_D$ is the curve
   $\mathbf{D}([t_0, t_2])$; $\mathbf{x}_K^\mathrm{R} = X_B = \mathbf{B}(t_3)$, and the tail
   $\mathbf{b}_B$ is the curve $\mathbf{B}([t_3, t_5])$; as oriented curves, so that
   $\mathcal{J}(\mathbf{d}_D) = \mathcal{J}(\mathbf{D}|_{[t_0, t_2]})$ and
   $\mathcal{J}(\mathbf{b}_B) = \mathcal{J}(\mathbf{B}|_{[t_3, t_5]})$.
3. $h_K(\frac\pi2 + t) + h_D(\frac{3\pi}2 + t) = 1$ for $t \in [t_0, t_2]$, and
   $h_K(t) + h_B(\pi + t) = 1$ for $t \in [t_3, t_5]$.

*Lean: [`theorem8_4_3_one`](../../MovingSofaOptimality/Gerver/Properties.lean#L983), [`theorem8_4_3_two`](../../MovingSofaOptimality/Gerver/Properties.lean#L1693), [`theorem8_4_3_three`](../../MovingSofaOptimality/Gerver/Properties.lean#L992), [`rightBody`](../../MovingSofaOptimality/Optimality/Domain.lean#L567), [`leftBody`](../../MovingSofaOptimality/Optimality/Domain.lean#L570),
[`gm_D_mem_leftBody`](../../MovingSofaOptimality/Gerver/Properties.lean#L495), [`gm_D_edge`](../../MovingSofaOptimality/Gerver/Properties.lean#L524), [`gm_B_edge`](../../MovingSofaOptimality/Gerver/Properties.lean#L653), [`gm_tailD`](../../MovingSofaOptimality/Gerver/Properties.lean#L728), [`gm_tailB`](../../MovingSofaOptimality/Gerver/Properties.lean#L757), [`lemma8_1_6_left`](../../MovingSofaOptimality/Optimality/Domain.lean#L916).*

Baek's paper writes $\mathbf{x}_K^\mathrm{R} = X_{B_K} = \mathbf{D}(t_3)$ in (2); $\mathbf{B}(t_3)$ is
meant, as $\mathbf{D}$ is defined on $[t_0, t_2]$ only (REPORT.md, E25). The formalization reads
"as oriented curves" as the equality of the sets together with the equality of the curve area
functionals, which is what Theorem 10.26 uses. Orientations of curves are not formalized, and
$\mathcal{J}$ of a convex arc is $\frac12 \int h\, d\sigma$, so both sides are computed: from the
density of $\breve\sigma$ (Proposition 10.23) and from the pieces of $\mathbf{D}$ and $\mathbf{B}$
(REPORT.md, Section 7).

*Proof sketch.* The proof follows the paper. We treat the left body $D$; the right body is the
mirror image. The idea is that $\mathbf{D}(t)$ lies in $D$ and on its supporting line $d_K(t)$.

*The curve $\mathbf{D}$ lies in $D$.* Let $t \in [t_0, t_2]$. By Theorem 10.19, $\mathbf{D}(t)$ lies in
the closure of the niche, hence in $K$ and above the $x$-axis, and not in the niche; so it lies in
no quadrant $Q^-_K(s)$, $s \in [0, \pi/2)$. The curve ends at
$\mathbf{D}(t_2) = \mathbf{x}(t_4) = \mathbf{x}_K^\mathrm{L}$ on the line $d_K^\mathrm{L}$, and its
velocity $\mathbf{D}'(r)$ is a positive multiple of $u_r$ (Theorem 10.11 (4)), with
$\langle u_r, v_{t_4} \rangle = \sin(r - t_4) < 0$. So $\mathbf{D}(t)$ lies in the half-plane
$\breve H_K^\mathrm{L} = H^\mathrm{d}_K(t_4)$ above that line. For $s \in [0, t_4)$, a point of
$\breve H_K^\mathrm{L}$ outside $H^\mathrm{d}_K(s)$ lies in $Q^-_K(s)$
([Lemma 9.10](09-optimality.md#lemma-910-the-core-leaves-the-cut-half-planes-baek-lemma-816) (2)).
So $\mathbf{D}(t)$ lies in every $H^\mathrm{d}_K(s)$, $s \in [0, t_4]$, that is, in $D$.

(3) $\mathbf{D}(t)$ lies on the inner wall $d_K(t)$ (Theorem 10.11 (3)), which bounds
$H^\mathrm{d}_K(t) \supseteq D$, with the outer normal $-v_t = u_{3\pi/2 + t}$. So $\mathbf{D}(t)$ lies
on the edge $e_D(\frac{3\pi}2 + t)$, and
$h_D(\frac{3\pi}2 + t) = -\langle \mathbf{D}(t), v_t \rangle = 1 - h_K(\frac\pi2 + t)$.

(1) Let $t \in (t_0, t_2)$. For $s$ near $t$, $\mathbf{D}(s)$ lies on the edge
$e_D(\frac{3\pi}2 + s)$, between its two vertices. By
[Theorem 2.9](02-preliminaries.md#theorem-29-limits-of-vertices-baek-theorem-213), these vertices
tend to $v_D^+(\frac{3\pi}2 + t)$ as $s \to t^+$ and to $v_D^-(\frac{3\pi}2 + t)$ as $s \to t^-$. As
$\mathbf{D}$ is continuous, both equal $\mathbf{D}(t)$.

(2) The point $\mathbf{D}(t_2) = \mathbf{x}_K^\mathrm{L}$ lies on the supporting lines of $D$ at the
angles $\frac{3\pi}2 + t_2$ and $2\pi - \varphi$ (the line $d_K^\mathrm{L}$). So $D$ has a corner
there, and its vertices at all the angles in between are $\mathbf{D}(t_2)$; in particular
$Y_D = \mathbf{D}(t_2)$. With (1), the vertices of $D$ at the angles from $\frac{3\pi}2$ to
$2\pi - \varphi$ run along $\mathbf{D}$, so the tail $\mathbf{d}_D$ is the curve
$\mathbf{D}([t_0, t_2])$. $\square$

### Proposition 10.23 (the surface area measures; Baek, Proposition 8.4.4)

1. $\sigma_K = \langle \mathbf{A}'(t), v_t \rangle\, dt$ on $[0, \pi/2)$;
2. $\breve\sigma_B = \langle -\mathbf{B}'(t), v_t \rangle\, dt$ on $[t_3, t_5)$;
3. $\sigma_K = \langle -\mathbf{C}'(t - \frac\pi2), u_{t - \pi/2} \rangle\, dt$ on $(\pi/2, \pi]$;
4. $\breve\sigma_D = \langle \mathbf{D}'(t - \frac\pi2), u_{t - \pi/2} \rangle\, dt$ on
   $(\frac\pi2 + t_0, \frac\pi2 + t_2]$.

*Lean: [`proposition8_4_4`](../../MovingSofaOptimality/Gerver/Properties.lean#L1216), [`sigmaBreve`](../../MovingSofaOptimality/Optimality/Variation.lean#L68).*

Baek's paper states (4) on $(t_0, t_2]$ with the density $\langle \mathbf{D}'(t), u_t \rangle$. As
$\mathbf{D}(s) = v_D(\frac{3\pi}2 + s)$, the measure $\breve\sigma_D$ lives on
$(\frac\pi2 + t_0, \frac\pi2 + t_2]$, with the shifted density of item (3), the form that
Theorem 10.25 and
[Theorem 9.30](09-optimality.md#theorem-930-the-directional-derivative-of-the-upper-bound-baek-theorem-856)
use. As printed, the left side is $\breve\sigma_D$ on $(t_0, t_2]$, which vanishes (REPORT.md, E26).

*Proof.* As in Baek's proof, $dv_K^+ = v_t\, \sigma_K$ (Theorem 6.12). On an interval where the
vertex $v_K^+(t)$ follows one of the curves $\mathbf{A}, \mathbf{B}, \mathbf{C}, \mathbf{D}$, which
are piecewise continuously differentiable with bounded derivatives, its Lebesgue–Stieltjes measure
is the derivative of the curve times $dt$, and its $v_t$-component gives the density of $\sigma_K$.

- (1): $v_K^+ = \mathbf{A}$ on $[0, \pi/2)$, and $\sigma_K$ has no atom at $0$ (Theorem 10.13).
- (3): $v_K^+(t) = \mathbf{C}(t - \frac\pi2)$ on $[\pi/2, \pi]$, and
  $\langle \mathbf{C}'(t - \frac\pi2), v_t \rangle = \langle -\mathbf{C}'(t - \frac\pi2), u_{t - \pi/2} \rangle$.
- (2): $v_B^+(\pi + t) = \mathbf{B}(t)$ for $t \in [t_3, t_5)$ (Theorem 10.22 and its proof), and
  $\mathbf{B}' = (\rho_A - 1)\, v_t = (1 - \rho_A)\, v_{\pi + t}$. So $\sigma_B$ has the density
  $1 - \rho_A(t) = \langle -\mathbf{B}'(t), v_t \rangle$ at the angle $\pi + t$. There is no atom at
  $\pi + t_3$, where the edge of $B$ is the single point $\mathbf{B}(t_3)$. Shifting by $\pi$ gives
  $\breve\sigma_B$.
- (4): the same for $D$: $v_D^+(\frac{3\pi}2 + t) = \mathbf{D}(t)$ for $t \in [t_0, t_2]$, and
  $\mathbf{D}' = (1 - \rho_C)\, u_t = (1 - \rho_C)\, v_{3\pi/2 + t}$; the shift by $\pi$ moves the
  angle $\frac{3\pi}2 + t$ to $\frac\pi2 + t$. $\square$

### Definition 10.24 (the measure $\iota_K$ and the intervals $J_i$; Baek, Definitions 8.4.6 and 8.4.7)

For a cap $K$ with the injectivity condition, $\iota_K = i_K(t)\, dt$ on $[0, \pi]$ is the measure
of Definition 9.28: $i_K(t) = \langle \mathbf{x}_K'(t), v_t \rangle$ and
$i_K(t + \frac\pi2) = \langle -\mathbf{x}_K'(t), u_t \rangle$ for $t \in (0, \pi/2]$. Let
$J_i = [t_{i-1}, t_i)$ for $1 \le i \le 5$ and $J_i = \pi - J_{11 - i}$ for $6 \le i \le 10$. The
intervals $J_1, \dots, J_{10}$ and the point $\lbrace \pi/2 \rbrace$ partition $[0, \pi]$.

*Lean: [`iFun`](../../MovingSofaOptimality/Optimality/Variation.lean#L75), [`iota`](../../MovingSofaOptimality/Optimality/Variation.lean#L81), [`MovingSofaOptimality.GerverParams.jInt`](../../MovingSofaOptimality/Gerver/Properties.lean#L1234).*

### Theorem 10.25 (Romik's equations as measures; Baek, Theorem 8.4.5)

With $B = B_K$ and $D = D_K$:

| Interval | Measure $\sigma_K$ | Interval | Measure $\sigma_K$ |
| --- | --- | --- | --- |
| $J_1$ | $0$ | $J_6$ | $\breve\sigma_D$ |
| $J_2 \cup J_3$ | $\iota_K$ | $J_7$ | $\breve\sigma_D + \iota_K$ |
| $J_4$ | $\breve\sigma_B + \iota_K$ | $J_8 \cup J_9$ | $\iota_K$ |
| $J_5$ | $\breve\sigma_B$ | $J_{10}$ | $0$ |

*Lean: [`theorem8_4_5`](../../MovingSofaOptimality/Gerver/Properties.lean#L1356), [`gm_sigma_restrict_A`](../../MovingSofaOptimality/Gerver/Properties.lean#L1271), [`gm_sigma_restrict_C`](../../MovingSofaOptimality/Gerver/Properties.lean#L1276), [`gm_iota_restrict`](../../MovingSofaOptimality/Gerver/Properties.lean#L1296).*

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

*Lean: [`theorem8_4_6`](../../MovingSofaOptimality/Gerver/Properties.lean#L1713), [`sofaArea`](../../MovingSofaOptimality/Monotone/CapDefs.lean#L83), [`upperQ`](../../MovingSofaOptimality/Optimality/UpperBound.lean#L359), [`gm_convexCurveArea_B`](../../MovingSofaOptimality/Gerver/Properties.lean#L1611), [`gm_convexCurveArea_D`](../../MovingSofaOptimality/Gerver/Properties.lean#L1638).*

*Proof.* By Definition 9.13,

```math
\mathcal{Q}(K, B, D) = \lvert K \rvert + \mathcal{J}(\mathbf{d}_D) + \mathcal{J}(Y_D, \mathbf{x}_K^\mathrm{L}) - \mathcal{J}(\mathbf{x}_K|_{[\varphi, \pi/2 - \varphi]}) + \mathcal{J}(\mathbf{x}_K^\mathrm{R}, X_B) + \mathcal{J}(\mathbf{b}_B) .
```

By Theorem 10.22 (2), $Y_D = \mathbf{x}_K^\mathrm{L}$ and $X_B = \mathbf{x}_K^\mathrm{R}$, so the two
segment terms vanish, and the curve areas of the tails are $\mathcal{J}(\mathbf{D}|_{[t_0, t_2]})$
and $\mathcal{J}(\mathbf{B}|_{[t_3, t_5]})$. With $\mathbf{x}_K = \mathbf{x}$ (Theorem 10.11),
Theorem 10.19 turns the remaining terms into
$\lvert K \rvert - \lvert \mathcal{N}(K) \rvert = \mathcal{A}(K)$. $\square$
