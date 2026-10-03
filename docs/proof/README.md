# The moving sofa

**Gerver's sofa is optimal, and it is the only optimal sofa: proofs, with a Lean 4 formalization**

A companion text to the Lean 4 formalization in this repository
([lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa)); for its authorship see
[Contributors](../contributors.md).

**Abstract.** A moving sofa is a connected planar shape that can be moved around the right-angled
corner of a hallway of unit width, and the moving sofa problem asks for the largest area of one.
Gerver found a sofa of area $2.21953\ldots$ in 1992 and conjectured that it is optimal; Baek proved
the conjecture in 2024. This text gives a complete proof of Baek's theorem, including the facts about
Gerver's sofa that the paper takes from Gerver and Romik or states without proof, and proves that
Gerver's sofa is the only moving sofa of maximum area: every other one is its image under a rotation
and a translation. Baek's proof reduces a maximum sofa to a monotone one, a convex cap minus the
niche that the inner corner of the hallway carves out of it. Limits of maximum polygon sofas are
balanced, turn through a right angle, and satisfy an injectivity condition: seen from the sofa, the
inner corner never crosses its own path. For such sofas a quadratic functional $\mathcal{Q}$ of three
convex bodies bounds the area; it is concave by Mamikon's theorem, and it is maximized at Gerver's
sofa, where it equals the area. The uniqueness proof shows that every maximum sofa, not only the
limits of polygon sofas, turns through a right angle and satisfies the injectivity condition, by
approximating it with maximizers of a penalized polygon problem; then the equality case of Baek's
bound forces equality in each of Mamikon's terms, which makes the sofa a translate of Gerver's. A last
chapter shows that the definitions of Google DeepMind's formal-conjectures describe the same moving
sofas and the same Gerver's sofa as Baek's, so that its statements follow, among them the
uniqueness, which it lists as open. Every result is proved in Lean 4 with Mathlib, and each numbered
statement names the declarations that prove it.

## Contents

- [1. Introduction](#1-introduction)
  - [1.1 The problem](#11-the-problem)
  - [1.2 The main theorems](#12-the-main-theorems)
  - [1.3 Background](#13-background)
  - [1.4 Outline of the proof](#14-outline-of-the-proof)
  - [1.5 This text and the formalization](#15-this-text-and-the-formalization)
- [2. Preliminaries](02-preliminaries.md)
  - [2.1 The plane](02-preliminaries.md#21-the-plane)
  - [2.2 The hallway and moving sofas](02-preliminaries.md#22-the-hallway-and-moving-sofas)
  - [2.3 Planar convex bodies](02-preliminaries.md#23-planar-convex-bodies)
  - [2.4 Standard position](02-preliminaries.md#24-standard-position)
  - [2.5 Supporting hallways](02-preliminaries.md#25-supporting-hallways)
- [3. Monotone sofas, caps and niches](03-monotone.md)
  - [3.1 Monotonization](03-monotone.md#31-monotonization)
  - [3.2 Caps and niches](03-monotone.md#32-caps-and-niches)
  - [3.3 The parts of a cap](03-monotone.md#33-the-parts-of-a-cap)
  - [3.4 The cap contains its niche](03-monotone.md#34-the-cap-contains-its-niche)
  - [3.5 The sofa area functional](03-monotone.md#35-the-sofa-area-functional)
- [4. Balanced maximum sofas](04-balanced.md)
  - [4.1 Gerver's balancing argument and its gap](04-balanced.md#41-gervers-balancing-argument-and-its-gap)
  - [4.2 Simple Nef polygons](04-balanced.md#42-simple-nef-polygons)
  - [4.3 Polygon caps and polygon niches](04-balanced.md#43-polygon-caps-and-polygon-niches)
  - [4.4 Support values](04-balanced.md#44-support-values)
  - [4.5 Maximum polygon caps](04-balanced.md#45-maximum-polygon-caps)
  - [4.6 Balanced polygon caps](04-balanced.md#46-balanced-polygon-caps)
  - [4.7 Balanced maximum sofas](04-balanced.md#47-balanced-maximum-sofas)
- [5. The rotation angle](05-rotation-angle.md)
  - [5.1 A first bound on the rotation angle](05-rotation-angle.md#51-a-first-bound-on-the-rotation-angle)
  - [5.2 Horizontal side lengths](05-rotation-angle.md#52-horizontal-side-lengths)
  - [5.3 The triangle at the corner](05-rotation-angle.md#53-the-triangle-at-the-corner)
  - [5.4 The triangle lies in the niche](05-rotation-angle.md#54-the-triangle-lies-in-the-niche)
  - [5.5 The full right angle](05-rotation-angle.md#55-the-full-right-angle)
- [6. The surface area measure](06-surface-area.md)
  - [6.1 Lebesgue–Stieltjes measures](06-surface-area.md#61-lebesguestieltjes-measures)
  - [6.2 The surface area measure](06-surface-area.md#62-the-surface-area-measure)
  - [6.3 The differential Gauss–Minkowski theorem](06-surface-area.md#63-the-differential-gaussminkowski-theorem)
  - [6.4 The area formula](06-surface-area.md#64-the-area-formula)
  - [6.5 Weak convergence](06-surface-area.md#65-weak-convergence)
- [7. The injectivity condition](07-injectivity.md)
  - [7.1 The statement](07-injectivity.md#71-the-statement)
  - [7.2 Arm lengths](07-injectivity.md#72-arm-lengths)
  - [7.3 The inequality on maximum polygon caps](07-injectivity.md#73-the-inequality-on-maximum-polygon-caps)
  - [7.4 The inequality on balanced maximum caps](07-injectivity.md#74-the-inequality-on-balanced-maximum-caps)
  - [7.5 Bounding the arm lengths](07-injectivity.md#75-bounding-the-arm-lengths)
  - [7.6 Gerver's sofa](07-injectivity.md#76-gervers-sofa)
- [8. Convex curves and Mamikon's theorem](08-convex-curves.md)
  - [8.1 Convex domains and quadratic functionals](08-convex-curves.md#81-convex-domains-and-quadratic-functionals)
  - [8.2 The curve area functional](08-convex-curves.md#82-the-curve-area-functional)
  - [8.3 Convex curves](08-convex-curves.md#83-convex-curves)
  - [8.4 Mamikon's theorem](08-convex-curves.md#84-mamikons-theorem)
- [9. The upper bound and the optimality of Gerver's sofa](09-optimality.md)
  - [9.1 The domain of the upper bound](09-optimality.md#91-the-domain-of-the-upper-bound)
  - [9.2 The upper bound](09-optimality.md#92-the-upper-bound)
  - [9.3 Concavity of the upper bound](09-optimality.md#93-concavity-of-the-upper-bound)
  - [9.4 The directional derivative at Gerver's sofa](09-optimality.md#94-the-directional-derivative-at-gervers-sofa)
  - [9.5 The optimality of Gerver's sofa](09-optimality.md#95-the-optimality-of-gervers-sofa)
- [10. Gerver's sofa](10-gerver.md)
  - [10.1 Romik's description](10-gerver.md#101-romiks-description)
  - [10.2 The rotating frame](10-gerver.md#102-the-rotating-frame)
  - [10.3 Existence and uniqueness of the parameters](10-gerver.md#103-existence-and-uniqueness-of-the-parameters)
  - [10.4 The cap of Gerver's sofa](10-gerver.md#104-the-cap-of-gervers-sofa)
  - [10.5 The niche of Gerver's sofa](10-gerver.md#105-the-niche-of-gervers-sofa)
  - [10.6 The area of Gerver's sofa](10-gerver.md#106-the-area-of-gervers-sofa)
  - [10.7 The left and right bodies (Baek, §8.4.3–8.4.4)](10-gerver.md#107-the-left-and-right-bodies-baek-843844)
- [11. Uniqueness I: approximating a maximizing cap](11-selection.md)
  - [11.1 The given maximizer](11-selection.md#111-the-given-maximizer)
  - [11.2 Penalties at dyadic samples](11-selection.md#112-penalties-at-dyadic-samples)
  - [11.3 Penalized maximizers](11-selection.md#113-penalized-maximizers)
  - [11.4 Convergence to the given cap](11-selection.md#114-convergence-to-the-given-cap)
  - [11.5 Raising one height](11-selection.md#115-raising-one-height)
  - [11.6 Floating normals](11-selection.md#116-floating-normals)
  - [11.7 Pinned normals](11-selection.md#117-pinned-normals)
  - [11.8 The pinned bounds](11-selection.md#118-the-pinned-bounds)
- [12. Uniqueness II: every maximum is Gerver's sofa](12-uniqueness.md)
  - [Theorem 12.1 (uniqueness of Gerver's sofa)](12-uniqueness.md#theorem-121-uniqueness-of-gervers-sofa)
  - [12.1 The curvature bounds](12-uniqueness.md#121-the-curvature-bounds)
  - [12.2 The injectivity condition](12-uniqueness.md#122-the-injectivity-condition)
  - [12.3 The right-angle motion](12-uniqueness.md#123-the-right-angle-motion)
  - [12.4 Equality in the upper bound](12-uniqueness.md#124-equality-in-the-upper-bound)
  - [12.5 Gerver's sofa is the closure of its interior](12-uniqueness.md#125-gervers-sofa-is-the-closure-of-its-interior)
  - [12.6 Proof of Theorem 12.1](12-uniqueness.md#126-proof-of-theorem-121)
- [13. The bridge to formal-conjectures](13-bridge.md)
  - [13.1 The two sets of definitions](13-bridge.md#131-the-two-sets-of-definitions)
  - [13.2 Coordinates and rigid motions](13-bridge.md#132-coordinates-and-rigid-motions)
  - [13.3 Moving sofas and the sofa constant](13-bridge.md#133-moving-sofas-and-the-sofa-constant)
  - [13.4 Gerver's constants and Romik's parameters](13-bridge.md#134-gervers-constants-and-romiks-parameters)
  - [13.5 The two Gerver's sofas](13-bridge.md#135-the-two-gervers-sofas)
  - [13.6 Formal-conjectures' theorems](13-bridge.md#136-formal-conjectures-theorems)
  - [13.7 The Challenge, the Solution and Comparator](13-bridge.md#137-the-challenge-the-solution-and-comparator)
- [Appendix A. Gerver's four constants](appendix-a.md)
  - [A.1 The reduced equations](appendix-a.md#a1-the-reduced-equations)
  - [A.2 The boundary of the domain](appendix-a.md#a2-the-boundary-of-the-domain)
  - [A.3 A first bound on φ](appendix-a.md#a3-a-first-bound-on-φ)
  - [A.4 The φ-derivative of Q](appendix-a.md#a4-the-φ-derivative-of-q)
  - [A.5 Every solution has φ < 1/20](appendix-a.md#a5-every-solution-has-φ--120)
  - [A.6 The residuals F and G](appendix-a.md#a6-the-residuals-f-and-g)
  - [A.7 Bounds on the strip](appendix-a.md#a7-bounds-on-the-strip)
  - [A.8 The signs of the partial derivatives](appendix-a.md#a8-the-signs-of-the-partial-derivatives)
  - [A.9 Uniqueness](appendix-a.md#a9-uniqueness)
- [Appendix B. Rigorous numerics for Gerver's sofa](appendix-b.md)
  - [B.1 Interval arithmetic](appendix-b.md#b1-interval-arithmetic)
  - [B.2 Romik's equations](appendix-b.md#b2-romiks-equations)
  - [B.3 The area of Gerver's sofa](appendix-b.md#b3-the-area-of-gervers-sofa)
  - [B.4 The generators](appendix-b.md#b4-the-generators)

## 1. Introduction

### 1.1 The problem

The hallway is the L-shaped region $L = H_L \cup V_L$, the union of its horizontal side
$H_L = (-\infty, 1] \times [0, 1]$ and its vertical side $V_L = [0, 1] \times (-\infty, 1]$. Both
sides have width 1, and they meet at the unit square $[0, 1]^2$; the origin is the inner corner of
the hallway and $(1, 1)$ its outer corner. Write $R_t$ for the counterclockwise rotation of the plane
by the angle $t$, and $|X|$ for the area (Lebesgue measure) of a set $X$.

A *moving sofa* is a closed, connected set $S$ in the plane that can be carried from the horizontal
side to the vertical side by a continuous rigid motion that never leaves the hallway: there are
continuous functions $\theta : [0, 1] \to \mathbb{R}$ and $c : [0, 1] \to \mathbb{R}^2$ with
$\theta(0) = 0$ such that the maps $\Phi_s(p) = R_{\theta(s)}\, p + c(s)$ satisfy

```math
\Phi_0(S) \subseteq H_L, \qquad \Phi_s(S) \subseteq L \text{ for every } s \in [0, 1], \qquad \Phi_1(S) \subseteq V_L.
```

The motion starts at a translation, so the sofa may sit anywhere in the plane; only its position at
time $s$ matters. The *moving sofa problem*, posed by Moser in 1966 [1], asks for

```math
\alpha_{\max} = \sup \lbrace \lvert S \rvert : S \text{ is a moving sofa} \rbrace,
```

and for the moving sofas that attain it; Figures 1.1 and 1.2 show the best one known, Gerver's sofa,
on its way around the corner. Closedness costs nothing, since the closure of a movable set moves
along the same motion; connectedness is part of the problem as Moser posed it. [Definition
2.4](02-preliminaries.md#definition-24-moving-sofa-and-rotation-angle-baek-definitions-112-and-233)
gives the definition in Lean, and the [Definitions](../definitions.md) page compares it with that of
formal-conjectures.

![The L-shaped hallway of unit width, with the horizontal side H on the left and the vertical side V at the bottom. Gerver's sofa, in blue, is halfway through its turn around the inner corner o, rotated by 45 degrees; dashed outlines show the sofa where its turn starts, pushed into the corner of the horizontal side, and where its turn ends, in the vertical side](figures/01-introduction/hallway.svg)

*Figure 1.1.* Gerver's sofa in the hallway. It slides along the horizontal side $H_L$ into the
corner (dashed, left), turns through a right angle around the inner corner $o$ (solid, halfway), and
leaves along the vertical side $V_L$ (dashed, bottom).

![An animation: Gerver's sofa slides to the right along the horizontal side of the hallway, turns clockwise around the inner corner through a right angle while touching both outer walls, and slides down the vertical side](figures/01-introduction/gerver-moving.gif)

*Figure 1.2.* The motion of Gerver's sofa: a slide, a turn through a right angle, and a slide.

A sofa that never turns lies at the start in a horizontal strip of width 1 and at the end in a
vertical one, so it fits in a unit square, and its area is at most 1. A sofa that turns can be much
longer, but seen from the sofa, the inner corner of the hallway traces a curve as the sofa turns, and
the sofa must keep clear of it. The sofas of largest known area all have a *niche*, a hollow in their
lower side that makes room for the corner.

### 1.2 The main theorems

**Gerver's sofa.** Seen from the sofa, the hallway turns around it. Fix the sofa and suppose that at
the moment it has turned by $t \in [0, \pi/2]$, the hallway occupies $\mathbf{x}(t) + R_t L$: the
hallway turned by $t$, with its inner corner at the point $\mathbf{x}(t)$. The curve
$\mathbf{x} : [0, \pi/2] \to \mathbb{R}^2$ is the *rotation path*, and a rotation path determines the
largest set that moves along it, the *shape* of the path: the set of points of the horizontal side
that lie in every turned hallway, and at the end in the turned vertical side,

```math
\operatorname{shape}(\mathbf{x}) = H_L \cap \bigcap_{t \in [0, \pi/2]} \bigl(\mathbf{x}(t) + R_t L\bigr) \cap \bigl(\mathbf{x}(\pi/2) + R_{\pi/2} V_L\bigr).
```

Romik [4] derived Gerver's sofa from differential equations that balance the sides of the sofa, and
found its rotation path in closed form. It is glued from five explicit curves, on the five phases
$[0, \varphi]$, $[\varphi, \theta]$, $[\theta, \pi/2 - \theta]$, $[\pi/2 - \theta, \pi/2 - \varphi]$ and
$[\pi/2 - \varphi, \pi/2]$, where $\varphi \approx 0.0392$ and $\theta \approx 0.6813$ are two angles.
Each curve is a rotated polynomial or trigonometric curve, and the 22 parameters of the five curves,
the two angles among them, solve a system of equations: Romik's equations (27)–(44), which make the
path start at the origin, symmetric and continuously differentiable across the phases, and impose two
contact conditions where the phases meet. *Gerver's sofa* $G$ is the shape of this rotation path (Figures 1.3 and 1.4). Chapter
10 gives the formulas.

![Gerver's sofa, a blue region between the lines y = 0 and y = 1, with a flat top, rounded ends, and a niche in the middle of its lower side; the niche is bounded by the orange rotation path, an arch from x(0) at the origin to x(pi/2) about 1.23 units to its left](figures/01-introduction/gerver-sofa.svg)

*Figure 1.3.* Gerver's sofa $G$ and its rotation path $\mathbf{x}$ (orange), from
$\mathbf{x}(0) = (0, 0)$ to $\mathbf{x}(\pi/2)$. The sofa lies between the lines $y = 0$ and
$y = 1$, and the path bounds its niche.

![Gerver's sofa in its own frame, in blue, inside the hallway turned by pi/4 about it, in grey: the two outer walls a and c meet at the outer corner y(pi/4) above the sofa and touch its rounded ends, and the two inner walls b and d meet at the inner corner x(pi/4), which lies at the top of the niche, on the orange rotation path](figures/01-introduction/supporting-hallway.svg)

*Figure 1.4.* The sofa's frame. At $t = \pi/4$ the hallway $\mathbf{x}(t) + R_t L$ (grey) contains
$G$: its outer walls $a(t)$ and $c(t)$ touch the sofa, and its inner corner $\mathbf{x}(t)$ lies on
the boundary of the niche. As $t$ runs from $0$ to $\pi/2$, the inner corner traces the rotation
path.

Romik solves the equations numerically and states that the solution is unique; the paper uses this
to define Gerver's sofa, and here it is proved.

#### Theorem 1.1 (Gerver's sofa is well defined)

Romik's equations (27)–(44) have exactly one solution with $\varphi \in [0.039, 0.04]$ and
$\theta \in [0.68, 0.69]$, and Gerver's sofa $G$, the shape of its rotation path, has area
$2.2192 \le \lvert G \rvert \le 2.2199$.

*Proof.* Theorems [10.8](10-gerver.md#theorem-108-gervers-sofa-is-well-defined-romik-section-4) and
[10.21](10-gerver.md#theorem-1021-the-area-of-gervers-sofa); Appendix B gives the rigorous numerics behind both. $\square$

*Lean: [`Baek.gerver_params_exists`](../../Challenge.lean#L328), [`Baek.gerver_params_unique`](../../Challenge.lean#L332), [`Baek.gerver_sofa_area`](../../Challenge.lean#L338).*

Gerver's value of the area is $\lvert G \rvert = 2.21953166887\ldots$ [3, 4]; the bounds of Theorem
1.1 identify the set defined from Romik's equations with the sofa that Gerver found.

#### Theorem 1.2 (optimality; Baek, Theorem 1.1.1)

Gerver's sofa $G$ is a moving sofa, and every moving sofa $S$ has $\lvert S \rvert \le \lvert G \rvert$.
So $\alpha_{\max} = \lvert G \rvert$.

*Proof.* This is [Theorem 9.33](09-optimality.md#theorem-933-optimality-of-gervers-sofa-baek-theorem-111). $\square$

*Lean: [`Baek.gerver_sofa_optimal`](../../Challenge.lean#L344), [`MovingSofaOptimality.theorem1_1_1`](../../MovingSofaOptimality/Main.lean#L318).*

#### Theorem 1.3 (uniqueness)

Let $S$ be a moving sofa with $\lvert S \rvert = \lvert G \rvert$. Then there are an angle $\theta$ and
a vector $v$ such that

```math
R_\theta S + v = G.
```

*Proof.* This is [Theorem 12.1](12-uniqueness.md#theorem-121-uniqueness-of-gervers-sofa), proved in
[§12.6](12-uniqueness.md#126-proof-of-theorem-121) from the results of Chapters 11 and 12. $\square$

*Lean: [`Baek.gerver_sofa_unique`](../../Challenge.lean#L351), [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L233).*

*Remarks.* (i) With Theorem 1.2, the moving sofas of maximum area are exactly the moving sofas that
a rotation and a translation map onto $G$. Not every rotated copy of $G$ is a moving sofa: a motion
starts at a translation, and a turned copy of $G$ need not fit in the horizontal side. (ii) The
theorem is about sets, not about sets up to measure zero: a closed set with the area of $G$ that
moves around the corner is a copy of $G$, point for point. (iii) Reflections are not needed, since
Gerver's sofa is symmetric under the reflection in a vertical line. (iv) Baek's paper does not
consider uniqueness. The proof given here was written for this formalization (§1.3).

**The bridge to formal-conjectures.** Google DeepMind's formal-conjectures [8] states the moving
sofa problem with definitions of its own. A moving sofa there comes with its motion, a continuous
path of isometries of $\mathbb{R}^2$ that starts at the identity, so the sofa itself lies in $H_L$;
the *sofa constant* is the supremum of the areas of such sofas; and Gerver's sofa is defined from
Gerver's own description [3]: four constants $A$, $B$, $\varphi$, $\theta$ that solve four
equations, a radius function on $[0, \pi/2]$, and a rotation path given by integrals of it.

#### Theorem 1.4 (the bridge)

1. A set $s \subseteq \mathbb{R}^2$ is a moving sofa in the sense of formal-conjectures if and only
   if $s \subseteq H_L$ and $s$ is a moving sofa.
2. The sofa constant of formal-conjectures equals $\alpha_{\max}$.
3. Gerver's four equations have exactly one solution, and the Gerver's sofa that formal-conjectures
   defines from it is $G$.

*Proof.* Part 1 is Theorem [13.9](13-bridge.md#theorem-139-the-two-notions-of-moving-sofa-agree), part 2 Theorem
[13.10](13-bridge.md#theorem-1310-the-two-optimal-areas-agree), and part 3 Theorems
[13.13](13-bridge.md#theorem-1313-gervers-system-has-exactly-one-solution) and
[13.19](13-bridge.md#theorem-1319-the-two-gervers-sofas-agree), with [Appendix A](appendix-a.md) for the uniqueness of the
solution. $\square$

*Lean: [`Bridge.isMovingSofa_iff`](../../Challenge.lean#L363), [`Bridge.sofaConstant_eq`](../../Challenge.lean#L371), [`Bridge.gerversSofa_eq`](../../Challenge.lean#L379),
[`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`](../../Challenge.lean#L272).*

#### Corollary 1.5 (formal-conjectures' statements)

In the definitions of formal-conjectures: Gerver's sofa is a moving sofa whose area is the sofa
constant; and a moving sofa has area equal to the sofa constant if and only if an isometry of the
plane maps Gerver's sofa onto it.

*Proof.* By Theorem 1.4, the sofa constant is $\alpha_{\max}$, which is $\lvert G \rvert$ by Theorem
1.2, and formal-conjectures' Gerver's sofa is $G$, which lies in $H_L$ and is a moving sofa. If a
moving sofa $s$ has area $\lvert G \rvert$, it is a moving sofa in Baek's sense by Theorem 1.4(1),
so Theorem 1.3 gives a rotation and a translation that map it onto $G$, and the inverse map, an
isometry, maps $G$ onto $s$. Conversely, an isometry preserves area. Theorem
[13.20](13-bridge.md#theorem-1320-formal-conjectures-theorems) gives the details. $\square$

*Lean: [`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](../../Challenge.lean#L388),
[`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](../../Challenge.lean#L392),
[`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../../Challenge.lean#L396).*

formal-conjectures marks the first statement solved and the second, the uniqueness, open.

### 1.3 Background

Moser posed the problem in 1966 [1]. Hammersley [2] found a sofa of area
$\pi/2 + 2/\pi \approx 2.2074$, a quarter-disk of radius 1 on each side of a $4/\pi \times 1$
rectangle from which a half-disk of radius $2/\pi$ is removed, and showed that $\alpha_{\max} \le 2\sqrt2$.
Gerver [3] found a sofa of area $2.21953\ldots$, bounded by 18 analytic curves and segments, and
conjectured that it is optimal. His Theorem 1 states a balance condition that a sofa of maximum area
satisfies, and his Theorem 2 shows that his sofa satisfies it. Romik [4] derived Gerver's sofa from
differential equations that express the balance, and solved them in closed form; his description
defines Gerver's sofa here. Kallus and Romik [5] proved by a computer-assisted method that
$\alpha_{\max} \le 2.37$. Baek [6] proved that $\alpha_{\max} = \lvert G \rvert$, in a paper of 119
pages that needs a computer only for numerical evaluations that a scientific calculator can do.
Chapters 2 to 10 follow Baek's proof.

That Gerver's sofa is the only moving sofa of maximum area is not proved in Baek's paper, and
formal-conjectures lists it as an open problem. The proof of Chapters 11 and 12 was written for this
formalization, by an AI model, ChatGPT Pro 6, in October 2026 (see [Contributors](../contributors.md)); it
reuses Baek's machinery and has not been peer reviewed. We know of no earlier proof, but have not
searched the literature systematically. Two earlier Lean formalizations of Baek's proof prove
formal-conjectures' statement of the optimality, but not the uniqueness; the
[prior work](../prior-work.md) page compares them with this one.

### 1.4 Outline of the proof

**Monotone sofas** (Chapters 2 and 3). Every moving sofa of area at least $2.2$ can be moved with a
rotation angle $\omega \in [\sec^{-1}(2.2), \pi/2]$, the angle through which it has turned when it
reaches the vertical side (Baek's Theorem 1.5.1). For each $t \in [0, \omega]$, push the hallway
turned by $t$ against the sofa until both outer walls touch it: this is the *supporting hallway*
$L_t$, with inner corner $\mathbf{x}(t)$, as in Figure 1.4. The intersection of the strip $H =
\mathbb{R} \times [0, 1]$, the supporting hallways and a final strip is again a moving sofa, and it
contains a translate of the sofa; so a maximum sofa may be taken *monotone*, equal to that
intersection. A monotone sofa is $K \setminus \mathcal{N}(K)$: its *cap* $K$, the convex body cut
out by the outer walls, minus its *niche* $\mathcal{N}(K)$, the part of $K$ cut away by the inner
corners of the supporting hallways (Figure 1.5). The problem becomes the maximization of the *sofa
area functional*

```math
\mathcal{A}_\omega(K) = \lvert K \rvert - \lvert \mathcal{N}(K) \rvert
```

over the caps $K$ of rotation angle $\omega$. The area of the cap is a quadratic functional of $K$,
but the area of the niche has no tractable formula: the inner corner may trace a complicated curve.

![Three panels for Gerver's sofa. (a) The cap K, light blue, below the grey outer walls of nine supporting hallways, whose envelope is the top and the rounded ends of K. (b) The niche N(K), orange, an arch on the floor below the orange rotation path x(t), with nine inner corners marked and the dashed walls of their quarter-planes; the cap is outlined dashed around it. (c) The sofa S, the cap minus the niche](figures/03-monotone/cap-niche.svg)

*Figure 1.5.* Gerver's sofa as a monotone sofa (Figure 3.4): (a) its cap $K$, cut out by the outer
walls of the supporting hallways; (b) its niche $\mathcal{N}(K)$, cut out by their inner corners
$\mathbf{x}(t)$; (c) the sofa $K \setminus \mathcal{N}(K)$.

**Balanced maximum sofas and the rotation angle** (Chapters 4 and 5). Keep only the supporting
hallways of the angles of a finite set $\Theta$: the cap becomes a polygon cap, the niche a polygon
niche, and the polygon area functional $\mathcal{A}_\Theta(K) = \lvert K \rvert - \lvert
\mathcal{N}_\Theta(K) \rvert$ has a maximizer. A maximum polygon cap is *balanced*: in every
direction, the sides of the cap and the niche with that outer normal have the same total length as
those with the opposite normal, since otherwise translating one hallway would increase the area.
This is Gerver's balancing argument [3]; Baek runs it on caps rather than on polygon sofas, which
closes a gap in Gerver's proof, where pushing a hallway can disconnect the sofa. As $\Theta$ fills
$[0, \omega]$, the maximum polygon caps converge to a maximum cap (Figure 1.6), the cap of a
*balanced maximum sofa*, which has the largest area among the monotone sofas of rotation angle
$\omega$. Elementary geometry with the balance shows that a balanced maximum sofa of area at least
$2.2$ can be turned through the full right angle (Baek's Theorem 1.5.2). So a maximum sofa may be
taken balanced, with $\omega = \pi/2$.

![Three rows, for n = 4, 8 and 16, each showing a blue polygon sofa between faint lines y = 0 and y = 1 with a dashed outline of Gerver's sofa centred on the same vertical line. For n = 4 the polygon sofa is visibly wider, with straight slanted ends and a jagged notch; for n = 8 it is closer; for n = 16 its ends and its notch nearly follow the dashed outline](figures/04-balanced/limit.svg)

*Figure 1.6.* Maximum polygon sofas for $\omega = \pi/2$ and $n = 4$, $8$ and $16$ equally spaced
angles, computed numerically (Figure 4.7), approaching Gerver's sofa (dashed). Their areas $2.4148$,
$2.3027$ and $2.2584$ decrease towards $\lvert G \rvert = 2.2195$.

**The injectivity condition** (Chapters 6 and 7). The *surface area measure* $\sigma_K$ of a convex
body records the lengths of its sides by their normal angles, and gives the area by Schneider's
formula $\lvert K \rvert = \frac12 \int h_K \, d\sigma_K$, where $h_K$ is the support function. The
balance of the maximum polygon caps passes to the limit as a differential inequality on the balanced
maximum sofa,

```math
\sigma_K \le k_0\bigl(g(t)\bigr)\, dt \quad \text{on } [0, \pi/2), \qquad k_0(x) = \max\bigl(\lvert x - 1 \rvert, (\lvert x - 1 \rvert + 1)/2\bigr),
```

where $g(t)$ and its mirror $f(t)$ are the *arm lengths*, the distances from the outer corner of
$L_t$ to the points where the sofa touches the two outer walls. The inner corner moves with velocity
$\mathbf{x}'(t) = -(f(t) - 1)\, u_t + (g(t) - 1)\, v_t$, where $u_t = (\cos t, \sin t)$ and
$v_t = (-\sin t, \cos t)$. Starting from the trivial bounds $f, g \ge 0$, the inequality yields
better and better lower bounds, and after eleven rounds $f, g > 1$ on $(0, \pi/2)$. Then the
inner corner moves strictly to the left as $t$ increases, so its path is a simple arc: this is the
*injectivity condition* (Figure 1.7), Baek's key property, and $\mathcal{K}^\mathrm{i}$ denotes the
caps that satisfy it.

![The cap K of Gerver's sofa, with its niche shaded orange under an arch, and the rotation path x drawn thick in orange from x(0) on the right to x(π/2) on the left, along the top of the niche. At three points of the path, t = π/8, π/4 and 3π/8, a small green quadrant is shaded between the directions −u_t and v_t, and the velocity x'(t), drawn as a black arrow, points into it](figures/07-injectivity/rotation-path.svg)

*Figure 1.7.* The injectivity condition for Gerver's sofa (Figure 7.2): the velocity
$\mathbf{x}'(t)$ lies between the directions $-u_t$ and $v_t$ (green), so the inner corner moves
to the left, from $\mathbf{x}(0) = (0, 0)$ to $\mathbf{x}(\pi/2) \approx (-1.228, 0)$, and its path
does not cross itself.

**The upper bound** (Chapters 8 and 9). For a monotone sofa with the injectivity condition, Baek
replaces the niche by a smaller region of the same shape as the niche of Gerver's sofa: a core,
traced by the inner corner over $[\varphi, \pi/2 - \varphi]$, and two tails, swept by the inner
walls. The area of the cap minus this region is an upper bound $\mathcal{Q}$ for the area of the
sofa, equal to it for Gerver's sofa. Unlike the area, $\mathcal{Q}$ is a quadratic functional of
three convex bodies, the cap $K$ and two bodies $B$ and $D$ that bound the tails, on a convex domain
$\mathcal{L}$ of such triples. *Mamikon's theorem*, that the region swept by tangent segments of
length $\ell(t)$ to a convex curve has area $\frac12 \int \ell(t)^2 \, dt$, writes $\mathcal{Q}$ as
a linear functional minus a sum of such areas, which are convex in the triple (Figure 1.8); so
$\mathcal{Q}$ is concave. Romik's equations make the directional derivatives of $\mathcal{Q}$ at the
triple of Gerver's sofa nonpositive in every direction of $\mathcal{L}$, so Gerver's sofa maximizes
$\mathcal{Q}$, and for a balanced maximum sofa $S$ of rotation angle $\pi/2$, which satisfies the
injectivity condition,

```math
\lvert S \rvert \le \mathcal{Q}(K_S, B_S, D_S) \le \mathcal{Q}(K_G, B_G, D_G) = \lvert G \rvert.
```

A balanced maximum sofa has the largest area of all moving sofas, so this proves Theorem 1.2.

![Gerver's cap K, light blue, with the core part of its niche white under the orange core, and four purple regions swept by tangent segments: a thin fan at the bottom right corner, a large fan from the right side and top of the cap up to a purple arch traced by the outer corner, a thin wedge above the top edge, and segments from the left side of the cap to a vertical line. A bold black outline encloses the cap and the four regions, minus the core part of the niche](figures/09-optimality/mamikon-cap.svg)

*Figure 1.8.* The concavity of $\mathcal{Q}$ for Gerver's cap (Figure 9.5). The regions swept by
tangent segments (purple) have areas $\frac12 \int \ell(t)^2 \, dt$, convex in the cap by
Mamikon's theorem, and together with the region of area $\mathcal{Q}$ they fill a region (bold
outline) whose area is linear in the cap.

**Gerver's sofa** (Chapter 10 and Appendix B). The proof uses the structure of Gerver's sofa: that
it is a monotone sofa with the injectivity condition, which of the walls of $L_t$ touch it on each
phase, and that its niche has the shape of the core and two tails, so that $\mathcal{Q}$ equals its
area. Baek's paper states this structure (its Theorem 8.4.1) without proof. Here it is proved from
Romik's equations, with rigorous bounds on Romik's parameters and interval arithmetic for the
inequalities that hold only numerically.

**Uniqueness** (Chapters 11 and 12). Baek's argument shows that *some* maximum sofa, a balanced one,
turns through a right angle and satisfies the injectivity condition; a maximum sofa given in
advance need not be a limit of maximum polygon sofas. The uniqueness proof gives these properties
to every maximum sofa. Let $S$ be a moving sofa with $\lvert S \rvert = \lvert G \rvert$; the proof
follows $S$ through a chain of rigid motions and monotonizations (Figure 1.9).

1. *Monotonization.* $S$ moves with a rotation angle $\omega \in [\sec^{-1}(2.2), \pi/2]$, and a
   translate of $S$ lies in a monotone sofa $T$ of rotation angle $\omega$ and the same area, whose
   cap $K$ maximizes $\mathcal{A}_\omega$.
2. *Selection.* Polygon caps that maximize the sofa area minus a penalty for straying from $K$
   converge to $K$ itself (note 20, Proposition 1).
3. *Variations.* Moving one side of a selected polygon gives inequalities between its side lengths
   that survive the limit as bounds on the sides of $K$ (Proposition 2).
4. *The right angle.* If $\omega < \pi/2$, these bounds give $T$ width at most 1 in the directions
   $u_t$, $t \in [\omega, \pi/2]$, that the turn has not reached, so a rotated copy of $T$ can turn
   through a right angle; monotonizing again gives a monotone sofa $U$ of rotation angle $\pi/2$ and
   area $\lvert G \rvert$ that contains a rigid image of $S$ (Proposition 4). If $\omega = \pi/2$,
   take $U = T$.
5. *Injectivity.* Applied to the cap of $U$, the selection and the variations give the curvature
   bound $\sigma_K \le k_0(g(t))\, dt$, and Baek's iteration then gives the injectivity condition
   (Proposition 3).
6. *Rigidity.* Now $\lvert U \rvert \le \mathcal{Q}(U) \le \mathcal{Q}(G) = \lvert G \rvert = \lvert U \rvert$,
   so both inequalities are equalities. Along the segment from Gerver's triple to that of $U$, the
   concave $\mathcal{Q}$ is then constant, and its concavity gap, a sum of the squared differences
   of Mamikon's tangent lengths, vanishes. So the tangent lengths of $U$ and $G$ agree, which forces
   the support functions of their caps to differ by a horizontal translation: $U = G + (b, 0)$
   (Proposition 5).
7. *Recovery.* Gerver's sofa is the closure of its interior (Proposition 6). A closed subset of $G$
   with the area of $G$ contains the interior of $G$, since the rest of the interior is an open set
   of measure zero, and so it is all of $G$. The rigid image of $S$ in $U$ is therefore all of $U$.

![A flow chart of five boxes joined by downward arrows: S, a moving sofa with the area of G; S + v0 contained in T, a monotone sofa of angle ω whose cap maximizes the sofa area; R_a(S + v0) contained in R_a T, which moves with angle π/2; g1(S) contained in U = G + (b, 0); and g(S) = G. The arrows are labelled translate and monotonize, rotate by a, translate and monotonize, and translate by (−b, 0)](figures/12-uniqueness/chain.svg)

*Figure 1.9.* The uniqueness proof as a chain of rigid motions (Figure 12.1). Every box contains
the image of $S$ under the maps so far, and every set has area $\lvert G \rvert$.

**The bridge** (Chapter 13 and Appendix A). A continuous path of isometries that starts at the
identity consists of orientation-preserving isometries, whose angle of rotation lifts to a
continuous real function; this matches the two notions of moving sofa. Gerver's four equations have
a unique solution, proved by elementary inequalities, and Romik's parameters are explicit functions
of Gerver's four constants. formal-conjectures' rotation path, given by integrals, is Romik's path
seen in a rotating frame, so the two Gerver's sofas are the same set.

### 1.5 This text and the formalization

Chapters 2 to 10 follow Baek's paper: Chapters 2 and 3 its Chapter 2, with the definitions of its
Chapter 1; Chapters 4 to 9 its Chapters 3 to 8, in order; and Chapter 10 what the paper states about
Gerver's sofa, its Section 8.4 and Theorem 6.1.2, with Romik's description of the sofa. Chapters 11
and 12 prove the uniqueness, following the informal proof written for this formalization ("note 20",
in the [archive](../archive/uniqueness/20-complete-paper-proof.md)), and Chapter 13 and Appendix A
prove the bridge. Appendix B explains the rigorous numerics. Definitions, lemmas, propositions,
theorems and corollaries are numbered together within each chapter; figures and tables separately. A
result of Baek's paper carries the paper's number in its name, as in "Theorem 1.2 (optimality; Baek,
Theorem 1.1.1)", and a step of the uniqueness proof the number of its proposition in note 20.

Every numbered statement ends with a line *Lean: …* naming the Lean 4 declarations [9, 10] that
state and prove it, linked to their source. The proofs here follow the formal proofs, but are
written for a human reader, and the longest of them are given as sketches that state the steps and
the key estimates and say where the full argument is. Where a statement of Baek's paper is false as
printed, the text states and proves the intended version and says so; the audit in
[`REPORT.md`](../../REPORT.md) lists every such correction. The formal proofs are checked by Lean's
kernel; the [verification](../verification.md) page explains how to build them and audit their
axioms. The figures are computed from the same definitions by the scripts in
[`scripts/figures/`](../../scripts/figures).

### References

1. L. Moser. Problem 66-11, Moving furniture through a hallway. *SIAM Review* 8 (1966) 381.
2. J. M. Hammersley. On the enfeeblement of mathematical skills by "Modern Mathematics" and by
   similar soft intellectual trash in schools and universities. *Bull. Inst. Math. Appl.* 4 (1968)
   66–85.
3. J. L. Gerver. On moving a sofa around a corner. *Geom. Dedicata* 42 (1992) 267–283.
   [doi:10.1007/BF02414066](https://doi.org/10.1007/BF02414066)
4. D. Romik. Differential equations and exact solutions in the moving sofa problem. *Exp. Math.* 27
   (2018) 316–330. [doi:10.1080/10586458.2016.1270858](https://doi.org/10.1080/10586458.2016.1270858)
5. Y. Kallus, D. Romik. Improved upper bounds in the moving sofa problem. *Adv. Math.* 340 (2018)
   960–982. [doi:10.1016/j.aim.2018.10.022](https://doi.org/10.1016/j.aim.2018.10.022)
6. J. Baek. Optimality of Gerver's sofa. [arXiv:2411.19826v1](https://arxiv.org/abs/2411.19826v1) (2024).
7. R. Schneider. *Convex Bodies: The Brunn–Minkowski Theory*, 2nd edition. Encyclopedia of
   Mathematics and its Applications 151, Cambridge University Press, 2013.
   [doi:10.1017/CBO9781139003858](https://doi.org/10.1017/CBO9781139003858)
8. Google DeepMind. formal-conjectures, `FormalConjectures/Wikipedia/MovingSofa.lean`.
   <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean>
9. The mathlib Community. The Lean mathematical library. In *Proceedings of the 9th ACM SIGPLAN
   International Conference on Certified Programs and Proofs (CPP 2020)*, 367–381.
   [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824)
10. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming language. In *Automated
    Deduction – CADE 28*, Lecture Notes in Computer Science 12699 (2021), 625–635.
    [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37)
