# 2. Preliminaries

[Contents](README.md) · [← 1. Introduction](README.md#1-introduction) · [3. Monotone sofas, caps and niches →](03-monotone.md)

This chapter fixes the notation of the plane, defines the hallway and moving sofas
([Definitions 2.3](#definition-23-the-hallway-baek-definition-111) and
[2.4](#definition-24-moving-sofa-and-rotation-angle-baek-definitions-112-and-233)), and collects
the facts about planar convex bodies that the whole proof uses: the support function, edges and
vertices, the one-sided continuity of the vertices (Theorem 2.9, Baek's Theorem 2.1.3), the
Hausdorff distance and Blaschke's selection theorem (§2.3). It then puts a moving sofa in standard
position (§2.4) and defines its supporting hallways, Baek's §2.2 (§2.5).

Two facts prepare the next chapter. Seen in its own frame of reference, a moving sofa that turns by
the angle $\omega$ lies, for every $t \in [0, \omega]$, in some copy of the hallway turned by $t$
([Proposition 2.15](#proposition-215-the-sofa-in-its-own-frame-baek-proposition-122)); and a
compact set that lies in such a copy lies in the *supporting hallway* $L_S(t)$, the copy whose two
outer walls touch it
([Proposition 2.20](#proposition-220-the-supporting-hallway-contains-the-sofa-baek-proposition-223)).
So a moving sofa lies in all its supporting hallways, and [Chapter 3](03-monotone.md) studies their
intersection.

## 2.1 The plane

The plane is $\mathbb{R}^2$ with points $p = (x, y)$; the variables $x$ and $y$ always denote the
two coordinates. Angles are real numbers. Baek takes the angles of normals on the circle
$S^1 = \mathbb{R}/2\pi\mathbb{Z}$; here every function of such an angle is $2\pi$-periodic, and an
interval of $S^1$ is read as an interval of $\mathbb{R}$.

### Definition 2.1 (the plane; Baek, Definitions 1.1.3, 2.1.3 and 2.3.1)

The inner product of $p$ and $q$ is $\langle p, q \rangle$ (Baek writes $p \cdot q$), and the
*area* $\lvert X \rvert$ of a set $X \subseteq \mathbb{R}^2$ is its Lebesgue measure. For an angle
$t$, the unit vectors $u_t$ and $v_t$ and the counterclockwise rotation $R_t$ by $t$ are

```math
u_t = (\cos t, \sin t), \qquad v_t = (-\sin t, \cos t), \qquad R_t(x, y) = (x \cos t - y \sin t,\ x \sin t + y \cos t) .
```

So $(u_t, v_t)$ is the standard frame turned by $t$, and $v_t = u_{t + \pi/2}$,
$R_s u_t = u_{t + s}$, $R_s v_t = v_{t + s}$. Every vector decomposes in this frame, and the frames of
two angles are related by

```math
p = \langle p, u_t \rangle\, u_t + \langle p, v_t \rangle\, v_t, \qquad \langle u_s, u_t \rangle = \cos(s - t), \qquad \langle u_s, v_t \rangle = \sin(s - t) .
```

*Lean: [`MovingSofaOptimality.uvec`](../../MovingSofaOptimality/Basic/Plane.lean#L26), [`MovingSofaOptimality.vvec`](../../MovingSofaOptimality/Basic/Plane.lean#L29), [`MovingSofaOptimality.dot`](../../MovingSofaOptimality/Basic/Plane.lean#L32),
[`MovingSofaOptimality.rot`](../../MovingSofaOptimality/Basic/Plane.lean#L39), [`MovingSofaOptimality.area`](../../MovingSofaOptimality/Basic/Plane.lean#L59), [`uvec_add_pi_div_two`](../../MovingSofaOptimality/Basic/Plane.lean#L152), [`rot_uvec`](../../MovingSofaOptimality/Basic/Plane.lean#L191),
[`eq_dot_uvec_smul_add`](../../MovingSofaOptimality/Basic/Plane.lean#L177), [`dot_uvec_uvec`](../../MovingSofaOptimality/Basic/Plane.lean#L140), [`dot_uvec_vvec'`](../../MovingSofaOptimality/Basic/Plane.lean#L146).*

The area is defined for every set, as the real number $\lvert X \rvert = \mathrm{vol}(X)$, and is
meaningful for bounded measurable sets, the only sets whose area the proof takes.

### Definition 2.2 (lines and half-planes; Baek, Definitions 2.1.4 and 2.1.5)

For an angle $t$ and a real number $h$, the *line* with normal angle $t$ at signed distance $h$ from
the origin, and the closed and open half-planes it bounds, are

```math
l(t, h) = \lbrace p : \langle p, u_t \rangle = h \rbrace, \qquad H_-(t, h) = \lbrace p : \langle p, u_t \rangle \le h \rbrace, \qquad H_-^\circ(t, h) = \lbrace p : \langle p, u_t \rangle < h \rbrace ,
```

and $H_+(t, h)$, $H_+^\circ(t, h)$ are the half-planes where $\langle p, u_t \rangle \ge h$ and
$> h$. The half-planes $H_-(t, h)$ and $H_-^\circ(t, h)$ have *normal angle* $t$, their outer
normal being $u_t$; since $H_+(t, h) = H_-(t + \pi, -h)$, the half-planes $H_\pm$ have the normal
angle $t + \pi$ (Figure 2.1).

![The unit vectors u_t and v_t drawn as arrows from the origin O, with the angle t marked between the x-axis and u_t and the unit circle dashed; the line l(t, h) runs perpendicular to u_t, at the end of a dashed segment of length h from O along u_t, and the half-plane H minus of t, h, on the side of the line that contains O, is shaded blue, the other side being H plus](figures/02-preliminaries/frame.svg)

*Figure 2.1.* The frame $u_t, v_t$ and the line $l(t, h)$, which meets the ray from $O$ in the
direction $u_t$ at the distance $h$. The half-plane $H_-(t, h)$ (shaded) contains $O$ when
$h > 0$.

*Lean: [`line`](../../MovingSofaOptimality/Basic/Plane.lean#L43), [`halfMinus`](../../MovingSofaOptimality/Basic/Plane.lean#L46), [`halfMinusOpen`](../../MovingSofaOptimality/Basic/Plane.lean#L49), [`halfPlus`](../../MovingSofaOptimality/Basic/Plane.lean#L52), [`halfPlusOpen`](../../MovingSofaOptimality/Basic/Plane.lean#L55).*

## 2.2 The hallway and moving sofas

### Definition 2.3 (the hallway; Baek, Definition 1.1.1)

The *hallway* is $L = H_L \cup V_L$, the union of its *horizontal side* and its *vertical side*

```math
H_L = (-\infty, 1] \times [0, 1], \qquad V_L = [0, 1] \times (-\infty, 1] .
```

Its *inner corner* is the origin and its *outer corner* is $(1, 1)$ (Figure 2.2). A point
$(x, y)$ lies in $L$ if and only if

```math
x \le 1, \qquad y \le 1, \qquad x \ge 0 \ \text{ or } \ y \ge 0 .
```

*Lean: [`horizSide`](../../MovingSofaOptimality/Sofa/Defs.lean#L30), [`vertSide`](../../MovingSofaOptimality/Sofa/Defs.lean#L33), [`MovingSofaOptimality.hallway`](../../MovingSofaOptimality/Sofa/Defs.lean#L36), [`Baek.hallway`](../../Challenge.lean#L101),
[`ms_mem_hallway_iff`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L63).*

### Definition 2.4 (moving sofa and rotation angle; Baek, Definitions 1.1.2 and 2.3.3)

Let $S \subseteq \mathbb{R}^2$ and $\omega \in \mathbb{R}$. A *movement* of $S$ with *rotation angle*
$\omega$ is a pair of functions $\theta : [0, 1] \to \mathbb{R}$ and $c : [0, 1] \to \mathbb{R}^2$,
continuous on $[0, 1]$, with $\theta(0) = 0$ and $\theta(1) = -\omega$, such that the rigid motions
$\Phi_s(p) = R_{\theta(s)}\, p + c(s)$ satisfy

```math
\Phi_0(S) \subseteq H_L, \qquad \Phi_s(S) \subseteq L \ \text{ for every } s \in [0, 1], \qquad \Phi_1(S) \subseteq V_L .
```

A *moving sofa with rotation angle* $\omega$ is a closed and connected (in particular nonempty) set
that has a movement with rotation angle $\omega$, and a *moving sofa* is a set that is a moving sofa
with some rotation angle.

![The hallway L, with its horizontal side H_L on the left and its vertical side V_L at the bottom, the inner corner (0, 0) and the outer corner (1, 1); Gerver's sofa is drawn solid as Phi one half of S, turned by 45 degrees around the corner, and dashed as Phi zero of S in the horizontal side and as Phi one of S in the vertical side, turned by a right angle](figures/02-preliminaries/hallway.svg)

*Figure 2.2.* Gerver's sofa $S$ moving in the hallway, with rotation angle $\omega = \pi/2$: at the
start $\Phi_0(S) \subseteq H_L$ (dashed), halfway $\Phi_{1/2}(S)$, turned clockwise by $\pi/4$, and
at the end $\Phi_1(S) \subseteq V_L$ (dashed), turned clockwise by $\pi/2$.

*Lean: [`IsMovement`](../../MovingSofaOptimality/Sofa/Defs.lean#L43), [`IsMovingSofaWithAngle`](../../MovingSofaOptimality/Sofa/Defs.lean#L54), [`MovingSofaOptimality.IsMovingSofa`](../../MovingSofaOptimality/Sofa/Defs.lean#L59),
[`Baek.IsMovingSofa`](../../Challenge.lean#L105), [`Baek.isMovingSofa_iff_lib`](../../Solution.lean#L31).*

Baek's Definition 1.1.2 asks that $S$ be a translate of a nonempty, connected and closed subset of
$H_L$ that a continuous curve $\Phi_s$ in the group $\mathrm{SE}(2)$ of orientation-preserving
isometries, with $\Phi_0$ a translation, moves inside $L$ from $H_L$ to $V_L$ (the paper's
footnotes). Every orientation-preserving isometry is $p \mapsto R_\theta\, p + c$, and the angle of
a continuous curve in $\mathrm{SE}(2)$ lifts to a continuous real function, by path lifting in the
circle; as $\Phi_0$ is a translation, the lift may start at $\theta(0) = 0$. So the two definitions
agree. The formalization takes the lifted form from the start;
[Chapter 13](13-bridge.md) proves the lifting for the motions of formal-conjectures, which are
paths of isometries. Baek's rotation angle (Definition 2.3.3) is the clockwise angle
$\theta(0) - \theta(1) = -\theta(1)$ through which the sofa turns. The Challenge states the
definition in Mathlib's vocabulary as [`Baek.IsMovingSofa`](../../Challenge.lean#L105), which leaves $\theta(1)$ free, and
[`Baek.isMovingSofa_iff_lib`](../../Solution.lean#L31) identifies it with [`MovingSofaOptimality.IsMovingSofa`](../../MovingSofaOptimality/Sofa/Defs.lean#L59).

*Remark.* The rotation angle belongs to the movement, not to the set: a disk of diameter 1 has
movements with every rotation angle. "A moving sofa $S$ with rotation angle $\omega$" means a set
together with the existence of a movement of rotation angle $\omega$, as in the Lean predicate
[`IsMovingSofaWithAngle`](../../MovingSofaOptimality/Sofa/Defs.lean#L54); the paper speaks of "the" rotation angle with this meaning.

Baek's Theorem 1.5.1 ([Chapter 5](05-rotation-angle.md)) shows that a moving sofa of area at least
$2.2$ has a movement with rotation angle $\omega \in [\sec^{-1}(2.2), \pi/2]$, where
$\sec^{-1}(2.2) = 1.09893\ldots$, about $63^\circ$ ([`theorem1_5_1`](../../MovingSofaOptimality/Intro/RotationAngleBound.lean#L163)). Gerver's sofa has area
$2.21953\ldots > 2.2$, so a moving sofa of maximum area has a movement with
$\omega \in (0, \pi/2]$, and from §2.4 on the rotation angle lies in $(0, \pi/2]$.

### Proposition 2.5 (moving sofas are compact)

Every moving sofa is bounded, and hence compact.

*Proof sketch.* Let $\theta, c$ be a movement of $S$. At time $0$ the sofa is the translate
$S + c(0)$ of a subset of $H_L$, so the coordinate $y$ is bounded on $S$, by some $Y$, and $x$ is
bounded above. It remains to bound $x$ from below. If $\theta(1) = 0$, the final position
$S + c(1) \subseteq V_L$ does it. If $\theta(1) < 0$, the intermediate value theorem gives a time
$s$ with $\theta(s) = \varphi$ for an angle $\varphi \in [-\frac12, 0)$; then every point of
$R_\varphi S + c(s)$ has $y \le 1$, and the $y$-coordinate of $R_\varphi p + c(s)$ is
$x \sin\varphi + y\cos\varphi + c_2(s)$ for $p = (x, y)$, with $\sin \varphi < 0$ and
$\lvert y \rvert \le Y$; this bounds $x$ from below. If $\theta(1) > 0$, the movement passes through
an angle $\varphi \in (0, \frac12]$; then $R_\varphi S + c(s)$ avoids the open quarter-plane
$(-\infty, 0)^2$, which $L$ avoids, and for $x$ very negative both coordinates of
$R_\varphi p + c(s)$ would be negative. A closed bounded set is compact. $\square$

*Lean: [`isBounded_of_isMovingSofa`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L265), [`isCompact_of_isMovingSofa`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L331).*

The paper takes areas and support functions of moving sofas without saying that they are bounded;
Proposition 2.5 supplies this. A translate of a moving sofa with rotation angle $\omega$ is again
one, with the movement $p \mapsto \Phi_s(p - v)$ ([`mpc_isMovingSofaWithAngle_translate`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L626)).

## 2.3 Planar convex bodies

### Definition 2.6 (convex body, support function; Baek, Definitions 2.1.1 and 2.1.6–2.1.8)

A (planar) *convex body* is a nonempty, compact and convex subset of $\mathbb{R}^2$. Its interior
may be empty: a segment and a point are convex bodies. For a nonempty compact set $S$ and an angle
$t$, the *support function* $h_S$, the *supporting line* $l_S(t)$ and the *supporting half-plane*
$H_S(t)$ of $S$ are

```math
h_S(t) = \sup_{p \in S} \langle p, u_t \rangle, \qquad l_S(t) = l(t, h_S(t)), \qquad H_S(t) = H_-(t, h_S(t)) ,
```

and the *width* of $S$ in the direction $u_t$ is $h_S(t) + h_S(t + \pi)$, the distance between the
parallel supporting lines $l_S(t)$ and $l_S(t + \pi)$.

*Lean: [`IsConvexBody`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L40), [`supp`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L43), [`suppLine`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L46), [`suppHalf`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L49), [`width`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L52).*

The supporting line $l_S(t)$ touches $S$ from the side of $u_t$: $S$ lies in $H_S(t)$ and meets
$l_S(t)$ (Figure 2.3).

### Lemma 2.7 (the support function)

Let $S$ and $T$ be nonempty compact sets and $K$ a convex body.

1. $h_S$ is continuous and $2\pi$-periodic, and for every $t$ some point $p \in S$ has
   $\langle p, u_t \rangle = h_S(t)$.
2. If $S \subseteq T$, then $h_S \le h_T$; and $h_{S + v}(t) = h_S(t) + \langle v, u_t \rangle$ for
   every vector $v$.
3. A point $p$ lies in $K$ if and only if $\langle p, u_t \rangle \le h_K(t)$ for every angle $t$,
   that is, $K = \bigcap_t H_K(t)$. In particular, two convex bodies with the same support function
   are equal.

*Proof.* (1) The function $(t, p) \mapsto \langle p, u_t \rangle$ is continuous, and $S$ is compact,
so its supremum over $p \in S$ is attained and depends continuously on $t$; and
$u_{t + 2\pi} = u_t$. (2) follows from the definition. (3) Every point of $K$ satisfies the
inequalities. Conversely, if $p \notin K$, the Hahn–Banach separation theorem gives a linear
functional $f$ with $f(q) < f(p)$ for all $q \in K$; writing $f = \langle \cdot, r u_\theta \rangle$
with $r > 0$, the maximum $h_K(\theta)$ of $\langle q, u_\theta \rangle$ over $K$ is less than
$\langle p, u_\theta \rangle$. $\square$

*Lean: [`continuous_supp`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L116), [`supp_add_two_pi`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L113), [`exists_dot_eq_supp`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L105), [`dot_le_supp`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L101), [`supp_mono`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L109),
[`supp_translate`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L176), [`mem_iff_forall_dot_le_supp`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L126), [`eq_of_supp_eq`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L170).*

### Definition 2.8 (edges and vertices; Baek, Definitions 2.1.9, 2.1.10 and 2.1.14)

Let $K$ be a convex body and $t$ an angle. The *edge* of $K$ with normal angle $t$ is
$e_K(t) = K \cap l_K(t)$, a nonempty segment of the line $l_K(t)$. Its endpoints are the *vertices*
$v_K^-(t)$ and $v_K^+(t)$: $v_K^+(t)$ is the point of $e_K(t)$ farthest in the direction $v_t$, and
$v_K^-(t)$ the point farthest in the direction $-v_t$, so that $e_K(t)$ is the segment
$[v_K^-(t), v_K^+(t)]$. The edge may be a single point, $v_K^-(t) = v_K^+(t)$. For angles $a$ and
$b$ with $\sin(b - a) \ne 0$, the supporting lines $l_K(a)$ and $l_K(b)$ meet in the point

```math
v_K(a, b) = h_K(a)\, u_a + \frac{h_K(b) - h_K(a) \cos(b - a)}{\sin(b - a)}\, v_a .
```

*Lean: [`edge`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L55), [`vplus`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L59), [`vminus`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L64), [`vint`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L69), [`edge_eq_segment`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L266), [`vplus_mem_edge`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L260), [`vminus_mem_edge`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L263),
[`vint_mem_line_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L311), [`vint_mem_line_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L314).*

![A rounded triangle K, light blue, in the first quadrant, the origin O with the arrows u_t and v_t, and the supporting line l_K(t) perpendicular to u_t at the end of a dashed segment of length h_K(t) from O; the supporting half-plane H_K(t), on the side of the line containing K, is shaded grey; the line meets K along the orange edge e_K(t), whose upper end is v_K plus of t and whose lower end is v_K minus of t](figures/02-preliminaries/convex-body.svg)

*Figure 2.3.* A convex body $K$, its support function $h_K(t)$, the distance from $O$ to the
supporting line $l_K(t)$, and the supporting half-plane $H_K(t)$ (grey). The edge $e_K(t)$ (orange)
runs from $v_K^-(t)$ to $v_K^+(t)$, the end farthest in the direction $v_t$. At a normal angle where
the boundary of $K$ is round, the edge is a single point.

In Lean, $v_K^\pm(t) = h_K(t)\, u_t + m^\pm\, v_t$, where $m^+$ and $m^-$ are the largest and the
smallest value of $\langle q, v_t \rangle$ on the edge, and $v_K(a, b)$ is given by the formula
above, which defines it for all $a$ and $b$.

Baek's §2.1 also introduces the *surface area measure* $\sigma_K$ of a convex body, a measure on the
angles that records the lengths of the sides of $K$ by their normal angles: $\sigma_K(\lbrace t \rbrace)$
is the length of $e_K(t)$, so $v_K^+(t) = v_K^-(t) + \sigma_K(\lbrace t \rbrace)\, v_t$ (Baek's
Proposition 2.1.2). [Chapter 6](06-surface-area.md) constructs $\sigma_K$ and proves its properties
([`sigma`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L281), [`proposition2_1_2`](../../MovingSofaOptimality/Basic/SurfaceArea.lean#L366)); this chapter and the next use it only in one identity of the mirror
symmetry in [Chapter 3](03-monotone.md).

### Theorem 2.9 (limits of vertices; Baek, Theorem 2.1.3)

Let $K$ be a convex body and $t$ an angle. Then

```math
\lim_{s \to t^+} v_K^+(s) = \lim_{s \to t^+} v_K^-(s) = \lim_{s \to t^+} v_K(t, s) = v_K^+(t), \qquad \lim_{s \to t^-} v_K^+(s) = \lim_{s \to t^-} v_K^-(s) = \lim_{s \to t^-} v_K(s, t) = v_K^-(t) .
```

In particular $v_K^+$ is right-continuous and $v_K^-$ is left-continuous.

*Lean: [`tendsto_vplus_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L532), [`tendsto_vminus_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L536), [`tendsto_vint_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L540), [`tendsto_vplus_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L550),
[`tendsto_vminus_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L554), [`tendsto_vint_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L558).*

As printed, the paper's first display takes the limits of $v_K^+(t)$ and $v_K^-(u)$, where
$v_K^+(s)$ and $v_K^-(s)$ are meant (REPORT.md, E26).

![A close-up of the convex body of Figure 2.3 at the vertex v_K plus of t, where the orange edge e_K(t) ends on the supporting line l_K(t) and the boundary of K turns into an arc; three dashed supporting lines l_K(s), for angles s decreasing to t, touch the arc at blue dots and cross l_K(t) at orange circles; both the dots and the circles approach v_K plus of t](figures/02-preliminaries/vertex-limits.svg)

*Figure 2.4.* The right limits at $v_K^+(t)$. For $s$ slightly larger than $t$, the edge $e_K(s)$
is a single point of the arc (dots), and $v_K(t, s)$ lies on $l_K(t)$ beyond $v_K^+(t)$ (circles);
both tend to $v_K^+(t)$ as $s$ decreases to $t$.

*Proof.* We prove the right limits; the left limits follow in the same way with the frame
$(u_t, -v_t)$ in place of $(u_t, v_t)$. Let $P = v_K^+(t)$, let $s = t + \delta$ with
$0 < \delta < \pi/2$, and let $w$ be a point of $e_K(s)$, for instance $v_K^+(s)$ or $v_K^-(s)$.
Since $u_s = \cos\delta\, u_t + \sin\delta\, v_t$ and $w$ maximizes $\langle \cdot, u_s \rangle$ on
$K$, while $P \in K$,

```math
\cos\delta \,\langle w, u_t \rangle + \sin\delta\, \langle w, v_t \rangle \ \ge\ \cos\delta\, \langle P, u_t \rangle + \sin\delta\, \langle P, v_t \rangle , \tag{2.1}
```

and $\langle w, u_t \rangle \le h_K(t) = \langle P, u_t \rangle$ because $w \in K$. Let $R$ bound
$\lvert \langle q, v_t \rangle \rvert$ on $K$. Then (2.1) gives

```math
0 \ \le\ h_K(t) - \langle w, u_t \rangle \ \le\ 2R \tan\delta, \qquad \langle w, v_t \rangle \ \ge\ \langle P, v_t \rangle .
```

As $\delta \to 0^+$, every cluster point $q$ of $w$ lies in the compact set $K$, has
$\langle q, u_t \rangle = h_K(t)$, so that $q \in e_K(t)$, and has
$\langle q, v_t \rangle \ge \langle P, v_t \rangle$. Since $P$ is the point of $e_K(t)$ farthest in
the direction $v_t$, $q = P$. A function with values in a compact set and a single cluster point
converges to it, so $v_K^\pm(s) \to P$.

The point $v_K(t, s)$ lies on $l_K(t)$, so its $u_t$-coordinate is $\langle P, u_t \rangle$; its
$v_t$-coordinate is $(h_K(s) - h_K(t) \cos\delta) / \sin\delta$. With $w = v_K^+(s)$, so that
$h_K(s) = \langle w, u_s \rangle$, this is

```math
\langle w, v_t \rangle - \bigl(h_K(t) - \langle w, u_t \rangle\bigr) \cot\delta ,
```

which is at most $\langle w, v_t \rangle$, and at least $\langle P, v_t \rangle$ by (2.1). Both
bounds tend to $\langle P, v_t \rangle$, so $v_K(t, s) \to P$ (Figure 2.4). $\square$

Baek proves the theorem with a small triangle at $v_K^+(t)$ that contains the edges $e_K(s)$ for $s$
close to $t$; the formalization argues by compactness, as above.

### Corollary 2.10 (one-sided derivatives of the support function)

Let $K$ be a convex body and $t$ an angle. The support function $h_K$ has the right derivative
$\langle v_K^+(t), v_t \rangle$ and the left derivative $\langle v_K^-(t), v_t \rangle$ at $t$.

*Proof.* For $s = t + \delta$ with $\delta > 0$ small,

```math
\frac{h_K(s) - h_K(t)}{\delta} = \frac{\sin\delta}{\delta} \cdot \frac{h_K(s) - h_K(t)\cos\delta}{\sin\delta} + h_K(t)\, \frac{\cos\delta - 1}{\delta} .
```

The middle factor is the $v_t$-coordinate of $v_K(t, s)$, which tends to
$\langle v_K^+(t), v_t \rangle$ by Theorem 2.9, while $\sin\delta / \delta \to 1$ and
$(\cos\delta - 1)/\delta \to 0$. The left derivative is computed in the same way. $\square$

*Lean: [`hasDerivWithinAt_supp_right`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L604), [`hasDerivWithinAt_supp_left`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L620).*

The two one-sided derivatives differ by $\langle v_K^+(t) - v_K^-(t), v_t \rangle$, the length of
the edge $e_K(t)$; so $h_K$ is differentiable at $t$ exactly when $e_K(t)$ is a single point.

### Definition 2.11 (Hausdorff distance; Baek, Definition 2.1.12)

The *Hausdorff distance* of two convex bodies is

```math
d_{\mathrm H}(K_1, K_2) = \sup_t\, \lvert h_{K_1}(t) - h_{K_2}(t) \rvert ,
```

and a sequence of convex bodies $K_n$ *converges* to $K$ if $d_{\mathrm H}(K_n, K) \to 0$, that is,
if $h_{K_n} \to h_K$ uniformly.

*Lean: [`hausdorffDist`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L74), [`HausdorffTendsto`](../../MovingSofaOptimality/Basic/ConvexBody.lean#L77).*

Baek cites this formula from Schneider's Lemma 1.8.14 as a property of the usual Hausdorff distance
of compact sets; the formalization takes it as the definition, and compares it with Mathlib's
Hausdorff distance where needed, in the proof of the next theorem.

### Theorem 2.12 (Blaschke selection theorem)

Let $B$ be a compact set and $K_1, K_2, \ldots$ convex bodies contained in $B$. Some subsequence of
$(K_n)$ converges, in the sense of Definition 2.11, to a convex body contained in $B$.

*Proof sketch.* Mathlib provides the Hausdorff distance $d$ of nonempty compact sets, for the
maximum norm on $\mathbb{R} \times \mathbb{R}$, and the facts that the nonempty compact sets form a
complete metric space for it and that those contained in a totally bounded set form a totally
bounded family. So the closure of the family of nonempty compact subsets of $B$ is compact, and a
subsequence $K_{n_i}$ converges for $d$ to a nonempty compact set $L \subseteq B$. The limit is
convex: a point $a p + b q$ with $p, q \in L$, $a, b \ge 0$, $a + b = 1$, is within $\varepsilon$ of
a point $a p' + b q'$ of $K_{n_i}$, for $p', q' \in K_{n_i}$ close to $p$ and $q$. Finally,
$\lvert \langle p - q, u_t \rangle \rvert \le \lvert p_1 - q_1 \rvert + \lvert p_2 - q_2 \rvert$
gives $\lvert h_A(t) - h_{A'}(t) \rvert \le 2\, d(A, A')$ for nonempty compact sets $A, A'$, so the
support functions converge uniformly. $\square$

*Lean: [`mpc_blaschke`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L223), [`mpc_supp_le_add_hausdorff`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L197).*

The theorem is used in [Chapter 4](04-balanced.md), to take limits of maximum polygon caps, and in
[Chapter 11](11-selection.md).

## 2.4 Standard position

### Definition 2.13 (strips and the parallelogram; Baek, Definitions 2.3.2 and 2.3.5)

The *horizontal strip* is $H = \mathbb{R} \times [0, 1]$ and the *vertical strip* is
$V = [0, 1] \times \mathbb{R}$; for an angle $\omega$,

```math
V_\omega = R_\omega(V) = \lbrace p : 0 \le \langle p, u_\omega \rangle \le 1 \rbrace .
```

For $\omega \in (0, \pi/2]$, the *parallelogram* is $P_\omega = H \cap V_\omega$, with lower left
vertex $O = (0, 0)$ and upper right vertex $o_\omega = (\tan(\pi/4 - \omega/2), 1)$.

*Lean: [`hStrip`](../../MovingSofaOptimality/Sofa/Defs.lean#L64), [`vStrip`](../../MovingSofaOptimality/Sofa/Defs.lean#L67), [`vStripRot`](../../MovingSofaOptimality/Sofa/Defs.lean#L70), [`para`](../../MovingSofaOptimality/Sofa/Defs.lean#L77), [`MovingSofaOptimality.oPt`](../../MovingSofaOptimality/Sofa/Defs.lean#L80), [`ms_mem_vStripRot_iff`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L340).*

For $\omega < \pi/2$, $P_\omega$ is the parallelogram with vertices $O$, $(\sec\omega, 0)$,
$o_\omega$ and $(-\tan\omega, 1)$. Its two upper sides lie on the lines $y = 1$ and
$\langle p, u_\omega \rangle = 1$ and meet at $o_\omega$, since
$(1 - \sin\omega)/\cos\omega = \tan(\pi/4 - \omega/2)$; its two lower sides lie on $y = 0$ and
$\langle p, u_\omega \rangle = 0$ and meet at $O$ (Figure 2.5). For $\omega = \pi/2$, $V_\omega = H$,
and $P_{\pi/2} = H$ is a strip. (The paper's table of symbols swaps $H$ and $V$; REPORT.md, E26.)

### Definition 2.14 (standard position; Baek, Definitions 1.2.4 and 2.3.4)

A moving sofa $S$ with rotation angle $\omega \in (0, \pi/2]$ is in *standard position* if

```math
h_S(\omega) = h_S(\pi/2) = 1 ,
```

that is, if the upper sides $y = 1$ of $H$ and $\langle p, u_\omega \rangle = 1$ of $V_\omega$ are
supporting lines of $S$ from above.

*Lean: [`IsStandardPosition`](../../MovingSofaOptimality/Sofa/Defs.lean#L74).*

![A sofa S, light blue, with a flat top, rounded ends and a round niche in its lower side, lying in a long parallelogram P_omega that leans to the left; the horizontal strip H between y = 0 and y = 1 is shaded grey and the rotated strip V_omega green, they cross in P_omega, whose lower left vertex O and upper right vertex o_omega are marked; the line y = 1 and the line x cos omega + y sin omega = 1 touch S from above](figures/02-preliminaries/standard-position.svg)

*Figure 2.5.* A moving sofa $S$ with rotation angle $\omega = 1.2$ in standard position: the upper
sides of the strips $H$ (grey) and $V_\omega$ (green) touch $S$, and $S$ lies in their intersection
$P_\omega$. The sofa is the monotone sofa of a cap with rotation angle $1.2$
([Chapter 3](03-monotone.md)).

[Proposition 3.1](03-monotone.md) shows that every moving sofa with rotation angle
$\omega \in (0, \pi/2]$ has a translate in standard position, unique when $\omega < \pi/2$ and
unique up to horizontal translations when $\omega = \pi/2$.

### Proposition 2.15 (the sofa in its own frame; Baek, Proposition 1.2.2)

Let $S$ be a moving sofa with rotation angle $\omega \in (0, \pi/2]$ in standard position. Then:

1. $S \subseteq H$;
2. for every $t \in [0, \omega]$, $S$ lies in a translate $c + R_t(L)$ of the hallway turned by $t$;
3. $S \subseteq V_\omega$.

![Three panels, each with the sofa S of Figure 2.5 fixed and a hallway drawn grey around it: in the first the hallway is not turned and its horizontal side, inside the dashed strip H, holds S; in the second it is turned by omega over 2; in the third it is turned by omega and its vertical side, inside the dashed strip V_omega, holds S](figures/02-preliminaries/sofa-frame.svg)

*Figure 2.6.* The movement seen from the sofa. At the time when the sofa has turned clockwise by
$t$, the hallway, seen from the sofa, is turned counterclockwise by $t$ and contains it. At $t = 0$
its horizontal side holds $S$, and at $t = \omega$ its vertical side does.

*Proof.* Let $\theta, c$ be a movement of $S$ with rotation angle $\omega$, and
$\Phi_s(p) = R_{\theta(s)}\, p + c(s)$; let $c(s) = (c_1(s), c_2(s))$.

1. As $\theta(0) = 0$, $\Phi_0(p) = p + c(0)$, and $\Phi_0(S) \subseteq H_L$ gives
   $0 \le y + c_2(0) \le 1$ for every point $(x, y)$ of $S$. Some point of $S$ has $y = h_S(\pi/2) = 1$
   (Lemma 2.7), so $c_2(0) \le 0$, and then every point of $S$ has $y \ge -c_2(0) \ge 0$; and
   $y \le h_S(\pi/2) = 1$.
2. The angle $\theta$ is continuous with $\theta(0) = 0$ and $\theta(1) = -\omega \le -t$, so
   $\theta(s) = -t$ for some $s \in [0, 1]$ by the intermediate value theorem. Then
   $R_{-t}\, p + c(s) \in L$ for every $p \in S$, that is,
   $S \subseteq R_t(L - c(s)) = -R_t c(s) + R_t(L)$ (Figure 2.6).
3. The first coordinate of $\Phi_1(p) = R_{-\omega}\, p + c(1)$ is
   $\langle p, u_\omega \rangle + c_1(1)$, and $\Phi_1(S) \subseteq V_L$ gives
   $0 \le \langle p, u_\omega \rangle + c_1(1) \le 1$ on $S$. As in (1), some point of $S$ has
   $\langle p, u_\omega \rangle = h_S(\omega) = 1$, so $c_1(1) \le 0$, and
   $0 \le \langle p, u_\omega \rangle \le 1$ on $S$. $\square$

*Lean: [`proposition1_2_2`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L355).*

By (1) and (3), a moving sofa in standard position lies in $P_\omega = H \cap V_\omega$.

## 2.5 Supporting hallways

By Proposition 2.15, a moving sofa lies in a copy of the hallway turned by $t$ for each
$t \in [0, \omega]$, but nothing yet ties these copies to the sofa or makes them depend continuously
on $t$. The supporting hallway fixes the copy: push it against the sofa until both outer walls
touch.

### Definition 2.16 (the parts of the hallway; Baek, Definition 2.2.1)

The hallway $L$ has the *inner corner* $\mathbf{x}_L = (0, 0)$ and the *outer corner*
$\mathbf{y}_L = (1, 1)$; the *outer walls* $a_L$ and $c_L$, the lines $x = 1$ and $y = 1$; the
*inner walls* $\vec b_L = \lbrace 0 \rbrace \times (-\infty, 0]$ and
$\vec d_L = (-\infty, 0] \times \lbrace 0 \rbrace$, half-lines from the inner corner, on the lines
$b_L$ ($x = 0$) and $d_L$ ($y = 0$); and the quarter-planes

```math
Q_L^+ = (-\infty, 1]^2, \qquad Q_L^- = (-\infty, 0)^2, \qquad L = Q_L^+ \setminus Q_L^- .
```

*Lean: [`MovingSofaOptimality.xL`](../../MovingSofaOptimality/Sofa/Defs.lean#L85), [`MovingSofaOptimality.yL`](../../MovingSofaOptimality/Sofa/Defs.lean#L87), [`MovingSofaOptimality.aL`](../../MovingSofaOptimality/Sofa/Defs.lean#L89), [`MovingSofaOptimality.cL`](../../MovingSofaOptimality/Sofa/Defs.lean#L91), [`bVecL`](../../MovingSofaOptimality/Sofa/Defs.lean#L93), [`dVecL`](../../MovingSofaOptimality/Sofa/Defs.lean#L95), [`MovingSofaOptimality.bL`](../../MovingSofaOptimality/Sofa/Defs.lean#L97), [`MovingSofaOptimality.dL`](../../MovingSofaOptimality/Sofa/Defs.lean#L99), [`qPlusL`](../../MovingSofaOptimality/Sofa/Defs.lean#L101), [`qMinusL`](../../MovingSofaOptimality/Sofa/Defs.lean#L103).*

### Definition 2.17 (supporting hallway; Baek, Definitions 2.2.2 and 2.2.3)

Let $S$ be a nonempty compact set and $t$ an angle. The rigid motion

```math
f_{S,t}(p) = R_t\, p + (h_S(t) - 1)\, u_t + (h_S(t + \pi/2) - 1)\, v_t
```

turns the plane by $t$, and the *supporting hallway* of $S$ with angle $t$ is $L_S(t) = f_{S,t}(L)$.
Its parts are the images of the parts of $L$ (Figure 2.7): the inner corner
$\mathbf{x}_S(t) = f_{S,t}(\mathbf{x}_L)$, the outer corner $\mathbf{y}_S(t) = f_{S,t}(\mathbf{y}_L)$,
the walls $a_S(t)$, $b_S(t)$, $c_S(t)$, $d_S(t)$, $\vec b_S(t)$, $\vec d_S(t)$, and the
quarter-planes $Q_S^\pm(t)$, each the image under $f_{S,t}$ of the part of $L$ with the same letter.

*Lean: [`hallwayMap`](../../MovingSofaOptimality/Sofa/Defs.lean#L107), [`suppHallway`](../../MovingSofaOptimality/Sofa/Defs.lean#L111), [`innerCorner`](../../MovingSofaOptimality/Sofa/Defs.lean#L114), [`outerCorner`](../../MovingSofaOptimality/Sofa/Defs.lean#L116), [`wallA`](../../MovingSofaOptimality/Sofa/Defs.lean#L118), [`wallB`](../../MovingSofaOptimality/Sofa/Defs.lean#L120), [`wallC`](../../MovingSofaOptimality/Sofa/Defs.lean#L122),
[`wallD`](../../MovingSofaOptimality/Sofa/Defs.lean#L124), [`wallBVec`](../../MovingSofaOptimality/Sofa/Defs.lean#L126), [`wallDVec`](../../MovingSofaOptimality/Sofa/Defs.lean#L128), [`qPlus`](../../MovingSofaOptimality/Sofa/Defs.lean#L130), [`qMinus`](../../MovingSofaOptimality/Sofa/Defs.lean#L132).*

![Left: the hallway L, with the inner corner x_L at the origin, the outer corner y_L at (1, 1), the outer walls a_L (x = 1) and c_L (y = 1), the inner walls b_L and d_L from x_L, the lines of all four walls continued dashed beyond the hallway, and the open quarter-plane Q_L minus, below and to the left of x_L, shaded orange. Right: Gerver's sofa G and its supporting hallway turned by t = 0.5, with the corresponding parts: the outer corner y(t) above the sofa, the outer walls a(t) and c(t) touching the sofa's rounded ends, the inner corner x(t) at the top of the niche, the inner walls b(t) and d(t), and the quarter-plane Q minus of t shaded orange below x(t)](figures/02-preliminaries/supporting-hallway.svg)

*Figure 2.7.* The parts of the hallway $L$ (left), and the corresponding parts of the supporting
hallway $L_G(t)$ of Gerver's sofa $G$ for $t = 0.5$ (right), written $\mathbf{x}(t)$, $a(t)$, … for
short. The outer walls $a(t)$ and $c(t)$ touch $G$.

In the frame of $L_S(t)$, a point $q$ has the coordinates

```math
X = \langle q, u_t \rangle - h_S(t) + 1, \qquad Y = \langle q, v_t \rangle - h_S(t + \pi/2) + 1 ,
```

the coordinates of $f_{S,t}^{-1}(q)$, and $q$ lies in the image under $f_{S,t}$ of a part of $L$
when $(X, Y)$ lies in that part. In particular, $q \in L_S(t)$ if and only if $X \le 1$, $Y \le 1$,
and $X \ge 0$ or $Y \ge 0$ ([`ms_mem_hallwayMap_image`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L57)).

### Proposition 2.18 (the supporting hallway; Baek, Proposition 2.2.1)

Let $S$ be a nonempty compact set, $t$ an angle and $c$ a vector. The outer walls of the translate
$p \mapsto R_t\, p + c$ of $R_t(L)$, the images of $a_L$ and $c_L$, are the supporting lines
$l_S(t)$ and $l_S(t + \pi/2)$ of $S$ if and only if the translate is $f_{S,t}$. So $L_S(t)$ is the
unique translate of $R_t(L)$ whose outer walls are supporting lines of $S$.

*Proof.* The point $R_t(x, y) + c$ has $\langle R_t(x, y) + c, u_t \rangle = x + \langle c, u_t \rangle$
and $\langle R_t(x, y) + c, v_t \rangle = y + \langle c, v_t \rangle$. So the image of $a_L$
($x = 1$) is the line $l(t, 1 + \langle c, u_t \rangle)$, and the image of $c_L$ ($y = 1$) is
$l(t + \pi/2, 1 + \langle c, v_t \rangle)$. They are $l(t, h_S(t))$ and
$l(t + \pi/2, h_S(t + \pi/2))$ if and only if $\langle c, u_t \rangle = h_S(t) - 1$ and
$\langle c, v_t \rangle = h_S(t + \pi/2) - 1$, that is, by the decomposition in the frame
$(u_t, v_t)$, if and only if $c = (h_S(t) - 1)\, u_t + (h_S(t + \pi/2) - 1)\, v_t$. $\square$

*Lean: [`proposition2_2_1`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L109).*

### Proposition 2.19 (the parts of the supporting hallway; Baek, Proposition 2.2.2)

Let $S$ be a nonempty compact set and $t$ an angle. Then $L_S(t) = Q_S^+(t) \setminus Q_S^-(t)$, and
the parts of $L_S(t)$ are given by the support function of $S$ as in Table 2.1.

*Table 2.1.* The parts of the supporting hallway $L_S(t)$.

| Part of $L$ | Part of $L_S(t)$ | In terms of $h_S$ |
| --- | --- | --- |
| inner corner $\mathbf{x}_L = (0, 0)$ | $\mathbf{x}_S(t)$ | $(h_S(t) - 1)\, u_t + (h_S(t + \pi/2) - 1)\, v_t$ |
| outer corner $\mathbf{y}_L = (1, 1)$ | $\mathbf{y}_S(t)$ | $h_S(t)\, u_t + h_S(t + \pi/2)\, v_t$ |
| outer wall $a_L$: $x = 1$ | $a_S(t)$ | $l_S(t) = l(t, h_S(t))$ |
| inner wall line $b_L$: $x = 0$ | $b_S(t)$ | $l(t, h_S(t) - 1)$ |
| outer wall $c_L$: $y = 1$ | $c_S(t)$ | $l_S(t + \pi/2) = l(t + \pi/2, h_S(t + \pi/2))$ |
| inner wall line $d_L$: $y = 0$ | $d_S(t)$ | $l(t + \pi/2, h_S(t + \pi/2) - 1)$ |
| $Q_L^+ = (-\infty, 1]^2$ | $Q_S^+(t)$ | $H_S(t) \cap H_S(t + \pi/2)$ |
| $Q_L^- = (-\infty, 0)^2$ | $Q_S^-(t)$ | $H_-^\circ(t, h_S(t) - 1) \cap H_-^\circ(t + \pi/2, h_S(t + \pi/2) - 1)$ |

*Proof.* In the coordinates $(X, Y)$ of $L_S(t)$, each part of $L$ is described by the conditions
in its first column: the inner corner is $X = Y = 0$, the outer wall $a_L$ is $X = 1$, the
quarter-plane $Q_L^-$ is $X < 0$ and $Y < 0$, and so on. Substituting $X$ and $Y$ gives the third
column; for instance $X < 0$ reads $\langle q, u_t \rangle < h_S(t) - 1$. Finally
$L = Q_L^+ \setminus Q_L^-$ and $f_{S,t}$ is a bijection. $\square$

*Lean: [`proposition2_2_2_hallway`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L131), [`proposition2_2_2_innerCorner`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L147), [`proposition2_2_2_outerCorner`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L151),
[`proposition2_2_2_wallA`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L155), [`proposition2_2_2_wallB`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L160), [`proposition2_2_2_wallC`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L165),
[`proposition2_2_2_wallD`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L172), [`proposition2_2_2_qPlus`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L178), [`proposition2_2_2_qMinus`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L185).*

The paper's formula for $Q_S^-(t)$ lacks the "$- 1$" in its second half-plane (REPORT.md, E26); the
table gives the correct one. So $Q_S^+(t)$ is the closed quarter-plane bounded by the two outer
walls, with corner $\mathbf{y}_S(t)$, and $Q_S^-(t)$ the open quarter-plane bounded by the two inner
walls, with corner $\mathbf{x}_S(t)$; both lie on the side of the walls opposite to $u_t$ and $v_t$.

### Proposition 2.20 (the supporting hallway contains the sofa; Baek, Proposition 2.2.3)

Let $S$ be a nonempty compact set that lies in a translate $L' = c + R_t(L)$ of the hallway turned
by $t$. Then $S \subseteq L_S(t)$.

![A small disk S inside a hallway L' turned by an angle t, whose walls are dashed grey, and inside the supporting hallway L_S(t), whose walls are solid and whose outer walls both touch the disk; arrows from the corners of L' to the corners of L_S(t) show that L_S(t) is L' pushed towards S, which moves its inner walls away from the disk](figures/02-preliminaries/push.svg)

*Figure 2.8.* Proposition 2.20. Pushing the hallway $L'$ (dashed) along $-u_t$ and $-v_t$ until its
outer walls touch $S$ gives $L_S(t)$ (solid); the push moves the inner walls away from $S$.

*Proof.* Let $X' = \langle p - c, u_t \rangle$ and $Y' = \langle p - c, v_t \rangle$ be the
coordinates of a point $p$ in the frame of $L'$. Since $S \subseteq L'$, every $p \in S$ has
$X' \le 1$, $Y' \le 1$, and $X' \ge 0$ or $Y' \ge 0$. Taking the supremum over $S$,
$h_S(t) \le \langle c, u_t \rangle + 1$ and $h_S(t + \pi/2) \le \langle c, v_t \rangle + 1$: the
outer walls of $L_S(t)$ are not beyond those of $L'$. So the coordinates $(X, Y)$ of $p \in S$ in
the frame of $L_S(t)$ satisfy $X \ge X'$ and $Y \ge Y'$, while $X \le 1$ and $Y \le 1$ because
$\langle p, u_t \rangle \le h_S(t)$ and $\langle p, v_t \rangle \le h_S(t + \pi/2)$. Hence
$X \ge 0$ or $Y \ge 0$, and $p \in L_S(t)$ (Figure 2.8). $\square$

*Lean: [`proposition2_2_3`](../../MovingSofaOptimality/Monotone/SupportingHallway.lean#L194).*

By Propositions 2.15 and 2.20, a moving sofa $S$ with rotation angle $\omega \in (0, \pi/2]$ in
standard position lies in $P_\omega$ and in each of its supporting hallways $L_S(t)$,
$t \in [0, \omega]$. [Chapter 3](03-monotone.md) shows that the intersection of these sets is
itself a moving sofa, and describes it by a convex body, its cap.
