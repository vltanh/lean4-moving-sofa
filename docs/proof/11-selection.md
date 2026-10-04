# 11. Uniqueness I: approximating a maximizing cap

[Contents](README.md) · [← 10. Gerver's sofa](10-gerver.md) · [12. Uniqueness II: every maximum is Gerver's sofa →](12-uniqueness.md)

This chapter and the next prove that Gerver's sofa $G$ is the only moving sofa of maximum area up
to a rotation and a translation: a rotation about the origin followed by a translation maps every
moving sofa $S$ with $|S| = |G|$ onto $G$, as a set
([Theorem 12.1](12-uniqueness.md#theorem-121-uniqueness-of-gervers-sofa)). Baek's paper does not
prove this. The argument is that of note 20
([`docs/archive/uniqueness/20-complete-paper-proof.md`](../archive/uniqueness/20-complete-paper-proof.md)), an informal proof in six propositions,
written for this formalization by ChatGPT Pro 6 and not peer reviewed
([§1.3](README.md#13-background)); the library [`MovingSofaUniqueness/`](../../MovingSofaUniqueness) formalizes it. The two chapters follow the formal proof, and a
remark marks each place where it takes a different route from note 20.

Baek's proof establishes the key properties of a maximum sofa only for a special one, a limit of
maximum polygon caps, and the given sofa need not be such a limit (§11.1). This chapter approximates
a given maximizing cap $K_*$ by polygon caps that are almost balanced. At stage $n$, a polygon cap
maximizes the polygon sofa area minus a weighted squared penalty on the differences between its
support function and that of $K_*$ at dyadic normals. These penalized maximizers converge to $K_*$
(§11.2 to §11.4), and the penalty spoils the balance $\sigma = \tau$ of Baek's maximum polygon caps
only by a multiple of the distance to $K_*$ (§11.5 to §11.7). In the limit, $K_*$ satisfies the
pinned bounds $w_{K_*}^\circ \le \sigma_{K_*}(\pi/2)$ and $z_{K_*}^\circ \le \sigma_{K_*}(\omega)$
(§11.8), from which [Chapter 12](12-uniqueness.md) obtains the right-angle motion.

## 11.1 The given maximizer

Baek's proof of [Theorem 9.33](09-optimality.md#theorem-933-optimality-of-gervers-sofa-baek-theorem-111)
compares every moving sofa with a balanced maximum sofa, whose cap $K_\omega$ is a limit of maximum
polygon caps $K_i$ and maximizes $\mathcal{A}_\omega$
([Theorems 4.35](04-balanced.md#theorem-435-existence-of-balanced-maximum-caps-baek-theorem-352) and
[4.38](04-balanced.md#theorem-438-maximality-baek-theorem-355)). The $K_i$ are balanced
([Theorem 4.31](04-balanced.md#theorem-431-maximum-polygon-caps-are-balanced-baek-theorem-349)), and
$K_\omega$ inherits two consequences: the pinned bounds of
[Theorem 5.6](05-rotation-angle.md#theorem-56-horizontal-sides-of-balanced-maximum-caps-baek-theorem-414),
which give a right-angle motion
([Theorem 5.2](05-rotation-angle.md#theorem-52-the-right-angle-baek-theorem-152)), and, at the right
angle, the injectivity condition
([Theorem 7.2](07-injectivity.md#theorem-72-injectivity-condition-baek-theorems-611-and-171)), on
which Baek's upper bound $\mathcal{Q}$ rests ([Chapter 9](09-optimality.md)).

Uniqueness needs both properties for the cap of the given sofa $S$, and Baek's argument does not
provide them. Note 03
([`docs/archive/uniqueness/03-global-reduction-obstructions.md`](../archive/uniqueness/03-global-reduction-obstructions.md)) records three obstructions, which note 20 is
designed to avoid.

1. *Exact maximizers do not select a given maximizer.* A cap that maximizes $\mathcal{A}_\omega$
   need not be a limit of maximum polygon caps, although the polygon objectives approximate
   $\mathcal{A}_\omega$ from above. On $[0, 1]$, the functions $F_n(x) = x/n$ decrease uniformly to
   $F = 0$; every point maximizes $F$, but every $F_n$ has its only maximum at $1$ (Figure 11.1). A
   penalty that vanishes at the chosen maximizer $x^*$ repairs this: the maxima of
   $F_n(x) - (x - x^*)^2$ converge to $x^*$. Sections 11.2 to 11.4 make this repair for caps.
2. *Comparing areas does not compare sets.* Baek's proof compares the area of $S$ with that of a
   balanced maximum sofa, which need not contain $S$. The proof of Theorem 12.1 replaces each
   comparison by a containment: a translate of $S$ lies in its monotonization, a rotated copy of
   that lies in a second monotonization, and that one is a translate of $G$.
3. *Equal areas do not make equal sets.* The unit square $E$ and $E \cup ([1, 2] \times \lbrace 0 \rbrace)$ are closed, connected and of the same area, and the first is a proper subset of the
   second ([Figure 12.7](12-uniqueness.md)). The last step of the proof therefore uses that $G$ is
   the closure of its interior
   ([Proposition 12.22](12-uniqueness.md#proposition-1222-regular-closedness-note-20-proposition-6)).

![Two panels. Left: on the interval from 0 to 1, the zero function F drawn thick along the axis, and the lines F_n(x) = x/n for n = 1, 2, 4, 8 from the origin, each ending at a dot above x = 1. Right: the penalized functions G_n(x) = F_n(x) - (x - x*)^2, concave parabolas whose maxima, marked by dots, move left towards the point x* = 0.3 marked on the axis](figures/11-selection/toy.svg)

*Figure 11.1.* Note 03's example. Left: the functions $F_n(x) = x/n$ decrease uniformly to $F = 0$
on $[0, 1]$, and each attains its maximum only at $x = 1$ (dots), although every point maximizes
$F$. Right: the penalized functions $G_n(x) = F_n(x) - (x - x^*)^2$ attain their maxima at
$x^* + \frac1{2n}$, which converge to the chosen maximizer $x^* = 0.3$.

The proof starts from the cap of the monotonization of $S$, which maximizes $\mathcal{A}_\omega$
because it attains the value $|G|$ (Lemma 11.3).

### Definition 11.1 (maximizing cap)

Let $\omega \in (0, \pi/2]$. A cap $K \in \mathcal{K}^\mathrm{c}_\omega$ *maximizes*
$\mathcal{A}_\omega$ if $\mathcal{A}_\omega(C) \le \mathcal{A}_\omega(K)$ for every cap
$C \in \mathcal{K}^\mathrm{c}_\omega$.

*Lean: [`MovingSofaUniqueness.IsMaxCap`](../../MovingSofaUniqueness/Main.lean#L37).*

### Lemma 11.2 (the maximum value)

Let $\omega \in (0, \pi/2]$. Every cap $K \in \mathcal{K}^\mathrm{c}_\omega$ has
$\mathcal{A}_\omega(K) \le |G|$. Consequently a cap with $\mathcal{A}_\omega(K) = |G|$ maximizes
$\mathcal{A}_\omega$.

*Proof.* [Theorem 4.40](04-balanced.md#theorem-440-balanced-maximum-sofas-baek-theorem-356) gives a
balanced maximum cap $B$ of angle $\omega$ such that $B \setminus \mathcal{N}(B)$ is a monotone sofa
with cap $B$. By Theorem 4.38, $\mathcal{A}_\omega(K) \le \mathcal{A}_\omega(B)$, and by
[Theorem 3.29](03-monotone.md#theorem-329-the-area-of-a-monotone-sofa-baek-theorem-2510),
$\mathcal{A}_\omega(B) = |B \setminus \mathcal{N}(B)|$. This is the area of a moving sofa, at most
$|G|$ by Theorem 9.33. $\square$

Only the value of the maximum enters here; the cap $K$ is not replaced by $B$.

*Lean: [`MovingSofaUniqueness.cap_area_le_gerver`](../../MovingSofaUniqueness/Main.lean#L48), [`MovingSofaUniqueness.isMaxCap_of_area_eq`](../../MovingSofaUniqueness/Main.lean#L59),
[`MovingSofaUniqueness.area_le_gerver`](../../MovingSofaUniqueness/Main.lean#L41).*

### Lemma 11.3 (the monotonization of a maximizing sofa)

Let $S$ be a moving sofa with rotation angle $\omega \in (0, \pi/2]$ and $|S| = |G|$. There are a
vector $v$ and a monotone sofa $T$ of angle $\omega$ with $S + v \subseteq T$ and $|T| = |G|$. The
cap $\mathcal{C}(T)$ of every monotone sofa $T$ of angle $\omega$ with $|T| = |G|$ maximizes
$\mathcal{A}_\omega$.

*Proof.* By [Proposition 3.1](03-monotone.md#proposition-31-standard-position-baek-propositions-121-and-231),
a translate $S + v$ of $S$ is in standard position and moves with the same angle. By
[Theorem 3.3](03-monotone.md#theorem-33-monotonization-baek-theorem-232), its monotonization
$T = \mathcal{I}(S + v)$ is a moving sofa of angle $\omega$ that contains $S + v$. So $T$ is a
monotone sofa, and $|G| = |S + v| \le |T| \le |G|$ by Theorem 9.33. For the second claim,
$\mathcal{C}(T)$ is a cap
([Theorem 3.10](03-monotone.md#theorem-310-the-cap-of-a-moving-sofa-baek-theorem-241)) with
$\mathcal{A}_\omega(\mathcal{C}(T)) = |T| = |G|$ (Theorem 3.29), and Lemma 11.2 applies. $\square$

*Lean: [`MovingSofaUniqueness.maximal_envelope`](../../MovingSofaUniqueness/Main.lean#L120), [`MovingSofaUniqueness.own_cap_isMax`](../../MovingSofaUniqueness/Main.lean#L139).*

The cap of $T$ is the *given* maximizing cap of the rest of the proof. The following table lists
the steps that turn it into a translate of Gerver's cap, with the corresponding propositions and
numbered inequalities of note 20; [Chapter 12](12-uniqueness.md) assembles them.

| Step | Note 20 | Here | Lean |
| --- | --- | --- | --- |
| Penalized polygon caps converge to a given maximizing cap | Proposition 1 | Proposition 11.13 | [`exists_selectedCapSequence`](../../MovingSofaUniqueness/Selection.lean#L871) |
| Their defects $\sigma - \tau$ are small | Proposition 2, (11)–(13) | Propositions 11.16, 11.19, Lemma 11.20, Corollary 11.21 | [`floating_defect_le`](../../MovingSofaUniqueness/Variation.lean#L280), [`pinned_defect_le`](../../MovingSofaUniqueness/Variation.lean#L580) |
| The pinned bounds of the given cap | Proposition 4, (19) | Proposition 11.23 | [`pinned_bounds_of_maximal_positive`](../../MovingSofaUniqueness/Variation.lean#L750) |
| Curvature bounds, injectivity | Proposition 3, (14)–(17) | Definition 12.2, Lemmas 12.3, 12.7, Propositions 12.6, 12.9, Corollary 12.10 | [`curvature_of_maximal_positive`](../../MovingSofaUniqueness/Curvature.lean#L1380), [`isKi_of_maximal_area`](../../MovingSofaUniqueness/Main.lean#L77) |
| A right-angle motion | Proposition 4 | Proposition 12.13 | [`maximal_monotone_has_right_angle`](../../MovingSofaUniqueness/Main.lean#L148) |
| Equality in $\mathcal{Q}$ gives Gerver's cap | Proposition 5, (21) | Lemma 12.18, Proposition 12.19 | [`ki_sofa_eq_gerver_translate`](../../MovingSofaUniqueness/Main.lean#L92) |
| $G$ is the closure of its interior | Proposition 6 | Proposition 12.22 | [`gerver_regularClosed`](../../MovingSofaUniqueness/RegularClosed.lean#L289) |
| The theorem | Theorem | Theorem 12.1 | [`image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L212) |

For the rest of this chapter, $\omega \in (0, \pi/2]$ is fixed, and $K_*$ is a cap of angle
$\omega$ that maximizes $\mathcal{A}_\omega$ with $\mathcal{A}_\omega(K_*) > 0$. The cap of
Lemma 11.3 qualifies, as $|G| \ge 2.2$ ([Chapter 10](10-gerver.md)). The positivity keeps the
penalized maximizers in a bounded region (Proposition 11.10).

## 11.2 Penalties at dyadic samples

Recall the polygon caps of [Chapter 4](04-balanced.md). An angle set $\Theta$ is a finite nonempty
subset of $(0, \omega)$, and its *defining normals* are
$\Theta^\diamond = \Theta \cup (\Theta + \pi/2) \cup \lbrace \omega, \pi/2 \rbrace$
([Definition 4.4](04-balanced.md#definition-44-angle-sets-baek-definitions-321322)). A polygon cap
$C \in \mathcal{K}^\mathrm{c}_\Theta$ is a cap whose edges have normals in
$\Theta^\diamond \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$, and $\mathcal{C}_\Theta(K)$ is the
polygon cap circumscribed about a cap $K$
([Definition 4.5](04-balanced.md#definition-45-polygon-caps-baek-definitions-323324),
[Proposition 4.6](04-balanced.md#proposition-46-the-approximating-polygon-cap-baek-proposition-321)).
The polygon niche is $\mathcal{N}_\Theta(C) = F_\omega \cap \bigcup_{t \in \Theta} Q_C^-(t)$, and
$\mathcal{A}_\Theta(C) = |C| - |\mathcal{N}_\Theta(C)|$
([Definition 4.7](04-balanced.md#definition-47-polygon-niche-and-polygon-area-functional-baek-definitions-325326)).
For every cap $K$, $\mathcal{A}_\omega(K) \le \mathcal{A}_\Theta(K)$
([Theorem 4.9](04-balanced.md#theorem-49-polygon-upper-bound-baek-theorem-323)).

For $k \ge 0$ let

```math
\Theta^{(k)} = \Theta_{\omega, 2^{k+1}} = \lbrace i\omega/2^{k+1} : 0 < i < 2^{k+1} \rbrace ,
```

the uniform angle set with $2^{k+1}$ intervals
([Definition 4.33](04-balanced.md#definition-433-balanced-maximum-cap-baek-definitions-351352)),
whose elements are the *dyadic angles of level* $k$. These sets increase with $k$, and their union
is dense in $[0, \omega]$.

### Definition 11.4 (support samples and their penalty)

Let $\Theta$ be an angle set. *Support samples* for $\Theta$ are finitely many normals
$s_i \in \Theta^\diamond$ with weights $w_i \ge 0$, $i \in I$; a normal may occur several times.
Their *total weight* is $W = \sum_i w_i$, and their *weight at the normal* $t$ is
$w(t) = \sum_{s_i = t} w_i$. For convex bodies $K$ and $K_*$, the *penalty* of $K$ with target
$K_*$ is

```math
P(K) = \sum_{i \in I} w_i \bigl(h_K(s_i) - h_{K_*}(s_i)\bigr)^2 .
```

*Lean: [`SupportSamples`](../../MovingSofaUniqueness/Selection.lean#L177), [`SupportSamples.penalty`](../../MovingSofaUniqueness/Selection.lean#L196), [`SupportSamples.totalWeight`](../../MovingSofaUniqueness/Selection.lean#L192),
[`SupportSamples.atNormal`](../../MovingSofaUniqueness/Selection.lean#L201), [`sampledPenalty`](../../MovingSofaUniqueness/Selection.lean#L43).*

### Lemma 11.5 (changing the supports)

Let $\eta \ge 0$ and let $K$ satisfy $|h_K(s_i) - h_{K_*}(s_i)| \le \eta$ at every sample. Let $K'$
be a convex body.

1. If $|h_{K'}(s_i) - h_K(s_i)| \le r$ at every sample, then
   $|P(K') - P(K)| \le W(2\eta r + r^2)$.
2. If $h_{K'}(s_i) = h_K(s_i)$ at every sample with $s_i \ne t$, and
   $|h_{K'}(t) - h_K(t)| \le r$, then $|P(K') - P(K)| \le w(t)(2\eta r + r^2)$.

*Proof.* For real numbers $a, b, c$,
$(b - c)^2 - (a - c)^2 = 2(a - c)(b - a) + (b - a)^2$, whose absolute value is at most
$2\eta r + r^2$ when $|a - c| \le \eta$ and $|b - a| \le r$. Multiply by $w_i$ and sum over the
samples; in (2) only the samples at $t$ contribute. $\square$

*Lean: [`abs_square_increment_le`](../../MovingSofaUniqueness/Selection.lean#L59), [`sampledPenalty_change_bound`](../../MovingSofaUniqueness/Selection.lean#L79),
[`sampledPenalty_change_on_normal`](../../MovingSofaUniqueness/Selection.lean#L105), [`SupportSamples.penalty_change_uniform`](../../MovingSofaUniqueness/Selection.lean#L271),
[`SupportSamples.penalty_change_one`](../../MovingSofaUniqueness/Selection.lean#L257).*

### Definition 11.6 (persistent dyadic samples)

The *dyadic samples of stage* $n$ consist, for every level $m \le n$ and every
$t \in \Theta^{(m)}$, of one sample at $t$ and one at $t + \pi/2$, each of weight

```math
w_m = \frac{(1/2)^{m+1}}{2\,\lvert \Theta^{(m)} \rvert} = \frac{(1/2)^{m+1}}{2\,(2^{m+1} - 1)} .
```

They are support samples for $\Theta^{(n)}$, since $\Theta^{(m)} \subseteq \Theta^{(n)}$. Write
$P_n$ for their penalty with target $K_*$. An angle of level $m$ also lies in every later level, so
at stage $n$ it carries one sample from each level between its first one and $n$ (Figure 11.2).

*Lean: [`dyadicSamples`](../../MovingSofaUniqueness/Selection.lean#L327), [`dyadicLevelWeight`](../../MovingSofaUniqueness/Selection.lean#L310), [`DyadicSampleIndex`](../../MovingSofaUniqueness/Selection.lean#L322), [`dyadicPenalty`](../../MovingSofaUniqueness/Selection.lean#L383).*

![Two panels. Top: Gerver's cap, a convex region with a flat top and rounded ends, with outward normal arrows at the points where its support function is sampled, thick at the normals π/4 and 3π/4 of level 0 and thin at the normals of level 1, and a dashed polygon circumscribed about the cap along the supporting lines at these normals. Bottom: four rows of dots on an axis of normal angles from 0 to π, one row per level 0 to 3; row m has dots at the dyadic angles of level m and at the same angles plus π/2, with dots that shrink from row to row, and the label total 1/2, 1/4, 1/8, 1/16 on the right](figures/11-selection/samples.svg)

*Figure 11.2.* The dyadic samples at the right angle. Top: Gerver's cap $\mathcal{C}(G)$, the
outward normals $u_s$ at which its support function is sampled at levels 0 (thick) and 1 (thin),
and the polygon $\mathcal{C}_{\Theta^{(1)}}(\mathcal{C}(G))$ circumscribed about the cap at these
normals (dashed), whose penalty is zero. Bottom: the sampled normals of levels 0 to 3. The samples
of level $m$ have total weight $(1/2)^{m+1}$, and keep their weights at every later stage.

### Lemma 11.7 (the dyadic penalty)

1. The total weight of the dyadic samples of stage $n$ is $1 - (1/2)^{n+1} \le 1$.
2. *Persistence.* If $m \le n$ and $t \in \Theta^{(m)}$, then every convex body $K$ satisfies
   $w_m \bigl(h_K(t) - h_{K_*}(t)\bigr)^2 \le P_n(K)$ and
   $w_m \bigl(h_K(t + \pi/2) - h_{K_*}(t + \pi/2)\bigr)^2 \le P_n(K)$.
3. *Recovery.* The polygon cap $R_n = \mathcal{C}_{\Theta^{(n)}}(K_*)$ circumscribed about $K_*$
   has $P_n(R_n) = 0$, and

   ```math
   \mathcal{A}_\omega(K_*) \le \mathcal{A}_{\Theta^{(n)}}(R_n) - P_n(R_n) .
   ```

*Proof.* (1) Level $m$ has $2|\Theta^{(m)}|$ samples of weight $w_m$, of total weight
$(1/2)^{m+1}$, and $\sum_{m=0}^n (1/2)^{m+1} = 1 - (1/2)^{n+1}$. (2) The two terms belong to $P_n$,
whose terms are nonnegative. (3) The cap $R_n$ contains $K_*$ and lies in the supporting
half-planes of $K_*$ at the normals of $\Theta^\diamond$ (Proposition 4.6). So
$h_{R_n} = h_{K_*}$ on $\Theta^\diamond$, and every term of $P_n(R_n)$ vanishes. Finally
$\mathcal{A}_\omega(K_*) \le \mathcal{A}_\Theta(K_*) = \mathcal{A}_\Theta(R_n)$ by Theorem 4.9,
Proposition 4.6 and
[Proposition 4.8](04-balanced.md#proposition-48-polygon-niches-baek-proposition-322). $\square$

*Lean: [`dyadic_totalWeight`](../../MovingSofaUniqueness/Selection.lean#L358), [`dyadic_totalWeight_le_one`](../../MovingSofaUniqueness/Selection.lean#L378), [`persistent_sample_first`](../../MovingSofaUniqueness/Selection.lean#L392),
[`persistent_sample_second`](../../MovingSofaUniqueness/Selection.lean#L400), [`SupportSamples.penalty_recovery_zero`](../../MovingSofaUniqueness/Selection.lean#L226),
[`SupportSamples.recovery_objective_ge`](../../MovingSofaUniqueness/Selection.lean#L237), [`dyadic_recovery_ge`](../../MovingSofaUniqueness/Selection.lean#L409).*

## 11.3 Penalized maximizers

### Definition 11.8 (penalized maximizer)

Given support samples for $\Theta$ and a target $K_*$, a polygon cap
$K \in \mathcal{K}^\mathrm{c}_\Theta$ is a *penalized maximizer* if

```math
\mathcal{A}_\Theta(C) - P(C) \le \mathcal{A}_\Theta(K) - P(K) \qquad \text{for every } C \in \mathcal{K}^\mathrm{c}_\Theta .
```

*Lean: [`IsPenalizedMax`](../../MovingSofaUniqueness/Selection.lean#L506).*

### Lemma 11.9 (two orthogonal samples bound a polygon cap)

Let $t \in \Theta$, $q > 0$ and $c \ge 0$, and let a polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$
satisfy $q\bigl(h_K(s) - h_{K_*}(s)\bigr)^2 \le c$ for $s = t$ and for $s = t + \pi/2$. Then
$K \subseteq [-R, R] \times [0, 1]$, where

```math
R = \frac{H}{\sin t} + \frac{H}{\cos t}, \qquad H = |h_{K_*}(t)| + |h_{K_*}(t + \pi/2)| + \frac cq + 1 .
```

*Proof.* From $x^2 \le c/q$ follows $|x| \le c/q + 1$, so $h_K(t) \le H$ and
$h_K(t + \pi/2) \le H$. A point $(x, y) \in K$ has $0 \le y \le 1$, as $K$ is a cap. Since
$t \in (0, \pi/2)$, the inequality $x\cos t + y \sin t \le H$ gives $x \le H/\cos t$, and
$-x \sin t + y \cos t \le H$ gives $-x \le H/\sin t$. $\square$

*Lean: [`polygon_subset_sampleBox`](../../MovingSofaUniqueness/Selection.lean#L451), [`sampleBoxRadius`](../../MovingSofaUniqueness/Selection.lean#L437).*

At the right angle a polygon cap can slide horizontally without changing $\mathcal{A}_\Theta$; the
penalty at two orthogonal normals stops it. Note 20 uses an artificial box at the right angle
instead.

### Proposition 11.10 (penalized maximizers exist)

Let support samples for $\Theta$ have samples of positive weight at $t$ and at $t + \pi/2$ for some
$t \in \Theta$, and let some polygon cap $R_0 \in \mathcal{K}^\mathrm{c}_\Theta$ satisfy
$\mathcal{A}_\Theta(R_0) - P(R_0) > 0$. Then a penalized maximizer exists. In particular, at every
stage $n$ the dyadic samples with target $K_*$ have a penalized maximizer $K_n$; it satisfies

```math
\mathcal{A}_\omega(K_*) \le \mathcal{A}_{\Theta^{(n)}}(K_n) - P_n(K_n) ,
```

and all the $K_n$ lie in one box $[-R, R] \times [0, 1]$.

*Proof.* The idea is that of the existence of maximum polygon caps
([Theorem 4.23](04-balanced.md#theorem-423-existence-of-maximum-polygon-caps-baek-theorem-343)):
bound the competitors, then pass to the limit in their finitely many supports. Write
$F = \mathcal{A}_\Theta - P$.

*Existence.* By [Lemma 4.22](04-balanced.md#lemma-422-bounded-width-baek-lemma-342) there is
$c > 0$ such that every polygon cap $C$ of an angle set of angle $\omega$ that contains $t$, with
$\mathcal{A}_\Theta(C) > 0$, has width at most $c$ along $u_0$. If $F(C) > 0$, then
$\mathcal{A}_\Theta(C) > 0$, and since $C$ lies in a horizontal strip of height one,
$P(C) < \mathcal{A}_\Theta(C) \le |C| \le c$. Hence $F \le c$, and the supremum $M$ of $F$ is
positive and finite. Take polygon caps $C_j$ with $F(C_j) > 0$ and $F(C_j) \to M$. Their penalties
are at most $c$, so by Lemma 11.9, with $q$ the smaller of the two positive weights, all $C_j$ lie in
one box. Their supports at the finitely many normals of $\Theta^\diamond$ are then bounded, and
along a subsequence they converge to values $h_\infty$. As in the proof of Theorem 4.23, the polygon
cap $C_\infty = \mathcal{C}_\Theta(h_\infty)$ has these supports on $\Theta^\diamond$, and for every
$\varepsilon > 0$, eventually $|C_j| \le |C_\infty| + \varepsilon$ and
$|\mathcal{N}_\Theta(C_\infty)| \le |\mathcal{N}_\Theta(C_j)| + \varepsilon$. The penalty depends
continuously on the supports at the sample normals, so $F(C_\infty) \ge M$, and $C_\infty$ is a
penalized maximizer.

*The dyadic samples.* Here $\Theta^{(0)} = \lbrace \omega/2 \rbrace$, and the samples of level 0, at
$\omega/2$ and $\omega/2 + \pi/2$, have weight $w_0 = 1/4$ at every stage. By Lemma 11.7 (3),
$F(R_n) \ge \mathcal{A}_\omega(K_*) > 0$, so a penalized maximizer $K_n$ exists, and
$F(K_n) \ge F(R_n) \ge \mathcal{A}_\omega(K_*)$. As above, $P_n(K_n) \le c$, with
$c = c_{\omega, \omega/2}$ independent of $n$, since $\omega/2$ lies in every $\Theta^{(n)}$. By
Lemma 11.7 (2) and Lemma 11.9 with $q = w_0$, all the $K_n$ lie in one box. $\square$

*Lean: [`exists_penalizedMax`](../../MovingSofaUniqueness/Selection.lean#L528), [`penalty_and_area_le_of_positive`](../../MovingSofaUniqueness/Selection.lean#L513), [`exists_dyadic_penalizedMax`](../../MovingSofaUniqueness/Selection.lean#L801),
[`selected_objective_ge`](../../MovingSofaUniqueness/Selection.lean#L818), [`selected_sequence_bounded`](../../MovingSofaUniqueness/Selection.lean#L829), [`lemma3_4_2`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L343), [`mpc_limit_polycap`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L688).*

## 11.4 Convergence to the given cap

### Lemma 11.11 (the polygon objective in the limit)

Let $k_n$ be strictly increasing, and let polygon caps $K_n \in \mathcal{K}^\mathrm{c}_{\Theta^{(k_n)}}$
lie in a common box $[-R, R] \times [0, 1]$ and converge in the Hausdorff distance to a convex body
$L$. Then for every $\varepsilon > 0$, eventually

```math
\mathcal{A}_{\Theta^{(k_n)}}(K_n) \le \mathcal{A}_\omega(L) + \varepsilon .
```

*Proof.* This is the argument of the proof of
[Theorem 4.38](04-balanced.md#theorem-438-maximality-baek-theorem-355), which does not use that the
caps are maximal. By Theorem 4.9,
$\mathcal{A}_{\Theta^{(k_n)}}(K_n) = |K_n| - |\mathcal{N}_{\Theta^{(k_n)}}(K_n)|$. The area of
convex bodies is upper semicontinuous in the Hausdorff distance, so eventually
$|K_n| \le |L| + \varepsilon/2$. A point of $\mathcal{N}(L)$ lies in $F_\omega \cap Q_L^-(t)$ for
some $t \in (0, \omega)$. The two strict inequalities that define $Q_L^-(t)$ hold with a margin at a
nearby dyadic angle, which lies in $\Theta^{(k_n)}$ for all large $n$, and the supports of $K_n$
converge uniformly; so the point lies in $\mathcal{N}_{\Theta^{(k_n)}}(K_n)$ for all large $n$.
These niches lie in the bounded box $[-R, R] \times [0, 2R]$, so by Fatou's lemma eventually
$|\mathcal{N}(L)| \le |\mathcal{N}_{\Theta^{(k_n)}}(K_n)| + \varepsilon/2$. $\square$

*Lean: [`dyadic_objective_limsup`](../../MovingSofaUniqueness/Selection.lean#L692), [`niche_subset_box`](../../MovingSofaUniqueness/Selection.lean#L623), [`polyNiche_subset_box`](../../MovingSofaUniqueness/Selection.lean#L684), [`mpc_area_usc`](../../MovingSofaOptimality/Balanced/CapGeometry.lean#L282),
[`mpc_area_lsc`](../../MovingSofaOptimality/Balanced/CapGeometry.lean#L296), [`mpc_niche_eventually`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L444).*

### Lemma 11.12 (dyadic supports determine a cap)

Two caps $K, L \in \mathcal{K}^\mathrm{c}_\omega$ with $h_K(t) = h_L(t)$ and
$h_K(t + \pi/2) = h_L(t + \pi/2)$ for every dyadic angle $t$ of every level are equal.

*Proof.* Support functions are continuous and the dyadic angles are dense in $[0, \omega]$, so
$h_K = h_L$ on $J_\omega = [0, \omega] \cup [\pi/2, \omega + \pi/2]$; also
$h_K = h_L = 0$ at $\omega + \pi$ and $3\pi/2$. A cap is the intersection of its supporting
half-planes at the normals of $J_\omega \cup \lbrace \omega + \pi, 3\pi/2 \rbrace$
([Definition 3.9](03-monotone.md#definition-39-cap-baek-definitions-241-and-242)). $\square$

*Lean: [`caps_eq_of_dyadic_supports`](../../MovingSofaUniqueness/Selection.lean#L759), [`eqOn_of_dyadic_eq`](../../MovingSofaUniqueness/Selection.lean#L730), [`caps_eq_of_upper_supports`](../../MovingSofaUniqueness/Selection.lean#L743).*

### Proposition 11.13 (selection; note 20, Proposition 1)

Let $\omega \in (0, \pi/2]$, and let $K_*$ be a cap of angle $\omega$ that maximizes
$\mathcal{A}_\omega$ with $\mathcal{A}_\omega(K_*) > 0$. There are a strictly increasing sequence
$(k_n)$, polygon caps $K_n \in \mathcal{K}^\mathrm{c}_{\Theta^{(k_n)}}$ and $R \ge 0$ such that

1. $K_n$ is a penalized maximizer for the dyadic samples of stage $k_n$ with target $K_*$;
2. $K_n \subseteq [-R, R] \times [0, 1]$ for every $n$;
3. $K_n \to K_*$ in the Hausdorff distance.

*Proof.* The penalized maximizers have a limit $L$. Their objectives are at least
$\mathcal{A}_\omega(K_*)$, and in the limit at most $\mathcal{A}_\omega(L) \le \mathcal{A}_\omega(K_*)$;
so their penalties tend to zero, which pins $L$ to $K_*$.

**Step 1. Penalized maximizers.** Proposition 11.10 gives a penalized maximizer at every stage, with
objective at least $\mathcal{A}_\omega(K_*)$, all in one box $[-R, R] \times [0, 1]$.

**Step 2. A limit.** By the Blaschke selection theorem
([Theorem 2.12](02-preliminaries.md#theorem-212-blaschke-selection-theorem)) a subsequence $K_n$, at
the stages $k_n$, converges in the Hausdorff distance to a convex body $L$. A Hausdorff limit of
polygon caps of angle $\omega$ is a cap of angle $\omega$, as in the proof of
[Theorem 4.35](04-balanced.md#theorem-435-existence-of-balanced-maximum-caps-baek-theorem-352).

**Step 3. The penalties vanish.** By Proposition 11.10, Lemma 11.11 and the maximality of $K_*$,
for every $\varepsilon > 0$ and all large $n$,

```math
0 \le P_{k_n}(K_n) \le \mathcal{A}_{\Theta^{(k_n)}}(K_n) - \mathcal{A}_\omega(K_*) \le \mathcal{A}_\omega(L) + \varepsilon - \mathcal{A}_\omega(K_*) \le \varepsilon .
```

**Step 4. The limit is $K_*$.** Let $t$ be a dyadic angle of level $m$. For $k_n \ge m$, persistence
(Lemma 11.7 (2)) gives
$w_m \bigl(h_{K_n}(t) - h_{K_*}(t)\bigr)^2 \le P_{k_n}(K_n) \to 0$, while
$h_{K_n}(t) \to h_L(t)$. So $h_L(t) = h_{K_*}(t)$, and in the same way
$h_L(t + \pi/2) = h_{K_*}(t + \pi/2)$. By Lemma 11.12, $L = K_*$. $\square$

*Lean: [`exists_selectedCapSequence`](../../MovingSofaUniqueness/Selection.lean#L871), [`SelectedCapSequence`](../../MovingSofaUniqueness/Selection.lean#L858), [`selected_sequence_bounded`](../../MovingSofaUniqueness/Selection.lean#L829),
[`mpc_blaschke`](../../MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean#L846), [`mpc_limit_isCap`](../../MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean#L236), [`penalty_tendsto_zero_of_objective`](../../MovingSofaUniqueness/Selection.lean#L715).*

*Remark (the formal route).* Note 20 maximizes $\mathcal{A}_n(C) - \lambda_n \int (h_C - h_{K_*})^2$
with $\lambda_n \to 0$, chooses $\lambda_n$ with $e_n / \lambda_n \to 0$ for the uniform
approximation error $e_n = \sup |\mathcal{A}_n - \mathcal{A}_\omega|$, and restricts the caps to a
box at the right angle. The formalization keeps the penalty fixed, samples it at persistent dyadic
normals of total weight at most one, and uses no box. Since the recovery polygon has penalty zero at
every stage, the one-sided bound of Lemma 11.11 and the maximality of $K_*$ suffice, and a
subsequence is enough for the rest of the proof; neither $\lambda_n \to 0$ nor the uniform
approximation is needed.

## 11.5 Raising one height

Recall from [Chapter 4](04-balanced.md) the quantities that balance at a maximum polygon cap. For a
polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$ and $t \in \Theta^\diamond$, $\sigma_K(t)$ is the
length of the edge of $K$ with normal $t$. The *polyline* $\mathbf{p}_K$ is the part of the boundary
of $F_\omega \setminus \mathcal{N}_\Theta(K)$ between $C_K^+(\omega)$ and $A_K^-(0)$, and
$\tau_K(t)$ is the total length of its segments with normal $t$
([Theorem 4.25](04-balanced.md#theorem-425-the-polyline-baek-theorem-344),
[Definition 4.26](04-balanced.md#definition-426-balanced-polygon-cap-baek-definitions-343345)). For
$t \in \Theta$, the niche has sides of total length $\tau_K(t)$ on the inner wall $b_K(t)$ and
$\tau_K(t + \pi/2)$ on $d_K(t)$. For $t \in \lbrace \omega, \pi/2 \rbrace$, its sides on the line
$l(t, 0)$ have total length $\sigma_K(t + \pi) - \tau_K(t)$
([Lemma 4.27](04-balanced.md#lemma-427-sides-of-the-polygon-niche-baek-lemma-345)). Call
$\sigma_K(t) - \tau_K(t)$ the *defect* at $t$. The normals $\omega$ and $\pi/2$, which carry the two
strips of the parallelogram, are *pinned*; the other defining normals are *floating*.

A function $h$ on $\Theta^\diamond$, a choice of *support values*, defines a cap
$\mathcal{C}_\Theta(h)$, the intersection of the half-planes $H_-(s, h(s))$, $s \in \Theta^\diamond$,
and $H_+(s, h(s) - 1)$, $s \in \lbrace \omega, \pi/2 \rbrace$, which close the two strips; a niche
$\mathcal{N}_\Theta(h)$; and the value
$\mathcal{A}_\Theta(h) = |\mathcal{C}_\Theta(h)| - |\mathcal{N}_\Theta(h)|$
([Definition 4.13](04-balanced.md#definition-413-cap-niche-and-area-of-support-values-baek-definition-333)).
For $h = h_K$ these are $K$, $\mathcal{N}_\Theta(K)$ and $\mathcal{A}_\Theta(K)$
([Propositions 4.15](04-balanced.md#proposition-415-compatibility-of-caps-baek-proposition-334) and
[4.16](04-balanced.md#proposition-416-compatibility-of-niches-baek-proposition-335)). Let
$h^+_\varepsilon$ be $h_K$ raised by $\varepsilon > 0$ at one normal $t \in \Theta^\diamond$.
[Lemma 4.29](04-balanced.md#lemma-429-the-balancing-step-baek-lemma-347) computes the first
variation:

```math
\Bigl| \mathcal{A}_\Theta(h^+_\varepsilon) - \mathcal{A}_\Theta(K) - \bigl(\sigma_K(t) - \tau_K(t)\bigr)\varepsilon \Bigr| \le C\varepsilon^2 \qquad (0 < \varepsilon \le \varepsilon_0) . \tag{11.1}
```

At a floating normal the cap gains a strip of area about $\sigma_K(t)\varepsilon$ and the niche one
of area about $\tau_K(t)\varepsilon$ (Figure 11.3, left). At a pinned normal both lines of the strip
move: the cap gains about $\sigma_K(t)\varepsilon$ at one side and loses about
$\sigma_K(t + \pi)\varepsilon$ at the other, and the niche loses about
$(\sigma_K(t + \pi) - \tau_K(t))\varepsilon$ along the moved line (Figure 11.3, right).

The raised values need not be the supports of the cap they define. If $\mathcal{C}_\Theta(h^+)$ is
a translate $C + v$ of a polygon cap $C$, then $\mathcal{A}_\Theta(h^+) \le \mathcal{A}_\Theta(C)$
([Proposition 4.19](04-balanced.md#proposition-419-reduction-to-a-cap-translate-baek-proposition-337),
[Theorem 4.18](04-balanced.md#theorem-418-translation-invariance-baek-theorem-336)). So penalized
maximality can compare $K$ with $C$.

### Lemma 11.14 (maximality bounds the defect)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$, $t \in \Theta^\diamond$, $\varepsilon_0 > 0$, and let
$P : [0, \varepsilon_0] \to \mathbb{R}$ satisfy, for every $\varepsilon \in (0, \varepsilon_0]$,

```math
P(\varepsilon) - P(0) \le b\varepsilon + D\varepsilon^2 \qquad \text{and} \qquad \mathcal{A}_\Theta(h^+_\varepsilon) - P(\varepsilon) \le \mathcal{A}_\Theta(K) - P(0) .
```

Then $\sigma_K(t) - \tau_K(t) \le b$. If $\sigma_K(t) = 0$, then $\sigma_K(t) - \tau_K(t) \le b$ for
every $b \ge 0$.

*Proof.* With (11.1), for all small $\varepsilon > 0$,

```math
\bigl(\sigma_K(t) - \tau_K(t)\bigr)\varepsilon - C\varepsilon^2 \le \mathcal{A}_\Theta(h^+_\varepsilon) - \mathcal{A}_\Theta(K) \le P(\varepsilon) - P(0) \le b\varepsilon + D\varepsilon^2 .
```

Divide by $\varepsilon$ and let $\varepsilon \to 0$. If $\sigma_K(t) = 0$, the defect is
$-\tau_K(t) \le 0 \le b$. $\square$

*Lean: [`polygon_defect_le_penalty_growth`](../../MovingSofaUniqueness/Variation.lean#L133), [`le_zero_of_mul_le_sq`](../../MovingSofaUniqueness/Variation.lean#L37),
[`assigned_comparison_of_actual`](../../MovingSofaUniqueness/Variation.lean#L114), [`polygon_defect_le_of_zero_facet`](../../MovingSofaUniqueness/Variation.lean#L157), [`lemma3_4_7`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L570),
[`proposition3_3_7`](../../MovingSofaOptimality/Balanced/PolygonCap.lean#L926).*

## 11.6 Floating normals

### Lemma 11.15 (raising a floating height)

Let $K \in \mathcal{K}^\mathrm{c}_\Theta$, let $t \in \Theta^\diamond$ be floating, $\varepsilon \ge 0$,
and $K^+ = \mathcal{C}_\Theta(h^+_\varepsilon)$. Then $K^+$ is a polygon cap that contains $K$; at
every defining normal $s \ne t$, $h_{K^+}(s) = h_K(s)$, and
$h_K(t) \le h_{K^+}(t) \le h_K(t) + \varepsilon$. Consequently, if the sampled supports of $K$ are
within $\eta$ of those of $K_*$, then

```math
P(K^+) - P(K) \le 2\eta\, w(t)\, \varepsilon + w(t)\, \varepsilon^2 .
```

*Proof.* Raising a floating height moves one half-plane outward and keeps the two strips, so $K^+$
is a polygon cap containing $K$. This is the first case of the proof of
[Lemma 4.30](04-balanced.md#lemma-430-the-pushed-cap-is-a-translate-baek-lemma-348), which does not
use $\sigma_K(t) > 0$. Hence $h_K \le h_{K^+}$. Since $K^+$ lies in the half-planes of
$h^+_\varepsilon$, also $h_{K^+} \le h^+_\varepsilon$ on $\Theta^\diamond$. Every sample normal lies
in $\Theta^\diamond$, so Lemma 11.5 (2) applies with $r = \varepsilon$. $\square$

*Lean: [`floatingCap`](../../MovingSofaUniqueness/Variation.lean#L187), [`floatingCap_polygon`](../../MovingSofaUniqueness/Variation.lean#L191), [`subset_floatingCap`](../../MovingSofaUniqueness/Variation.lean#L214), [`floatingCap_support_bounds`](../../MovingSofaUniqueness/Variation.lean#L228),
[`floatingCap_support_other`](../../MovingSofaUniqueness/Variation.lean#L243), [`floating_penalty_growth`](../../MovingSofaUniqueness/Variation.lean#L265).*

### Proposition 11.16 (floating defects; note 20, Proposition 2)

Let $K$ be a penalized maximizer for support samples on $\Theta$ with target $K_*$, and let
$|h_K(s_i) - h_{K_*}(s_i)| \le \eta$ at every sample. At every floating normal
$t \in \Theta^\diamond$,

```math
\sigma_K(t) - \tau_K(t) \le 2\eta\, w(t) . \tag{11.2}
```

*Proof.* The cap $K^+$ of Lemma 11.15 is a polygon cap, so penalized maximality gives
$\mathcal{A}_\Theta(K^+) - P(K^+) \le \mathcal{A}_\Theta(K) - P(K)$, and
$\mathcal{A}_\Theta(h^+_\varepsilon) \le \mathcal{A}_\Theta(K^+)$. Apply Lemma 11.14 with
$b = 2\eta\, w(t)$ and $D = w(t)$. $\square$

*Lean: [`floating_defect_le`](../../MovingSofaUniqueness/Variation.lean#L280).*

![Two copies of a polygon cap K with angle set {ω/2}, ω = 1, inside a dashed parallelogram, each with its polygon niche, a quadrilateral at the corner O, in orange. Left: the edge of K with normal ω/2 is drawn thick in blue, the side of the niche on the inner wall at ω/2 thick in orange; the raised cap K+ and its niche are dashed, each a strip of width ε wider along these two segments. Right: the top edge of K is drawn thick; dotted lines at heights ε and 1 + ε mark the horizontal strip moved up by ε, and the cap K′ cut by the moved strip and its niche are dashed](figures/11-selection/moves.svg)

*Figure 11.3.* The two moves, for a polygon cap $K$ with angle set $\lbrace \omega/2 \rbrace$,
$\omega = 1$, inside $P_\omega$ (dashed), and its polygon niche (orange). Left: raising the height
at the floating normal $t = \omega/2$ by $\varepsilon$ adds to the cap a strip along its edge of
length $\sigma_K(t)$, and to the niche a strip along its side of length $\tau_K(t)$ on the inner wall
$b_K(t)$; the new cap $K^+$ and its niche are dashed. Right: raising the height at the pinned normal
$\pi/2$ moves both lines of the horizontal strip up by $\varepsilon$; the new cap $K'$ gains a strip
along its top edge, of length $\sigma_K(\pi/2)$, and loses one along its bottom edge.

*Remark (the formal route).* Note 20's penalty is an integral over all normals, so raising one
height changes the support function on a neighbourhood of $t$, a "sine hat", which note 20
estimates. The formal penalty samples only defining normals, where the support of $K^+$ changes
only at $t$ (Lemma 11.15). The weights $w(t)$ in (11.2) add up to at most one, which
[Proposition 12.6](12-uniqueness.md#proposition-126-curvature-bounds-note-20-proposition-3) uses.

## 11.7 Pinned normals

In this section $\omega < \pi/2$. Every polygon cap $K$ of angle $\omega$ then contains the origin
$O$, so $h_K \ge 0$ (REPORT.md, E4). It also contains the corner $o_\omega$ of $P_\omega$, where
the lines $l(\omega, 1)$ and $l(\pi/2, 1)$ meet ([§4.5](04-balanced.md#45-maximum-polygon-caps)); so
$o_\omega \cdot u_s = 1$ for $s \in \lbrace \omega, \pi/2 \rbrace$.

### Lemma 11.17 (the pinned sandwich)

Let $\omega < \pi/2$, $K \in \mathcal{K}^\mathrm{c}_\Theta$, $t \in \lbrace \omega, \pi/2 \rbrace$,
$\varepsilon \in [0, 1]$, and let $K' = \mathcal{C}_\Theta(h^+_\varepsilon)$ be the cap whose strip
at $t$ has moved by $\varepsilon$. Then (Figure 11.4)

```math
(1 - \varepsilon) K + \varepsilon\, o_\omega \subseteq K' \subseteq (1 + \varepsilon) K .
```

If $|h_K| \le R$ everywhere, then $|h_{K'}(s) - h_K(s)| \le 2R\varepsilon$ for every $s$.

*Proof.* Let $p \in K$ and $q = (1 - \varepsilon)p + \varepsilon\, o_\omega$. By convexity $q \in K$,
so $q$ satisfies every defining inequality of $K'$ except possibly those of the strip at $t$. There
$q \cdot u_t = (1 - \varepsilon)\, p \cdot u_t + \varepsilon$ lies in
$[\varepsilon, 1] \subseteq [\varepsilon, 1 + \varepsilon]$, as $0 \le p \cdot u_t \le 1$; so
$q \in K'$. Conversely, let $p \in K'$; then $p/(1 + \varepsilon)$ satisfies the inequalities of
$K$. At a floating $s$,
$p \cdot u_s/(1 + \varepsilon) \le h_K(s)/(1 + \varepsilon) \le h_K(s)$, as $h_K(s) \ge 0$. At $t$,
$p \cdot u_t \in [\varepsilon, 1 + \varepsilon]$, so $p \cdot u_t/(1 + \varepsilon) \in [0, 1]$. The
other strip is scaled into itself. Taking supports,
$(1 - \varepsilon)h_K(s) + \varepsilon\, o_\omega \cdot u_s \le h_{K'}(s) \le (1 + \varepsilon)h_K(s)$,
and $|o_\omega \cdot u_s| \le R$ since $o_\omega \in K$. $\square$

*Lean: [`pinned_contract_mem`](../../MovingSofaUniqueness/Variation.lean#L346), [`pinned_div_mem`](../../MovingSofaUniqueness/Variation.lean#L380), [`pinned_raw_support_bound`](../../MovingSofaUniqueness/Variation.lean#L426).*

![A polygon cap K filled in light blue, the larger dashed copy (1 + ε)K scaled from the origin O, the green cap K′ whose strip at π/2 has moved up by ε, and the smaller dotted copy (1 − ε)K + ε o_ω shrunk towards the corner o_ω, with a legend on the right](figures/11-selection/sandwich.svg)

*Figure 11.4.* The pinned sandwich of Lemma 11.17 for a polygon cap $K$ with angle set
$\lbrace \omega/4, \omega/2, 3\omega/4 \rbrace$, $\omega = 1$, and $\varepsilon = 0.15$: the
cap $K'$ whose strip at $\pi/2$ has moved up by $\varepsilon$ (green) contains
$(1 - \varepsilon)K + \varepsilon\, o_\omega$ (dotted) and lies in $(1 + \varepsilon)K$
(dashed).

### Lemma 11.18 (moving back to standard position)

In Lemma 11.17, suppose that $K' = C + v$ for a polygon cap $C \in \mathcal{K}^\mathrm{c}_\Theta$ and
a vector $v$. Then $|v \cdot u_s| \le (2/\cos\omega + 1)\varepsilon$ for every $s$, and if
$|h_K| \le R$, then

```math
|h_C(s) - h_K(s)| \le \Bigl(2R + \frac2{\cos\omega} + 1\Bigr)\varepsilon \qquad \text{for every } s .
```

*Proof.* The polygon cap $C$ has $h_C(s) = 1$ and $h_C(s + \pi) = 0$ for
$s \in \lbrace \omega, \pi/2 \rbrace$. Its translate $C + v = K'$ lies in the strip
$a_s \le p \cdot u_s \le a_s + 1$ with $a_s = h^+_\varepsilon(s) - 1 \in [0, \varepsilon]$. A point
of $C$ on its upper line gives $v \cdot u_s \le a_s$, and one on its lower line gives
$v \cdot u_s \ge a_s$. So $v_y \in [0, \varepsilon]$ and
$v_x \cos\omega + v_y \sin\omega \in [0, \varepsilon]$, whence $|v_x| \le 2\varepsilon/\cos\omega$
and $|v \cdot u_s| \le |v_x| + |v_y|$. Finally $h_C(s) = h_{K'}(s) - v \cdot u_s$, and
Lemma 11.17 bounds $h_{K'}(s) - h_K(s)$. $\square$

*Lean: [`translated_strip_support`](../../MovingSofaUniqueness/Variation.lean#L455), [`pinned_translation_bound`](../../MovingSofaUniqueness/Variation.lean#L480), [`pinned_normalized_support_bound`](../../MovingSofaUniqueness/Variation.lean#L537).*

### Proposition 11.19 (pinned defects; note 20, Proposition 2)

Let $\omega < \pi/2$, and let $K$ be a penalized maximizer for support samples on $\Theta$ with
target $K_*$ and total weight $W$, with $|h_K| \le R$ everywhere and
$|h_K(s_i) - h_{K_*}(s_i)| \le \eta$ at every sample. Then for $t \in \lbrace \omega, \pi/2 \rbrace$,

```math
\sigma_K(t) - \tau_K(t) \le 2W\eta\, G_\omega, \qquad G_\omega = 2R + \frac2{\cos\omega} + 1 .
```

*Proof.* If $\sigma_K(t) = 0$, this is the second part of Lemma 11.14. If $\sigma_K(t) > 0$,
Lemma 4.30 gives $\varepsilon_0 > 0$ such that for $\varepsilon \in (0, \varepsilon_0]$ the cap
$\mathcal{C}_\Theta(h^+_\varepsilon)$ is a translate $C_\varepsilon + v_\varepsilon$ of a polygon
cap $C_\varepsilon$; this is where $\sigma_K(t) > 0$ is needed. By Lemma 11.18 every support of
$C_\varepsilon$ is within $G_\omega \varepsilon$ of that of $K$, so Lemma 11.5 (1) gives
$P(C_\varepsilon) - P(K) \le W(2\eta G_\omega \varepsilon + G_\omega^2 \varepsilon^2)$. Penalized
maximality compares $K$ with $C_\varepsilon$, and Lemma 11.14 with $b = 2W\eta\, G_\omega$ gives the
bound. $\square$

*Lean: [`pinned_defect_le`](../../MovingSofaUniqueness/Variation.lean#L580), [`lemma3_4_8`](../../MovingSofaOptimality/Balanced/MaximumPolygonCap.lean#L955).*

### Lemma 11.20 (the balance identity)

Every polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$ satisfies

```math
\sum_{t \in \Theta^\diamond} \sin t\, \bigl(\sigma_K(t) - \tau_K(t)\bigr) = 0 . \tag{11.3}
```

*Proof.* This is the identity in the proof of
[Lemma 4.28](04-balanced.md#lemma-428-an-unbalanced-cap-has-a-long-side-baek-lemma-346). Walking
from $A_K^-(0)$ to $C_K^+(\omega)$ along the upper boundary of $K$, or along the polyline
$\mathbf{p}_K$, gives $\sum_t \sigma_K(t)\, v_t = \sum_t \tau_K(t)\, v_t$, and
$v_t \cdot u_0 = -\sin t$. $\square$

*Lean: [`polygon_weighted_defect_zero`](../../MovingSofaUniqueness/Variation.lean#L636), [`mpc_sum_sigma_sin`](../../MovingSofaOptimality/Balanced/CapGeometry.lean#L720), [`mpc_sum_tau_sin`](../../MovingSofaOptimality/Balanced/Polyline.lean#L669).*

### Corollary 11.21 (two-sided defect bound; note 20, Proposition 2)

Under the hypotheses of Proposition 11.19, at every $t \in \Theta^\diamond$,

```math
\bigl| \sigma_K(t) - \tau_K(t) \bigr| \le \frac{2\eta W + 4W\eta\, G_\omega}{\sin t} .
```

At the pinned normals $\sin t \ge \sin\omega$.

*Proof.* Propositions 11.16 and 11.19 bound every defect from above, and (11.3) turns these upper
bounds into lower bounds. Let $e(t) = 2\eta\, w(t)$, plus $2W\eta\, G_\omega$ at the two pinned
normals. Then $d(t) = \sigma_K(t) - \tau_K(t) \le e(t)$ for every $t$, and $e \ge 0$. All defining
normals lie in $(0, \pi)$, so $0 < \sin t \le 1$, and by (11.3)

```math
-\sum_{s \ne t} \sin s\; e(s) \le -\sum_{s \ne t} \sin s\; d(s) = \sin t\; d(t) \le \sin t\; e(t) .
```

So $|\sin t\; d(t)| \le \sum_s e(s) \le 2\eta W + 4W\eta\, G_\omega$, since the weights $w(s)$ add
up to $W$. $\square$

*Lean: [`abs_selected_defect_le`](../../MovingSofaUniqueness/Variation.lean#L683), [`abs_weighted_defect_le`](../../MovingSofaUniqueness/Variation.lean#L56), [`abs_defect_le_div`](../../MovingSofaUniqueness/Variation.lean#L75),
[`selectorDefectBound`](../../MovingSofaUniqueness/Variation.lean#L645), [`selectorDefectBound_sum_le`](../../MovingSofaUniqueness/Variation.lean#L659).*

## 11.8 The pinned bounds

Recall the wedge end $W_K(t) = ((h_K(t) - 1)/\cos t, 0)$, where the inner wall $b_K(t)$ meets the
floor, the right wedge gap $w_K(t) = h_K(0) - (h_K(t) - 1)/\cos t$, its mirror image $z_K(t)$ on
the left side
([Definition 3.18](03-monotone.md#definition-318-wedges-their-ends-and-gaps-baek-definitions-253255)),
and the infima $w_K^\circ = \inf_{t \in (0, \omega)} w_K(t)$ and
$z_K^\circ = \inf_{t \in (0, \omega)} z_K(t)$
([Definition 5.3](05-rotation-angle.md#definition-53-wedge-gap-infima-baek-definition-411)). The
proof of [Theorem 5.5](05-rotation-angle.md#theorem-55-horizontal-sides-of-maximum-polygon-caps-baek-theorem-412)
shows $w_K^\circ \le \tau_K(\pi/2)$ for a maximum polygon cap and then uses its balance. The first
inequality holds for every polygon cap.

### Lemma 11.22 (wedge gaps and the polyline)

For $\omega < \pi/2$, every polygon cap $K \in \mathcal{K}^\mathrm{c}_\Theta$ satisfies
$w_K^\circ \le \tau_K(\pi/2)$ and $z_K^\circ \le \tau_K(\omega)$.

*Proof.* The bottom edge of $K$ runs from $O$ to $A = A_K^-(0) = (h_K(0), 0)$, so its length is
$\sigma_K(3\pi/2) = h_K(0)$. By Lemma 4.27 (2), the niche covers a part of it of length
$\sigma_K(3\pi/2) - \tau_K(\pi/2)$, so the rest has length $\tau_K(\pi/2)$. Each wedge $F_\omega \cap Q_K^-(t)$, $t \in \Theta$, meets the floor to the left of
$W_K(t)$, which lies at the distance $w_K(t) \ge w_K^\circ$ from $A$ (Figure 11.5). Moreover
$w_K^\circ \le h_K(0)$, as $w_K(t) \to h_K(0)$ when $t \to \omega$. So the niche misses the segment of
length $w_K^\circ$ of the bottom edge that ends at $A$, and $\tau_K(\pi/2) \ge w_K^\circ$. The bound
for $z$ is the same argument on the left side, along the line $l(\omega, 0)$. $\square$

*Lean: [`ang_wedgeGapWInf_le_tau`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L345), [`ang_wedgeGapZInf_le_tau`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L421), [`lemma3_4_5_two`](../../MovingSofaOptimality/Balanced/Polyline.lean#L1040).*

![A polygon cap K with three wedges, in a dashed parallelogram; its polygon niche in orange meets the floor in a segment from O to the rightmost of three orange wedge endpoints, marked W*; the rest of the bottom edge, from W* to the vertex A, is drawn thick in green, with a bracket below it labelled tau(π/2) = w(t*)](figures/11-selection/gap.svg)

*Figure 11.5.* Lemma 11.22 for a polygon cap $K$ with angle set
$\lbrace \omega/4, \omega/2, 3\omega/4 \rbrace$, $\omega = 1$. The niche (orange) meets the bottom
edge of $K$, from $O$ to $A = A_K^-(0)$, in the segment from $O$ to the rightmost wedge endpoint
$W^* = W_K(t^*)$ (the orange dots are the three wedge endpoints). The rest of the edge (green) has
length $\tau_K(\pi/2) = w_K(t^*) \ge w_K^\circ$.

### Proposition 11.23 (pinned bounds; note 20, Proposition 4)

Let $\omega \in (0, \pi/2)$, and let $K_*$ be a cap of angle $\omega$ that maximizes
$\mathcal{A}_\omega$ with $\mathcal{A}_\omega(K_*) > 0$. Then

```math
w_{K_*}^\circ \le \sigma_{K_*}(\pi/2) \qquad \text{and} \qquad z_{K_*}^\circ \le \sigma_{K_*}(\omega) .
```

*Proof.* Along the selection of Proposition 11.13 the pinned defects tend to zero, so the bound
$w^\circ \le \tau(\pi/2)$ of Lemma 11.22 becomes $w^\circ \le \sigma(\pi/2)$ in the limit.

Take the selection $K_n \to K_*$, in a box $[-R_0, R_0] \times [0, 1]$, and put
$\eta_n = d_\mathrm{H}(K_n, K_*) \to 0$. Then $|h_{K_n}(s) - h_{K_*}(s)| \le \eta_n$ at every normal,
so the sampled supports are within $\eta_n$. The box gives $|h_{K_n}| \le R = R_0 + 1$, and the
total weight is at most one (Lemma 11.7). At $t = \pi/2$, where $\sin t = 1$, Corollary 11.21 gives
$|\sigma_{K_n}(\pi/2) - \tau_{K_n}(\pi/2)| \le e_n = (2 + 4G_\omega)\eta_n \to 0$, so by
Lemma 11.22

```math
w_{K_n}^\circ - e_n \le \tau_{K_n}(\pi/2) - e_n \le \sigma_{K_n}(\pi/2) .
```

By [Lemma 5.4](05-rotation-angle.md#lemma-54-continuity-of-the-wedge-gap-baek-lemma-411),
$|w_{K_n}^\circ - w_{K_*}^\circ| \le (1 + \sec\omega)\eta_n \to 0$, so the left side tends to
$w_{K_*}^\circ$. The length of the edge at a fixed normal is upper semicontinuous under Hausdorff
convergence, by the sandwich after
[Lemma 6.7](06-surface-area.md#lemma-67-one-sided-derivatives-of-the-support-function),
so the limit is at most $\sigma_{K_*}(\pi/2)$. The bound for $z$ is the same at $t = \omega$, where
Corollary 11.21 divides by $\sin\omega > 0$. $\square$

*Lean: [`pinned_bounds_of_maximal_positive`](../../MovingSofaUniqueness/Variation.lean#L750), [`lemma4_1_1`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L265), [`ang_le_sigmaAt_of_tendsto`](../../MovingSofaOptimality/Angle/HorizontalSide.lean#L892).*

Theorem 5.6 proves these bounds for a balanced maximum cap; here they hold for every maximizing cap
of positive sofa area. [Chapter 12](12-uniqueness.md) uses them to rotate the monotone sofa of $K_*$
into a right-angle motion
([Proposition 12.13](12-uniqueness.md#proposition-1213-right-angle-motion-note-20-proposition-4)).
