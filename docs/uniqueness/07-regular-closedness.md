# 07. Gerver's sofa is the closure of its interior

Date: 2026-10-02. Status: pen-and-paper deduction from the repository's existing Gerver-envelope and cap facts; not a new Lean theorem. No extra numerical enclosure or assumption that the boundary is a Jordan curve is needed.

This is the set-recovery property required in note 03. A drawing of a piecewise analytic boundary alone would not prove it, since a piecewise analytic set can have zero-area appendages.

## Available inputs

Use the standard Gerver frame of `MovingSofaOptimality/Gerver/StructureCap.lean` and `MovingSofaOptimality/Gerver/Niche.lean`, with L=pi/2, phi<theta<L-theta<L-phi. Write the rotation path as x(t), with

    x'(t)=alpha(t)u_t+beta(t)v_t,
    B(t)=x(t)+alpha(t)v_t,
    D(t)=x(t)-beta(t)u_t.

The existing `gn_envHyp` verifies the hypotheses of `EnvHyp` in `Envelope.lean`, including:

- alpha<0 and beta>0 on (0,L), and r(t)=-alpha(t)/beta(t) is nondecreasing;
- B'(t)=(rho_A(t)-1)v_t and rho_A<1 on [L-theta,L];
- D'(t)=(1-rho_C(t))u_t and rho_C<1 on [0,theta];
- B(L-theta)=x(phi), D(theta)=x(L-phi), and B(L)_y=D(0)_y=0;
- the niche is precisely the region at nonnegative height strictly below the curve formed by D([0,theta]), x([phi,L-phi]), and B([L-theta,L]).

The derivative statements for B,D are piecewise, away from the finitely many phase junctions; the curves themselves are continuous. The existing `gs_path_snd_le_one` supplies x(t)_y<=1 throughout [0,L].

The cap K is convex, downward closed above the x-axis, and has a horizontal top edge from C(0) to A(L) at height 1. Here A=B+u and C=D+v. All these inputs are proved before this research branch; see `gn_envHyp`, `env_niche_eq`, `gs_path_snd_le_one`, `gs_A_mem_K`, and `gs_C_mem_K`.

## 1. The niche boundary is a continuous graph

Along D, the horizontal derivative is (1-rho_C)cos t>0 away from the finitely many junctions. Along B it is (1-rho_A)sin t>0. Along x it is alpha cos t-beta sin t<0. Thus D followed by x in reverse and then B is a continuous curve with strictly increasing horizontal coordinate. The junction identities join the pieces without gaps or overlaps.

It is therefore the graph of a continuous height function H on

    I=[D(0)_x, B(L)_x].

The interval has positive length. Its endpoint heights are zero. The envelope theorem says that the niche consists of the points with x-coordinate in I and 0<=y<H(x). Extend H by zero outside I when convenient.

## 2. The cap is a full height-one rectangle over the niche's horizontal range

Because v_0=u_L=(0,1),

    C(0)=D(0)+(0,1),    A(L)=B(L)+(0,1).

Thus I is exactly the horizontal projection of the cap's top edge. Convexity and downward closure imply

    I x [0,1] subset K.

Since every cap point has height at most 1, the vertical section of K over every x in I is exactly [0,1].

## 3. The niche height is below 1 except possibly at one point

For 0<t<=theta,

    D(t)_y=x(t)_y-beta(t)sin t<1.

Its endpoint D(0) has height zero. Likewise B(t)_y=x(t)_y+alpha(t)cos t<1 for L-theta<=t<L, and B(L) has height zero.

Only the x-piece could reach height 1. If x(t)_y=1 at a parameter in [phi,L-phi], the global bound x_y<=1 and differentiability at this interior parameter of (0,L) imply

    0=x'(t)_y=beta(t)(cos t-r(t)sin t),
    hence r(t)=cot t.

The left side r is nondecreasing; cot is strictly decreasing on (0,L). This equality holds at most once. Consequently H<=1 everywhere on I and H<1 except possibly at a single abscissa. In particular H<1 on a dense subset of I. No assumption that the maximum height is strictly below 1 is needed.

## 4. Recover every point from interior points

Let G=K minus N(K), as established by `gs_gerverSofa_eq`.

For a point (x,y) in G with x in I, its vertical coordinate lies in [H(x),1]. Choose x_n in the interior of I with H(x_n)<1 and x_n->x. Continuity of H allows y_n in (H(x_n),1) with y_n->y. The strict inequalities and continuity show that each (x_n,y_n) lies in the interior of G. This includes endpoints of I, bottom points, top points, and the possible single height-one contact.

For a point of G whose abscissa is outside I, an entire neighborhood of that abscissa misses the niche. The full-dimensional compact convex body K is the closure of its interior, so the point is again a limit of interior points of G. Full dimensionality follows already from the rectangle in Section 2.

We have proved

    G=closure(interior(G)).

The reverse inclusion uses that G is closed, which also follows directly from the moving-sofa construction (or from the continuous height description).

## Consequence

If a Euclidean isometry U places a closed moving sofa S inside G and |S|=|G|, then U(S)=G by the lemma in note 03: a missing interior point would give a positive-area missing ball, and closure recovers the entire set.

Thus a shape-preserving containment reduction rules out both proper closed equal-area subsets and zero-area decorations of the starting sofa. The argument does not mistake equality almost everywhere for equality of sets.
