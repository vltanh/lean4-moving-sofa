# Constructing a tail background with a complementary curvature condition

**Scope.** This supplies an explicit background construction for a restricted input class, rather than only assuming the existence of a CT background. It replaces CT's lower tail-density condition by an exact complementarity identity. The construction still does not admit arbitrary competitors: it requires a regular middle, half-height geometry, a smooth-fit barrier, and matching output face intervals for the paired-area application. Labels CB are local. Baseline: `9307910d73167a19f92c1785433aa27febacd375`.

The envelope construction is the one-dimensional GM construction with ceiling one half instead of one, applied only to two tails. The area argument uses CT's elementary support pairing, not a new optimization of the background functional. All statements are written and self-reviewed; no computation is a proof premise.

## 1. Input hypotheses that can be tested on a cap

Let U be a compact convex downward cap of height exactly one and horizontal projection I=[l,r], of width W>2. Assume

$$I\times[0,1/2]\subseteq U\subseteq I\times[0,1],\qquad H_N(U)\le1/2.$$

Put L=pi/2 and choose

$$0<\eta<\frac{\min(1/2,W-2)}{2(W+1)}.\tag{CB.1}$$

Outside the two open tail intervals J_-=(L-eta,L) and J_+=(L,L+eta), assume the open-quarter curvature measure of the upper support h is dominated by dtheta. Assume h is differentiable at the two outer cut normals t_-=L-eta and t_+=L+eta, with no curvature atom there. No density or smoothness is required inside the two tails. A top atom at L is allowed, including a point top face before repair.

At the outer end t_e of each tail define the half-curvature arc

$$q_e(t)=\tfrac12+(h(t_e)-\tfrac12)\cos(t-t_e)+h'(t_e)\sin(t-t_e).$$

Require the explicit smooth-fit barrier

$$\boxed{h(t)\le q_e(t)\text{ on the corresponding closed tail interval}.}\tag{CB.2}$$

This is not inferred from proximity to the reference. It can fail, and is a genuine restriction. It is automatically true for inward shavings of an unchanged radius-one-half support arc when the outer-end value and derivative are retained.

## 2. A least half-curvature majorant on each tail

For a closed tail J of midpoint m_J, put

$$k(t)=\cos(t-m_J)>0,\quad z=\tan(t-m_J),\quad
\phi(z)=\frac{1/2-h(t)}{k(t)}.$$

Let Cphi be the lower convex envelope on the corresponding compact z interval, with the endpoint inequalities included, and define

$$\bar h(t)=\tfrac12-k(t)C\phi(z(t)).\tag{CB.3}$$

Off the two tails retain bar h=h. Since h is a convex-body support, its nonnegative curvature measure sigma gives

$$\phi''=\tfrac12 k^3dz-z_*(k\sigma).$$

The one-dimensional envelope lemma GM1 therefore gives endpoint equality and

$$0\le(C\phi)''\le\tfrac12 k^3dz.$$

On the interior of J, bar h is W^(2,infinity) and

$$0\le\bar h+\bar h''\le1/2.$$

On every component where bar h>h the convex envelope is affine, and consequently bar h+bar h''=1/2 almost everywhere. Thus, with e=bar h-h,

$$\boxed{e\ge0,\qquad e(2\rho_B-1)=0\quad\text{a.e. on both tails}.}\tag{CB.4}$$

The formula includes contact sets with density smaller than one half: on those sets e=0. No positive sign for an unsupported surplus is being assumed.

## 3. Why gluing does not insert a new interior atom

The barrier q_e satisfies q_e''+q_e=1/2. Therefore (1/2-q_e)/k is affine in z and lies below phi by CB.2. It is an admissible affine minorant, so

$$h\le\bar h\le q_e.$$

At the outer cut normal, h and q_e have the same value and derivative. The sandwich forces bar h to have that same one-sided derivative. The repaired and unchanged pieces thus join without a curvature atom at either outer cut.

At L the common support value stays one. On the left, e(L)=0 and e>=0 imply e'(L-)<=0; on the right they imply e'(L+)>=0. The top derivative jump therefore only increases. The original top atom is nonnegative. All other joins are unchanged.

The resulting upper support has nonnegative curvature everywhere, with the usual unchanged lower-half support of a downward cap. It is the support of a genuine compact convex cap B, with

$$U\subseteq B\subseteq I\times[0,1],\quad H(B)=1,\quad W(B)=W,$$

and global open-quarter curvature between zero and one. The height and width assertions follow from the unchanged axis supports; containment follows from support domination. This is not a smoothing prescription or a claim that the input itself has become regular without changing it.

## 4. The other single-background CT hypotheses follow

Translate horizontally to I=[0,W]. Write f=h_B(t), g=h_B(t+L), p=f'-g+1, q=g'+f-1, u=f''+f and v=g''+g. Standard support-point depth comparisons give

$$-W\le p\le1,\qquad-1\le q\le W.$$

Together with 0<=u,v<=1 and the kinematic equations, this gives |p'|,|q'|<=W+1 almost everywhere.

Let [a,b] be B's top face. The horizontal support-point displacements satisfy

$$a-l=\int_0^L v(t)\cos t\,dt\le1,\qquad
r-b=\int_0^L u(t)\sin t\,dt\le1.$$

Hence b-a>=W-2>0, q(0)=r-a-1>=W-2 and p(L)=1-(b-l)<=2-W. Since B contains the half-height rectangle, p(0)>=1/2 and q(L)<=-1/2. CB.1 and the derivative bound now imply

$$p,q>0\text{ on }[0,\eta],\qquad p,q<0\text{ on }[L-\eta,L].$$

The two inner tail abscissa intervals have lengths at most eta each, by 0<=u,v<=1. Their separation is at least b-a-2eta>0. Thus the CT sign and tail-separation hypotheses hold; they need not be postulated separately for this construction.

Every positive corner height of U is at most H_N(U)<=1/2, since its open quadrant approaches its corner from below. At middle turn angles [eta,L-eta], the two supports used by B are unchanged from U, so those corner heights are unchanged. On either end-angle interval, the rectangle bound gives

$$c_{B,y}(t)\le W\sin t\cos t+1-\sin t-\cos t\le W\eta<1/4.$$

Consequently H_N(B)<=1/2. The unit-curvature intercept argument confines its niche to (a,b). Thus B has all the single-cap geometric hypotheses required for CT's pairing, apart from the lower density bound that will be replaced by CB.4.

## 5. The transfer needs complementarity, not a pointwise lower bound

Set e_f=h_B(t)-h_U(t) on the late first-quarter tail, and e_g=h_B(t+L)-h_U(t+L) on the early second-quarter tail. Both are nonnegative and vanish outside their tails.

The same two global tangency and angle-pruning arguments as CT apply using only unit upper curvature, the sign conditions and separated tails. For the right tail, the background outer and inner abscissae have derivatives

$$dx_{outer}=-u\sin t\,dt,\qquad dx_{inner}=(1-u)\sin t\,dt.$$

They are absolutely continuous and monotone. Strict monotonicity of the outer abscissa is unnecessary: the ordinary one-dimensional monotone substitution formula includes flat intervals, on which its Jacobian is zero. Its image point also has zero abscissa measure. The first-wall support tests therefore give

$$\text{niche saving}\le\int e_f(1-u),\qquad
\text{outer cap loss}\ge\int e_f u.$$

The reflected left-tail calculation gives the analogous pair with v. The entire niche saving is confined to these two tails. The loss over the old top-face interval is disjoint from the exterior arc losses. Subtracting yields the CT estimate with its sign left explicit:

$$\Psi(B)-\Psi(U)\ge
\int_a^b(1-A_U(x))dx+\int e_f(2u-1)+\int e_g(2v-1).$$

Both last integrals vanish by the constructed complementarity CB.4. Hence:

**Theorem CB1 (constructed single-cap transfer).** The cap B explicitly produced by CB.3 satisfies

$$\boxed{\Psi(B)-\Psi(U)\ge\int_a^b(1-A_U(x))dx.}\tag{CB.5}$$

This does not contradict HC's density-one-quarter example. For an input already below the half-curvature ceiling, the envelope need not raise that input at all. No comparison with HC's arbitrarily chosen pre-cut background is asserted. The background here is tied to the input by the obstacle/complementarity condition.

## 6. A constructive two-cap admission test, with its unresolved part visible

Apply the construction independently to two actual caps U_1,U_2 of the same width and projection. If their two output backgrounds B_1,B_2 have the same top-face interval [a,b], then their two face-loss budgets pay the actual clipping, and CT's final argument gives

$$\boxed{|E(U_1,U_2)|\le\Psi(B_1)+\Psi(B_2)\le M.}\tag{CB.6}$$

The last inequality uses the established SR/AF comparison on these now regular backgrounds, not weighted maximality of either input cap. The full canonical envelope is connected through the midline because input niches and input roofs satisfy the half-height hypotheses.

Matching output faces is an explicit equality of the two pairs of one-sided derivatives at L. It has not been proved automatically. In addition, arbitrary competitors may fail the regular-middle, half-height or outer smooth-fit tests. An original partial-turn body still needs valid completion before its containment in this full envelope may be inferred.

Thus CB supplies a genuine construction and removes an independent lower-tail-density assumption, but it is not global background admission. There is no claim that either remaining global frontier has been closed.

No numerical solver, interval search, CI, Lean/Lake compilation, dependency installation or manuscript build is used. The construction and estimates are hand proofs with the GM/CT/SR/AF dependencies stated explicitly.
