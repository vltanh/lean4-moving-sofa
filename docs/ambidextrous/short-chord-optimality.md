# A six-point hand certificate for short-chord optimality

**Scope.** This extends FL's ordinary-area argument to some common face lengths below one. It proves full turns and zero clipping from six actual body points and two explicit inequalities. It does not assert that all short-face maximizers satisfy those inequalities. The final sharp bound uses the branch's written weighted theorem WV2, whose historical chain is not independently verified here. Labels SCG are local.

Baseline: `bbd0e986b988b5b2cb30e1ec81606f8e92584078`. The new geometry uses no curvature, smoothness, stationary variation or computer search.

## 1. The six retained points and the certificate

Let S be a compact connected ambidextrous body in the common incoming strip 0<=y<=1. Its horizontal projection is [l,r]. Suppose that for a<b it contains all four points

$$(a,0),(a,1),(b,0),(b,1),$$

and actual horizontal extreme witnesses

$$P=(l,y_L),\qquad Q=(r,y_R),\qquad0\le y_L,y_R\le1.$$

The rectangle between the four points need not be contained in S. It is contained in K=conv(S), which suffices for support bounds. Put

$$T=b-a,\quad R=r-a,\quad B=b-l,$$

$$m_R=\min(y_R,1-y_R),\qquad m_L=\min(y_L,1-y_L).$$

For 0<T<1 the certificate is

$$R>1,\quad B>1,$$

$$\boxed{2TR+m_R(1-T^2)>1+T^2,\qquad
2TB+m_L(1-T^2)>1+T^2.}\tag{SCG.1}$$

All tests are rational when the input points are rational. No trigonometric evaluation is needed. For T>=1, the simpler four-point unit-square argument applies instead.

**Theorem SCG1.** Under either T>=1 or SCG.1, one has |S|<=M, using the existing weighted inequality WV2. For |S|>8/5 the conditions force both conventional reduced turns to be full and give

$$\boxed{|S|\le\Psi(U)+\Psi(V)\le M.}\tag{SCG.2}$$

U,V are the downward caps of the actual upper and reflected lower hull boundaries. They are not assumed to maximize the weighted objective; WV2 is used as a universal bound on its cap domain.

## 2. A two-vector strip lemma

Let 0<T<1, R>1 and 0<=m<=1. Put

$$t_0=\pi/2-2\arctan T,\qquad
\cos t_0=\frac{2T}{1+T^2},\quad
\sin t_0=\frac{1-T^2}{1+T^2}.$$

If 2TR+m(1-T^2)>1+T^2, then

$$\boxed{\max(T\cos t+\sin t,\ R\cos t+m\sin t)>1
\quad(0<t<\pi/2).}\tag{SCG.3}$$

**Proof.** For t>t0, the first term exceeds one: equivalently T>(1-sin t)/cos t, whose right side decreases strictly and equals T at t0. On [0,t0], the second term is concave because its second derivative is its negative and its value is nonnegative. Its endpoint values are greater than one, so all intermediate values are greater than one as well. This includes t=t0. QED.

For T>=1 the first term alone exceeds one throughout the open quarter. Replacing t by pi/2-t exchanges sine and cosine. Strictness in SCG.1 is retained: its weak version need not exclude a terminal strip at the equality direction.

## 3. Full turns follow, rather than being assumed

If |S|<=8/5, then |S|<M by the existing exact lower bound for M. Otherwise use the earlier conventional-motion reduction, with positive reduced endpoints at most pi/2 and terminal strips of width one.

Write f(t)=h_K(t), g(t)=h_K(t+pi/2), c=cos t and s=sin t. The retained upper point at b and the right extreme imply

$$f(t)-ac\ge\max(Tc+s,Rc+y_Rs)>1$$

by SCG.3 and y_R>=m_R. The point (a,0) supplies the opposite support bound, so the width of K in direction (c,s) exceeds one for every interior t. The lower turn cannot end there.

Reflect y in one half. The same argument uses 1-y_R>=m_R and forces the upper turn to be full. For T>=1 the contained unit square gives the same conclusion. These are widths of the actual hull; feasibility of the convex hull as a sofa is not assumed. Canonical support tightening is now valid for both complete quarters.

## 4. Retained points force both niches between a and b

The left extreme and upper point at a give

$$g(t)+bs\ge\max(Ts+c,Bs+y_Lc)>1$$

by the sine/cosine-swapped strip lemma. Reflection uses 1-y_L>=m_L. Hence both turns satisfy

$$f(t)-ac>1,\qquad g(t)+bs>1\tag{SCG.4}$$

on the open quarter.

The actual point (a,0) avoids the forbidden quadrant. Its first inner-wall condition is strictly violated by SCG.4, so it must satisfy the second. This gives g(t)+as<=1. Likewise (b,0) must satisfy the first, giving f(t)-bc<=1. Every forbidden point (x,y) with y>=0 therefore obeys

$$x>\frac{1-g(t)}s\ge a,\qquad x<\frac{f(t)-1}c\le b.$$

The lower positive niche projects into (a,b), and the two reflected retained points prove the same for the upper niche. No connected-family hypothesis on the niche triangles or sign assumption on their corner heights is needed.

## 5. Ordinary-area accounting

Let A(x),D(x) be the upper and lower hull boundaries. The downward caps with roofs A and 1-D have height one, common width W=r-l and the appropriate upper supports. Connectedness of S makes every fiber nonempty, and a surviving point bounds the two niche heights by their corresponding cap roofs.

All positive niche material lies over (a,b), where K contains the full height-one rectangle. Thus both niches lie in K. They cannot overlap with positive fiber length, since their union would cover a whole vertical line through the projection of S. Consequently

$$|S|\le |K|-|N(U)|-|N(V)|.$$

The exact hull-area identity |K|=|U|+|V|-W gives SCG.2 after applying WV2. Boundary lines have area zero and the open-quadrant convention is preserved.

## 6. Verified example and a discarded parameter illustration

Section 5 of [central-short-face-optimality.md](central-short-face-optimality.md) constructs an actual full-turn body from an ellipse with semiaxes 7/10 and 1/2, horizontally added to a segment of length 9/10. Its actual hull has W=23/10, T=9/10, and both horizontal extreme heights are one half. Its two SCG margins equal 233/200. The proof there verifies positive surviving fibers, retained face endpoints and the actual hull identity.

The first draft displayed W=12/5,T=2/5 as arithmetic parameters satisfying SCG.1. That was not a verified feasible example. The later FAS flank inequalities show those parameters are incompatible with full-turn feasibility. They must not be used to argue that a geometric class is nonempty; the explicit ellipse body replaces them.

## 7. Remaining scope

The criterion does not force four full-height points to exist at every maximizing hull. A point face may supply only one such vertical column, and T tending to zero makes the strict tests ineffective with bounded extremes.

The later FAS theorem derives the SCG conditions for all sufficiently wide full-turn aligned positive-face bodies, while CSF gives additional cases where full turns themselves follow. Neither covers every short-face configuration.

The sharp constant uses WV2; the strip and confinement arguments are elementary and independent of that weighted proof. No CI, Lean/Lake compilation, dependency installation, manuscript build or long computation is used. The written dependency chain still requires independent review.
