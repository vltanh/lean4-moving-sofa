# A six-point hand certificate for short-chord optimality

**Scope.** This extends FL's ordinary-area argument to some common face lengths below one. It proves full turns and zero clipping from six actual body points and two explicit inequalities. It does not assert that all short-face maximizers satisfy those inequalities. The final sharp bound uses the branch's written weighted theorem WV2, whose historical chain is not independently verified here. Labels SCG are local.

Baseline: `bbd0e986b988b5b2cb30e1ec81606f8e92584078`. The new geometry uses no curvature, smoothness, stationary variation or computer search.

## 1. The six retained points and the certificate

Let S be a compact connected ambidextrous body in the common incoming strip 0<=y<=1. Its horizontal projection is [l,r]. Suppose that for a<b it contains all four points

$$(a,0),(a,1),(b,0),(b,1),$$

and actual horizontal extreme witnesses

$$P=(l,y_L),\qquad Q=(r,y_R),\qquad0\le y_L,y_R\le1.$$

The four points need not be corners of a rectangle contained in S. Their convex hull is a rectangle contained in K=conv(S), which is all that is used for support bounds. Put

$$T=b-a,\quad R=r-a,\quad B=b-l,$$

$$m_R=\min(y_R,1-y_R),\qquad m_L=\min(y_L,1-y_L).$$

For 0<T<1 the certificate is

$$R>1,\quad B>1,$$

$$\boxed{2TR+m_R(1-T^2)>1+T^2,\qquad
2TB+m_L(1-T^2)>1+T^2.}\tag{SCG.1}$$

All tests are rational when the input points are rational. No trigonometric evaluation is needed to check the certificate. When T>=1, the simpler four-point unit-square argument applies instead.

**Theorem SCG1.** Under either T>=1 or the short-chord certificate SCG.1, one has |S|<=M, provided the existing weighted inequality WV2 is used. More specifically, for |S|>8/5 the conditions force both conventional reduced turns to be full and give the exact no-clipping upper comparison

$$\boxed{|S|\le\Psi(U)+\Psi(V)\le M.}\tag{SCG.2}$$

Here U,V are the downward caps of the actual upper and reflected lower hull boundaries. They are not postulated weighted maximizers; WV2 is the universal value bound on its cap domain.

## 2. A two-vector strip lemma

Let 0<T<1, R>1 and 0<=m<=1. Put

$$t_0=\pi/2-2\arctan T,\qquad
\cos t_0=\frac{2T}{1+T^2},\quad
\sin t_0=\frac{1-T^2}{1+T^2}.$$

If 2TR+m(1-T^2)>1+T^2, then

$$\boxed{\max(T\cos t+\sin t,\ R\cos t+m\sin t)>1
\quad(0<t<\pi/2).}\tag{SCG.3}$$

**Proof.** For t>t0, the first term exceeds one: equivalently T>(1-sin t)/cos t, whose right side is strictly decreasing and equals T at t0. For 0<=t<=t0, the second term is a concave function of t because its second derivative is its negative and its value is nonnegative. At zero it equals R>1; at t0 it is greater than one by the hypothesis. Concavity puts all intermediate values above one. This includes t=t0. QED.

When T>=1 the first term alone is greater than one on the open quarter. Replacing t by pi/2-t gives the corresponding lemma with cosine and sine exchanged.

Strictness in SCG.1 is retained. Replacing its > by >= need not exclude a terminal strip at the equality direction; no such boundary extension is claimed.

## 3. Full turns follow, rather than being assumed

If |S|<=8/5, then |S|<M by the existing exact candidate lower bound. Otherwise use the branch's conventional-motion reduction, which gives positive reduced endpoint magnitudes at most pi/2, with terminal body-frame strips of width one.

Write f(t)=h_K(t), g(t)=h_K(t+pi/2), c=cos t and s=sin t. The retained upper points at b and r imply

$$f(t)-ac\ge\max(Tc+s,Rc+y_Rs)>1.$$

The last inequality follows from SCG.3 since y_R>=m_R. Since (a,0) belongs to K, its width in direction (c,s) is at least f(t)-ac, hence exceeds one for every interior t. The lower turn cannot terminate at any such angle.

For the upper turn reflect y in one half. The same argument uses the retained points (b,1), (r,1-y_R) and (a,0) of the reflected body; 1-y_R>=m_R. Its outgoing widths also exceed one. Thus both turns are full. For T>=1 the identical conclusion follows from the contained unit square.

Only support widths of the actual hull are used. Feasibility of the convex hull as a sofa is not assumed. Canonical support tightening of the actual motions is now justified for both complete quarters.

## 4. Retained points force both niches between a and b

The other extreme witness and top point at a give

$$g(t)+bs\ge\max(Ts+c,Bs+y_Lc)>1$$

by the sine/cosine-swapped strip lemma. The reflected inequality follows because 1-y_L>=m_L. Hence, for each turn, both strict inequalities

$$f(t)-ac>1,\qquad g(t)+bs>1\tag{SCG.4}$$

hold throughout the open quarter.

The actual point (a,0) must avoid the canonical forbidden quadrant. Its first inner-wall inequality is strictly violated by SCG.4, so its second one must be satisfied. Therefore

$$g(t)+as\le1.$$

Similarly, (b,0) strictly violates the second inner-wall inequality and must satisfy the first, giving f(t)-bc<=1. Every forbidden point (x,y) with y>=0 consequently satisfies

$$x>\frac{1-g(t)}s\ge a,\qquad
x<\frac{f(t)-1}c\le b.$$

Thus the full lower niche projects into (a,b). The two retained reflected floor points give exactly the same statement for the full upper niche. This proof does not require the positive triangles to form a connected family or their corner heights to have a fixed sign.

## 5. Ordinary-area accounting

Let A(x),D(x) be the upper and lower convex-hull boundaries over [l,r]. Let U have downward roof A and V have downward roof 1-D. They are normalized height-one convex caps with width W=r-l. Their upper supports agree with those of K and its vertical reflection.

Connectedness of S makes every fiber nonempty. A surviving point over x bounds the lower niche height from above and the reflected upper niche height in the same way. In particular those heights never exceed their respective cap roofs. By Section 4 all positive niche material lies over a<x<b, where K contains the entire height-one rectangle. Both niches therefore lie in K. They cannot overlap with positive fiber length: their union would then cover a whole vertical line through S, contradicting its projection.

As in FL, no clipping or overlap term remains:

$$|S|\le |K|-|N(U)|-|N(V)|.$$

The exact hull area is |K|=|U|+|V|-W. Substitution proves the first inequality in SCG.2, and WV2 proves the second. All boundary lines have area zero; the open forbidden-quadrant convention is preserved.

## 6. An explicit extension below face length one

Take l=0, r=12/5, a=1, b=7/5, and y_L=y_R=1/2. Then T=2/5 and R=B=7/5. The left and right margins in SCG.1 are both

$$2(2/5)(7/5)+(1/2)(1-4/25)-(1+4/25)=19/50>0.$$

Therefore any feasible body with those retained witnesses is covered, even though the two vertical chords are separated by only 2/5. This example certifies a conditional geometric region; it is not a claim that the six-point polygon itself supplies a new extremal sofa.

## 7. Remaining scope

The criterion gives a finite, hand-checkable sufficient condition for full turns and zero clipping in the short-face problem. It does not force the four full-height points to exist at every maximizing hull. A point face may supply only one such vertical column, and T tending to zero makes SCG.1 ineffective with bounded extremes. Such cases are not excluded by this theorem.

The sharp comparison depends on WV2, while Sections 2--4 are elementary geometric results independent of that weighted proof. No CI, Lean/Lake compilation, dependency installation, manuscript build or long computation is used. All written arguments remain subject to independent review.
