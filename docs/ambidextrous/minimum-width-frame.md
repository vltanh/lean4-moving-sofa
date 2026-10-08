# Minimum-width frame: reviewed geometry and signed area accounting

**Attribution.** This is a reviewed restatement of the user-supplied minimum-width-frame package, not a verbatim copy or a claim of independent invention. The original archive, proof, checker and author output are preserved unchanged in the reproduction bundle; hashes and corrections are in `minimum-width-package-review.md`. Labels MF distinguish this restatement from the original local MW labels and older repository labels.

The result supplies an actual-body change of frame and conditional area criteria. It does not close the general full-turn theorem. All arguments and historical inputs remain self-reviewed.

## 1. Transport to the minimum of the available safe-strip component

Let S be a compact connected full-turn body of positive area, and let K=conv(S). Write w(theta) for directional width. Let J be the connected component of {w<=1} containing the incoming normal. For competitive bodies J is a bounded closed interval in a lift of the angle circle: some width exceeds one, since otherwise two perpendicular strips would put the body in a rectangle of area at most one.

SI2 transports both full turns, with no change in S or area, to every normal in J. Choose a minimum of w on J. Its width is H=1-s with 0<H<=1. Rotate and translate, without dilation, so K has bottom and top supporting lines y=s and y=1. Denote its horizontal projection I=[l,r], W=r-l; top face [a,b] at height one; bottom face [c,d] at height s.

**Theorem MF1 (overlap).** The frame can be chosen so

$$\boxed{c\le b,\qquad a\le d.}$$

**Proof.** The one-sided support derivative formulas give w'(L-)=c-b and w'(L+)=d-a, L=pi/2. If min_J w<1, the minimum is interior to J and is a local minimum, giving the two signs. If min_J w=1 and J contains an interval, choose an interior point where w is constant. If J is a singleton, a positive left derivative or negative right derivative would put an adjacent interval in {w<1}, contradicting singleton connectedness. Thus the same signs hold. QED.

There may be other safe-strip components elsewhere; it is not asserted that w>1 everywhere outside J. The direction chosen need only minimize within this component. Horizontal width changes under rotation; any competitive width bound must be applied in the new representation rather than copied from the old coordinates.

## 2. Exact slack identity

Write the convex hull's fibers as [B(x),A(x)], so s<=B<=A<=1. Set

$$U=\{(x,y):x\in I,\ 0\le y\le A(x)\},$$

$$V=\{(x,y):x\in I,\ 0\le y\le1+s-B(x)\}.$$

Both are downward convex caps of height one and width W. The upper supports of U are those of K; those of V are those of the reflection rho_s(x,y)=(x,1+s-y) applied to K. Let n_U,n_V be the full positive niche roofs. The full canonical envelope E containing S has fibers

$$E_x=[\max(B,n_U),\ \min(A,1+s-n_V)].$$

They are nonempty because S is connected and projects onto I. For Psi(C)=|C|-|N(C)|-W(C)/2, direct pointwise algebra gives:

**Theorem MF2.**

$$\boxed{|S|\le|E|=\Psi(U)+\Psi(V)+G_s,}$$

$$\boxed{G_s=\int_I[\min(n_U,B)+\min(n_V,1+s-A)]dx-sW.}$$

Indeed the fiber length is A-B-n_U-n_V plus the two displayed minima, while Psi(U)+Psi(V)=sW+integral(A-B-n_U-n_V).

Define

$$T_s=\int_I[\min(n_U,s)+\min(n_V,s)]dx,$$

$$C_s=\int_I[(\min(n_U,B)-s)_++(\min(n_V,1+s-A)-s)_+]dx.$$

Then exactly

$$\boxed{G_s=T_s+C_s-sW,\qquad C_s\ge0.}$$

With the existing written weighted-cap bound Delta(C)=M/2-Psi(C)>=0, the sharp remaining inequality is

$$|S|\le M-\Delta(U)-\Delta(V)+T_s+C_s-sW.$$

In particular G_s<=0 is sufficient, but has not been proved universally. The negative term is sW, not 2sW. This bookkeeping accepts the actual subunit span instead of trying to stretch the body back to height one.

## 3. Endpoint near-alignment

For 0<s<1 put H=1-s, sigma=sqrt(1-H^2), and r0=1/H. The retained top/bottom face endpoints imply

$$c\le a+\sigma\quad\hbox{or}\quad c\ge r-r_0,$$

$$d\ge b-\sigma\quad\hbox{or}\quad d\le l+r_0,$$

and the two inequalities with the upper and lower faces exchanged. Consequently

$$\boxed{a,c<r-r_0\Longrightarrow |a-c|\le\sigma,}$$

$$\boxed{b,d>l+r_0\Longrightarrow |b-d|\le\sigma.}$$

For the first dichotomy, test the actual point (c,s) at angle t0=arccos(H). If the first wall protects it, an actual right extreme with height at least s gives (r-c)H<=1. If the second protects it, the support supplied by (a,1) gives (c-a)sigma<=1-H^2=sigma^2. This is the stated alternative. Testing (d,s) at L-t0 gives the other endpoint alternative. Reflection rho_s supplies the primed ones. QED.

These bounds do not say the faces are central or coincide. The exceptional intervals have width r0, which exceeds one for s>0. The original package lists all eight individual endpoint alternatives; they follow by the same two tests and reflection.

## 4. Conditional confinement above the actual body levels

Put t2=2 arctan(H), and u*=L-t2. For the lower quadrant at t, its level-s interval is

$$I_t^s=(x_L(t),x_R(t)),$$

$$x_L(t)=\frac{1-g(t)+s\cos t}{\sin t},\qquad
x_R(t)=\frac{f(t)-1-s\sin t}{\cos t},$$

when its endpoints are correctly ordered. Here f=h_K(t), g=h_K(t+L).

**Lemma MF3.** If b-c>=1 and c<=l+1-u*, every nonempty I_t^s has x_L(t)>=c.

**Proof.** The retained point (c,s) is safe, so either c<=x_L or c>=x_R. Consider the latter possibility when I_t^s is nonempty. The top point (b,1) gives

$$x_R(t)\ge b-\psi(t),\qquad \psi(t)=\frac{1-H\sin t}{\cos t}.$$

For 0<t<t2 one has psi(t)<1, by writing tan(t/2)<H. Thus x_R>b-1>=c, a contradiction. At t=t2<L, equality is the only remaining possibility, and continuity from below forces x_L>=c=x_R, contradicting a nonempty interval.

For t>t2 write t=L-u with 0<u<u*. The assumptions x_R<=c and positive corner height above level s, together with g(t)<=-l sin t+cos t, imply

$$(c-l)\sin t>1-H\cos t.$$

Therefore

$$c-l>\frac{1-H\sin u}{\cos u}\ge\tan(\pi/4-u/2)\ge1-u.$$

The last inequality is the tangent-line lower bound for tan on [0,pi/4]. This gives u>l+1-c>=u*, again a contradiction. For s=0, t2=L and the first open-angle argument covers the entire quarter. QED.

Reflecting x or applying rho_s supplies the other three bounds. In particular, assume

$$b-c\ge1,\quad d-a\ge1,$$

$$a,c\le l+1-u^*,\qquad b,d\ge r-1+u^*.$$

Then the lower niche above y=s lies over [c,d], where B=s; the upper niche below y=1 lies over [a,b], where A=1. Thus C_s=0 and

$$\boxed{|S|\le M-\Delta(U)-\Delta(V)+T_s-sW.}$$

If the two positive niche footprints have total length at most W, then T_s<=sW and this proves |S|<=M. The footprint condition and the four central-face conditions are real hypotheses, not consequences of minimum width alone.

## 5. What this resolves and what remains

At s=0, overlapping nondegenerate faces fall into the aligned case of the existing FD/FAS theorems, so that case is covered. A point face at the end of a long opposite face remains possible in the case classification. At s>0, the signed term -sW can provide the margin, but neither the general sign of G_s nor the above centrality and footprint assumptions have been established for all competitors.

The companion `scaled-reference-slack-margin.md` proves an explicit margin for the package's reference-scale family. It does not supply universal admission to that family. The partial-turn circular completion comparison still requires its own margin and care with disconnected full envelopes; MF1 begins with two available full turns.

The geometric identities are hand arguments. Their use of the existing weighted theorem retains its stated independent-review limitations. Script checks are supplementary, not continuum certificates. No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used.