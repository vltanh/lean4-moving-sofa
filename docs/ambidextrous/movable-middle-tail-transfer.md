# Tail transfer with genuinely variable middle supporting data

**Scope.** This removes the requirement that the entire middle support agree with the reference in TC/STW. The background cap may have independently changed middle arcs; its open-quarter curvature is bounded between zero and one and it retains three explicit reference collars. The altered cap may then have arbitrary, including nonsmooth and outward, top-normal changes. The conclusion is an actual clipping budget relative to the background. It does not admit arbitrary opposite-face bodies or unrestricted neighborhoods. Labels MT are local.

Baseline: `1a1805f904ad8c67dfec182a12970c6c021dedd0`. The only background geometry used is proved below from support inequalities and the explicit reference collars. No computation, weighted-maximizer hypothesis, Gerver theorem, or global saturation-of-exposure premise is used.

## 1. Background and altered caps

Use the centered reference constants

$$m=1/(3\sin\beta),\qquad 1<m<4/3,\qquad
I=[-m,m],\quad a=-m/2,\quad b=m/2,\quad L=\pi/2.$$

Put

$$\eta=2\arctan(1/10),\quad s_\eta=20/101,\quad c_\eta=99/101,\quad
D=10/101,\quad t_0=L-\eta.$$

Here eta<beta. Let B be a compact convex downward cap, with upper roof A_B and support h_B, such that

$$I\times[0,1/2]\subseteq B\subseteq I\times[0,1],$$

$$h_B=h_*\quad\text{on }[0,\eta]\cup[L-\eta,L+\eta]\cup[\pi-\eta,\pi],\tag{MT.1}$$

and on each open upper quarter its support belongs to W^(2,infinity), with

$$0\le h_B+h_B''\le1\quad\text{a.e.}\tag{MT.2}$$

In addition suppose its corner heights satisfy

$$(h_B(t)-1)\sin t+(h_B(t+L)-1)\cos t\le1/2\quad(0<t<L).\tag{MT.3}$$

The middle support on (eta,L-eta) and (L+eta,pi-eta) is not fixed. The collars imply height one, top face [a,b], fixed horizontal projection, and the reference half-height extreme points. The background need not be horizontally symmetric.

An altered cap U is any compact convex downward cap containing I times [0,1/2], contained in I times [0,1], and satisfying

$$h_U=h_B\quad\text{on }[0,L-\eta]\cup[L+\eta,\pi],\tag{MT.4}$$

$$h_U(\theta)\le1+b|\cos\theta|\quad(L-\eta\le\theta\le L+\eta).\tag{MT.5}$$

No curvature bound on U and no inclusion between U and B is assumed. Both signs of h_U-h_B are allowed. Distinct backgrounds and alterations may be used for the two turns.

## 2. Background envelope geometry and pruning its end angles

Write f=h_B(t), g=h_B(t+L), and define p=f'-g+1, q=g'+f-1. Let mu=(cos t,sin t), nu=(-sin t,cos t), and

$$c=(f-1)\mu+(g-1)\nu,\quad
B_t=c+p\nu,\quad D_t=c-q\mu.$$

The letter B_t denotes a tangency point, not the background cap B. If u=f''+f and v=g''+g, then

$$B_t'=(u-1)\nu,\qquad D_t'=(1-v)\mu.$$

Both horizontal coordinates are nondecreasing by MT.2. Also (B_t)_y>=0 and (D_t)_y>=0: the former has derivative (u-1)cos t<=0 and final value zero, and the latter has derivative (1-v)sin t>=0 and initial value zero. Hence the baseline intercepts satisfy

$$\frac{f(t)-1}{\cos t}\le b,\qquad
\frac{1-g(t)}{\sin t}\ge a.\tag{MT.6}$$

Every positive niche point therefore has abscissa in (a,b). Every niche point lies below its witnessing corner, so MT.3 bounds its height by one half.

For fixed x set

$$R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.$$

Their parameter derivatives are

$$\partial_tR_t(x)=\frac{x-(B_t)_x}{\sin^2t},\qquad
\partial_tL_t(x)=\frac{x-(D_t)_x}{\cos^2t}.\tag{MT.7}$$

On [t0,L], the collars give

$$f=1/2+b\cos t+(1/2)\sin t,\qquad
 g=m\sin t+(1/2)\cos t,$$

$$p=1-(3m/2)\sin t<0,\qquad
q=(3m/2)\cos t-1/2<0.\tag{MT.8}$$

The signs follow from m>1, m<4/3, sin t>=99/101 and cos t<=20/101.

For t>=t0 and x<=(B_(t0))_x=b-D, one has

$$\min(R_t(x),L_t(x))\le\min(R_{t0}(x),L_{t0}(x)).\tag{MT.9}$$

Indeed, if x<=c_x(t0), the second wall is the smaller wall at t0. Since q(t0)<0, (D_(t0))_x>c_x(t0)>=x, and monotonicity of D_x makes L_t(x) nonincreasing throughout the future. If c_x(t0)<=x<=b-D, the first wall is the smaller wall at t0, and monotonicity of B_x makes R_t(x) nonincreasing. These two cases prove MT.9 without assuming that the altered cap has the same active parameters.

Reflect this argument horizontally to prune t<=eta at every x>=a+D. Reflection applies to the background hypotheses; B itself need not equal its reflection. Outside (a,b) its positive niche is absent. It follows that, outside

$$J=(a,a+D)\cup(b-D,b),$$

the background niche roof is attained by a parameter in the compact interval [eta,t0] whenever that roof is positive. In particular only the two end tail strips can lose old niche material when MT.4 is imposed.

## 3. Exact background tail arcs

For 0<d<D, let t=L-arcsin(2d). Its first-wall tangency and outer support point are

$$x_{in}=b-d,\quad n_B(x_{in})=1/2-\sqrt{1/4-d^2},$$

$$x_{out}=b+d,\quad A_B(x_{out})=1/2+\sqrt{1/4-d^2}.\tag{MT.10}$$

The outer assertion follows from the exact smooth support in the collar. For the inner assertion, MT.7 and global monotonicity of B_x make R_t(x_in) the maximum of the entire first-wall family. The sign p(t)<0 makes the companion wall strictly higher at that tangency. Thus it is the actual positive niche roof. The reflected statement holds on the left.

This proves that the circular tails needed by TC survive arbitrary changes of the middle satisfying MT.1--MT.2; it does not merely postulate a reference contact pattern for the new background.

## 4. Altered niches and the signed pairing

MT.4--MT.6 and the barrier MT.5 confine N(U) to (a,b). Its middle corner heights are those of B, at most one half. At a changed late angle, MT.5 and the unchanged companion support give

$$c_{U,y}(t)\le(3m/2)\sin t\cos t+(\cos^2t)/2-\cos t
\le2220/10201<1/2.$$

The early bound is its horizontal reflection. Thus n_U<=1/2 and U minus N(U) has interval fibers through height one half.

Put e(t)=h_B(t)-h_U(t), with either sign. At the two abscissae in MT.10, the supporting-line and single-angle niche tests give

$$\boxed{n_B(b-d)-n_U(b-d)\le\frac{e(t)}{\sin t}
\le A_B(b+d)-A_U(b+d).}\tag{MT.11}$$

For the niche test, the unchanged companion clearance above the background first wall is

$$\frac{(3m/2)\sin t-1}{\cos t}\ge19/8.$$

The largest permitted upward displacement of the changed first wall, from MT.5, is

$$\frac{h_U(t)-h_B(t)}{\sin t}
\le\frac{1-\sin t}{2\sin t}\le1/99.$$

Thus the companion is still above the first wall even for a negative defect e. Taking a positive part gives the niche lower test when the first wall is below the baseline. The outer inequality uses the same support at the outer point; no new global active-contact assertion is needed.

Outside J, MT.9 and its reflection give n_U>=n_B because a middle attaining parameter is unchanged. Outside the two outer tail strips and [a,b], every upper-roof point of B has an attaining support outside the changed window; hence A_U<=A_B there. On [a,b], A_B=1>=A_U. The only potentially negative cap losses are on the outer strips paired by MT.11.

Integrating the signed inequalities proves:

**Theorem MT1 (movable-middle tail transfer).**

$$\boxed{\Psi(B)-\Psi(U)\ge\int_a^b(1-A_U(x))\,dx.}\tag{MT.12}$$

The widths cancel in this difference. Neither side was obtained by dropping a signed area term or counting absent hull material as surviving sofa material.

## 5. Two independent backgrounds and actual area

Let B_1,B_2 satisfy MT.1--MT.3, and let U_1,U_2 be independently altered caps satisfying MT.4--MT.5 relative to them. The full envelope E=(U_1 minus N(U_1)) intersect rho(U_2 minus N(U_2)) has nonempty interval fibers through y=1/2, is compact and connected, and has both full canonical turns. Its exact clipping term obeys

$$G\le\int_a^b(1-A_{U_1}+1-A_{U_2})\le
\Psi(B_1)-\Psi(U_1)+\Psi(B_2)-\Psi(U_2).$$

Consequently

$$\boxed{|E|\le\Psi(B_1)+\Psi(B_2).}\tag{MT.13}$$

The next note applies the already calibrated fixed-width functional only to the curvature-controlled backgrounds. It does not require the altered caps themselves to satisfy any curvature bound. MT.13 is therefore a transfer of an ordinary-area budget across rough tail changes, not another unconstrained maximization.

## 6. Remaining scope

The middle supports of the backgrounds are genuinely variable, not required to equal the reference. However unit curvature in the background middles, the exact three collars, the half-height rectangle, and the corner-height bound are stated admission hypotheses. The proof does not produce those backgrounds from an arbitrary saturated opposite-face body. Nor does it replace an unknown partial turn by a full turn.

This is a hand proof. Short computations may test its formulas but are not premises. No CI, Lean/Lake compilation, dependency installation, manuscript build, or long search is used. Unrestricted optimality remains unproved.
