# A lower exposure bound from one good quarter and a good future

**Scope.** This supplies a lower bound on actual limiting exposure in a specific, proved visible part of a weighted maximizer's niche. Unlike the rejected saturation shortcut, global visibility is proved from monotonicity of the other wall family and of the future first-wall family. The argument retains the microscopic alternating edges of the selected finite niches. Labels VE are local.

The inputs are WP/WR/HF (selected finite caps with uniform support convergence), EB1 (their exposure measures converge to the actual cap curvature), and TF2 (positive tangency heights). These are historical written dependencies, not independently verified in this note. The geometric lower bound below is new and analytic. No numerical experiment or infinite-niche differentiability formula is used.

## 1. Geometry on the specified interval

Let U be a signed weighted global maximizer. Use f,g,p,q,u=f''+f,v=g''+g and L=pi/2 as before. Assume

$$0\le v\le1\quad\hbox{a.e. on }(0,L),$$

and for some b in (0,L),

$$0\le u\le1\quad\hbox{a.e. on }(b,L).\tag{VE.1}$$

Define

$$c=(f-1)\mu_t+(g-1)\nu_t,\qquad
B=c+p\nu_t,\qquad D=c-q\mu_t,$$

where mu_t=(cos t,sin t), nu_t=(-sin t,cos t). Then

$$B'=(u-1)\nu_t,\qquad D'=(1-v)\mu_t.$$

Thus D_x is nondecreasing on the whole quarter, and B_x is nondecreasing on [b,L]. Let J be a compact interval inside (b,L) on which p<0<q. All inequalities have uniform strict margins on J.

The full niche is the region above the baseline and below

$$n(x)=\max\{0,\sup_{0<t<L}\min(R_t(x),L_t(x))\},$$

with the wall-line functions defined in SR1. Its wall derivatives are

$$\partial_t R_t(x)=\frac{x-B_x(t)}{\sin^2t},\qquad
\partial_t L_t(x)=\frac{x-D_x(t)}{\cos^2t}.\tag{VE.2}$$

The repeated letter L_t denotes the second line, not the endpoint L.

## 2. Both required pieces are globally visible

**Lemma VE1.** For t in J:

(a) D(t) lies on the full niche roof. Except when D is constant on a nontrivial parameter interval, its maximizing parameter is unique and only the second wall is active there.

(b) c(t) lies on the full niche roof and its maximizing parameter is unique. Its x-coordinate decreases strictly along J.

**Proof of (a).** For x=D_x(t), monotonicity of D_x and VE.2 make L_t(x) a global maximum of the second-wall family. At the point D(t), the first wall is strictly higher: the first inner product is f-1-q, so its vertical clearance is q/sin(t)>0. Therefore min(R_t,L_t)=D_y(t) equals the global second-wall maximum and is the full roof. TF2 supplies D_y(t)>0.

If another parameter has the same second-wall value at this x, VE.2 and monotonicity force D_x to be constant between the two parameters. Then D'=(1-v)mu and cos(t)>0 imply D itself is constant there. The nontrivial plateau intervals are countable and have zero D-arc length. At every remaining image point the maximizing parameter is unique and the strict companion gap rules out first-wall activity.

**Proof of (b).** At x=c_x(t), for every s<t,

$$x-D_x(s)\ge x-D_x(t)=q(t)\cos t>0.$$

Integrating VE.2 shows L_s(x)<L_t(x)=c_y(t). For every s>t, since t>b and B_x is nondecreasing on the whole future,

$$x-B_x(s)\le x-B_x(t)=p(t)\sin t<0,$$

so R_s(x)<R_t(x)=c_y(t). Thus no earlier or later parameter ties or exceeds the corner value. It is positive: the cap contains its top-face rectangle of width T>1 and height one, giving

$$c_y(t)\ge T\sin t\cos t+1-\sin t-\cos t
>(1-\sin t)(1-\cos t)>0.$$

Finally c_x'=p cos(t)-q sin(t)<0, with a uniform negative bound on J. QED.

These are global envelope statements. They do not assert that all tangent or corner pieces of an arbitrary cap are active.

The two graph images in VE1 are disjoint on J. If its right endpoint is t1, then

$$\max_{t\in J}D_x(t)=D_x(t1)<c_x(t1)=\min_{t\in J}c_x(t).\tag{VE.3}$$

Hence their exposure contributions can be added without counting any physical boundary portion twice.

## 3. How finite exposed edges converge on a unique-source graph

Let U_n be the WP sequence and let n_n be its finite positive niche roof. Denote by nu_n^f and nu_n^g the measures that assign to each grid angle the total exposed first- or second-wall length. EB1 gives weak convergence to u(t)dt and v(t)dt, respectively.

The following local facts justify reading part of those limiting measures from VE1. Details are included because uniform convergence of curves alone would not preserve their ordinary perimeter.

### Local uniform roof convergence and bounded slopes

Near any compact positive-height piece of the limiting roof, all active parameters of sufficiently large n stay in a fixed compact subinterval of (0,L). Indeed the finite corner heights are at most C t near zero and C(L-t) near L, uniformly in n: supports are uniformly bounded and Lipschitz, and the finite cap height is at most one. A quadrant cannot reach above its corner. Positive-height points therefore exclude endpoint parameters uniformly.

On that remaining compact angular interval, both wall families are uniformly Lipschitz in x, and their support offsets converge uniformly. Density of the nested angle meshes gives local uniform convergence of their max-min roofs. In particular n_n -> n uniformly near these pieces, and their graph slopes have a common bound.

### Localization of active parameters

Suppose a limiting positive roof point has a unique maximizing parameter t. Any sequence of nearby finite exposed points and their source angles has a convergent subsequence. The wall equalities, companion inequalities and local uniform convergence show that its limiting angle attains the full roof at the limiting point. Uniqueness forces that angle to be t. This also proves uniform angle localization on compact sets of such points by a subsequence contradiction.

On a second-wall tangency with strict companion gap, only second-wall sources can occur eventually in such a compact neighborhood. For the D graph, the exceptions are its countably many plateau image points. They can be removed in arbitrarily small total x-length. Because the slopes and angle ranges are uniformly bounded, the corresponding finite graph lengths and exposure masses are bounded by a constant times that removed x-length. Thus they do not obstruct the limiting statement. The inverse parameter along the remaining monotone D graph is continuous at every unique-source point.

### Tangent flux, including alternating first and second edges

Orient a finite roof graph in the direction of increasing x. A first-wall edge of length ds has tangent -nu_theta=(sin theta,-cos theta); a second-wall edge has tangent mu_theta=(cos theta,sin theta). Thus, as vector measures along the graph,

$$
(dx,dy)=(-\nu_\theta)d\mu_n^f+(\mu_\theta)d\mu_n^g,\tag{VE.4}
$$

where mu_n^f,mu_n^g are the physical exposed-length measures there. Since the angular range stays away from the axes, both tangent x-components have a uniform positive lower bound. Total exposed length is consequently controlled by the x-length of the graph interval.

The x-flux is Lebesgue measure. The y-flux is the distributional derivative of n_n, which converges weakly to that of n by uniform convergence and the common slope bound. Active-angle localization lets the coefficients in VE.4 be replaced in the limit by the unique-source angle t(x). Solving the two-by-two linear system gives

$$d\mu^g=\cos t(x)\,dx+\sin t(x)\,dy,\qquad
 d\mu^f=\sin t(x)\,dx-\cos t(x)\,dy.\tag{VE.5}$$

This identifies the two limiting source lengths, not the sum with the ordinary arc length. Alternating staircase edges are retained by the two coefficients. For continuous compactly supported angular weights, the same equations hold after multiplying by that weight composed with t(x). Approximation after removing the plateau image points gives the D-graph conclusion as well.

On D(t), oriented with increasing t, dx=(1-v)cos(t)dt and dy=(1-v)sin(t)dt. VE.5 therefore gives second-wall contribution (1-v)dt and zero first-wall contribution. This also follows directly from its strict companion gap.

On c(t), increasing x corresponds to decreasing t, so

$$(dx,dy)=-[p\mu_t+q\nu_t]dt$$

when dt denotes positive parameter measure on J and the path orientation has been reversed. VE.5 gives second-wall contribution -p dt and first-wall contribution q dt. Both are nonnegative in the specified sign regime.

These identities may first be applied on slightly smaller graph intervals with continuous cutoffs. Exhausting J removes endpoint terms; neither endpoints nor plateau image points contribute to the limiting absolutely continuous angular measures. All remaining parts of the finite niche add nonnegative exposure.

## 4. The lower bound used in the arm argument

**Theorem VE2.** Under VE.1, on the open set

$$\{t>b:p(t)<0<q(t)\},$$

one has

$$\boxed{v(t)\ge1-v(t)-p(t)\quad\text{for almost every }t.}\tag{VE.6}$$

**Proof.** On any compact subinterval J in that set, Lemma VE1 proves the two globally visible pieces, and VE.3 separates their physical images. Section 3 reads their contributions into the weak limit of nu_n^g. For every nonnegative continuous weight phi supported inside J,

$$\int\phi(t)v(t)dt\ge\int\phi(t)[1-v(t)-p(t)]dt.$$

This proves the density inequality almost everywhere on J. Exhaust the open sign set by countably many such intervals. QED.

In particular v<=1 implies p>=-1 on this set. Where -1<=p<0, WR's upper inequality is v<=kappa(p)=(1-p)/2. Hence VE.6 forces the exact relation

$$\boxed{v=(1-p)/2.}\tag{VE.7}$$

The equality is obtained only in this justified visible region, by matching a newly proved lower bound with the old upper bound. It is not the invalid inference from exposure=curvature and an upper bound alone.

## 5. Validation boundary

The proof uses local graph convergence, uniqueness of the active parameter and the two normal directions to preserve source flux. It never claims that the full limiting niche perimeter equals the limiting sum of finite edge lengths. It never assumes C2 support, differentiable curvature, or a stable finite contact chart for the complete niche.

The conclusion is conditional on one globally good quarter, a good future for the other quarter, and weighted maximality through EB. The next note uses these hypotheses in a contradiction argument. This is not yet an unrestricted two-turn area theorem. No CI, Lean/Lake compilation, long script, dependency installation, or manuscript build is used.
