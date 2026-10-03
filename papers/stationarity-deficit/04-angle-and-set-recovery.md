# 4. Preserve the set through angle extension and final recovery

## 4.1 Pinned edge bounds imply an extra motion

Put L=pi/2 and a_0=11/5. Suppose K is a normalized omega-cap with

\[
\operatorname{arcsec}(11/5)\le\omega<L,\quad |K|\ge11/5,
\quad w_K^\circ\le\sigma_K(\{L\}),\quad z_K^\circ\le\sigma_K(\{\omega\}).       \tag{4.1}
\]

Suppose further that T=K minus N_omega(K) is a monotone moving sofa. The feasibility assumption in this sentence is essential. We will construct a right-angle motion of a rotated copy of the SAME T.

Set C=cos omega, S=sin omega, U=tan omega, c=sec omega-tan omega, o=(c,1). Then

\[
P_\omega=\{0\le y\le1,\ 0\le p\cdot u_\omega\le1\},
\quad c=1/(\sec\omega+\tan\omega),\quad U\ge4\sqrt6/5>19/10.
\]

Use the thresholds

\[
d_0=\begin{cases}5/4&U<11/5,\\11/10&U\ge11/5.\end{cases}                    \tag{4.2}
\]

They are strictly smaller than U.

### Step 1: one extent is large

If both h_K(0) and h_K(L+omega) were at most c+d_0, then K would lie in P_omega with two corner triangles removed. Each removed triangle has base U-d_0 and height (U-d_0)/U. The triangles are disjoint: simultaneous inequalities p_x>c+d_0 and p.v_omega>c+d_0 would imply C p_y>(1+S)(c+d_0)>C, contradicting y<=1. Thus the remaining area is

\[
\sec\omega-(U-d_0)^2/U=c+2d_0-d_0^2/U.                    \tag{4.3}
\]

Since c<1/4, in the first case this is less than

\[
1/4+5/2-125/176=359/176<11/5.
\]

In the second case, c<1/U gives c+11/5-121/(100U)<11/5. Either contradicts (4.1). Hence one extent is greater than c+d_0. Temporarily reflect if necessary and write h_K(0)=c+d, where d>d_0 and d<=U.

### Step 2: the two scalar inequalities have exact certificates

Put r_y=1-d/U and g=sqrt(1-r_y^2). We claim

\[
d\sin\omega>1,\qquad g>2\cos\omega.                      \tag{4.4}
\]

For d_0=5/4, the square of the first left side is at least 150/121>1. For d_0=11/10 and U>=11/5, it is at least 14641/14600>1.

The quantity 1-(1-d/U)^2 is increasing in d for 0<=d<=U. To prove the second inequality it is therefore enough to set d=d_0. After clearing positive denominators it becomes, respectively,

\[
40U^3-89U^2+40U-25>0,
\qquad220U^3-521U^2+220U-121>0.
\]

In the first case set z=U-19/10>=0; the polynomial is

\[
40z^3+139z^2+135z+407/100.
\]

In the second set z=U-11/5>=0; it is

\[
220z^3+931z^2+1122z+4598/25.
\]

Every coefficient is positive. This proves (4.4) without a root search or decimal approximation.

**Failed simplification.** The threshold 11/10 cannot be used throughout. At omega=arcsec(11/5), its squared first left side is 24/25<1. Thus the two cases in (4.2) cannot simply be discarded.

### Step 3: remove a fixed triangle

The rightmost bottom point q_0=(c+d,0) belongs to K. The intersection of the support lines with normals 0 and omega is r=(c+d,r_y). Put s=(c+d-g,0); then |r-s|=1. Nonnegative sine interpolation of the two support inequalities gives, for 0<t<omega,

\[
h_K(t)-1\le r\cdot u_t-1\le s\cdot u_t.
\]

Thus all right wedge gaps are at least g. By (4.1), the top edge has length at least g, so q_1=(c-g,1) belongs to K.

Let alpha=L-omega, which lies in (0,omega), and set

\[
\Delta=\operatorname{conv}\{O,c u_0,c v_\omega\}.
\]

Among these vertices c u_0 maximizes the u_alpha projection, and c v_omega maximizes the v_alpha projection. The two witnesses q_0,q_1 give

\[
(q_0-c u_0)\cdot u_\alpha=d\sin\omega>1,
\quad
(q_1-c v_\omega)\cdot v_\alpha=-\cos(2\omega)+g\cos\omega>1.
\]

Consequently every point of Delta satisfies both STRICT inner-quadrant inequalities at alpha, so Delta is contained in N_omega(K). The temporary reflection preserves Delta and the fan; reflecting back proves the same inclusion for the original K. The actual sofa has not been replaced by its reflection.

### Step 4: the remaining polygon has the required widths

Write fan coordinates p=A u_0+B v_omega. Then P_omega has 0<=A,B<=sec omega and Delta has A+B<=c. For t in [omega,L], both coefficients of A,B in p.u_t are nonnegative. The width of the cut polygon A+B>=c is therefore

\[
\max\{(o-c u_0)\cdot u_t,(o-c v_\omega)\cdot u_t\}
=\max\{\sin t,\cos(t-\omega)\}\le1.                     \tag{4.5}
\]

Since T is contained in that polygon, T has those widths as well.

### Step 5: concatenate actual placements

Let beta=L-omega and choose B with |p|<=B for p in T. For 0<=alpha<=beta, the set

\[
R_\alpha T+b(\alpha),\qquad
b(\alpha)=(1-B,h_T(L-\alpha+\pi))
\]

lies in the horizontal side of the hallway. Its minimum height is zero, its vertical width is at most one by (4.5), and its first coordinate is at most one. The placement varies continuously.

Start with the shape R_beta T and decrease alpha from beta to zero. Relative to that starting shape, the rotation is alpha-beta. At alpha=0, interpolate translations inside the convex horizontal side to the start of T's original motion. Then follow that original clockwise omega-angle motion. The total clockwise angle is beta+omega=L. Every contained subset undergoes exactly the same isometries.

We have proved the angle-extension lemma from (4.1), independently of global optimality.

## 4.2 A general regular-closedness criterion

**Lemma 4.1 (continuous lower envelope).** Let C be a compact convex set with nonempty interior, contained in y in [0,1]. Suppose C contains I times [0,1], where I=[a,b] and a<b. Let H:I->[0,1] be continuous, with {x in (a,b):H(x)<1} dense in I. Suppose a niche N has vertical sections [0,H(x)) for x in I and is empty outside I. Then G=C minus N satisfies

\[
G=\overline{\operatorname{int}G}.                          \tag{4.6}
\]

**Proof.** The niche is relatively open in C and G is closed. Take (x,y) in G with x in I. Choose interior abscissas x_n->x with H(x_n)<1. By continuity H(x_n)->H(x)<=y<=1, so choose H(x_n)<y_n<1 with y_n->y. Each (x_n,y_n) is an interior point of G: it lies in the interior of the rectangle and strictly above the continuous lower graph. If x lies outside I, a neighborhood misses the niche; density of the interior of the full-dimensional convex set C supplies interior approximations there. This proves G is contained in the closure of its interior; closedness gives the reverse inclusion. \(\square\)

For the concrete Gerver construction, the retained envelope facts give this situation. Its successive inner contact/path arcs form a continuous graph. The side contact arcs have height strictly below one; on the central path a height-one point must have zero vertical derivative. Writing x'=a(t)u_t+b(t)v_t, with a<0<b, this would require -a(t)/b(t)=cot t. The first side is nondecreasing and the second strictly decreasing, so there is at most one such point. Hence H<1 on a dense set. The bounding top segment and the cap's downward closure supply the rectangle.

The geometric identification of those arcs and their derivative signs is retained from the concrete Gerver analysis; Lemma 4.1 is the topological deduction. No assertion about the topology of an arbitrary competitor is added.

## 4.3 Recover the original set, not only almost-everywhere equality

**Lemma 4.2.** Let G be regular closed and of finite planar measure. If F is closed, F is contained in G, and |F|=|G|, then F=G.

**Proof.** If a point of interior G were outside F, openness of the complement of F would give a positive-radius ball contained in G minus F. This contradicts equality of finite measures. Thus interior G is contained in F. Closedness and (4.6) imply G is contained in F. \(\square\)

The regular-closedness premise matters. A square together with an attached exterior segment has the same area as the square; both sets are closed and connected, but they are different. The enlarged set is not regular closed. Likewise finiteness cannot be dropped merely because two measures are both infinite.

## Attribution and scope

The pinned-gap geometry is a reworking of Baek, Section 4.2, with its two scalar checks written as positive-coefficient polynomial identities. The topological criterion and the explicit preservation of contained subsets are used to keep the uniqueness conclusion about the starting set. This section does not assert that stationarity alone supplies a connected cap-minus-niche set.
