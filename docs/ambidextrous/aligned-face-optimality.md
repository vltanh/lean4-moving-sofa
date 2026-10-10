# Optimality for aligned long-face ambidextrous bodies, without a curvature assumption

**Scope.** This is an ordinary-area theorem for a stated geometric class. It combines the newly proved signed weighted cap bound WV2 with an elementary no-clipping argument. It does not assert that an arbitrary global ambidextrous maximizer belongs to this class. Labels FL are local. All dependencies remain written and self-reviewed.

## 1. Statement

Normalize the common incoming strip to 0<=y<=1. Let S be a compact connected ambidextrous body, and K=conv(S). Suppose K has vertical span one, and its bottom and top exposed faces are the same horizontal interval [a,b], at heights zero and one respectively. Assume b-a>=1.

**Theorem FL1.** Then

$$\boxed{|S|\le M.}\tag{FL.1}$$

No curvature bound, smoothness, arm bound, reflection symmetry of S, contact order, or separately assumed full-quarter turn is required. The aligned-face and length hypotheses are genuine restrictions. The candidate meets them, but not every nearby feasible body does.

## 2. The required full turns follow from the contained unit square

If |S|<=8/5, the conclusion follows from the known candidate lower bound M>8/5. Otherwise use the established canonical/sign reduction to obtain conventional reduced endpoint angles alpha,gamma in (arccos(5/8),pi/2]. The outgoing body-frame strip in either turn has width one in its corresponding normal.

Since K contains [a,b] times [0,1], it contains an axis-aligned unit square. At every partial angle omega in (0,pi/2), the width of that square in either outgoing normal is cos(omega)+sin(omega)>1. Widths of S and conv(S) are equal. A partial endpoint would contradict the outgoing strip. Thus both reduced turns reach pi/2. Canonical support tightening then gives both full-quarter witnesses for S without assuming any curvature or maximizing property.

This argument uses only the previously established motion reduction for |S|>8/5. It does not complete a partial turn by convention.

## 3. The two downward caps

Let I=[l,r] be the horizontal projection of K, of length W. Write its upper and lower roofs as A(x),B(x), with B<=A. Define downward caps U,V with roofs A and 1-B respectively, both based at y=0. They have the same projection, height one, and are convex and compact. Their upper support functions agree with the upper support of K and of rho(K), respectively, where rho(x,y)=(x,1-y).

In particular the full niches N(U) and rho(N(V)) are the two canonical forbidden sweeps that S avoids. Their areas are not initially assumed to lie in K; that will follow below.

The endpoints (a,0),(b,0) of the exposed bottom segment and (a,1),(b,1) of the exposed top segment are extreme points of K. Since K is the convex hull of a compact set S, all these extreme points belong to S. One direct proof uses the planar finite convex-combination representation of a hull point: an extreme point cannot be a nontrivial combination of distinct points of S.

## 4. Every positive niche triangle belongs to one connected horizontal interval

Work first with U. For 0<t<L=pi/2, put f=h_U(t), g=h_U(t+L), c=cos(t), s=sin(t). Its inner corner height is

$$c_y(t)=(f-1)s+(g-1)c.$$

The cap contains [a,b] times [0,1], so

$$f\ge bc+s,\qquad g\ge-as+c.$$

Consequently, with T=b-a>=1,

$$c_y(t)\ge Tsc+1-s-c\ge(1-s)(1-c)>0.\tag{FL.2}$$

The positive-height portion of the open forbidden quadrant is therefore a nonempty triangle. Its horizontal projection equals its baseline interval

$$I_t=\left(\frac{1-g}{s},\frac{f-1}{c}\right).\tag{FL.3}$$

These interval endpoints are continuous in t and their gap is c_y(t)/(sc)>0. Their union is one connected open interval. For example, the set of pairs (t,x) with x in I_t is connected: any point can be joined to the midpoint of its fiber, and these midpoints form a continuous path. Its x-projection is therefore connected.

Neither a nor b lies in this union, because the retained points (a,0),(b,0) avoid every canonical forbidden quadrant. On the other hand, at t=pi/4,

$$\frac{1-g}{s}\le a+\sqrt2-1,\qquad
\frac{f-1}{c}\ge b-(\sqrt2-1).$$

Since T>=1>2(sqrt(2)-1), the interval I_(pi/4) contains (a+b)/2. The connected union of all I_t, avoiding a and b and meeting (a,b), is thus contained in (a,b). This proves

$$\boxed{\operatorname{proj}_xN(U)\subset(a,b).}\tag{FL.4}$$

Apply the identical argument to V. Its retained baseline points are the reflections of the top-face endpoints of S. Hence proj_x N(V) is also contained in (a,b). There is no curvature or signed-roof formula in this argument.

## 5. Niche containment and the ordinary-area identity

Connectedness of S makes its projection the whole interval I. At every x in I, choose a surviving point of S. Avoidance of the lower downward forbidden sweep forces that point's height to be at least the full lower niche height. Thus the full lower niche height is at most A(x). The analogous reflected statement bounds the upper niche within its own cap.

By FL.4, both positive niches occur only at a<x<b. Over this interval K contains the entire vertical segment [0,1], because its two faces coincide there. Therefore both N(U) and rho(N(V)) are contained in K, up to the irrelevant baseline boundaries.

They cannot overlap in positive height: a lower downward interval and an upper upward interval that overlap would together cover the entire vertical fiber, contradicting the existence of the surviving point of S at that x. Consequently their areas subtract without an overlap correction, and

$$|S|\le |K|-|N(U)|-|N(V)|.$$

Fiberwise, |K|=|U|+|V|-W. Hence

$$
\boxed{|S|\le\Psi(U)+\Psi(V).}\tag{FL.5}
$$

WV2 applies to both normalized caps and gives Psi(U),Psi(V)<=M/2. This proves FL1.

## 6. What is now closed, and what remains

This removes the curvature hypothesis from the earlier aligned-face optimality route. Full turns and zero clipping have been derived from the stated face geometry and actual retained points, rather than inserted as additional assumptions. The theorem bounds actual ordinary area, not merely an auxiliary functional.

The exceptional geometries remain: point faces, shorter common faces, shifted or nonmatching top/bottom faces, and motion configurations not forced into this class. The known near-candidate clipping examples cannot be excluded by a uniform area threshold below M. FL1 is not a theorem that all maximizers have aligned long faces.

The primary remaining unrestricted task is therefore a valid reduction to this class or an ordinary-area bound for its complement. The weighted cap optimization itself need not be repeated. Exact two-turn uniqueness remains deferred.

No computer-assisted search or numerical calculation is part of this proof. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. The continuum reasoning and its historical dependencies remain subject to independent review.
