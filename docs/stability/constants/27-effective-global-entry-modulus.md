# A quantitative global entry modulus without exhaustive shape search

This is an analytic argument using the established polygon variation geometry,
Baek's global cap bound, and the explicit reference estimates recorded earlier.
It is not Lean-verified. The coarse powers and constants are deliberately chosen
for transparent inequalities, not as sharp stability estimates.

## Statement

Let epsilon=M-|S| for an original moving sofa S. Under horizontal-midpoint/top
normalization, the argument gives

    d_H(S_c,G) <= 3000000*epsilon^(1/12),
                        0<=epsilon<=10^(-144).                (1)

Every admissible reduced angle also obeys

    0<=alpha=pi/2-omega<500*epsilon^(1/6),
                        0<epsilon<=10^(-30).                  (2)

Thus, for every prescribed rational eta>0, the explicit rational bound

    epsilon <= min(10^(-144),(eta/6000000)^12)                 (3)

forces d_H(S_c,G)<eta. This addresses GLOBAL separation from an arbitrary
specified neighborhood, including motions arbitrarily close to a right angle.
The much stronger local coefficient 2.3 is not being used to prove (1)--(3).

Equation (3) does not, on its own, name a radius eta for every local certificate
in the 2.3 proof. Those reference-local radii must be explicitly bounded before
advertising a numerical cutoff for that precise sharp local theorem. Notes29--32
now supply a proposed analytic completion of that step. The global compactness
separation gap is replaced here by a coarse modulus, not an unexecuted enumeration.

## 1. Coarse angle input and attribution

Kallus and Romik, "Improved upper bounds in the moving sofa problem" (2018),
Theorem 9 and the proof of their Theorem 2 establish

    omega<=asin(84/85)  ==>  |S|<=2.21.

Together with M>=2.2192, this implies epsilon<23/2500 forces
omega>asin(84/85)>2*atan(4/5). This published result is stronger than our earlier
coarse 77.32-degree computation and is credited as an input, not a new bound.
Primary source: arXiv:1706.06630v2; DOI 10.1016/j.aim.2018.10.022.
Equation numbering differs between versions, so the theorem/proof is the
reference rather than the earlier note's inaccurate equation numbers.

All deficits used below are far below 23/2500. We only need

    0<=alpha<1/4,       tan(omega)>=40/9.                      (4)

## 2. Uniform geometry for large partial-angle caps

A standard omega-cap contains the origin. Let W be its horizontal width and
assume A_omega(K)>0. At pi/4 the full-floor inner triangle has height at least
W/2-sqrt(2), and its two floor endpoints lie strictly within the horizontal
projection of K. Since the fan floor over that projection has height at most
W*cot(omega)<=W/4, the part above height W/4 has area at least

    (W/4-sqrt(2))_+^2

and belongs to the actual fan niche. Since |K|<=W, positive A implies W<32.
The bound follows immediately for W>=32 from sqrt(2)<3/2 and
(W/4-3/2)^2>W. Thus the whole cap lies in [-32,32]x[0,1] and has radius<64.

For alpha>=a0>0, put c=sec(omega)-tan(omega)=tan(alpha/2). Every standard cap
contains the triangle with vertices (0,0),(c,0),(c,1). A disk centered at
(3c/4,1/4) of radius c/8 lies in that triangle (c<1), so the common interior
radius is at least a0/16. These bounds are for all caps in question, not only
maximizers satisfying balancedness.

## 3. Penalized caps satisfy approximate pinned bounds

Fix 0<a0<=1/100 and suppose alpha>=a0. Let K be the cap of the specified
monotone envelope of S, so A_omega(K)>=M-epsilon. Maximize

    A_omega(C)-lambda*integral_0^(pi/2+omega)(h_C-h_K)^2,
    lambda=2^(-20).

For fixed omega<pi/2, the standard cap family is compact in its bounded
parallelogram. Polygon recovery and uniform approximation of area/niche give
selected polygon maximizers converging to a cap C with

    A_omega(C)>=M-epsilon,      P(C)<=epsilon/lambda.           (5)

This uses the global bound A_omega(C)<=M, not the value of a penalized maximum.
Both K and C have radius<64 by Section 2. Their support difference is
128-Lipschitz and has sup norm D<128. The one-sided interval argument of note26
therefore gives

    P(C)>=D^3/1024,       D<=1024*epsilon^(1/3).               (6)

We now quantify the pinned-variation proof rather than assume C is balanced.
Let D_n be the selected polygon's sup support difference. A floating sine hat
has integral at most 4delta, so its defect satisfies

    d_n(t)=sigma_n(t)-tau_n(t)<=8*lambda*D_n*delta.

At a pinned strip, a height displacement z changes the assigned heights by at
most |z|. The common interior ball and homothetic containment give Hausdorff
change at most 128*16*|z|/a0. Restoring standard position costs at most
sec(omega)*|z|<=2|z|/a0. Thus the total support change is below 4096|z|/a0.
The penalty's first derivative is at most

    2*lambda*D_n * 4 * 4096/a0 = 2^15*lambda*D_n/a0.

The assigned-versus-actual area comparison has the same favorable sign as in
the original pinned-variation proof. Zero-length pinned facets need no move.
The completed-boundary identity sum d_n(t)sin(t)=0 converts the two pinned
upper bounds into absolute bounds: floating positive weights sum to less than
32lambda D_n, there are two pins, and their sines exceed 1/2. Passing to the
limit using continuity of the gap infima and upper semicontinuity of the fixed
facet atoms yields

    w_C^circ<=sigma_C({pi/2})+zeta,
    z_C^circ<=sigma_C({omega})+zeta,
    zeta<=2^18*lambda*D/a0=D/(4a0).                            (7)

The quantitative coefficient follows directly from the displayed positive-
defect budget; no rate of convergence of the selected polygons is required.
The comparison cap C is NOT assumed to be a moving sofa or to contain its niche.

## 4. Strict angle geometry survives the errors

Assume epsilon<=a0^6/10^16. Then 1024^3*64^3=2^48<10^16 implies

    D<a0^2/64,       zeta<a0/256.                              (8)

The standard truncated-parallelogram area argument, applied to |C|>=A(C)>2.2,
shows that one of its two mirrored outer extents is at least c+11/10. Reflect
both C and K temporarily if necessary. Write that right extent c+d, where
11/10<=d<=T=tan(omega). Set

    r_y=1-d/T,       g=sqrt(1-r_y^2).

The supporting corner and its unit-distance floor point give w_C^circ>=g.
Hence the top facet reaches at least to (c-g+zeta,1), while (c+d,0) is in C.
These two support witnesses are the same ones used in the exact remaining-
angle theorem, with g replaced by g-zeta in the second.

For T>=40/9, elementary inequalities give

    d*sin(omega)>=44/41>1+1/16,
    g^2-4*cos(omega)^2>1/T,
    g+2*cos(omega)<3/2,
    g-2*cos(omega)>(2/3)/T>=(2/3)a0.

Since cos(omega)=sin(alpha)>=a0/2, (8) implies

    -cos(2omega)+(g-zeta)*cos(omega)>1+a0^2/4.                 (9)

The exact geometry uses the two lower bounds above for the two inner-wall
support gaps at angle alpha, at all three vertices of

    Delta=conv{(0,0), c*u_0, c*v_omega}.

Replacing C's supports by K's loses at most D in each gap. Equations (8)--(9)
therefore still put the whole closed triangle Delta strictly inside the inner
quadrant of K at angle alpha. Reflection preserves Delta and the fan, so the
conclusion transfers back when the left extent was used.

The ORIGINAL S avoids that quadrant. Thus S is contained in P_omega minus
Delta. This truncated parallelogram has width at most one at every normal in
[omega,pi/2], by the explicit formula max(sin t,cos(t-omega))<=1. The same S,
rotated through alpha, consequently admits the full right-angle motion: prepend
the support-positioned strip rotation to its given motion. No motion of C,
containment S subset C, or connectedness of C minus its niche is asserted.

## 5. A nonzero missing angle contradicts the effective right-angle estimate

Apply note26 to R_alpha S. Its deficit is still epsilon and

    d_H(R_alpha S+translation,G)<=10300*sqrt(epsilon).

The CONVEX HULL of the reference contains a horizontal rectangle of height one
and width greater than one. More directly, the four points (a,0),(b0,0),(a,1),
(b0,1) belong to the actual sofa G, with b0-a>1. The floor points are retained
niche endpoints, and the upper two lie on its top face. The rectangle interior
need not belong to G: the niche cuts through it. Width depends only on the
convex hull, so these four actual support witnesses suffice. For
0<=alpha<=1/4 the width at normal pi/2+alpha is at least
cos(alpha)+(b0-a)sin(alpha)>=cos(alpha)+sin(alpha)>=1+alpha/2.
But R_alpha S has width at most one in that normal because S lies in its
original horizontal strip. Hausdorff distance changes each support by at most
the distance and hence changes width by at most twice the distance. Thus

    alpha<=41200*sqrt(epsilon).

This corrects the previous wording that placed the entire rectangle inside
the nonconvex sofa. No numerical coefficient or subsequent argument changes.

If alpha>=a0 and epsilon<=a0^6/10^16 this is impossible:
41200^2*a0^4<10^16 for a0<=1/100. The same deficit condition is below 10^(-20),
so note26's explicit right-angle threshold is satisfied. We have proved

    epsilon<=a0^6/10^16  ==>  alpha<a0,   0<a0<=1/100.         (10)

For 0<epsilon<=10^(-30), choose a0=500*epsilon^(1/6). It is at most 1/200,
and 500^6>10^16, so (10) proves (2). This step uses approximate maximality and
strict support gaps, not a global compactness separation constant.

## 6. Compare a partial-angle sofa with a full-angle cap

Normalize S by horizontal midpoint and top. Connectedness and the visited
pi/4 hallway bound its horizontal span by six. Let K be its full right-angle
cap: take the convex hull and its vertical projections to the floor. Its
upper supports equal those of S at every angle in [0,pi]. Its floor supports
are the two horizontal endpoints, and its height is one.

Every visited inner wedge, for t<=omega, is contained in K. Here is why this
does not assume injectivity. A nonempty wedge's floor endpoints lie strictly
between the horizontal extremes. Its corner's abscissa lies between them. If
the corner were above K, the vertical line through it would have all its K
points strictly in the wedge. Connectedness of S forces a point of S on that
line, contradicting the visited hallway. The corner and both floor endpoints
therefore belong to K, and convexity contains the wedge.

For an omitted angle t in [omega,pi/2], each floor-truncated wedge still lies
within the six-wide horizontal span. Writing its right-wall inequality and
using height one gives y<6*cot(t)<=6*tan(alpha)<=12alpha. Thus the UNION of
omitted wedges has area at most 72alpha. With U=K minus N(K), this gives

    |S minus U|<=72alpha,       |N(K) minus K|<=72alpha,
    A(K)>=|S|-144alpha,
    |U minus S|<=epsilon+144alpha.                            (11)

The second estimate is important: A(K) need not equal |U| until niche
containment is known. Equation (11) explicitly retains that exterior-niche
correction rather than assuming it away.

Set ebar=epsilon+144alpha. Baek's cap bound and note26 imply

    0<=M-A(K)<=ebar,
    delta=d_H(K_c,K_G,c)<=514*sqrt(ebar),                     (12)

provided ebar<=10^(-4). The omitted full-angle hallway slack of S is at most
16alpha, from the Lipschitz bound of supports and point projections in the
fixed normalized containing box.

## 7. Finish the numerical actual-set modulus

For epsilon<=10^(-144), (2) implies

    ebar<=72001*epsilon^(1/6),
    sqrt(ebar)<269*epsilon^(1/12).

In particular ebar<10^(-4), and (12) gives

    delta+16alpha <=138266*10^(-12)+8000*10^(-24)
                    <1/2040000.

Thus the explicit reference roof-slack and outer-margin estimates apply.
Orthogonal erosion places the reference eroded by sqrt(2)delta inside U.
Its missing area is at most ebar by (11). The same surviving-disk argument as
in note26 gives reverse radius rho=20*(delta+sqrt(ebar)); it is below 1/24.
Forward recovery costs at most (51/5)*(delta+16alpha), which is less than rho
because 16alpha<=ebar/9<=sqrt(ebar). Consequently

    d_H(S_c,G)<=10300*sqrt(ebar)
              <2770700*epsilon^(1/12)
              <3000000*epsilon^(1/12).

This proves (1). At epsilon=0 the existing normalized uniqueness theorem
handles equality directly. Applying (1) with the stricter radius budget in
(3) proves the effective neighborhood-entry statement.

## Review boundary and what remains numerical

The new global modulus is analytic; exact scalar checks alone do not verify
its polygon-limit and geometric lemmas. In particular review Sections 3--4's
penalty/assigned-height comparison and support-gap transfer, and Section 6's
exterior-niche correction. No original input sofa is replaced in the conclusion
by an auxiliary maximizer.

The previously missing global separation mechanism is addressed by (3).
Notes29--32 add explicit reference-local radii and a proposed numerical cutoff
for the sharp local constants 2.3/50/3.1. The new weak exponent is an entry tool,
not an improvement of the sharp exponent one half. Neither its small threshold
nor the final cutoff is advertised as a practically useful optimizer error bar.
Independent review of the analytic arguments remains necessary.
