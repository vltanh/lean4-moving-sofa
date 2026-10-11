# The universal near-reversal shape

Status: new analytic theorem draft, dependent on the reverse majorant, quadratic maximization, geometric realization, alignment lemma, and uniform stability estimate. It has not been independently reviewed or Lean-checked. Numerical pictures or tests are not used to infer this theorem.

Write e=pi-beta. The rescaling in this file is

    A_e(x,y)=(e*x,y).

It is a normalization for studying the shapes, NOT a claim that anisotropic scaling preserves rigid hallway motions.

## 1. Explicit limiting body

Put

    k=sqrt(3), alpha=k/2,
    D=cos alpha+sin alpha/k,
    T0=tan alpha/k,
    C=3(1+3T0)/[4(1+T0)].

The limiting left boundary has the following parametrization, -1/2<=u<=1/2:

    X_L(u)=[cos alpha-cos(k u)]/D,
    Y_L(u)=[u cos(k u)+sin(k u)/(2k)]/D.                (1)

The function Y_L is strictly increasing from -1/2 to 1/2, so (1) defines a graph X=g_0(Y).

For 0<=v<=1, write u=v-1/2 and define

    H(v)=1+[cos alpha/D]v
              -[cos(k u)-sin(k u)/k]/(2D),
    X_R(v)=H'(v)=[cos alpha+cos(k u)/2+k sin(k u)/2]/D,
    Y_R(v)=H(v)-v H'(v).                               (2)

This is the upper right boundary, from a point at height 1/2 to (3/2,0). Reflect it across the horizontal axis for the lower right boundary. The two horizontal segments join its top and bottom endpoints to (0,+/-1/2), the endpoints of (1). These curves bound a compact convex body T with nonempty interior.

For example, the top segment length is exactly

    3(1-T0)/[2(1+T0)]>0.

The body's area is

    area(T)=C=1.35653373245229... .                     (3)

## 2. The explicit finite-angle optimizers converge to T

Let S_e be the normalized reverse optimizer from the geometric theorem. Then

    d_H(A_e S_e,T)=O(e^2),                             (4)

where d_H is Hausdorff distance.

Substitute t=e u and phi=e v into the explicit corner and support formulas. The limits are (1)-(2): k_e e->sqrt(3), eta_e->1/sqrt(3), e B_e->-1/D, and e A_e->cos(alpha)/D. In this sentence A_e,B_e with scalar subscripts refer to the coefficients in the old stationary formula, not the spatial map A_e.

After removing factors e/sin(e), every rescaled coordinate formula is analytic and even in e near zero, uniformly over its compact parameter interval; the denominator tends to D>0. Therefore the parametrized boundary error is O(e^2), which implies (4). Convexity passes to the limit, and positivity of the displayed arc/segment widths gives nonempty interior. Area continuity for these bounded convex bodies and e V(e)->C prove (3).

The positive endpoint derivative is

    Y_L'(+/-1/2)=3(1-T0)/[2(1+T0)]>0;

throughout the interval,

    Y_L'(u)=[(3/2)cos(k u)-k u sin(k u)]/D>0.

These facts also follow directly from (1), using T0<1.

## 3. Every asymptotically optimal reverse sofa has this limit

Let e_n->0+, and let S_n be arbitrary aligned reverse sofas satisfying

    e_n area(S_n)->C.                                 (5)

They need not be convex, symmetric, smooth, or of full width. Normalize each actual strip vertically around zero and fix the horizontal canonical-corner gauge.

By the exact reverse theorem,

    delta_n=e_n[V(e_n)-area(S_n)]>=0,
    delta_n->0.

The uniform stability theorem proves actual widths w_n->1 and uniform convergence of the rescaled canonical corners to the curve (1). This is a quantitative step: the path error relative to the finite-e optimizer is O(sqrt(delta_n)+delta_n), and that optimizer differs from (1) by O(e_n^2).

The midpoint hallway and the bounded rescaled canonical midpoint put A_{e_n}S_n in one common bounded rectangle. Explicitly, its wall expression is

    sin(e_n/2)(x-C_x)+cos(e_n/2)|y-C_y| in [0,1].

After multiplying x and C_x by e_n, the coefficients e_n/sin(e_n/2) and e_n cot(e_n/2) stay bounded. Thus no distant zero-area appendage is lost by assuming a bound that was never proved.

Take any Hausdorff-convergent subsequence with limit S. At parameter v in [0,1], the rescaled wall normals converge to

    N1(v)=(v,1), N2(v)=(1-v,-1).

The limiting canonical corner is (X_L(v-1/2),Y_L(v-1/2)). Closed hallway containment passes to the limit, as does the strip condition -1/2<=y<=1/2.

For every interior height Y choose the unique v in (0,1) with Y=Y_L(v-1/2). At that height, both wall coordinates of (X,Y) relative to the corner have the sign of X-X_L(v-1/2). Avoiding the forbidden wedge therefore forces X>=g_0(Y). The limiting outer support inequalities, with right-hand sides H(v), force X below the right cap in (2).

The endpoint heights need a separate argument. At Y=-1/2, a point with X<0 is also forbidden: as v->0+, its first wall coordinate divided by v tends to X-Y_L'(-1/2)<0, and its second wall coordinate tends to X<0. Reflection handles Y=1/2. Thus no additional segment on the top or bottom boundary is inadvertently admitted by using a zero horizontal component at v=0 or 1.

Consequently S is a subset of T. Area is upper semicontinuous under bounded Hausdorff convergence, so (5) gives area(S)>=C. Since area(T)=C, equality holds. Because S is closed and T is the closure of its interior, a missing point would give a missing positive-area interior neighborhood. Hence S=T.

Every convergent subsequence has the same limit. We conclude

    A_{e_n}S_n -> T in Hausdorff distance.              (6)

This is a statement about the actual possibly nonconvex sofa sets, not just their convex hulls or support paths.

## 4. The same conclusion holds without any motion-class restriction

Now let S_n be arbitrary unrestricted moving sofas at bends pi-e_n, with e_n area(S_n)->C. Normalize the incoming strip horizontally. The alignment lemma supplies lambda_n S_n in an aligned class, with

    area(lambda_n S_n)>= [A_n+sqrt(A_n^2-1)]/2,
    A_n=area(S_n), lambda_n->1.

The forward-class bound is O(1) near reversal, whereas these scaled areas diverge like C/e_n. The aligned class must therefore be reverse for all sufficiently large n. Moreover e_n area(lambda_n S_n)->C, so Section 3 applies.

Undoing the scalar lambda_n, which tends to one, does not change a bounded Hausdorff limit. After the corresponding translations and incoming-strip normalization,

    A_{e_n}S_n -> T.                                   (7)

By the unrestricted asymptotic theorem, the condition e_n area(S_n)->C is equivalent to asymptotic relative optimality area(S_n)/M(pi-e_n)->1. Thus EVERY asymptotically optimal family, regardless of its original motion or geometry, has the same explicit rescaled limiting shape.

## 5. An additional consequence for actual unrestricted maximizers

Existence of unrestricted maximizers is proved in `HALLWAY_WELL_POSEDNESS.md`. For such a maximizer, A_n=M(pi-e_n)>=V(e_n). The alignment loss is at most

    A_n-area(lambda_n S_n)
       <=1/[2(A_n+sqrt(A_n^2-1))]=O(e_n).

Its normalized reverse deficit is therefore O(e_n^2). The stability estimate gives width deficit O(e_n^2) for the aligned scaled sofa and rescaled canonical-path error O(e_n). These estimates do not by themselves assert the same Hausdorff rate for arbitrary sets; (7) is the set-level conclusion proved here.

## What this does not prove

No exact unrestricted finite-angle equality M(pi-e)=V(e) follows. No uniqueness of an unrestricted maximizer at a fixed e>0 follows. Nor does the theorem determine the middle-angle phase transition. It upgrades the sharp area asymptotic to a universal geometric limit and retains the distinction between path stability, set convergence, and exact finite-angle optimality.
