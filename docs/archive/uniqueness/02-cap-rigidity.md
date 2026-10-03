# 02. The cap part is rigid modulo horizontal translation

Date: 2026-10-02. Status: pen-and-paper proof; not yet formalized in Lean.

## Theorem

Fix 0<phi<pi/4 and put psi=pi/2-phi. Let K_0,K_1 be nonempty compact convex caps in the repository's standard position, with rotation angle pi/2. In particular their top support is h_j(pi/2)=1, their bottom support is h_j(3pi/2)=0, and they are downward closed above the x-axis. Let S_phi(K) denote `mamikonS phi K`, namely the four Mamikon terms of Definition 8.3.2.

For any 0<c<1, equality

    S_phi((1-c)K_0+c K_1) = (1-c)S_phi(K_0)+c S_phi(K_1)

holds if and only if K_1=K_0+(a,0) for some real a.

The injectivity condition, balancedness, symmetry of the cap, and Romik's equations are not hypotheses of this rigidity theorem.

## Proof

Write f=h_1-h_0. It is Lipschitz and hence absolutely continuous, and f(pi/2)=0. By note 01, the four nonnegative Mamikon gaps must vanish individually. Set a=-f(pi).

### 1. The fourth term determines the upper-left quadrant

This is the tangent-intersection term on (pi/2,pi), with target T=pi. Its complete kernel from note 01 is

    f(t)=f(pi) cos(pi-t)+C sin(pi-t).

Continuity at t=pi/2 and f(pi/2)=0 give C=0. Hence

    f(t)=a cos t                         for pi/2 <= t <= pi.       (1)

No derivative at pi/2 or pi is assumed.

### 2. The third term transmits that translation to the right of the top

This term has interval (psi,pi/2) and target T=pi/2+psi=pi-phi. It follows that f(t)=p.u(t) on the interval for a constant vector p, with p.u(T)=f(T). Continuity at pi/2 gives p_y=0. By (1), f(T)=a cos T. Since cos T=-cos phi is nonzero, p_x=a. Thus

    f(t)=a cos t                         for psi <= t <= pi/2.      (2)

### 3. The second term transmits the translation across the middle interval

This is the outer-corner term on (phi,psi). Its equality equation is

    f'(t)=f(t+pi/2)=-a sin t             almost everywhere.

The second equality follows from (1), since t+pi/2 lies in (pi/2,pi). Absolute continuity implies f(t)=a cos t+C on [phi,psi]. Matching (2) at psi gives C=0. Therefore

    f(t)=a cos t                         for phi <= t <= psi.       (3)

### 4. The first term determines the remaining right-hand interval

The tangent target is T=pi/2 and the interval is (0,phi). Since f(T)=0, its kernel is f(t)=A cos t. Matching (3) at phi, where cos phi>0, gives A=a. Continuity includes t=0. Together,

    h_1(t)-h_0(t)=a cos t                for 0 <= t <= pi.          (4)

### 5. Recover the full convex sets, not just the upper supports

A standard cap is downward closed in y>=0, so it contains the entire bottom segment from (-h_K(pi),0) to (h_K(0),0). For pi<=t<=2pi, sin t<=0; projecting a cap point vertically to its bottom segment can only increase its dot product with u(t). Thus its support in these directions is the support of that bottom segment.

Equation (4) says that both endpoints of the bottom segment of K_1 are those of K_0 translated by (a,0). The lower support functions therefore also differ by a cos t. The support functions agree in every direction after translation, which identifies the compact convex sets: K_1=K_0+(a,0).

Conversely, translating a body by (a,0) translates every tangent-intersection curve, outer-corner curve, and supporting-face endpoint by that same vector. Each alpha function is unchanged. The square-gap formula proves equality for every c. This completes the proof.

## Consequence for the upper-bound functional Q

For x=(K,B,D) in L, use the decomposition from the existing `theorem8_3_8` / `mamikonSegmentEquality_iff`. The concavity gap of Q is the sum of the convexity gaps of S_phi(K), R_phi(B), and L_phi(D). Hence if two triples attain the same global maximum of Q, their cap components differ by a horizontal translation.

In particular every Q-maximizing triple has cap C(G)+(a,0), where G is Gerver's sofa. This conclusion does NOT identify the auxiliary bodies B,D, which encode more than the actual cap geometry.

For any cap K in K^i with A(K)=|G|, the existing bounds give

    |G|=A(K) <= Q(K,B_K,D_K) <= Q(C(G),B_G,D_G)=|G|.

Thus the canonical extension is a Q maximizer and K=C(G)+(a,0). The niche construction is translation-covariant under horizontal translations: every supporting inner quadrant and the upper half-plane defining the niche translate accordingly. Therefore

    K \ N(K) = G+(a,0).

This proves uniqueness among maximizing caps in K^i and their cap-minus-niche sofas. It also proves that every balanced maximum cap of rotation angle pi/2 is a horizontal translate of C(G), because the existing development places all such caps in K^i and gives them maximal sofa area.

## Quantitative identity

Let x_G be Gerver's triple, x any other triple in L, and delta alpha_j the changes in the six alpha functions (the four cap terms and the two tail terms). Combining note 01 with the quadratic deficit identity gives

    Q(x_G)-Q(x) = -DQ(x_G;x)
                  + (1/2) sum_{j=1}^6 integral (delta alpha_j)^2.

The directional derivative uses the segment from x_G toward x, as in the repository. It is nonpositive. Thus the cap energy alone is bounded above by twice the Q deficit. Its exact zero modes are the horizontal translations proved above.

## What this does not prove

The existing reduction for an arbitrary moving sofa compares its AREA to the area of a selected balanced maximum sofa. It does not say that the original sofa is contained in that selected sofa or that its own cap lies in K^i. Neither assertion can be inserted into the argument without proof. The remaining global problem is to obtain a shape-preserving reduction or injectivity for every maximizing sofa, not to solve the cap equality equations.

## Source anchors

- `MovingSofaOptimality/Optimality/Concavity.lean`: `mamikonS`, `lemma8_3_3`, `lemma8_3_7`, `theorem8_3_8`.
- `MovingSofaOptimality/Convex/Mamikon.lean`: `theorem7_4_1`, `theorem7_4_2`.
- `MovingSofaOptimality/Optimality/Domain.lean`: `opt_cap_down`, `opt_cap_A_mem`, `opt_cap_C_mem`, and the standard-cap facts.
- `MovingSofaUniqueness/Rigidity/EqualityConditions.lean`: `mamikonSegmentEquality_iff`, `ki_upperQL_eq_gerver_of_sofaArea_eq`.
- `MovingSofaOptimality/Main.lean`: `theorem8_1_1_balanced`, `corollary8_5_8`.

All references refer to the source already present at commit 865eb1f4e936a976d1405cb59f7a83ffc00fe32b. The rigidity argument above is new mathematical work in this research branch and is not claimed to have been kernel-checked.
