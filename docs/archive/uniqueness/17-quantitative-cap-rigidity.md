# 17. Quantitative cap rigidity, including the singular endpoint

Date: 2026-10-02. Pen-and-paper proof. No Lean execution or CI is used.

This independently checks the cap-identification step of notes 02 and 16 by proving a stronger stability estimate. The estimate is for the cap, not for a motion or for arbitrary sofas before the shape-preserving reductions.

## Theorem

Put L = pi/2. Let 0 < phi < pi/4, psi = L-phi, and d = L-2phi. Let K_0,K_1 be standard right-angle caps, with support functions h_0,h_1. Put

    f = h_1-h_0,   a = -f(pi),   F(t) = f(t)-a cos(t).

In particular F(L)=F(pi)=0. Write eta_1,...,eta_4 for the differences of the tangent-displacement functions of the four terms in S_phi = mamikonS, in their defining order. Let E_j be their L2 norms on the respective intervals and E = sum_j E_j^2. Then

    d_H(K_1, K_0+(a,0)) <= C_phi sqrt(E),                       (1)

where

    C_phi^2 = sec(phi)^2 [L + phi tan(phi)^2
                          + (L-2phi+tan(phi))^2/2].            (2)

For 0 < phi <= 1/25, one has C_phi^2 < 3. Thus the simpler uniform bound is

    d_H(K_1, K_0+(a,0))^2 <= 3 E.                             (3)

All assertions are valid for nonsmooth compact convex caps. No symmetry, injectivity, maximality, or parameterization of either cap is assumed.

## 1. Exact equations for the displacement differences

For a supporting-line intersection with target normal T, at almost every t in its interval,

    eta(t) = [f(T)-f(t) cos(T-t)]/sin(T-t) - f'(t).              (4)

This follows from the sine-intersection formula and the support-face identity v_K^+(t).v_t = h'_{K,+}(t). Support functions are Lipschitz; their classical derivative agrees almost everywhere with this one-sided derivative. A translation a cos(t) has zero displacement difference, so (4) is unchanged on replacing f by F.

The four intervals and target equations are:

    I_1 = (0,phi),       T_1 = L;
    I_2 = (phi,psi),     eta_2(t) = F(t+L)-F'(t);
    I_3 = (psi,L),       T_3 = L+psi = pi-phi;
    I_4 = (L,pi),        T_4 = pi.

All eta_j are square integrable: they are differences of bounded measurable tangent displacements in the Mamikon formula. The associated tangent curves satisfy the general hypotheses proved for these terms in the existing development.

For a tangent term, the absolutely continuous integrating-factor equation is

    (F(t)/sin(T-t))' = F(T)/sin(T-t)^2
                       - eta(t)/sin(T-t).                     (5)

It is used only on compact subintervals where the sine is positive. Endpoint values are subsequently obtained by continuity; no division by zero at an endpoint occurs.

## 2. Fourth interval: control despite sin(pi-t) tending to zero

Here F(pi)=F(L)=0. Integrating (5) from L to t<pi gives

    F(t) = -sin(pi-t) integral_L^t eta_4(s)/sin(pi-s) ds.

Cauchy-Schwarz gives

    |F(t)|^2 <= E_4^2 sin(pi-t)^2 integral_L^t csc(pi-s)^2 ds
              = E_4^2 sin(pi-t) cos(pi-t)
              <= E_4^2/2.

The apparent singularity is canceled by the outside sine. Hence, including both endpoints by continuity,

    sup_[L,pi] |F| <= A,   A = E_4/sqrt(2).                    (6)

This explicit calculation rules out an undetected endpoint mode. In particular |F(T_3)|<=A.

## 3. Third interval

Solve (5) with F(L)=0. Its homogeneous-in-eta part, with the prescribed F(T_3), is

    F(T_3) sin(t-L)/sin(T_3-L).

Since sin(T_3-L)=cos(phi), the remaining integral gives

    F(t) = F(T_3) sin(t-L)/cos(phi)
           - sin(T_3-t) integral_L^t eta_3(s)/sin(T_3-s) ds.

On [psi,L], sin(T_3-s)>=cos(phi), |sin(t-L)|<=sin(phi), and the interval length is phi. Therefore

    sup_[psi,L] |F| <= B,
    B = tan(phi) A + sqrt(phi) sec(phi) E_3.                   (7)

## 4. Middle interval

The outer-corner equation is F'(t)=F(t+L)-eta_2(t). Throughout [phi,psi], the shifted argument belongs to [L,pi]. Integrating backwards from psi and applying (6)-(7) gives

    sup_[phi,psi] |F| <= C,
    C = B + d A + sqrt(d) E_2.                                (8)

Absolute continuity is sufficient; no second derivative of a support function is being assumed.

## 5. First interval

Here T=L and F(L)=0, so F'(t)+tan(t)F(t)=-eta_1(t). Thus

    F(t) = cos(t)[F(phi)/cos(phi)
                  + integral_t^phi eta_1(s)/cos(s) ds].

Consequently

    sup_[0,phi] |F| <= D,
    D = sec(phi) C + sqrt(phi) sec(phi) E_1.                   (9)

We have D>=C>=B. Also d+tan(phi)>=1: the function L-2phi+tan(phi) decreases on [0,pi/4] and has value 1 at pi/4, since its derivative is tan(phi)^2-1<=0. It follows that D>=A as well. Combining (6)-(9),

    sup_[0,pi] |F| <= D
      = sqrt(phi) sec(phi) E_1
        + sqrt(d) sec(phi) E_2
        + sqrt(phi) sec(phi)^2 E_3
        + (d+tan(phi)) sec(phi) E_4/sqrt(2).

A final Cauchy-Schwarz inequality gives sup |F| <= C_phi sqrt(E), with the squared coefficient sum exactly (2).

## 6. Full support functions and Hausdorff distance

The lower supports of a standard right-angle cap are those of its bottom segment. Indeed sin(t)<=0 in the lower semicircle, and projecting a cap point vertically onto its bottom segment can only increase its scalar product with u_t.

On [pi,3L], the relevant endpoint is the left one, and the translated support difference is zero because F(pi)=0. On [3L,2pi], that difference is F(0) cos(t). Thus its absolute value in every lower direction is at most the upper supremum. The Hausdorff distance of nonempty compact convex bodies is the supremum difference of their support functions over the full circle. This proves (1).

## 7. A rational constant for Gerver's phi

For 0<phi<=1/25, use cos(phi)>=1-phi^2/2>=1249/1250 and tan(phi)<=2phi (because sec(s)^2<=2 for 0<=s<=pi/4). In particular d+tan(phi)<=L. With pi<22/7, (2) gives

    C_phi^2 <= (1250/1249)^2 [11/7 + 121/98 + 4/15625]
             = 214863350/76440049 < 3.

This is rational arithmetic, not a numerical optimization. The parameter interval used by the existing Gerver development is contained in (0,1/25].

## 8. Consequences for uniqueness and the area deficit

The square-gap identity gives, for 0<c<1,

    (1-c)S_phi(K_0)+c S_phi(K_1)
      - S_phi((1-c)K_0+c K_1) = c(1-c) E/2.

Therefore equality of the cap Mamikon functional implies E=0 and (1) gives K_1=K_0+(a,0). This recovers note 02 without relying merely on an informal endpoint-matching assertion.

For x=(K,B,D) in the upper-bound domain and x_G Gerver's triple, the quadratic deficit identity and the six square gaps give

    Q(x_G)-Q(x) = -DQ(x_G;x) + E_all/2,

where E_all includes the four cap and two tail displacement energies. The first term is nonnegative by the established first-variation inequality. Thus E<=2(Q(x_G)-Q(x)). For K in K^i and its canonical extension, A(K)<=Q(x)<=|G| yields

    d_H(K,C(G)+(a,0))^2 <= 6 (|G|-A(K)).                       (10)

In particular a maximizing K in K^i is the Gerver cap up to horizontal translation.

Equation (10) does not assert quantitative stability of arbitrary moving sofas under the earlier reductions, nor Hausdorff continuity of a cap-minus-niche operation. Only its cap conclusion, or its exact zero case followed by translation covariance of the niche, is used for shape uniqueness.

## Sources and scope

The existing inputs are the Mamikon square formula and convex-linear tangent data (`Convex/Mamikon.lean`, `Optimality/Concavity.lean`), the quadratic deficit identity (`Convex/QuadraticEquality.lean`), and the upper-bound and directional-derivative theorems (`Main.lean`, `Optimality/UpperBound.lean`). The derivation and explicit coercivity constant above are new paper work. They have not been machine-checked.
