# The two-wing quadratic is nonnegative on the common-strip cone

The two-wing functional is **not** concave on an unrestricted affine space of wing profiles. The right statement is positivity of its negative quadratic part for differences from the reference pair when the two competing wings fit in one common strip of height one. The finite trace remainder has an exact copositive factorization.

This theorem is independent of a curvature upper bound and includes H^1 support differences. It is an algebraic result for the domain of [TW.1–TW.4](two-wing-domain.md), not yet admission of every sofa to that domain. Labels WS are local.

## 1. Quadratic part and translation gauge

Complete the outward gaps by TW1. A difference from the reference wing pair is harmonic on both short gaps of each wing. Write v_R and v_D for the differences of the corresponding cut vertices P_R and P_D; the inward vertices have the same differences. The negative homogeneous quadratic part of the functional will be denoted B(delta).

Common translation does not change B. Subtract the common vector v_D, so that the left-wing gap difference is zero and the right-wing gap difference is v=(v_x,v_y) dot n_t. Put

$$
y=\tan\beta,\quad X=v_x\cos\beta,\quad Z=v_y\sin\beta,
\quad \ell=\pi/2-2\beta.
$$

Here y is a scalar angle parameter, not a point coordinate. On the lower core write

$$
f(t)=\delta r(t),\quad g(t)=\delta d(t+\pi/2),
\quad f(\beta)=X+Z,
\quad g(b)=0,
$$

and denote F=f(b), G=g(beta), U=delta r(pi/2)/cos(beta), V=delta d(pi/2)/cos(beta). The upper reflected half has the same formulas with Z replaced by -Z and the reflected vertical traces.

Expanding the area and core integrals, their f² and g² core terms cancel. The core's contribution to B is exactly

$$
\frac12\int_\beta^b(f'^2+g'^2+fg'-gf').
\tag{WS.1}
$$

The remaining long support arcs contribute one half of integral (w'^2-w²). Short gaps and cut determinants contribute only finite endpoint expressions. All these terms are retained below.

## 2. Minimize the arc energies without discarding a boundary term

For prescribed endpoint values w_0,w_1 on an interval of length d<pi,

$$
\frac12\int(w'^2-w^2)\geq
\frac12[(w_0^2+w_1^2)\cot d-2w_0w_1\csc d].
\tag{WS.2}
$$

Equality holds for the harmonic interpolant. Subtract that interpolant and integrate by parts: the remainder has zero endpoints and is one half of integral (e'^2-e²), nonnegative by the Dirichlet inequality. This proves the assertion for H^1 functions as well.

The minimizer of WS.1 solves f'=g+a, g'=-f+b_0, with constants a,b_0. Set

$$
C=\sin2\beta=\frac{2y}{1+y^2},\quad
S=\cos2\beta=\frac{1-y^2}{1+y^2},\quad
T=\cot(\ell/2)=\frac{1+y}{1-y},\quad f_0=X+Z,
$$

$$
F_0=F-Cf_0-SG,\qquad G_0=Sf_0-CG,
$$

$$
a=(TF_0-G_0)/2,\qquad b_0=(F_0+TG_0)/2.
$$

The exact minimum is

$$
E_{\rm core}=\tfrac12[a(F-f_0)-b_0G].
\tag{WS.3}
$$

Indeed the solution of f''+f=b_0 with the stated initial values gives precisely the two linear equations defining a,b_0. On that solution the integrand of WS.1 is a f'+b_0 g', so its integral is WS.3. The remainder after subtracting the solution has zero endpoints. For z=e_f+i e_g it is

$$
\frac12\int\left(|(e^{it/2}z)'|^2-\tfrac14|z|^2\right)>0
\tag{WS.4}
$$

unless z=0. This follows from the Dirichlet inequality on length ell<pi. Thus the minimization is global, not a stationary-point assumption.

## 3. The complete one-half finite expression

Apply WS.2 to the right arc from b to pi-beta, splitting at pi/2, and to the left arc from beta to pi/2+beta, splitting at pi/2. Add the two short-gap contributions and the cut determinant. The resulting lower bound for the one-half contribution is

$$
\begin{aligned}
E_y(X,Z,U,V,F,G)={}&E_{\rm core}\\
&+\frac12\left[
\frac{F^2-2FU+U^2}{y}
+y(-X+Z)^2-2U(-X+Z)
+\frac{V^2+G^2-2VG}{y}\right]\\
&+\frac{Z^2}{y}-yX^2
+\frac12[(X+Z)G-( -Xy+Z/y)(X+Z)].
\end{aligned}
\tag{WS.5}
$$

For clarity about scaling: the actual vertical trace is cos(beta) times U or V. The identity cos²(beta)(cot(beta)+tan(beta))=1/y accounts for the U²/y and V²/y terms. The gap contribution is sin(beta)cos(beta)(v_y²-v_x²)=Z²/y-yX². The last term is the lower half of the cut determinant, computed as one half of det(v,delta z_-(beta)). The left cut contributes zero in the chosen gauge. The reflected upper half supplies its corresponding expression, not a duplicated assumption of symmetry.

Let E_y^red(X,Z,U,V)=min_{F,G} E_y. Its quadratic coefficient matrix in F,G is

$$
H_2=\begin{pmatrix}d&-1/4\\-1/4&d\end{pmatrix},
\qquad d=\frac{y^2-y+2}{4y(1-y)}.
\tag{WS.6}
$$

It is positive definite for 0<y<1. The two LDL pivots are

$$
\frac{y^2-y+2}{4y(1-y)},\qquad
\frac{y^2-y+1}{y(1-y)(y^2-y+2)}.
$$

Thus E_y^red is explicit: if E_y=e_0+l^T(F,G)+(F,G)H_2(F,G)^T, it is e_0-l^T H_2^{-1}l/4. This formula and WS.5 specify it without a numerical optimizer.

## 4. The common strip supplies the needed sign restrictions

Translate the competing pair vertically until the higher of its two top supports equals one. Since their union fits in a strip of height at most one, both bottoms remain nonnegative. Reflect horizontally and exchange the wings if necessary so the right top is the higher one. These operations preserve the functional and reference pair up to its symmetries.

Before the translation gauge in Section 1, write its four vertical support differences as

$$
\delta r(L)=0,\quad\delta d(L)=-c A,
\quad\delta r(-L)=-c B_0,\quad\delta d(-L)=-c C_0,
\qquad A,B_0,C_0\geq0,
\tag{WS.7}
$$

where c=cos(beta). The name B_0 here is a scalar bottom deficit, not the quadratic B(delta) or the core constant b_0. Put z_0=(v_D)_y/c for the common translation removed in Section 1. The four gauge-adjusted traces are then

$$
(U,V)=(-z_0,-A-z_0),\qquad
(U^\rho,V^\rho)=(-B_0+z_0,-C_0+z_0).
$$

Consequently the complete quadratic satisfies

$$
B(\delta)\geq
E_y^{\rm red}(X,Z,-z_0,-A-z_0)
+E_y^{\rm red}(X,-Z,-B_0+z_0,-C_0+z_0).
\tag{WS.8}
$$

This is where using one common strip matters. Bounds on each wing's height in two unrelated vertical positions would not give the three nonnegative deficits in WS.7.

## 5. Three-variable minimization and a short final factorization

The right side of WS.8 is a strictly convex quadratic in X,Z,z_0. Its minimizer is

$$
X_* =\frac{(1-y)^2(A+B_0+C_0)}{2(1+y^2)},\quad
Z_* =\frac{y(A+B_0-C_0)}{1+y^2},\quad
z_* =-\frac{3A+B_0-3C_0}{4}.
\tag{WS.9}
$$

For an exact check, its quadratic coefficient matrix is

$$
H_3=\begin{pmatrix}
\frac{1+y^2}{2d_0}&0&0\\
0&\frac{(1+y^2)(2y^2-y+2)}{2y d_0}&\frac{1+y^2}{d_0}\\
0&\frac{1+y^2}{d_0}&\frac{2y}{d_0}
\end{pmatrix},\qquad d_0=y^2-y+1.
$$

Its LDL pivots are

$$
\frac{1+y^2}{2d_0},\quad
\frac{(1+y^2)(2y^2-y+2)}{2y d_0},\quad
\frac{2y}{2y^2-y+2},
$$

all positive. Substituting WS.9 in the two expressions WS.5 after the 2-by-2 minimization gives

$$
P_k(A,B_0,C_0)=\frac{(A-B_0)^2+C_0^2}{8}
+(k-\tfrac14)AC_0+(k-\tfrac34)B_0C_0,
\qquad k=\sin2\beta.
\tag{WS.10}
$$

These are finite rational identities in y, not approximations. They can be checked by differentiating WS.5, applying the displayed 2-by-2 inverse, and expanding; no eigenvalue sampled at beta is a premise.

The decisive identity is

$$
\boxed{
P_k=\frac{[B_0-A+(4k-3)C_0]^2}{8}
+\frac{1-(4k-3)^2}{8}C_0^2
+(2k-1)AC_0\geq0.
}
\tag{WS.11}
$$

For pi/12<beta<pi/4, one has 1/2<k<1, so the last two coefficients are positive. Because A,C_0 are nonnegative, the assertion follows. Equality in WS.11 requires C_0=0 and B_0=A.

**Theorem WS1 (strip-cone nonnegativity).** The negative quadratic part of the completed two-wing functional, evaluated on any difference from a strip-height-one reference pair with the same cut-width equalities, is nonnegative when the competing wings lie in one common strip of height at most one. No curvature-density upper bound is assumed.

The proof is WS.1–WS.11, including the nonnegative residuals discarded in the successive minimizations. If the competing wings both touch both boundaries of that common strip, then A=B_0=C_0=0. Equality B(delta)=0 then forces all arc residuals and finite minimization residuals to vanish. Equations WS.9 give X=Z=z_0=0, WS.6 gives F=G=0 in both halves, and the interpolation formulas force every remaining difference to vanish after the common horizontal translation is removed.

## 6. A negative control against overstatement

The unrestricted quadratic is not positive semidefinite. In WS.10 set A=1, B_0=0, C_0=-1 and choose the explicitly minimizing traces and arc interpolants. Then

$$
B=1/2-k<0.
$$

The negative C_0 violates the common-strip hypothesis. This explains why a numerical Hessian test on unrestricted profiles finds a negative direction and why that test does not refute WS1. Conversely WS1 must not be advertised as joint concavity on the entire affine profile space.

The symbolic and numerical checks are kept separately as diagnostics of these identities. The written proof uses the displayed rational matrices and factorization. It still does not show that an arbitrary ambidextrous body has the geometric admission required in TW.5.
