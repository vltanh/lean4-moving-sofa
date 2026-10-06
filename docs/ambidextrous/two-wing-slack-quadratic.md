# A sharp cut-slack extension for wings spanning the common strip

This closes a defined part of roadmap R4: the inward cut-vertex membership and the cut-width equalities can be removed **when each wing touches both y=0 and y=1**. The proof retains the favorable first-order cut work; its quadratic part alone can be negative.

Use the relaxed data and the actual-intersection functional widehat W from [CS.1–CS.3](two-wing-cut-slack.md). Fix the reference beta and M of WC. The four nonnegative cut slacks are denoted r_+,r_-,d_+,d_- in this note; these are numbers, not derivatives or positive parts. Put y=tan(beta), so 0<y<1, and set

$$
s_R=(r_++r_-)/2,\quad e_R=(r_+-r_-)/2,
\qquad s_D=(d_++d_-)/2,\quad e_D=(d_+-d_-)/2.
\tag{SQ.1}
$$

In particular 0<=s_R,s_D<=1.

## 1. Statement

**Theorem SQ1 (full-height slack calibration).** Let R,D be nonempty compact convex bodies in 0<=y_coord<=1, each having vertical width exactly one. Assume all directional-width inequalities TW.1, but not the inward memberships of TW.2. Then

$$
\boxed{\widehat{\mathcal W}(R,D)\leq M.}
\tag{SQ.2}
$$

Equality holds exactly for the reference wing pair translated together horizontally. More quantitatively, after the harmless actual-corner completion CS1,

$$
\begin{aligned}
M-\widehat{\mathcal W}\ \geq{}&
\sum_{B=R,D}\int_\beta^{\pi-\beta}\mu(t)[1-w_B(t)]dt\\
&+\frac{y(3-y)}4(s_R+s_D)\\
&+\frac{y^2+2y+3/y}{8}(e_R+e_D)^2
 +\frac{1+3/y}{8}(e_R-e_D)^2.
\end{aligned}
\tag{SQ.3}
$$

The full identity also has the nonnegative interpolation and finite-matrix residuals described below. For uncompleted wings add their nonnegative gained areas to the left deficit. There is no assumption of reflection symmetry or a curvature upper bound.

## 2. Exact reduction of the quadratic part

Complete both actual corners of each wing by CS1. Relative to the reference pair, subtract the common translation given by the displacement of the left outward vertex. In this gauge the left outward gap has zero difference. The right outward vertex difference is v; write

$$
X=c v_x,\qquad Z=s v_y,\qquad z_0=(\delta P_D)_y/c,
\quad c=\cos\beta,\ s=\sin\beta.
$$

Because the original and competing wings all have top one and bottom zero, the two lower-half vertical traces, divided by c, are U=V=-z_0; the reflected upper traces are U=V=z_0. This is the specific full-height input; it must not be assumed for unequal-height wings.

On the lower core let f(t)=delta r(t) and g(t)=delta d(t+pi/2), for beta<=t<=b=pi/2-beta. Their endpoint values are

$$
f(\beta)=X+Z=:f_0,\qquad f(b)=F,
\qquad g(\beta)=G,\qquad g(b)=0.
$$

After the core-area cancellation, its negative quadratic contribution is one half of integral (f'^2+g'^2+fg'-gf'). Put

$$
C=\frac{2y}{1+y^2},\quad S=\frac{1-y^2}{1+y^2},
\quad T=\frac{1+y}{1-y},
$$
$$
F_0=F-Cf_0-SG,\quad G_0=Sf_0-CG,
\quad a_0=(TF_0-G_0)/2,\quad b_0=(F_0+TG_0)/2.
$$

Its exact minimum for these endpoints is

$$
E_{\rm core}=\tfrac12[a_0(F-f_0)-b_0G].
\tag{SQ.4}
$$

For verification, the minimizer satisfies f'=g+a_0 and g'=-f+b_0. Its integrand is a_0 f'+b_0 g'. Subtracting it leaves a zero-endpoint pair whose energy is

$$
\tfrac12\int\bigl(|(e^{it/2}(e_f+i e_g))'|^2
-\tfrac14|e_f+i e_g|^2\bigr)\geq0,
$$

with equality only for zero error, by the Dirichlet inequality on the core interval of length less than pi.

Every remaining arc has energy one half of integral (w'^2-w^2). For endpoint values a,b on length d<pi its minimum is

$$
\tfrac12[(a^2+b^2)\cot d-2ab\csc d].
\tag{SQ.5}
$$

This follows by subtracting the harmonic interpolant and applying the zero-endpoint Dirichlet inequality. It is valid for H^1 functions.

## 3. A fully specified finite expression

The actual inward-vertex differences, in scaled coordinates, are

$$
X_R=X+(r_++r_-)/2,\quad Z_R=Z+(r_+-r_-)/2,
$$
$$
X_D=-(d_++d_-)/2,\quad Z_D=(d_--d_+)/2.
$$

Define the half-gap energies

$$
G_0(x,z)=\tfrac12(z^2/y-yx^2)-yxz,\qquad
G_\pi(x,z)=\tfrac12(z^2/y-yx^2)+yxz.
$$

These are the integrals in SQ.5 for a harmonic vertex support over [0,beta] and [pi-beta,pi], respectively. After minimizing the four noncore arcs, the complete lower-half expression is

$$
\begin{aligned}
E={}&E_{\rm core}
+\tfrac12\left[
\frac{F^2-2FU+U^2}{y}
+y(-X+Z-r_-)^2-2U(-X+Z-r_-)\right.\\
&\left.\hspace{20mm}+y d_+^2+2Vd_+
+\frac{V^2+G^2-2VG}{y}\right]\\
&+G_0(X,Z)+G_\pi(X_R,Z_R)+G_0(X_D,Z_D)\\
&+\tfrac12[(yX_R-Z_R/y)f_0+(f_0+r_+)G+d_-F].
\end{aligned}
\tag{SQ.6}
$$

The final line is the **actual inward-cut determinant**, not the old fixed-width point's determinant. It follows from det(delta I_R,delta z_-(beta))/2 minus det(delta I_D,delta z_-(b))/2. In particular the lower inward support traces are -X+Z-r_- on the right and -d_+ on the left.

Let E_red be the minimum of SQ.6 over F,G. Its quadratic coefficient matrix (one half its Hessian) is

$$
H_2=\begin{pmatrix}d&-1/4\\-1/4&d\end{pmatrix},
\qquad d=\frac{y^2-y+2}{4y(1-y)}.
$$

Its LDL pivots are

$$
\frac{y^2-y+2}{4y(1-y)},\qquad
\frac{y^2-y+1}{y(1-y)(y^2-y+2)},
$$

both positive. Explicitly, if E=e_0+l^T(F,G)+(F,G)H_2(F,G)^T, then E_red=e_0-l^T H_2^{-1}l/4, and the omitted residual is a positive H_2 square.

## 4. Sum both halves and retain the slack remainder

The reflected half replaces Z by -Z, exchanges r_+ with r_- and d_+ with d_-, and uses U=V=z_0 instead of -z_0. Consequently the full negative quadratic B satisfies

$$
B\geq E_{\rm red}(X,Z,-z_0,-z_0;r_+,r_-,d_+,d_-)
+E_{\rm red}(X,-Z,z_0,z_0;r_-,r_+,d_-,d_+).
\tag{SQ.7}
$$

This expression is minimized over X,Z,z_0 at

$$
X_*=-\frac y2(s_R+s_D),\qquad Z_*=-\frac{e_R+e_D}{2},
$$
$$
z_* =\frac{(1-y)e_R+(3y-1+2/y)e_D}{4}.
\tag{SQ.8}
$$

Its quadratic coefficient matrix is, with d_0=y^2-y+1,

$$
H_3=\begin{pmatrix}
\frac{1+y^2}{2d_0}&0&0\\
0&\frac{(1+y^2)(2y^2-y+2)}{2yd_0}&\frac{1+y^2}{d_0}\\
0&\frac{1+y^2}{d_0}&\frac{2y}{d_0}
\end{pmatrix}.
$$

Its three LDL pivots are

$$
\frac{1+y^2}{2d_0},\quad
\frac{(1+y^2)(2y^2-y+2)}{2yd_0},\quad
\frac{2y}{2y^2-y+2},
$$

again positive. Substitution of SQ.8 into SQ.6 after the two H_2 minimizations gives the exact remaining polynomial

$$
\begin{aligned}
P={}&\frac{y^2+2y+3/y}{8}(e_R+e_D)^2
+\frac{1+3/y}{8}(e_R-e_D)^2\\
&-\frac y4(s_R^2+s_D^2+2y s_Rs_D).
\end{aligned}
\tag{SQ.9}
$$

Equations SQ.4–SQ.9 specify the finite algebra completely: differentiate SQ.6 twice, use the displayed two-by-two inverse, substitute SQ.8, and expand. The accompanying symbolic checker verifies these rational identities in the indeterminate y. The proof does not depend on a sampled eigenvalue or a numerical optimizer.

## 5. The first-order slack pays for the negative quadratic term

By CS2 and exact quadratic expansion,

$$
M-\widehat{\mathcal W}
=\sum_B\int\mu(1-w_B)+y(s_R+s_D)+B.
\tag{SQ.10}
$$

For s_R,s_D in [0,1],

$$
s_R^2+s_D^2+2y s_Rs_D\leq(1+y)(s_R+s_D).
$$

Use s_i^2<=s_i and 2s_Rs_D<=s_R+s_D. Combining this with B>=P proves SQ.3, hence SQ.2. This is why a negative quadratic direction alone would have been the wrong test for the slack extension.

At equality, the strictly positive coefficient y(3-y)/4 forces s_R=s_D=0. All four nonnegative cut slacks vanish. The completed wings then satisfy the original TW.2 with inward points equal to Q_R,Q_D, so WC2 gives the reference pair up to a common horizontal translation. Equivalently all the arc and finite-matrix residuals above vanish. Since corner completion changes only the wing areas, equality also forces each original wing to equal its completed candidate wing: a proper closed convex subset of a full-dimensional convex body has smaller area. Conversely the candidate attains equality. This proves SQ1.

## 6. Scope and two negative controls

If both means equal epsilon and both differences are zero, SQ.9 gives P=-y(1+y)epsilon^2/2<0. Thus no claim of unrestricted joint concavity has been made. The positive linear term in SQ.10 is essential.

Also, the full-height trace equations U=V=-z_0 are essential to the present derivation. If one wing does not touch both strip boundaries, its vertical support deficits introduce additional variables and cross terms. This note does not establish their sign. It does not claim that canonical wings of every maximizer span the strip.

**Geometric corollary.** If a body has relaxed full-height wing data and an ordinary-area comparison CS.4, then its area is at most M. Equality identifies the wings and the reference core; closed containment and the established regular closedness of the reference envelope give exact body recovery. Constructing such data for every unrestricted maximizer is still open.

This is a written, self-reviewed extension of a conditional certificate. It is not an independently verified solution of the ambidextrous problem. No CI or Lean/Lake compilation is used.
