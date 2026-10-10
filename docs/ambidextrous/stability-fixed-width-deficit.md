# Fixed-width deficit: a quantitative transfer of PR #8's energy method

This is an **auxiliary-functional** theorem. It applies to arbitrary H^1 profiles, without requiring convexity or motion feasibility. It is inspired by the separation between residual coercivity and geometric enclosure in [PR #8, note 05](https://github.com/vltanh/lean4-moving-sofa/blob/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability/05-nonsmooth-certificate.md). Its formulas and constants are derived here for the ambidextrous functional; Gerver's Green constant is not reused.

The source for our definitions and the unique fixed-width optimizer is [AF1](adaptive-functional-global-calibration.md). The use of AF3 below is explicitly identified. This does not assert stability of ordinary ambidextrous sofa area.

## 1. A nonsmooth exact deficit, not just a Taylor inequality

Set L=pi/2 and use the space X_a and half-functional F of the AF supplement. Let (f_a,g_a) be the unique maximizer in X_a. For a competitor (f,g) in the same space write

\[
v=f-f_a,\qquad w=g-g_a,\qquad z=v+iw,
\qquad y(t)=e^{-it/2}z(t).
\]

The four endpoint values of v,w vanish. Set

\[
p=f'-g+1,\quad q=g'+f-1,
\quad p_a=f_a'-g_a+1,\quad q_a=g_a'+f_a-1.
\]

Define the two convex functions and their Bregman remainders by

\[
j_-(x)=\tfrac12\min(x,0)^2,\quad
j_+(x)=\tfrac12\max(x,0)^2,
\]

\[
\mathfrak d_\pm(x,x_0)
=j_\pm(x)-j_\pm(x_0)-j_\pm'(x_0)(x-x_0)\geq0.
\tag{SD.1}
\]

Their derivatives are min(x,0) and max(x,0), respectively, including at zero. No differentiation of a moving contact set is required.

**Theorem SD1 (exact fixed-width energy).**

\[
\begin{aligned}
F(f_a,g_a)-F(f,g)
={}&\frac12\int_0^L\left(|y'|^2-\frac94|y|^2\right)dt\\
&+\int_0^L\mathfrak d_-(p,p_a)\,dt
+\int_0^L\mathfrak d_+(q,q_a)\,dt.
\end{aligned}
\tag{SD.2}
\]

Consequently

\[
F(f_a,g_a)-F(f,g)\geq\frac7{32}\int_0^L|y'|^2dt.
\tag{SD.3}
\]

**Proof.** Write F=F_0 minus the integrals of j_-(p),j_+(q), where F_0 is the unpenalized quadratic C+I. Its expansion is exact:

\[
F_0(f_a+v,g_a+w)=F_0(f_a,g_a)+DF_0(f_a,g_a)[v,w]-B_0(v,w),
\]

with B_0 the gauge integral in (A.4). Expanding each j by its defining Bregman remainder leaves the linear term DF(f_a,g_a)[v,w]. This vanishes because the maximizer is stationary along every zero-endpoint H^1 direction; the functions j have Lipschitz derivatives, so F is differentiable on this affine Hilbert space. This proves (SD.2).

The Dirichlet inequality on length L gives integral |y|^2 <= one quarter of integral |y'|^2. Thus B_0 >= (1/2)(1-9/16) integral |y'|^2 = (7/32) integral |y'|^2. The Bregman terms are nonnegative. QED.

This argument remains valid when a competitor has many switching points, intervals on which p or q vanishes, or no pointwise second derivative. It avoids an unproved Hessian formula across the competitor's changing contact sets.

## 2. Explicit pointwise coercivity

For any complex y in H^1_0(0,L),

\[
|y(t)|^2\leq\frac{t(L-t)}{L}\int_0^L|y'|^2
\leq\frac L4\int_0^L|y'|^2.
\tag{SD.4}
\]

**Proof.** The identity

\[
y(t)=\frac{L-t}{L}\int_0^t y'(s)ds-\frac tL\int_t^L y'(s)ds
\]

and Cauchy–Schwarz give the first inequality: the squared L^2 norm of the displayed piecewise-constant kernel is t(L-t)/L. Maximize that quadratic to obtain the second. QED.

Combining (SD.3)–(SD.4), and using |z|=|y|, yields

\[
\boxed{\sup_t\sqrt{|f-f_a|^2+|g-g_a|^2}
\leq\sqrt{\frac{4\pi}{7}\,[F(f_a,g_a)-F(f,g)]}.}
\tag{SD.5}
\]

The constant is explicit but is not claimed sharp.

## 3. Whole profiles and the separate width defect

Center a normalized periodic profile by a horizontal-translation mode, so h(0)=h(pi)=a. Let H_a be the whole profile assembled from two identical fixed-width optimizing halves, with reflection h^rho(t)=h(-t)+sin(t). Put

\[
\Phi(a)=2F(f_a,g_a)-2a,
\qquad D_{\rm shape}(h)=\Phi(a)-\widetilde{\mathcal Q}(h).
\]

The upper and reflected-lower deficits add exactly to D_shape. Applying (SD.5) to each gives

\[
\boxed{\|h-H_a\|_\infty^2\leq\frac{4\pi}{7}D_{\rm shape}(h).}
\tag{SD.6}
\]

Also, by comparing the two halves and using (sqrt(d_1)+sqrt(d_2))^2<=2(d_1+d_2),

\[
\boxed{\|h-h^\rho\|_\infty^2\leq\frac{8\pi}{7}D_{\rm shape}(h).}
\tag{SD.7}
\]

These are statements about support **profiles**. H_a need not be asserted feasible or convex, and no Minkowski average of sofas is declared feasible.

For a>=1/2, AF3 supplies the additional nonnegative term

\[
\Delta(a)=M_A-\Phi(a),
\]

and hence

\[
M_A-\widetilde{\mathcal Q}(h)
=\Delta(a)+D_{\rm shape}(h).
\tag{SD.8}
\]

At the candidate width a_*, H_a is the centered candidate profile. At other widths (SD.6) compares h to H_a, not directly to the candidate. A width estimate is a separate obligation; it must not be hidden in the use of a fixed-width norm.

## 4. The precise ordinary-area implication

For a feasible body S with centered actual hull support h, define its ordinary-area excess over the auxiliary functional by

\[
E(S)=|S|-\widetilde{\mathcal Q}(h).
\]

There is no assertion that E is nonpositive. The exact accounting is

\[
M_A-|S|=\Delta(a)+D_{\rm shape}(h)-E(S).
\tag{SD.9}
\]

In particular every hypothetical body of area at least M_A must satisfy

\[
\boxed{E(S)\geq\Delta(a)+\frac7{4\pi}\|h-H_a\|_\infty^2.}
\tag{SD.10}
\]

Thus a geometric estimate bounding E below the right side would exclude that body. It is not enough to know that the profile energy is coercive, or that E tends to zero along a near-candidate family: their relative sizes matter.

The exact area-defect counterexamples already committed remain compatible with (SD.9). This quantitative decomposition is the transferable stability mechanism. It neither assumes nor proves the missing ordinary-area comparison. No CI, Lean compilation, numerical experiment, or computer algebra was used.
