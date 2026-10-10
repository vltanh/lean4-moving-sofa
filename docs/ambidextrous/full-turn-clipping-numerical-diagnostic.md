# Numerical diagnostic of the full-turn clipping inequality: supporting evidence, not a proof

**Question.** For a compatible pair of full-turn caps with nonempty surviving fibers, does
\[
G\le\Delta(U)+\Delta(V),\qquad \Delta(U)=M/2-\Psi(U)
\]
hold? The algebraic identity
\[
\boxed{\Delta(U)+\Delta(V)-G=M-|E|}
\]
shows that this is precisely the unresolved sharp full-turn area bound, **not an independently established auxiliary lemma**. It cannot be assumed from the weighted one-turn value. In particular a numerical check of finitely many pairs cannot prove it.

## 1. An explicitly feasible test family

Take the centered Romik reference hull, with downward upper roof \(A_*(x)\), horizontal projection \(I=[-m,m]\), top face \([a,b]=[-m/2,m/2]\), and area \(M=1+4Y^2+\arctan Y\), \(4Y^3+3Y-1=0\). Define independently cut cap roofs
\[
A_{\tau_+}(x)=\min\{A_*(x),1-\tau_+(x-a)\},\quad
A_{\tau_-}(x)=\min\{A_*(x),1-\tau_-(x-a)\}.
\]
The full envelope from these two caps has the canonical full turns, and each retains the reference midline for the indicated small slopes. The model is a valid full-turn cap-pair test; it is not a random unsupported support sample.

For each cap compute its full niche roof as
\[
n_U(x)=\max\left(0,\sup_{0<t<\pi/2}\min\left\{
\frac{h_U(t)-1-x\cos t}{\sin t},
\frac{h_U(t+\pi/2)-1+x\sin t}{\cos t}
\right\}\right).
\]
Then
\[
\Psi(U)=\int_I(A_U-n_U)dx-|I|/2,
\quad
G=\int_I[\min(n_U,1-A_V)+\min(n_V,1-A_U)]dx.
\]
All values below are *floating-point discretizations*: the roof is obtained as a minimum of sampled supporting lines, cap support as a maximum over sampled abscissae, the niche as a maximum over sampled angles, and the resulting profiles are trapezoid-integrated.

## 2. Computed results

Using **4,000 horizontal points**, **4,000 roof-normal samples**, and **4,000 niche-angle samples**, the following raw results were obtained in short scripts (each execution was externally capped at five seconds).

| \(\tau_+\) | \(\tau_-\) | \(G\), approx. | \(\Delta(U)+\Delta(V)\), approx. | Difference, approx. |
|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | **-0.000038587** | **-0.000038587** |
| 0.01 | 0 | 0.006027419 | 0.007585575 | **+0.001558156** |
| 0.01 | 0.01 | 0.011887588 | 0.015209737 | **+0.003322149** |
| 0.02 | 0.005 | 0.014401751 | 0.019620446 | **+0.005218695** |

The exact reference has \(G=0\), \(\Delta(U)=\Delta(V)=0\): the displayed **negative** reference difference is a known numerical artifact. It decreases with resolution: approximately -0.000156586 at 700 horizontal points, -0.000099521 at 1,400, and -0.000038587 at 4,000. Thus even the sign of the raw numerical difference is not intrinsically certified.

For the one-sided cut \((0.01,0)\), the raw difference changes from approximately +0.001439985 (700) to +0.001496071 (1,400) to +0.001558156 (4,000). This trend is consistent with a positive exact difference; **it is not an error bound or a proof**.

The stronger adaptive aggregate clipping bound \(\mathscr C\) is also below \(M\) on these sampled cuts. It has a positive switching remainder when the cuts differ; for instance, the (0.02,0.005) sample has a computed aggregate-versus-actual difference of about 0.000191462. Again none of this proves the global stronger bound.

## 3. What was and was not tested

The experiment tests four prescribed cap pairs (with three positive-cut families) close to the known reference. It does not sweep all widths, orientations, end-face configurations, irregular supports, arbitrary full-turn bodies, or near-maximal candidates outside the reference tail domain. Some small cuts are already covered by the exact RB/TC hand theorem, but the new finite sampled values do not extend that theorem.

The 4,000-point reference discrepancy demonstrates that finite-angle and spatial quadrature cannot certify the sharp \(M\) target merely by looking for positive numerical margins. A valid numerical *proof* would need rigorous interval bounds, full compatibility conditions, and a complete covering of the parameter/function space; no such computation has been carried out.

**Assessment.** The desired clipping inequality is logically *possible* and is consistent with all these examples, but there is no proof that it holds universally. As stated on the genuine full-turn nonempty-fiber domain it is equivalent to the unsolved full-turn Romik optimality claim. This note records evidence and the numerical uncertainty rather than announcing closure.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long optimization was used. The diagnostic scripts were externally limited to five seconds per execution.
