# A quantitative ordinary-area deficit for variable middles and rough tails

**Scope.** This combines MT's new tail transfer with the already proved fixed-width support-functional coercivity. The middle supporting data need not equal the reference. Their deficit remains available after arbitrary admitted tail changes, including point-face cuts and some outward changes, independently in the two caps. The result is not an unrestricted neighborhood theorem or a proof that an arbitrary competitor is admitted. Labels ME are local.

Baseline: `1a1805f904ad8c67dfec182a12970c6c021dedd0`, followed by [movable-middle-tail-transfer.md](movable-middle-tail-transfer.md). Mathematical dependencies are the explicit reference, SR1's unit-curvature signed-roof identity, and the fixed-width first variation in AF1/Note 14. The weighted-maximizer chain WV, its limiting source-flux argument VE, Gerver's theorem, and the large computer certificates are not needed for this result.

## 1. The background cap has an exact functional deficit

Use MT's constants and hypotheses for a background cap B. Write

$$f(t)=h_B(t),\qquad g(t)=h_B(t+L),\qquad L=\pi/2.$$

The four traces are f(0)=g(L)=m and f(L)=g(0)=1. Its quarter curvatures are between zero and one and its width is 2m>2. Therefore SR1 applies. The two axis quadrants supply height zero at every abscissa except a possible null exception, because the threshold abscissae m-1 and 1-m overlap in the favorable order. The signed roof is thus nonnegative and equals the full-niche roof. The ordinary cap support-area identity gives

$$\Psi(B)=F(f,g)-m,\tag{ME.1}$$

where F is exactly AF equation (A.1), not a new functional.

Let f_*,g_* denote the centered reference pair and set

$$v=f-f_*,\qquad w=g-g_*,\qquad z=v+iw.$$

Both v,w vanish at 0,L; in fact the MT collars make them vanish on neighborhoods of both endpoints. The explicit reference pair is stationary for F on these fixed traces, as proved by the matched reference Euler equations and interface fluxes in Note 14/AF. Consequently the expansion below has no residual linear term.

## 2. Keep the nonnegative nonsmooth remainders

Put p_*=f_*'-g_*+1 and q_*=g_*'+f_*-1, and

$$e_p=v'-w,\qquad e_q=w'+v.$$

For the two convex scalar functions define

$$\mathcal R_-(x,e)=\min(x+e,0)^2-\min(x,0)^2-2\min(x,0)e,$$

$$\mathcal R_+(x,e)=\max(x+e,0)^2-\max(x,0)^2-2\max(x,0)e.$$

Each remainder is nonnegative. The squares of the positive/negative parts are continuously differentiable even at zero, so the displayed derivatives are valid there. No fixed sign of the competing p or q is required.

Expansion of the quadratic C+I part of F, plus reference stationarity, yields the exact identity

$$
\boxed{M/2-\Psi(B)=B_0(v,w)+\frac12\int_0^L
[\mathcal R_-(p_*,e_p)+\mathcal R_+(q_*,e_q)]\,dt,}\tag{ME.2}
$$

where

$$B_0(v,w)=\frac12\int_0^L
\left(|z'|^2-2|z|^2-\operatorname{Im}(\overline z z')\right)dt.$$

The equality Psi(U_*)=M/2 is the explicit reference area calculation. ME.2 does not infer ordinary-area enclosure from a calibration outside SR1's domain: MT.2 supplied exactly the domain needed for ME.1.

## 3. An explicit coercive constant

Let y(t)=exp(-it/2)z(t). Completing the square gives

$$B_0=\frac12\int_0^L(|y'|^2-\tfrac94|y|^2)dt.$$

Both endpoints of y vanish. The Dirichlet inequality on length L=pi/2 is

$$\|y\|_2\le\tfrac12\|y'\|_2.$$

It follows that

$$B_0\ge\frac7{32}\|y'\|_2^2.$$

Also z'=exp(it/2)(y'+iy/2), so the triangle inequality gives

$$\|z'\|_2\le\|y'\|_2+\tfrac12\|y\|_2
\le\tfrac54\|y'\|_2.$$

Thus the entirely explicit consequence is

$$\boxed{M/2-\Psi(B)\ge\frac7{50}\int_0^L(v'^2+w'^2)dt.}\tag{ME.3}$$

This is the existing fixed-width coercivity written with an ordinary support-derivative norm. It does not assert a universal derivative-energy bound for arbitrary rough caps. In particular the altered top-face cuts from MT do not meet the background hypotheses and are not charged this energy.

## 4. The middle deficit survives all admitted tail alterations

Let U be an MT alteration of B, and let A_U be its upper roof. MT1 gives

$$\Psi(B)-\Psi(U)\ge L(U),\qquad
L(U)=\int_a^b(1-A_U(x))dx.$$

Therefore

$$\boxed{\Delta(U):=M/2-\Psi(U)
\ge L(U)+\frac7{50}\int_0^L(v'^2+w'^2)dt.}\tag{ME.4}$$

The two terms have different roles. L(U) pays the actual two-turn clipping, including cuts that move long face atoms. The derivative norm measures only the curvature-controlled background's middle change. It is not applied to the rough altered support, avoiding the earlier axis-cut energy obstruction.

Take independent backgrounds B_1,B_2 and independent alterations U_1,U_2. Define z_i from each background as in Section 1. The full envelope E has nonempty interval fibers through the midline by MT and satisfies G<=L(U_1)+L(U_2). Inserting ME.4 into its exact ordinary-area identity proves:

**Theorem ME1 (middle deficit with arbitrary admitted rough tails).**

$$\boxed{|E|\le M-\frac7{50}\sum_{i=1}^2\int_0^L|z_i'(t)|^2dt\le M.}\tag{ME.5}$$

If either background differs from the reference, its zero endpoint traces make the corresponding energy strictly positive. The theorem does not classify equality among altered tails, and unrestricted uniqueness is not pursued here.

This is not a small numerical remainder claim: the entire clipping term has an explicit paid budget, and no error of unspecified sign remains in ME.5 on the stated domain.

## 5. Nontrivial middle changes are genuinely admitted

The domain is not confined to backgrounds that are secretly the reference. Choose any smooth function phi supported in a compact subinterval of a reference quarter where the reference curvature is strictly between zero and one. For example an interval strictly inside its central phase qualifies. On the upper support set

$$h_B=h_*+\varepsilon\phi,$$

with phi extended by zero outside that interval. For either sign of sufficiently small epsilon, the curvature remains between zero and one, all MT collars are unchanged, and the axis atoms and upper support traces remain those of the reference. The planar support criterion therefore gives a genuine convex cap with the prescribed support, not an arbitrary list of sampled offsets.

Its extreme points have height one half and its top has height one. Concavity of its upper roof gives the entire half-height rectangle. Its positive top-face atom remains m.

Here is an explicit sufficient corner-height check, rather than an assumption that all perturbations preserve feasibility. The reference maximum corner height is

$$H_* =1/2+R-\sqrt2,$$

where R=2/[3 sin(beta/2+pi/8)]. It is attained at t=pi/4: on the initial phase p_*,q_*>=0 make the corner height nondecreasing; on the central phase its expression is

$$1/2+R\cos(3z/2)-\sqrt2\cos z,\qquad z=t-\pi/4.$$

For z>0 in that phase, sin(3z/2)>=sin z and (3/2)R>sqrt(2), so the derivative is negative. The final phase is the reflected initial phase. Since beta>pi/12, R<4/3; since sqrt(2)>7/5,

$$H_*<13/30.$$

If ||h_B-h_*||_infinity<=1/100, each corner height increases by at most 2/100. Thus

$$H_B<13/30+1/50=34/75<1/2.$$

This verifies MT.3. Arbitrarily many independent compactly supported smooth middle perturbations with sufficiently small C2 norm and amplitude therefore qualify, with either sign and no imposed reflection relation. Combining them with arbitrary admitted nonsmooth tail alterations yields genuinely varying middle geometry and rough changing faces at once.

## 6. Exact remaining admission boundary

The proof still requires three exact reference support collars for the backgrounds, their unit-curvature bound, and a representation of the altered cap that differs from its background only in the top-normal window under MT.5. Arbitrary small perturbations that alter a collar or introduce a middle curvature atom need not be covered. This is not a complete Hausdorff, H1, or C1 neighborhood theorem.

No argument here produces such backgrounds from every saturated opposite-face body, and no global localization is inferred from the optimality being sought. Uncovered partial turns also remain separate. The result addresses the previously fixed-middle limitation on an explicit enlarged domain, not unrestricted closure.

All inequalities are hand proofs using the displayed identities and stated earlier analytic results. Short arithmetic checks are supplementary. No long search, CI, Lean/Lake compilation, dependency installation, or manuscript build is used.
