# Opposite positive faces carry the entire full-turn supremum

**Main point.** Point-face bodies do not require a separate *upper-value* theorem if the positive opposite-face class can be bounded. Every compact connected full-turn body of area greater than one admits area-convergent approximants with unit incoming span and two positive, strictly separated horizontal faces. After the existing width exclusion, those faces lie in opposite unit end intervals.

The construction uses a small shrink, disk rounding, two strip shavings, another shrink tending to one, and the already proved safe-strip transport SI2. It does not increase area in the limit or assume symmetry. This is a reduction of the unresolved full-turn problem, not its solution. Indeed it shows that the remaining opposite-face class is as hard as the whole full-turn supremum, rather than a remote low-area exception. Labels PD are local.

Baseline: `c68813d3b5148b21fdd44553c1ced55060bf4844`. The new inputs are RR1--RR2 in [rounded-strip-regularization.md](rounded-strip-regularization.md) and SI2 in [strip-interval-completion.md](strip-interval-completion.md). The proof is pen and paper.

## 1. Width functions have a uniform semiconvex bound

For a compact convex hull K of diameter at most D, put f(theta)=w_K(theta). Since

$$f(\theta)=\max_{x,y\in K}(x-y)\cdot n_\theta,$$

and each displayed sinusoid has second derivative bounded below by -D, the function

$$f(\theta)+D\theta^2/2$$

is convex on the real angle line. In particular f has finite one-sided derivatives, and

$$f'_-(t)\ge\frac{f(t)-f(t-h)}h-\frac{Dh}{2}\qquad(h>0).\tag{PD.1}$$

All widths of convex subsets of K have the same bound D. This observation gives the following stability fact without assuming C2 support or bounded curvature density.

**Lemma PD1.** Suppose f_j are such width functions, converge uniformly to f, and f'(t)>=c>0 almost everywhere on [eta-sigma,eta]. Then for large j their left derivatives are positive throughout [eta-sigma/2,eta], and their widths are strictly increasing there.

**Proof.** Choose a fixed h<sigma/4 with Dh/2<c/4. If e_j=||f_j-f||_infinity, (PD.1) gives

$$f'_{j,-}(t)\ge c-2e_j/h-Dh/2>c/2$$

for the indicated t once 2e_j/h<c/4. The same inequality holds at differentiability points, so integration of the Lipschitz width function gives strict increase. QED.

The strict lower derivative at eta is included. This will order the two final faces, not merely prove the endpoint strip is feasible.

## 2. Find a small record excursion above the safe-strip level

Let S have both full conventional turns with incoming normal theta0 and f(theta0)<=1. Assume |S|>1. There must be a direction with f>1: otherwise two perpendicular widths at most one enclose S in a rectangle of area at most one.

Lift angles to the real line. The connected component of {f<=1} containing theta0 is a bounded closed interval [a,b], possibly a singleton. It is bounded because f is pi-periodic and is greater than one somewhere. Its right endpoint satisfies f(b)=1, and there are d>b arbitrarily close to b with f(d)>1.

For such a d set

$$m=\frac{f(d)-1}{2(d-b)}>0.$$

Choose eta maximizing f(t)-m(t-b) on [b,d]. It is not b. For b<=t<=eta,

$$\boxed{f(t)\le f(\eta)-m(\eta-t),\qquad f(\eta)>1.}\tag{PD.2}$$

The left derivative at eta is at least m, by taking left difference quotients. A semiconvex function's derivatives have the corresponding one-sided limits, so on some interval [eta-sigma,eta] lying in (b,eta],

$$f'(t)\ge m/2>0\quad\text{a.e.}\tag{PD.3}$$

For completeness, add D t^2/2. The derivative of this convex function approaches its left derivative at eta from the left. Subtracting D t then gives (PD.3) on a sufficiently short interval. No differentiability at eta itself is required.

Take d_j decreasing to b through such points. The resulting eta_j tend to b and f(eta_j) tend to one from above. Their positive slopes and interval lengths may tend to zero; the construction only needs to choose each subsequent shaving sufficiently small.

## 3. Round and shave at a record normal

Fix one eta and its interval from Section 2. Apply RR to obtain

$$R_\lambda=\lambda S+rB,\qquad r=(1-\lambda)/2,$$

with convex hull K_lambda and width

$$f_\lambda=\lambda f+1-\lambda.$$

It has both original full turns. Its safe-strip set is exactly that of S, and its derivative is positive on the interval (PD.3).

Shave epsilon from each of its two supports normal to n_eta, with 0<epsilon<r, as in RR2. Denote the actual rounded-and-shaved body by B_epsilon, and the larger convex clipped hull by K_epsilon. RR2 proves B_epsilon is compact and connected, contains lambda S, and has two positive face segments at the cutting lines. Both B_epsilon and K_epsilon have the same final width

$$d_\epsilon=f_\lambda(\eta)-2\epsilon.$$

RR.4 shows w_(K_epsilon) -> f_lambda uniformly as epsilon decreases to zero. Lemma PD1 therefore makes w_(K_epsilon) strictly increasing on [eta-sigma/2,eta] for sufficiently small epsilon.

On the earlier part [b,eta-sigma/2], (PD.2) gives

$$f_\lambda(t)\le f_\lambda(\eta)-\lambda m\sigma/2.$$

On [theta0,b] it is at most one. Choose epsilon still smaller so that

$$2\epsilon<\min\{f_\lambda(\eta)-1,\ \lambda m\sigma/2\}.\tag{PD.4}$$

These facts and convex inclusion imply

$$\boxed{w_{B_\epsilon}(t)\le d_\epsilon\quad(\theta_0\le t\le\eta),
\qquad d_\epsilon>1.}\tag{PD.5}$$

The last interval is controlled by the strict increase of the clipped convex width; the earlier intervals use the displayed gap estimates. We never assume the actual shaved hull equals K_epsilon.

## 4. Restore unit span and complete the motions in the new orientation

Scale B_epsilon by k=1/d_epsilon<1. It keeps both original full motions by uniform shrinking. Equation (PD.5) gives a whole interval of safe straight-strip normals from theta0 to eta for this scaled body. SI2 transports its full turns along that interval, using finitely many angle steps if necessary. Thus the **same scaled body** has both full turns with incoming normal n_eta.

Rotate and translate it into the standard incoming coordinates 0<=y<=1. Call it S_(lambda,eta,epsilon). Its span is exactly one, and both horizontal faces have positive length by RR2.

They are strictly separated, not aligned. To see this, write H_epsilon=conv(B_epsilon). Its width is at most that of K_epsilon and they agree at eta. Hence

$$w'_{H_\epsilon,-}(\eta)
\ge w'_{K_\epsilon,-}(\eta)>0.\tag{PD.6}$$

The inequality follows directly from left difference quotients at their common endpoint value. In coordinates with incoming normal eta, let the top face be [a_+,b_+] and the bottom face [a_-,b_-]. The standard support derivative identity is

$$w'_-(\eta)=a_- - b_+.$$

After the positive scale factor k it still has positive sign. Therefore

$$\boxed{b_+<a_-.}\tag{PD.7}$$

The top face lies strictly to the left of the bottom face. Every face endpoint is an actual body point; RR2 supplied entire retained face segments, not just points in an abstract hull.

## 5. The area converges to the original area

Choose eta_j as in Section 2, lambda_j -> 1, and for each pair choose epsilon_j satisfying all the sufficiently-small requirements above, in particular epsilon_j<r_j. Then

$$d_j=\lambda_j f(\eta_j)+1-\lambda_j-2\epsilon_j\longrightarrow1,
\qquad k_j=1/d_j\longrightarrow1.$$

RR.6 gives

$$k_j^2\lambda_j^2|S|
\le |S_j|\le k_j^2|R_{\lambda_j}|,$$

and RR.5 makes both bounds tend to |S|. Thus

$$\boxed{|S_j|\longrightarrow|S|.}\tag{PD.8}$$

After undoing their final rotations and translations, these bodies also converge to S in Hausdorff distance: they contain k_j lambda_j S and are contained in k_j(lambda_j S+r_j B).

**Optional from-below choice.** The areas can be required to be strictly less than |S| at every step. For each fixed eta_j, f(eta_j)>1 and, as lambda tends to one,

$$|R_\lambda|\longrightarrow |S|<|S|f(\eta_j)^2.$$

Choose lambda_j sufficiently close to one that

$$|R_{\lambda_j}|<|S|f_{\lambda_j}(\eta_j)^2.$$

Then choose epsilon_j sufficiently small to retain

$$|R_{\lambda_j}|<|S|d_j^2.$$

The upper area bound above gives |S_j|<|S|. This is an existence argument based on continuity, not a numerical comparison with the conjectural optimum.

**Theorem PD2.** Every compact connected body of area greater than one with both full conventional turns admits full-turn, unit-span approximants having two positive strictly separated horizontal faces, with areas tending to its area from below. The construction uses only feasible shrinking, RR rounding/shaving, and an explicitly justified safe-strip transport.

## 6. Consequences for the remaining proof obligation

For |S|>41/25, sufficiently late approximants also have area greater than 41/25. The analytic AW-W theorem then forces their incoming widths to exceed two. The existing face classification FD1 places their positive separated faces in opposite unit end strips.

Consequently:

**Corollary PD3 (value reduction).** A full-turn counterexample to |S|<=M exists if and only if a full-turn counterexample with two positive horizontal faces in opposite unit end strips exists.

The reverse direction is immediate. For the forward direction apply PD2 to a body with |S|>M and take a sufficiently late approximant. Its area still exceeds M. This does not assume attainment or preserve a particular point-face hull exactly.

Equivalently, since the reference value exceeds 41/25, the supremum over all full-turn bodies equals the supremum over this positive opposite-end-face class. The separate point-face class need not be excluded by its own area inequality: a bound on all positive opposite-end faces automatically covers its area limits.

Applying PD2 to the reference itself gives such positive opposite-end-face bodies with areas strictly below M and tending to M. Thus there is **no uniform epsilon>0** for which that entire class has area at most M-epsilon. This remains true after excluding literal point faces. The theorem is not a construction above M and does not assume reference optimality.

This also corrects an overly favorable interpretation of the earlier case classification: the remaining opposite-face class is not known to be a quantitatively separated exceptional set. It carries the entire unresolved full-turn supremum.

## 7. Why this does not contradict FD3 or complete partial turns

FD3 forbids approximation of aligned point faces by aligned positive faces at fixed unit span and width greater than two. PD2 instead constructs **separated** positive faces and is allowed to change the incoming orientation. Its shrinking factors tend to one, but exact preservation of the old hull or old faces is not claimed.

For an arbitrary partial-turn body, RR preserves its already available intervals but does not create both full turns. RR.2 also preserves the safe-strip set of the unshaved body. The missing strip bridge with a genuine width bump is not supplied by PD2. SI3 still covers only the partial-turn cases whose required strip directions have a safe bridge.

Thus the current full-turn upper-value target is one class: two positive opposite-end faces. The uncovered partial-turn geometry remains separate. Neither unrestricted optimality nor its equality case is proved here.

No numerical search, CI, Lean/Lake compilation, dependency installation or manuscript build is used. These are self-reviewed written arguments; the old motion/width/face results remain explicit dependencies.
