# Filling a top face does not automatically pay its full convex-area gain

**Purpose.** TC/STW pay a clipping correction by paired outer-flank losses. That argument cannot be replaced by an unqualified instruction to fill a missing top face and count the entire cap-area increase as an increase of the signed objective. The following exact example rejects that intermediate inequality. It is not a counterexample to the new restricted clipping bounds or to Romik optimality. Labels FF are local.

## 1. The proposed stronger comparison

For a downward cap U, let F(U) be the convex hull of U and a proposed height-one segment Z. An attractive sufficient estimate would be

$$\Psi(F(U))-\Psi(U)\ge\int_{\operatorname{proj}Z}(1-A_U(x))\,dx.\tag{FF.1}$$

If true, a sharp upper bound on Psi(F(U)) would pay the missing face material directly. But filling the face can create positive new full niche area, which FF.1 does not account for.

## 2. An exact counterexample to FF.1

Let

$$U=\{(x,y):-1/2\le x\le1/2,\quad0\le y\le1/2+\sqrt{1/4-x^2}\}.$$

This is the downward cap of the radius-one-half disk centered at (0,1/2). It contains the whole half-height rectangle and has height one and a point top face. Its upper support is

$$h_U(\theta)=1/2+(1/2)\sin\theta\quad(0\le\theta\le\pi).$$

At a turn angle t, its inner-corner height is `(1-sin(t)-cos(t))/2`, nonpositive. Thus the entire positive-height niche has area zero. The cap area is 1/2+pi/8, its width is one, and Psi(U)=pi/8.

Take Z=[-1/2,1/2] times {1}. Then F(U)=Q is the unit square [-1/2,1/2] times [0,1]. At angle pi/4 its two inner-wall lines form the positive niche triangle

$$0\le y<3/2-\sqrt2-|x|.$$

Its area is `(3/2-sqrt(2))^2>0`, since 9/4>2. Therefore |N(Q)|>0, while widths of Q and U agree. Consequently

$$
\Psi(Q)-\Psi(U)=|Q|-|U|-|N(Q)|
<|Q|-|U|=\int_{-1/2}^{1/2}(1-A_U(x))\,dx.
$$

This contradicts FF.1. No numerical niche integration or optimal-value theorem is used.

## 3. Precise boundary

This rejects the universal finite-operation comparison FF.1, even with a convex cap, a half-height rectangle and a prescribed height-one face. It does not show that the final inequality Delta(U)>=a particular face loss is universally false; that is a different claim. It also does not refute a more restricted filling rule with a separately proved niche-growth budget.

A bounded exploratory test considered a stronger special premise in which a cap lies below explicit circular baseline-intercept barriers and the proposed face length equals half the width. None of the 12 prescribed cuts or 32 prescribed point-set caps tested numerically violated that narrower proposed rule. That is not evidence of complete coverage or a proof of the rule; no such extension is asserted. The samples and their unbounded-error qualification are preserved in the review bundle.

The proved TC/STW comparison retains exactly what FF.1 omits: niche savings or growth are paired with changes on separate outer-flank strips, with signs preserved. Its fixed middle-support and barrier hypotheses remain necessary proof inputs until replaced by a new argument.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long numerical search was used.
