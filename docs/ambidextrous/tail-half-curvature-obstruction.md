# The lower tail-curvature threshold is a real geometric restriction

**Purpose.** CT transfers an ordinary-area bound through inward tail cuts when the background tail curvature is at least one half. This note gives an analytic negative control if that hypothesis is discarded. A small inward cut of a genuine background cap then increases both its signed objective and its symmetric two-turn surviving area. This is not a body above Romik's area and does not contradict CT, MT, or the weighted theorem. Labels HC are local.

No numerical optimization or sampled cap realization is used. The example uses a circular cap with exact constants, followed by a smooth compactly supported support perturbation.

## 1. A feasible background with curvature one quarter

Let B be the downward cap whose upper boundary is the top of the stadium obtained by adding the horizontal segment [-4/5,4/5] to the radius-1/4 disk centered at (0,3/4). Equivalently its upper support is

$$h_B(\theta)=1/4+(4/5)|\cos\theta|+(3/4)\sin\theta\quad(0\le\theta\le\pi).\tag{HC.1}$$

Its horizontal projection is [-21/20,21/20], its endpoint heights are 3/4, and its height is one. Its top face has length 8/5. Both open-quarter curvature densities are exactly 1/4, with no interior atoms. It contains its entire half-height rectangle.

On the first and second quarters,

$$p(t)=3/4-(8/5)\sin t,\qquad q(t)=(8/5)\cos t-3/4.$$

The inner corner height is

$$c_y(t)=(4/5)\sin(2t)+(3/4)(1-\sin t-\cos t).$$

Put z=sin t+cos t in [1,sqrt(2)]. Then

$$c_y=(4/5)z^2-(3/4)z-1/20,$$

which increases on that interval. Its maximum is

$$\boxed{31/20-3\sqrt2/4<1/2,}\tag{HC.2}$$

because sqrt(2)>7/5. The unit-curvature intercept argument confines its positive niche to the top-face interval [-4/5,4/5]. Hence its niche lies in B and below height one half.

The symmetric two-turn body E_B=(B minus N(B)) intersect rho(B minus N(B)) is compact, connected through the midline and feasible for both full turns. Its clipping correction is zero because positive niche points lie below a cap roof equal to one. Thus |E_B|=2 Psi(B).

## 2. An inward smooth change of an actual support function

Choose a compact interval J strictly inside the late phase {t:p(t)<0,q(t)<0}; it exists because p(L)=-17/20 and q(L)=-3/4. Take a smooth nonnegative nonzero phi supported in the interior of J. On the first quarter replace f by

$$f_\varepsilon=f-\varepsilon\phi,$$

leaving the rest of the upper support unchanged.

For sufficiently small epsilon>0, the curvature

$$1/4-\varepsilon(\phi+\phi'')$$

stays strictly between zero and one. The support and its derivative agree with the old support near every join and axis. The planar support criterion therefore supplies a genuine convex cap U_epsilon, with the same width, height, top face and endpoint heights. Since its support is everywhere no greater than h_B, U_epsilon subset B. Its concave upper roof has both endpoint heights 3/4, so it still contains the half-height rectangle.

Shrinking epsilon further keeps p_epsilon<0 and q_epsilon<0 on the support of phi. Elsewhere the old sign pattern is unchanged. The alteration is localized near the top normal but away from the top normal itself; the face-loss integral below the old top face is zero.

## 3. The objective increases exactly

Both caps satisfy the unit-curvature signed-roof formula, and their width 21/10 exceeds two, so Psi=F-W/2 with no negative-roof correction. On the phase p<0,q<0, the dependence of F on the first support has first variation

$$DF[\delta f]=\int_J(2f''+2f-1)\delta f\,dt.$$

This follows directly by expanding AF equation (A.1); all boundary terms vanish because the perturbation is compactly supported. Its homogeneous quadratic term for a change delta f is integral_J(delta f^2-delta f'^2). Since f''+f=1/4 and delta f=-epsilon phi, the exact difference is

$$\boxed{\Psi(U_\varepsilon)-\Psi(B)
=\frac\varepsilon2\int_J\phi\,dt
-\varepsilon^2\int_J(\phi'^2-\phi^2)dt.}\tag{HC.3}$$

The first integral is positive. The second is finite and positive by the Dirichlet inequality, since J has length less than pi. Choosing epsilon sufficiently small makes HC.3 strictly positive, while retaining all previously specified geometric and sign bounds.

Thus an inequality claiming Psi(B)-Psi(U)>=0 for every inward tail alteration of every unit-curvature background is false. In particular the face-loss budget CT.9 cannot simply delete CT.2. The background here has rho=1/4, so the niche-side Jacobian 1-rho=3/4 exceeds the outer-cap Jacobian rho=1/4. The cut saves more niche area than the lost exterior cap area, exactly as CT.7 predicts.

## 4. This is not merely an auxiliary-functional artifact

Because U_epsilon subset B, its full niche stays below one half. Its own unit-curvature intercepts confine that niche to the unchanged top face. Its symmetric two-turn envelope E_epsilon is therefore also compact, connected and feasible, with zero clipping and |E_epsilon|=2 Psi(U_epsilon). Consequently

$$\boxed{|E_\varepsilon|>|E_B|.}\tag{HC.4}$$

No claim that either area exceeds M is made. The example is an ordinary-area improvement of a nonoptimal circular background, and a negative control on a proposed universal monotonicity premise.

The successful MT theorem retains exact half-curvature collars for signed alterations; the broader CT theorem permits variable inward-tail backgrounds only with the lower density bound one half. A global completion would need a new argument supplying such a background or paying for its failure, rather than deleting the bound.

This is a hand proof. No long script, CI, Lean/Lake compilation, dependency installation or manuscript build is used. The upper support, feasibility and exact finite variation have all been specified; no random support sample is called an actual sofa.
