# Cap-area identity, including nonsmooth convex bodies

This supplies the geometric identity used in the reverse-class majorant. It concerns the convex hull of a competitor, not a smoothness assumption on the moving sofa itself.

Fix 0<e<pi/2 and a compact convex body K with nonempty interior and actual vertical projection [-w/2,w/2]. Let h_plus and h_minus be its support functions in directions (sin phi,cos phi) and (sin phi,-cos phi), 0<=phi<=e. Put H_plus=h_plus(e), H_minus=h_minus(e).

Intersect the strip with all these outer support halfplanes. This cap is unbounded to the left, but its right boundary x=F(y) is bounded on the strip. Define its signed area relative to x=0 by Cap=integral_{-w/2}^{w/2} F(y) dy.

## Identity

    Cap = (1/2) integral_0^e
                  (h_plus^2-h_plus'^2+h_minus^2-h_minus'^2) dphi
           +(cot e/4)(H_plus+H_minus)^2
           -(tan e/4)(H_plus-H_minus)^2.                (1)

Equivalently the endpoint term is

    [H_plus H_minus+(cos(2e)/2)(H_plus^2+H_minus^2)]/sin(2e).

Support functions are Lipschitz and their derivatives in (1) are the almost-everywhere derivatives. No positivity of this signed area is asserted; a horizontal translation changes it by w times that translation.

## Smooth strictly convex case

The upper support arc is

    P_plus=(h_plus sin phi+h_plus' cos phi,
            h_plus cos phi-h_plus' sin phi),

and the lower arc is

    P_minus=(h_minus sin phi+h_minus' cos phi,
             -h_minus cos phi+h_minus' sin phi).

Let U=P_plus(e), D=P_minus(e). The two terminal support lines meet at

    V=((H_plus+H_minus)/(2 sin e),
       (H_plus-H_minus)/(2 cos e)).

The right boundary consists of the two arcs and the segments U--V and V--D. To see the ordering, the lower support inequality holds at U, so moving along the upper terminal tangent toward V has a nonnegative parameter. Thus V lies to the right of and below U. Similarly it lies to the right of and above D. Every support arc point belongs to K and hence satisfies all the other support inequalities, so none is cut off.

With rho=h+h'', differentiation gives P_plus'=rho(cos phi,-sin phi), and similarly P_minus'=rho(cos phi,sin phi). Integrating x dy on the two arcs and integrating h h'' by parts gives the integral term in (1) plus

    [H_plus h_plus'(e)+H_minus h_minus'(e)-U_x U_y+D_x D_y]/2.

There is no contribution of this type at phi=0: h h'-xy=0 at the upper starting point and h h'+xy=0 at the lower one. In particular the identity does not require w=1.

The two straight segments contribute

    (D_x+V_x)(V_y-D_y)/2+(V_x+U_x)(U_y-V_y)/2.

Adding these expressions cancels the products U_x U_y and D_x D_y. Because V lies on both terminal support lines, their remaining cross products cancel the terms involving h_plus'(e),h_minus'(e). The result is

    [(H_plus+H_minus)^2 cot e-(H_plus-H_minus)^2 tan e]/4,

which proves (1).

## Passage to an arbitrary convex body

Let h be the full-circle support function of K. Convolve it in angle with a nonnegative smooth approximate identity and add a positive constant tending to zero. Angular convolution is a Minkowski average of rotations of K; adding a constant is Minkowski addition of a small disk. These are smooth strictly convex support functions h_n converging to h uniformly and strongly in H^1. Translate their bodies vertically to center their actual vertical projections. The centering translations tend to zero and preserve both convergences. Write w_n for their heights; w_n tends to w.

All bodies, their support contact points, and their terminal vertices remain in a common bounded set, since e is fixed and their support functions have uniformly bounded Lipschitz norms. Choose a fixed vertical line x=-R to the left of all of them and truncate each cap there. The resulting convex sets are uniformly bounded. Their defining right-hand sides converge uniformly, and they share an interior point with uniformly positive slack for all sufficiently large n, because K has nonempty interior. A homothety about this point, with factor tending to one, sandwiches each truncated cap between an inner and outer homothetic copy of the limiting cap. Their areas therefore converge.

Subtracting R*w_n from the truncated cap areas proves convergence of the signed quantities Cap_n to Cap. Uniform convergence handles the endpoint terms in (1), and strong H^1 convergence handles its integrals. Passing to the limit proves (1) without differentiability or strict convexity assumptions on K.

This approximation is used solely for an area identity. It is not asserted to preserve a feasible sofa motion. Canonical feasibility and the excursion inequalities are applied directly to the original Lipschitz support functions, almost everywhere.
