# The forward central variational problem is strictly concave

**Analytic lemma about a specified functional, not a moving-sofa optimality theorem.** This supplements `FORWARD_CONTACT_MODEL.md` and does not assume reflection symmetry of competing paths. Its conclusion is limited to fixed endpoint values and a fixed central interval.

## Statement

Let 3pi/4<=beta<=7pi/9 (135..140 degrees), 13/20<=T<=3/4, d=cos beta, c=cos(beta/2), and B0=diag(1-d,1+d). On H^1 paths z:[-T,T]->R^2 with prescribed endpoints, define

    J(z)=integral_{-T}^T [1+(0,2c).z
          +z^T(B0-I/2)z-z'^T B0 z'-(1/2)cross(z,z')] dt.

There is a unique maximizer, and it is the solution of

    2B0 z''+J0 z'+(2B0-I)z+(0,2c)=0,

with those endpoints, where J0(x,y)=(-y,x). In particular the central path of the three-phase model is the unique maximizer for its own endpoint values. This does not optimize the phase-switch locations or boundary terms connecting the other phases.

## Uniform negative quadratic form

For a zero-endpoint variation v put X=||v_x'||_2, Y=||v_y'||_2, and r=2T/pi<1/2. Integration by parts gives

    integral cross(v,v')=2 integral v_x v_y'.

By Poincare and Cauchy-Schwarz, the mixed term in the quadratic part is at most rXY. On the stated beta interval,

    17/10 < 1-d < 9/5,
    1/5 < 1+d < 1/2.

For elementary checks: -cos beta>=sqrt(2)/2>7/10, while -cos beta<=cos(2pi/9)<cos(2/3)<=191/243<4/5. The latter uses pi>3 and the alternating cosine Taylor bound.

The vertical zeroth-order coefficient (1+d)-1/2 is negative and can be discarded in an upper bound. The horizontal coefficient is below 13/10. Consequently

    q(v)<=-[(17/10)-(13/10)r^2]X^2-(1/5)Y^2+rXY
         <=-(4/3)X^2-(1/5)Y^2+(1/2)XY.

The associated positive matrix is

    [[4/3,-1/4],[-1/4,1/5]],

whose determinant is 49/240>0. Thus q(v)<0 unless v=0. This is a continuous H^1 statement, not a Hessian test on a discretized basis or on symmetric variations only.

The negative form is coercive in the zero-endpoint H^1 norm. After subtracting any affine path with the prescribed endpoints, the usual coercive quadratic minimization (equivalently completing the square via the bounded positive bilinear form) gives a unique maximizer. Its weak Euler equation has constant coefficients, so its solution is smooth and satisfies the displayed differential equation. Alternatively, once a stationary solution is written explicitly, integration by parts shows that the difference in J is exactly q(v), proving its unique maximality directly.

## Relation to the model and its limits

The hyperbolic central solution in `FORWARD_CONTACT_MODEL.md` solves this equation. The first-phase functional similarly has negative zero-endpoint second variation on an interval of length alpha<pi. Neither fact proves that the complete piecewise boundary solves the whole forward moving-sofa problem: varying the switch locations changes admissibility and endpoint terms, and an arbitrary sofa need not realize the assumed contact pattern at all.

This lemma strengthens the variational interpretation of the candidate, but the certified crossing still remains a CONTACT-MODEL crossing rather than an established unrestricted phase transition.
