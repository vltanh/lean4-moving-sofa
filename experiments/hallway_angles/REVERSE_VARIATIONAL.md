# A quadratic variational route for reverse turns

Research checkpoint. This file derives a conditional area majorant, not yet an upper bound for every sofa in the full reverse class. It does not use the uniqueness theorem. The exposed-wall search is used only as a numerical comparison.

## Coordinates

Let `epsilon = pi - beta`, with `0 < epsilon < pi/2`, and normalize the entry strip to `-1/2 <= y <= 1/2`. During a reverse turn let `phi` run from 0 to epsilon. The outer wall normals are

    n1(phi) = (sin(phi), cos(phi)),
    n2(phi) = (sin(epsilon-phi), -cos(epsilon-phi)).

Let h_plus(phi) and h_minus(phi) be the support values of the two right boundary arcs, with h_plus(0)=h_minus(0)=1/2. The cap's boundary between the two terminal support lines is their intersection vertex. The functions must actually represent compatible convex arcs; arbitrary functions are used below only to relax a quadratic maximization problem.

The canonical inner corner c=(x,y) satisfies

    n1.c = h_plus(phi)-1,
    n2.c = h_minus(epsilon-phi)-1.

Writing a=h_plus(phi)-1, b=h_minus(epsilon-phi)-1 gives

    x = [cos(epsilon-phi) a + cos(phi) b]/sin(epsilon),
    y = [sin(epsilon-phi) a - sin(phi) b]/sin(epsilon).

Thus y(0)=-1/2 and y(epsilon)=1/2.

## Cap area

Let H_plus=h_plus(epsilon), H_minus=h_minus(epsilon). The integral of the cap's right boundary abscissa over the entry strip is

    Cap(h_plus,h_minus)
      = 1/2 integral_0^epsilon
          (h_plus^2-h_plus'^2+h_minus^2-h_minus'^2) dphi
        + [H_plus H_minus + (cos(2epsilon)/2)(H_plus^2+H_minus^2)]/sin(2epsilon).

This is a signed area relative to the line x=0; horizontal translations add the translation distance. The formula follows by integrating x dy along the two support arcs and the two terminal tangent segments. The endpoint terms at phi=0 cancel with the horizontal strip boundaries.

## Conditional area majorant

Suppose the canonical corner height y(phi) is strictly increasing. At the unique phi where y(phi)=Y, the forbidden wedge contains every point (X,Y) with X<x(phi), since both normals have positive x components. A feasible sofa therefore has its horizontal section between x(phi) and the cap's right boundary. Consequently

    area(S) <= Q(h_plus,h_minus)
      := Cap(h_plus,h_minus) - integral_0^epsilon x(phi) y'(phi) dphi.

For equality, the region between the cap and the corner graph must be feasible for *all* poses, not only the pose at matching height. This is a separate condition to check on a proposed extremizer.

IMPORTANT: the strict height-monotonicity hypothesis has not been established for every reverse-class optimizer. Canonical corner heights can leave the entry strip for arbitrary support data. A signed corner integral is not automatically the area of a swept forbidden region. These points must be resolved or retained as explicit hypotheses in any theorem.

## Constant-coefficient form

Set L=epsilon/2, t=phi-L, s=sin(L), c=cos(L), and z(t)=R_t c(phi). Put

    A = diag(2s^2, 2c^2),   b0=(2s,0).

Then the quadratic integral in Q, apart from its explicitly computable endpoint terms, is

    integral_{-L}^L [1 + b0.z
      + 1/2 z^T(A+I)z - 1/2 z'^T A z' - 1/2 cross(z,z')] dt.

The Euler equation is

    A z'' + J z' + (A+I) z + b0 = 0,

where J(x,y)=(-y,x). Its characteristic polynomial factors as

    (lambda^2+1) [sin(epsilon)^2 lambda^2 + sin(epsilon)^2+3].

Thus the two oscillatory frequencies are 1 and

    k = sqrt(1 + 3/sin(epsilon)^2).

This provides an analytic route to a candidate, rather than a new local search over shapes.

## Numerical diagnostics (not proofs)

An unconstrained quadratic maximization in paired integrated-Legendre bases gives the following stationary values. No symmetry is imposed in this calculation; the maximizer is symmetric to floating-point accuracy.

| Bend beta | epsilon | Stationary Q |
| --- | --- | ---: |
| 179 degrees | 1 degree | 77.7253117651 |
| 170 degrees | 10 degrees | 7.78892908191 |
| 150 degrees | 30 degrees | 2.64102508165 |
| 137 degrees | 43 degrees | 1.88050823837 |
| 135 degrees | 45 degrees | 1.80376416705 |
| 120 degrees | 60 degrees | 1.39997951197 |
| 100 degrees | 80 degrees | 1.11825614698 |

The observed corner heights are increasing and outer arc curvatures positive in these discretizations. All finite-dimensional Hessians tested are negative definite after removing horizontal translation. None of these diagnostics proves the continuous concavity, global motion-class optimality, or feasibility of the limiting curve.

## Endpoint-limit experiment

After scaling X=epsilon x and sending epsilon to zero, the formal reverse hallway becomes

    0 <= max(t(X-C)+Y-D, (1-t)(X-C)-Y+D) <= 1.

The corresponding regular-corner quadratic functional has a numerically stable stationary area 1.3565337324523. A direct sampled-envelope search gives decreasing values 1.3709472, 1.3636678, 1.3600865 at 49, 97, 193 orientations, consistent with a sampling error rather than a contradictory continuous value. Neither convergence nor sharp asymptotics for the original unrestricted problem is claimed at this checkpoint.
