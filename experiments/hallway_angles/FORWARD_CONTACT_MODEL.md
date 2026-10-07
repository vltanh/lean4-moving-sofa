# An analytic forward contact model near the numerical crossing

**Sixth-round research result, with an essential scope restriction.** This file derives a three-phase stationary contact model that closely reproduces the saved numerical forward branch near 136.7 degrees. It does NOT prove that every forward-class sofa has this contact pattern, that the model is globally optimal, or that its signed boundary is feasible without further geometric work. The accompanying scalar certificate proves a crossing of specified analytic expressions, not the unrestricted phase transition.

## 1. Contact pattern and variational equation

Write beta for the hallway bend. In body-fixed coordinates the outer-wall normals are

    n1(theta)=(-sin theta,cos theta),
    n2(theta)=(sin(beta-theta),cos(beta-theta)).

Let C(theta) be the inner corner and f_j=n_j.C its inner-wall support offsets. The model is symmetric under theta -> beta-theta and x -> -x. It assumes three phases:

- 0<=theta<=alpha: only the first inner/outer wall pair contributes moving boundary arcs; the second outer wall supports a fixed bottom vertex.
- alpha<=theta<=beta-alpha: both wall pairs and the corner trajectory contribute boundary arcs.
- beta-alpha<=theta<=beta: reflection of the first phase.

For a wall pair, the inner envelope is f n+f' Jn and the outer envelope adds n. Under the assumed boundary orientation, their signed-area contribution is the integral of f^2-f'^2+f+1/2, with endpoint term (f+1/2)f'. The central corner arc is traversed in the opposite boundary direction and contributes minus one half of integral cross(C,C'). These are signed boundary identities; they must not be confused with the area of the actual feasible intersection before the boundary pattern is justified.

In the first phase the Euler equation is f1''+f1=-1/2. The entry-strip conditions give

    f1(theta)=p sin theta+(cos theta-1)/2.

Thus the assumed paired envelope arcs have radius 1/2. Put L=beta/2, t=theta-L and z=R_{-t}C. With s=sin L, c=cos L, d=cos beta, and B0=diag(1-d,1+d), the central Euler equation is

    2B0 z''+Jz'+(2B0-I)z+(0,2c)=0.                  (1)

The characteristic determinant factors as

    (lambda^2+1)[4 sin(beta)^2 lambda^2+4 sin(beta)^2-3].

The relevant central mode is hyperbolic for beta>120 degrees. The implementation is deliberately restricted to 130..145 degrees; the certified scalar crossing below uses 135..140 degrees.

## 2. Eliminate the matching constants

Define

    mu=sqrt(3/[4 sin(beta)^2]-1),
    eta=sqrt((-1-2d)/(1-2d)),
    r=(1-2d)/[2(1+d)mu],
    z0=-2c/(1+2d),
    T=L-alpha.

The symmetric general central solution has the form

    z_x=A sin t+B sinh(mu t),
    z_y=A cos t+rB cosh(mu t)+z0.

At theta=alpha impose: n2.C'=0 (the inner envelope joins the corner), C_y=-cos(beta-alpha) (the second outer contact lies on the bottom strip boundary), and matching of f1,f1' to the first-phase circle. Eliminating the circle center and the central amplitude gives

    A=1/3,
    B=-2c/[3mu(cosh(mu T)+eta sinh(mu T))],             (2)

and the single scalar equation

    F(beta,T)=eta[3s sin T-c cos T-1]
      +tanh(mu T)[s sin T-3c cos T-eta^2]=0.           (3)

These equations encode the stated contacts; they are not sufficient conditions for unrestricted optimality. The physical central path is

    C_x=-z0 sin t+B[sinh(mu t)cos t-r cosh(mu t)sin t],
    C_y=A+z0 cos t+B[sinh(mu t)sin t+r cosh(mu t)cos t].

The early corner can be selected by solving the two linear equations n1.C=f1 and n2.C=x_R sin(beta-theta)-1, where x_R=C_x(alpha)+sin(beta-alpha); the late corner is its reflection. This specifies an analytic candidate motion, not an all-pose collision certificate.

## 3. Closed signed-area formula

All of the following quantities are evaluated at positive t=T:

    zx=A sin T+B sinh(mu T),
    zy=A cos T+rB cosh(mu T)+z0,
    dx=A cos T+mu B cosh(mu T),
    dy=-A sin T+rmu B sinh(mu T),
    alpha=beta/2-T,
    p=[s*zx+c*zy+(1-cos alpha)/2]/sin alpha,
    g=p sin alpha+(cos alpha)/2,
    gp=p cos alpha-(sin alpha)/2,
    f=-s*zx+c*zy, fp=-s*dx+c*dy.

Then the assumed closed oriented boundary has signed area

    W(beta,T)=alpha/2-2g*gp+p
       +2T+2c[A sin T+rB sinh(mu T)/mu+z0*T]
       -2[(1-d)zx*dx+(1+d)zy*dy]+2(f+1/2)fp.          (4)

To derive (4), integrate the first-phase pair using g''+g=0. For the central phase, multiply (1) by z and integrate by parts. The resulting bulk integral is 2T+c integral z_y, and the endpoint contribution is minus 2 z(T)^T B0 z'(T). Add the wall-pair boundary term at beta-alpha. This avoids numerical quadrature entirely.

Independent signed-area quadrature and sampled boundary polygons are useful checks of (4), but do not establish that the oriented boundary is the true boundary of a continuously feasible sofa.

## 4. An exact candidate-crossing equation

Let V(pi-beta) be the explicit reverse-class value. The contact-model crossing is defined by the two explicit transcendental equations

    F(beta,T)=0,
    W(beta,T)=V(pi-beta).                              (5)

`contact_crossing_certificate.py` proves that (5) has exactly one solution in

    135 degrees<=beta<=140 degrees, 13/20<=T<=3/4,

and encloses its bend by

    136.672184698 degrees < beta_model
                          < 136.672184699 degrees.    (6)

The corresponding numerical central half-length is about 0.69473347563146 radians, the first switch alpha is about 28.53079631 degrees, and the common signed area is about 1.867419190797876. These illustrative decimals other than (6) are not separate certified enclosures.

The scalar proof first establishes F_T>0 and opposite signs at T=13/20,3/4 over the whole beta interval. This defines a unique analytic T(beta). It then uses exact interval automatic differentiation and a verified interval-Newton tube to prove

    d/d beta [W(beta,T(beta))-V(pi-beta)]<0

throughout 135..140 degrees, and verifies opposite signs at the rational-degree endpoints in (6). The interval operations include exact angle reduction before trigonometric evaluation. No floating-point optimizer is used by that certificate.

## 5. What would identify beta_model with the actual phase transition?

Three further steps are required, and none is supplied merely by (3)-(6):

1. Prove the prescribed boundary has the correct order and is contained in every hallway along the candidate motion throughout the relevant beta interval.
2. Prove an upper bound for every aligned forward competitor matching W; a stationary contact solution and negative Hessian in one phase do not prove this.
3. Relate the aligned-class comparison to the unrestricted problem and rule out other motion/contact types. The explicit near-reversal global theorem does not reach this interval.

Consequently beta_model must NOT be denoted the established unrestricted beta_c. The result is an exact, uniquely specified contact-model crossing and a concrete target for a phase-transition proof. It is stronger than fitting two numerical curves, but weaker than solving the middle-angle moving-sofa problem.

The numerical competing-branch phenomenon was already reported by Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1 (corridor-ray angle about 43.327 degrees, supplementary to the bend here). No novelty claim is made for that phenomenon. The contact-model derivation and its relationship to prior analytic work still require mathematical and priority review.
