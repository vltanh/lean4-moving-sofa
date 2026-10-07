# Exact implicit crossing, not an established global transition

This note responds to the request for an exact value rather than a decimal interval. The current work does NOT establish an exact value for the unrestricted phase-transition angle beta_c, nor prove that there is exactly one such global transition. A unique-root characterization of a contact model is an exact mathematical definition, but it does not settle those geometric questions. No elementary closed form is obtained here, and no impossibility of such a form is claimed.

The result below is an algebraic simplification of the contact-model system in `FORWARD_CONTACT_MODEL.md`. It inherits that model's limitations: geometric feasibility of the complete forward boundary, a matching upper bound for every forward competitor, and unrestricted comparison near the crossing are not supplied by this note.

## 1. A compact exact system

All angles are in radians. Let alpha be the first switching angle, T=beta/2-alpha, and put

    d=cos beta,
    mu=sqrt(3/[4 sin(beta)^2]-1),
    eta=sqrt((-1-2d)/(1-2d)).

Define the contact residual

    G(beta,alpha) = [cos alpha+2cos(beta-alpha)+eta^2]
                     tanh(mu(beta/2-alpha))
                   -eta[cos alpha-2cos(beta-alpha)-1].             (1)

On G=0, the long signed-area expression in the preceding model reduces to

    W_red(beta,alpha)
      = {d beta+(1-2d)alpha/2-sin beta
          +[(1-4d)cos alpha-(1+2d^2)]/[3 sin alpha]}/(1+2d).      (2)

No hyperbolic functions remain in the reduced area itself; they remain in the matching equation. This simplification holds ON THE MATCHING LOCUS G=0. It is not an identity between the two area expressions for arbitrary off-branch parameters.

For completeness define the reverse expression directly as a function of beta:

    eta_R=sqrt((2+d)/(2-d)),
    K_R=(pi-beta)sqrt(1+3/sin(beta)^2)/2,
    R_R=eta_R sin K_R/(cos K_R+eta_R sin K_R),
    A_R(beta)=(pi-beta)/(2+d)+(1-2d)/(4sin beta)
                 +3d^2 R_R/[2sin beta(2+d)^2].                   (3)

Thus an exact definition of the MODEL crossing is the beta-coordinate of the unique solution of

    G(beta,alpha)=0,
    W_red(beta,alpha)=A_R(beta),                                (4)

on the branch selected by

    3pi/4 <= beta <= 7pi/9,
    13/20 <= beta/2-alpha <= 3/4.

These are root-selection ranges, not decimal error bars. The earlier certificate establishes uniqueness for the equivalent (beta,T) system on precisely this domain. The present note does not rerun that certificate or assert a new geometric theorem. All displayed denominators are nonzero on that domain: sin alpha>0, 1+2d<0, and 1-4cos(beta/2)^2>0.

## 2. Derivation of the reduced area

Use the previous notation s=sin(beta/2), c=cos(beta/2), z_x,z_y,z_x',z_y', p, A=1/3, B, r, z0. Put h=tanh(mu T).

The elementary identities

    3s sin T-c cos T=cos alpha-2cos(beta-alpha),
    s sin T-3c cos T=-cos alpha-2cos(beta-alpha)

show that G is minus the former contact residual F.

On the matching locus, the first-phase derivative agrees with the central derivative:

    g=s z_x+c z_y+1/2,
    g'=-s z_x'-c z_y'.

With f=-s z_x+c z_y and f'=-s z_x'+c z_y', the endpoint terms in the former area formula cancel as follows:

    -2g g'-2[(1-d)z_x z_x'+(1+d)z_y z_y']
        +2(f+1/2)f' = 2c z_y'.

Substitute z_y'=-A sin T+r mu B sinh(mu T). The remaining sine terms cancel, leaving

    W = alpha/2+p+2T+2c z0 T
          +2c r B sinh(mu T)(mu+1/mu)
      = beta/4+T/(2eta^2)+p
          -h/[mu(1-4c^2)(1+eta h)].                            (5)

Derivative matching also gives

    p={sin alpha/6+(2sc/3)(1+h/eta)/(1+eta h)}/cos alpha.

The contact equation eliminates h:

    h=-eta(3s sin T-c cos T-1)/(s sin T-3c cos T-eta^2).

Substitution, eta^2=(1-4c^2)/(3-4c^2), and the trigonometric addition formulas give

    p-h/[mu(1-4c^2)(1+eta h)]
      ={[(1-4d)cos alpha-(1+2d^2)]/[3sin alpha]-sin beta}
         /(1+2d).

Finally beta/4+T/(2eta^2)=[d beta+(1-2d)alpha/2]/(1+2d), proving (2). The substitutions are nonsingular on the specified branch. In particular cos alpha>0 and the coefficient used to eliminate h is negative there; this also follows from F=0, h>0, eta>0, and 3s sin T-c cos T-1>0 on the domain.

## 3. Checks and the off-branch failure

An exact symbolic rational reduction using u=tan(T/2), v=tan(beta/4) gave residual zero for the eliminated rational identity. This is supplementary algebra checking, not verification of the geometric model.

`test_contact_area_reduction.py` provides five local regression tests: exact rational substitution checks, the linear-angle identity, the equivalent contact equation, 80-digit on-branch comparisons with the independently transcribed long area expression, and an off-branch counterexample. All five passed locally; no CI, Lean build, or earlier full-suite rerun was attempted.

At beta=137 degrees and T=7/10 the old contact residual is nonzero, and the old and reduced area expressions differ by more than 3/100. Therefore replacing the old expression throughout its entire two-dimensional parameter rectangle without retaining the matching equation would be an error. No interval derivative or root-isolation certificate is silently modified here.

## 4. What remains unanswered

Equations (1)-(4) specify one real MODEL angle exactly, without choosing a decimal precision. They are an implicit exact characterization, not an elementary expression for beta. They do not prove beta_model=beta_c. In particular, computing more digits or writing a root operator around (4) does not supply the missing forward optimality and unrestricted comparison proofs.

The sufficient global cutoff from the preceding round is exactly pi-1/8. That different exact constant is a proved-range endpoint in the research draft, not the phase-transition angle.
