# Schanuel-conditional non-elementarity of the contact-model crossing

**Main result of the elementary-descent round.** This is a conditional mathematical proof draft. Schanuel's conjecture is an explicit assumption, not a theorem proved here. The conclusion concerns the analytic contact-model equations, not an established unrestricted geometric phase transition. The proof has not been independently reviewed or checked in Lean.

Unlike the earlier Farey bounds, this argument excludes an entire finite-expression class. Unlike the earlier Schanuel argument, it does not assume an algebraic hallway direction. It uses neither a numerical approximation to the root nor the rational-angle denominator exclusions.

## 1. Statement and expression class

Let L be the smallest algebraically closed subfield of C containing the algebraic numbers and closed under exp and every logarithm of every nonzero element. In particular L contains pi, e, all algebraic roots over its intermediate fields, all finite nested exp/log expressions, and the circular/hyperbolic functions and their ordinary inverses evaluated at its elements. Arbitrary special functions and a newly named inverse of the sofa equations are not included by definition.

**Theorem (conditional on Schanuel).** Every real solution (b,t) of the compact contact/crossing system below in

    2pi/3<b<pi, 0<t<b/2                              (D)

has b not in L. In particular the previously certified model root beta_model is not in L.

Because L is algebraically closed, the conclusion is equivalently that b is transcendental over L. This is much stronger than b/pi being irrational, or sin b being transcendental over Q. It is still conditional.

### The explicit system

Put d=cos b, q=sin b, s=sin(b/2), c=cos(b/2), and

    mu=sqrt(3/(4q^2)-1)>0,
    eta=sqrt((-1-2d)/(1-2d)),
    k=sqrt(1+3/q^2)/2, K=k(pi-b).

The contact equation is

    eta(3s sin t-c cos t-1)
      +tanh(mu*t)(s sin t-3c cos t-eta^2)=0.           (1)

Set alpha=b/2-t and

    W=[d*b+(1-2d)*alpha/2-q
       +((1-4d)cos alpha-(1+2d^2))/(3sin alpha)]/(1+2d),

    eta_R=sqrt((2+d)/(2-d)),
    R=eta_R sin K/(cos K+eta_R sin K),
    V=(pi-b)/(2+d)+(1-2d)/(4q)+3d^2 R/(2q(2+d)^2).

The second equation is

    W=V.                                             (2)

This uses the reduced signed-area expression ON the contact locus. Its equivalence to the earlier long model expression is used only on the branch where that equivalence was derived. The present theorem is stated directly for (1)-(2) on (D); it makes no geometric assertion for other solutions of that wider algebraic-analytic system.

All denominators are nonzero in (D): q>0, d in (-1,-1/2), and 0<alpha<pi/2. Also, writing e=pi-b<pi/3, sin e>=2e/pi gives 0<K<pi*sqrt(31)/12<pi/2. Hence cos K+eta_R sin K>0.

## 2. Algebraic structure used by the proof

Set

    E=exp(ib), z=exp(it), w=exp(2mu*t), u=exp(iK).

The identities in `COUPLED_CONTACT_CAPTURE.md` put the equations in the form

    P_b(z)w+Q_b(z)=0,                                 (3)
    a*t+A*b+B*pi+C_b(z)-D0-E0*R_b(u)=0.               (4)

All coefficients are algebraic over E; more precisely the selected half-angle square root H=exp(ib/2) suffices together with algebraic operations. The required properties are:

- P_b,Q_b are coprime; deg P_b=2 and P_b(0) is nonzero.
- C_b is a nonconstant rational function of z.
- R_b is a nonconstant fractional-linear function of u^2.
- a=-(1-2d)/(2(1+2d)), A=(d+6)/(4(d+2)), B=-1/(d+2), and E0=3d^2/(2q(d+2)^2) are nonzero.
- The frequency recovers the hallway direction algebraically:

      q^2=3/[4(mu^2+1)],
      E^4+(4q^2-2)E^2+1=0.                          (5)

The pole of C_b at z=H has numerator -4H^2*d*(d+2), nonzero in (D). The determinant for R_b as a function of u^2 is 2i*eta_R, also nonzero.

For completeness, coprimality in (3) is elementary. With

    p(z)=(-3is-c)z^2-2z+(3is-c),
    r(z)=(-is-3c)z^2-2eta^2*z+(is-3c),
    P_b=eta*p+r, Q_b=eta*p-r,

a common nonzero root would give numbers v=(z-z^(-1))/(2i) and v0=(z+z^(-1))/2 satisfying

    3s*v-c*v0=1, s*v-3c*v0=eta^2.

Using eta^2=(1-4c^2)/(3-4c^2), these imply v=s/(3-4c^2) and v0=c/(3-4c^2). But v^2+v0^2=1, whereas the latter sum is 1/(3-4c^2)^2<1, since 0<c<1/2. A root at zero is impossible because the constant coefficients of P_b,Q_b have nonzero real parts. The leading coefficient of P_b also has nonzero real part.

## 3. A rational graph cannot support a nonconstant monomial substitution

We need the following unconditional algebra lemma. Let F be algebraically closed of characteristic zero, v transcendental over F, A0,B0 in F nonzero, and r0,s0 rational. If coprime polynomials P,Q in F[X] satisfy deg P>0 and P(0) nonzero, then

    P(A0*v^r0)*B0*v^s0+Q(A0*v^r0)=0                 (6)

forces r0=s0=0.

Choose a positive integer m clearing the exponent denominators and put h=v^(1/m). Equation (6) is a Laurent polynomial identity in the transcendental h. If m*r0 is nonzero, choose a nonzero root zeta of P and a nonzero h0 in F with A0*h0^(m*r0)=zeta. Substitution into the Laurent identity would force Q(zeta)=0, contradicting coprimality. Thus r0=0. P(A0) cannot vanish, since Q(A0) would then also vanish. Equation (6) now forces s0=0.

When applying this lemma, h can be taken to be the actual exp(a_n/m). This simultaneously fixes all fractional-power branches; root-of-unity factors also belong to F.

## 4. An elementary bend would put all coupled data in one finite tower

Assume for contradiction that b is in L. Then b,E,mu,k,K,u and all the coefficients of (3)-(4) belong to a finite reduced tower anchored at pi as in `COUPLED_CONTACT_CAPTURE.md`.

Equation (4), since C_b is nonconstant, makes z algebraic over that field with t adjoined. Equation (3) makes w algebraic over the same field. Capture applied to x=i*t and the nonrational multiplier -2i*mu puts t,z,w in the SAME finite tower.

Choose a shortest reduced pi-anchored tower containing the finite tuple

    (b,t,2mu*t,K,E,z,w,u).                            (7)

Write F_0=acl(Qbar(pi)) and F_n for its top field. Saturation says that each of

    ib, it, 2mu*t, iK                                (8)

is a rational linear combination of i*pi,a_1,...,a_n, since both that number and its exponential lie in F_n.

The case n=0 is impossible: the real nonzero number 2mu*t cannot be a rational multiple of the purely imaginary i*pi. This uses saturation, hence Schanuel; it is not an unconditional transcendence assertion.

Assume n>0, write F=F_{n-1} and a_n=a, and consider the two possible final steps. Under Schanuel exactly one of a and exp(a) is transcendental over F, while the other belongs to F.

## 5. A last logarithmic step descends

Suppose a is transcendental over F and exp(a) belongs to F. Saturation writes every argument in (8) as a rational multiple of a plus a rational combination of earlier arguments. Therefore ALL FOUR exponentials E,z,w,u already belong to F, since exponentials of rational combinations of earlier arguments are algebraic monomials in their exponentials, and F is algebraically closed.

Consequently mu,k and every coefficient in (3)-(4) belong to F. Write

    it=y0+r*a, 2mu*t=h0+s*a,

with y0,h0 in F and r,s rational. The identity 2mu*t=(-2i*mu)(it), compared in the transcendental variable a, gives

    s=-2i*mu*r.

Its left side is real rational; if r is nonzero the right side is nonzero and purely imaginary. Thus r=s=0 and t,2mu*t belong to F.

Multiply (4) by i. All terms except A*(ib) are now in F: pi was placed in the base from the outset, t has descended, z and u already descended, and their rational-function coefficients belong to F. Since A is nonzero, ib and b belong to F. Then K=k(pi-b) also belongs to F.

The entire tuple (7) lies in F, contradicting minimality of the tower.

## 6. A last exponential step also descends

Suppose a belongs to F and v=exp(a) is transcendental over F. Saturation makes all four ARGUMENTS in (8) elements of F. Hence b,t,2mu*t,K belong to F, and t is nonzero. In particular

    mu=(2mu*t)/(2t) belongs to F.

The identities (5) then put q^2 in F and make E algebraic over F. Because F is algebraically closed, E belongs to F. Thus all coefficients in (3)-(4) belong to F.

Saturation expresses z and w as

    z=A0*v^r, w=B0*v^s,

with A0,B0 in F nonzero and r,s rational. Apply the algebra lemma of Section 3 to (3). It gives r=s=0, so z and w belong to F.

Finally (4), with E0 nonzero and R_b a nonconstant rational function of u, makes u algebraic over F. Thus u belongs to F. Again all of (7) is in F, contradicting minimality.

Both possible last steps are impossible. This proves b not in L under Schanuel.

## 7. Stronger consequences and the exact limitation

Under the SAME conjectural assumption, each of

    beta_model, beta_model/pi,
    exp(i*beta_model), sin(beta_model), cos(beta_model),
    tan(beta_model), mu(beta_model), k(beta_model)

lies outside L. For exp(ib) use logarithmic closure; for sine/cosine use the quadratic equations for exp(ib); for tangent use exp(2ib)=(1+i*tan b)/(1-i*tan b); for mu and k use their invertible rational relationships with sin(b)^2. Multiplication by pi handles the normalized angle. These implications use the ordinary real branches at the given solution.

In particular the conditional conclusion rules out finite nesting of radicals, exponentials, logarithms, trigonometric functions and their usual inverses, even when arbitrary algebraic roots are allowed. It also rules out a polynomial equation for b whose coefficients all lie in L, because L is algebraically closed.

This is NOT an unconditional nonexistence proof: Schanuel has not been proved here. It does not exclude representations using additional special functions outside L. It also does not prove that beta_model is the actual unrestricted phase-transition angle beta_c.

### Finite-rank version

If an expression for b over Qbar and pi used at most m exp/log operations (arbitrary field/algebraic-root operations are free), the initial tower of Section 4 can be built in at most m+2 steps: one additional exponential forms E and one forms u; their other ingredients are algebraic over the preceding fields. Capture uses Schanuel in rank at most m+5, and the subsequent saturation/descent uses no larger rank.

Therefore Schanuel's statement for all tuples of ranks up to m+5 already excludes every such expression of exp/log length at most m. This is a bound on the hypothesis needed for a proposed finite expression, not a claim to have proved any of those Schanuel cases.

## Sources, checks, and provenance

Timothy Y. Chow, *What is a closed-form number?*, American Mathematical Monthly 106 (1999), 440–448, Sections 2–3, discusses the field L, Lin's conditional theorem, and reduced-tower methods: https://arxiv.org/html/math/9805045 . The coupled coefficient-reconstruction argument here is a deduction for this system and is proved explicitly, not attributed to Chow as an existing theorem.

The tower groundwork in `ELEMENTARY_TOWER_LEMMAS.md` and `SCHANUEL_ALGEBRAIC_DIRECTION.md` was present at the starting checkpoint. The present proof strengthens the conclusion to nonmembership in L and avoids the latter file's rank case split by anchoring pi. The rational identities and nondegeneracy checks are independently testable; such tests do not formally verify the transcendence-degree argument.

No CI, workflow, or Lean build is involved. The theorem is a conditional proof draft requiring independent mathematical review.
