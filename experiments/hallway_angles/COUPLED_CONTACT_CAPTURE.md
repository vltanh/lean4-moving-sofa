# The crossing equations capture the switching data in an elementary tower

**Conditional lemma: Schanuel's conjecture is assumed.** This is a statement about the explicit analytic contact equations, not about geometric optimality. It extends the finite-tower lemmas in `ELEMENTARY_TOWER_LEMMAS.md` by anchoring pi in the base field. No numerical approximation or rational-denominator exclusion is used.

Let L be the smallest algebraically closed subfield of C containing Qbar and closed under exp and all complex logarithms. This includes every finite expression using algebraic constants, algebraic operations, exp/log, and the circular/hyperbolic functions and their usual inverses. It does not add arbitrary inverses such as the inverse of the sofa equations.

## 1. Towers anchored at pi

Put F_0=acl(Qbar(pi)) inside C. Every finite subset of L is contained in a tower

    F_j=acl(F_{j-1}(a_j,exp(a_j))), j=1,...,n,

where at each step either a_j or exp(a_j) belongs to F_{j-1}. Such a tower can be reduced so that i*pi,a_1,...,a_n are Q-linearly independent: if a_j is a rational combination of i*pi and earlier arguments, its value and its exponential already lie in the previous algebraically closed field, so delete it.

Schanuel then gives trdeg_Q F_j=j+1. The upper bound follows because the base has transcendence degree one and every step adds at most one; the lower bound follows by applying Schanuel to i*pi,a_1,...,a_j. The exponential of i*pi is algebraic.

**Saturation:** if x and exp(x) lie in F_n, then

    x in span_Q{i*pi,a_1,...,a_n}.                    (1)

Otherwise Schanuel on one more argument would require transcendence degree n+2 inside F_n.

**Capture:** let c in F_n be nonrational. If exp(x) and exp(c*x) are algebraic over F_n(x), then x,exp(x),exp(c*x) all belong to F_n.

Indeed, if x,c*x were independent modulo the rational span in (1), Schanuel on n+3 arguments would require transcendence degree at least n+3, whereas their inputs and exponentials lie in an algebraic extension of F_n(x), whose transcendence degree is at most n+2. A rational dependence gives (r+s*c)x in F_n, with r,s rational and not both zero. Since c is not rational, r+s*c is nonzero. Thus x is in F_n, and algebraic closedness places the exponentials there too.

This is a number-theoretic argument about the actual constants; it does not identify function-level non-elementarity with constant-level non-elementarity.

## 2. Rational forms of the two equations

Write b=beta, t=T, d=cos b, q=sin b, and work in

    2pi/3<b<pi,  0<t<b/2.

Let mu=sqrt(3/(4q^2)-1)>0, k=sqrt(1+3/q^2)/2, K=k(pi-b), and put

    E=exp(ib), z=exp(it), w=exp(2mu*t), u=exp(iK).

On the matching locus, the reduced area equation is

    a*t+A*b+B*pi+C_b(z)-D-E0*R_b(u)=0,               (2)

where

    a=-(1-2d)/(2(1+2d)),
    A=(d+6)/(4(d+2)), B=-1/(d+2),
    D=(1-2d)/(4q), E0=3d^2/(2q(d+2)^2),
    eta_R=sqrt((2+d)/(2-d)),
    R_b(u)=eta_R(u^2-1)/(i(u^2+1)+eta_R(u^2-1)).

The coefficient E0 is nonzero. R_b is a nonconstant fractional-linear function of u^2: its determinant is 2i*eta_R.

For H=exp(ib/2), set

    C_b(z)=[-q+i*((1-4d)(H^2+z^2)-2Hz(1+2d^2))
                        /(3(H^2-z^2))]/(1+2d).      (3)

This is the rational expression for the trigonometric part of the reduced forward area; H is algebraic over E. It is nonconstant: at z=H its numerator inside the fraction is -4H^2*d*(d+2), which is nonzero in the stated b range. Thus it has a genuine pole there.

The contact equation is

    P_b(z)*w+Q_b(z)=0,                               (4)

with the coprime quadratics from `CONTACT_TRANSCENDENCE.md`. All their coefficients are algebraic over E. In particular P_b(z) is nonzero at a solution and w=-Q_b(z)/P_b(z).

Equations (2)-(4) are exact identities for the compact model system. The long area expression is replaced by (2) only on the contact locus, not for arbitrary off-branch parameter values.

## 3. Elementary b forces elementary t at a crossing

Suppose b is in L and the compact contact/crossing system holds. All of b,E,mu,k,K,u and the coefficients of (2)-(4) are then in some finite reduced pi-anchored tower F_n.

Equation (2), with the rational function C_b nonconstant, makes z algebraic over F_n(t). Equation (4) makes w algebraic over the same field. Apply capture with

    x=i*t, c=-2i*mu.

The multiplier is nonrational because it is nonzero and purely imaginary. Its two exponentials are z and w. Capture gives t,z,w in F_n. Consequently every constant in the two coupled equations belongs to that SAME finite tower; no extra exp/log step for t is needed.

The crossing-area equation is essential. The contact equation alone makes w algebraic over F_n(z), not z algebraic over F_n(t), and would not justify this application of capture.

## 4. Why the pi anchor matters

At a final logarithmic tower step, the saturation formula expresses the four exponential arguments ib,it,2mu*t,iK as rational-affine functions of the new logarithm. Since pi is already in the preceding field, the nonzero coefficient A in (2) can force b to descend once t has descended. Without keeping pi in the base, an unnecessary extra rational-rank case appears. The complete last-step descent is in `SCHANUEL_NON_ELEMENTARITY.md`.

## Source and verification boundary

The reduced-tower approach and the Liouvillian number field are discussed in Timothy Y. Chow, *What is a closed-form number?*, American Mathematical Monthly 106 (1999), 440–448, Sections 2–3: https://arxiv.org/html/math/9805045 . The pi-anchored capture and its application to these equations are proved above, not quoted as theorems from that paper.

Schanuel is an assumption, not an established premise. This lemma has not been independently reviewed or formalized in Lean. Exact symbolic checks can verify formulas (2)-(4), but do not verify the field-theoretic inference or the conjecture.
