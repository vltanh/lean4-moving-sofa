# Conditional non-elementarity of the switching and reverse-phase data

**Schanuel is assumed throughout.** These are additional deductions for solutions of the compact model system in `SCHANUEL_NON_ELEMENTARITY.md`, on 2pi/3<b<pi and 0<t<b/2. They are not unconditional statements and do not identify the contact-model crossing with an unrestricted geometric transition. The proofs require independent review; symbolic checks below only verify supporting identities.

Retain

    alpha=b/2-t, h=2mu*t, K=k(pi-b),
    E=exp(ib), z=exp(it), w=exp(h), u=exp(iK),
    k^2=mu^2+5/4.

The main theorem already proves b,mu,k not in L. Because L is algebraically closed, each is transcendental over every subfield F of L. This file proves that t,h,alpha,K also lie outside L. Hence z,w,u lie outside L as well, by logarithmic closure.

## 1. Two field-theoretic preliminaries

Any finite collection of elementary data can be placed in a reduced pi-anchored tower whose top field F is invariant under complex conjugation. To construct one, append both a_j and its conjugate at every exp/log step of an initial tower, in that order, taking algebraic closures. If the step is exponential, both arguments lie in the previous conjugation-invariant field; if logarithmic, both exponentials do. Thus the paired steps are admissible and the top field is conjugation-invariant. Reducing redundant arguments does not change that field.

Let D be the rational span of the reduced tower arguments, including i*pi, and N=trdeg_Q F=dim_Q D. If x_1,...,x_r and all their exponentials lie in an algebraically closed extension H of F with trdeg_F H<=m, Schanuel implies

    dim_Q((D+span_Q{x_1,...,x_r})/D)<=m.              (1)

Indeed, choose independent representatives modulo D and adjoin them to a basis of D. Schanuel gives the required lower bound for their inputs and exponentials, all algebraic over H. This is a consequence of Schanuel over the already reduced finite tower, not an extra conjecture about arbitrary base fields.

Conjugation invariance permits a useful separation: if real non-elementary R and B are given, then iB and R are rationally independent modulo D. A rational relation modulo D lies in F; taking real and imaginary parts would put either R or B in F. Their non-elementarity forbids that.

## 2. The central half-angle t is not elementary

Suppose t is in L. Choose a conjugation-invariant finite tower F containing t and z=exp(it). Its field is algebraically closed. Since mu and b are not elementary, they do not belong to F. Also h=2mu*t is not in F because t is nonzero and belongs to F.

The quartic reconstruction of E from mu makes E algebraic over F(mu). The contact equation makes w algebraic over F(mu), since z belongs to F. The crossing-area equation makes u algebraic over F(mu,b). Thus the three arguments

    ib, h, iK

and their exponentials lie in H=acl(F(mu,b)), of relative transcendence degree at most two. By (1), there is a nontrivial rational relation

    r*b+s*h/i+v*K in F,

or, equivalently, r*ib+s*h+v*iK in F. Taking real parts forces s=0, because h is not in F. We obtain r*b+v*K=f in F. Here v cannot be zero, or b would belong to F. Since k is not elementary, r-v*k is nonzero. From K=k(pi-b),

    b=(f-v*k*pi)/(r-v*k) in F(k) subset acl(F(mu)).

Now H has relative transcendence degree at most one. But ib and h remain independent modulo D, as they are purely imaginary/real and b,h are not in F. This contradicts (1). Hence t is not in L.

## 3. The hyperbolic argument h=2mu*t is not elementary

Suppose h is in L, and choose F containing h and w=exp(h). Then t=h/(2mu) belongs to F(mu), while t is not in F by Section 2. Again E is algebraic over F(mu). The contact equation, viewed as a polynomial in z with fixed w, makes z algebraic over F(mu): the polynomial is not identically zero because P_b and Q_b are nonproportional. The area equation makes u algebraic over F(mu,b).

Apply (1) to ib,it,iK inside H=acl(F(mu,b)). It forces a nontrivial rational relation

    r*b+s*t+v*K=f in F.

The coefficient r-v*k is nonzero: otherwise either k is rational, or r=v=0 and the relation puts t in F. Both are impossible. Thus

    b=(f-s*t-v*k*pi)/(r-v*k) in acl(F(mu)),

and H has relative transcendence degree at most one.

If ib,it,iK had rank at most one modulo D, the nonzero class of it would span them. There would be rational r0,s0 and f0,g0 in F with

    b=r0*t+f0, K=s0*t+g0.

Here r0 is nonzero since b is not in F. Substituting t=h/(2mu) into K=k(pi-b) gives

    k[2(pi-f0)mu-r0*h]=s0*h+2g0*mu.                  (2)

The bracket is not the zero polynomial in mu because r0*h is nonzero. Therefore k would belong to F(mu). But mu is transcendental over F and k^2=mu^2+5/4. The rational function X^2+5/4 is not a square in F(X): its two zeros, plus/minus i*sqrt(5)/2, are simple. This contradicts (2).

Consequently the three arguments have rank at least two modulo D, while H has relative transcendence degree at most one, again contradicting (1). Hence h and w are not in L.

## 4. The first switching angle alpha is not elementary

Suppose alpha is in L and choose a conjugation-invariant F containing alpha and exp(i*alpha). Then

    t=b/2-alpha,
    z=exp(ib/2)*exp(-i*alpha)

is algebraic over F(mu), because exp(ib/2) is algebraic over E. The contact equation makes w algebraic over F(mu). The area equation again makes u algebraic over F(mu,b).

The arguments ib,h,iK and their exponentials therefore lie in H=acl(F(mu,b)). The numbers b and h are not elementary by the main theorem and Section 3. As in Section 2, a rational relation modulo D must have zero real h coefficient, then forces b algebraic over F(mu). This reduces the relative transcendence degree to one, but ib and h have rank two modulo D. Contradiction. Thus alpha is not in L.

## 5. The reverse phase K is not elementary

Suppose K is in L and choose a conjugation-invariant F containing K and u. Now

    k=K/(pi-b), mu^2=k^2-5/4

show that mu is algebraic over F(b), and E is algebraic over that field by direction reconstruction. The area equation makes z algebraic over F(b,t), since C_b(z) is nonconstant. The contact equation makes w algebraic over F(b,t).

The arguments ib,it,h and their exponentials lie in H=acl(F(b,t)), of relative transcendence degree at most two. A rational relation modulo D has zero h coefficient, by conjugation invariance and the fact that h is not elementary. The remaining relation puts t in F(b), because neither b nor t belongs to F. Thus H has relative transcendence degree at most one. But ib and h remain independent modulo D, contradicting (1).

Therefore K and u are not in L.

## Conclusions and boundary

Conditional on Schanuel, the model crossing has no elementary expression for its bend b, either switching parameter t or alpha, the hyperbolic argument h, or the reverse phase K. The associated exponentials E,z,w,u and frequencies mu,k are also outside L. Since L is algebraically closed, these are transcendence statements over the whole elementary-number field, not just over Q.

No theorem about the common signed area being elementary or non-elementary is asserted here. Some auxiliary constants, such as the matching amplitude 1/3, are elementary; the conclusion is only about the explicitly listed quantities. No additional global geometry or phase-transition identification is claimed.

The only new algebra beyond the main theorem is the rational-function nonsquare observation for X^2+5/4 and the exact frequency identity k^2-mu^2=5/4. These are included in `elementary_descent_algebra.py` and `test_elementary_descent.py`. Tests of those identities do not verify the transcendence-degree arguments, and Schanuel remains an assumption.

The reduced-tower background is discussed by Timothy Y. Chow, *What is a closed-form number?*, American Mathematical Monthly 106 (1999), 440–448: https://arxiv.org/html/math/9805045 . The case arguments above are given as deductions for this model, not as results quoted from that paper. No CI or Lean build was run.
