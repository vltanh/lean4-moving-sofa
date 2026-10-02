# 11. An analytic replacement for the eleven-step arm bootstrap

Date: 2026-10-02. New paper proof, not Lean-checked. This removes the need for a numerical/finite-iteration lemma from the new uniqueness argument.

## Theorem

Let 0<L<5/3. Let f,g:[0,L]->[0,infinity) be continuous and satisfy

    f(t)>=1+integral_0^t m(g(s)) ds,
    g(t)>=1+integral_t^L m(f(s)) ds,                            (1)

where, for x>=0,

    k(x)=max(|x-1|,(|x-1|+1)/2),   m(x)=x-k(x).

Then

    f(t)>=1+t/2,   g(t)>=1+(L-t)/2                              (2)

for every t in [0,L]. In particular f(t)>1 for t>0 and g(t)>1 for t<L.

For the moving-sofa application L=pi/2<5/3. The last strict inequality follows already from pi<22/7<10/3; no numerical iteration is needed.

## Proof

The explicit piecewise formula is

    m(x)=3x/2-1    for 0<=x<=1,
    m(x)=x/2      for 1<=x<=2,
    m(x)=1        for x>=2.

Consequently, for every x>=0,

    m(x)>=1/2-(3/2)(1-x)_+.                                    (3)

Define the continuous deficits

    p(t)=(1-f(t))_+,   q(t)=(1-g(t))_+,
    M=max(max_[0,L] p, max_[0,L] q).

Nonnegativity of f,g gives 0<=M<=1. Equations (1) and (3) imply

    p(t)<=[(3/2) integral_0^t q(s) ds-t/2]_+,
    q(t)<=[(3/2) integral_t^L p(s) ds-(L-t)/2]_+.                (4)

Suppose M>0. If M<=1/3, both right sides of (4) are zero, a contradiction. Thus M>1/3. Put

    c=(3M-1)/2>0.

Applying p,q<=M in (4) gives the stronger envelopes

    p(t)<=min(M,ct),   q(t)<=min(M,c(L-t)).                     (5)

By swapping f(t),g(L-t) when necessary, assume p(t_*)=M for some t_*. From (4)–(5),

    M <= integral_0^L [(3/2)min(M,cr)-1/2]_+ dr =: I.           (6)

Indeed the right side of the first inequality in (4), at t_*, is at most the integral of the positive part of its integrand over the full interval; substitute r=L-s and (5).

Set

    r_0=1/(3c),   r_1=M/c.

The integrand in I is zero up to r_0, rises linearly from zero to c between r_0 and r_1, and is the constant c after r_1. Crucially,

    r_1-r_0=(M-1/3)/c=2/3.

Its entire rising triangle has area c/3.

If L<=r_1, then

    I<=c/3=M/2-1/6<M,

contradicting (6).

If L>r_1, direct integration gives

    I=c/3+c(L-r_1)=c(L+1/3)-M.

Because L<5/3, c>0, and M<=1,

    I<2c-M=2M-1<=M,

again contradicting (6). Therefore M=0, and f,g>=1 on the whole interval.

Now m(f),m(g)>=1/2 by the piecewise formula. Substitute this into (1) to obtain (2). QED.

## Application to an arbitrary right-angle cap

This scalar theorem does not assume balancedness, symmetry, differentiability of f,g, or that they arise from a sofa. It needs only nonnegativity, continuity, and the two integral inequalities (1).

For a cap with the two curvature-measure bounds

    sigma_K|[0,L) <= k(g(t)) dt,
    sigma_K|(L,pi] <= k(f(t-L)) dt,

the arm-length Stieltjes identities give (1), with f(0)=g(L)=1 and the one-sided endpoint conventions from Chapter 6. The identities are df=g dt-d sigma_K and dg=d sigma_K(t+L)-f dt. The first measure bound implies no atom at 0, the second no atom at pi, while a top atom at L is allowed. These conventions must be checked before invoking the scalar theorem.

The inner-corner derivative then has the quantitative signs

    x_K'(t).u_t=1-f(t)<=-t/2,
    x_K'(t).v_t=g(t)-1>=(L-t)/2.

Both are strict for 0<t<L. This supplies the sign part of the injectivity condition in notes 05 and 08 without invoking the original F_11 lemma.

## Scope

The theorem above is proved by inequalities and an exact triangular-area computation. It does not by itself establish the curvature bounds for every maximizing cap; that geometric/variational argument remains a separate obligation. Nor is 5/3 claimed to be the optimal threshold for this scalar problem.

Definitions of k,m and the Stieltjes arm identities: `MovingSofa/Injectivity/DiscreteIneq.lean` and `MovingSofa/Injectivity/ArmLengths.lean`, corresponding to Baek §§6.2–6.3. The maximum-deficit argument here replaces, rather than assumes, the finite bootstrap in §6.5.
