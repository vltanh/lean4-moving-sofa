# Global terminal kernels for the reverse-arm problem

**Conditional analytic identities and inequalities.** This note adds genuinely global endpoint information to the repaired local curvature law. It does not assume that the required endpoint condition or stationary approximants have already been proved for arbitrary reverse maximizers. No optimality interval is extended by this note alone.

Fix 0<e<pi/2, q=sin(e), d=cos(e), A=1+d. Let r_+(s), r_-(s) be the two support-curvature densities indexed by their own normal parameter s in [0,e]. In the paired arm equations, rho_+(phi)=r_+(phi) and rho_-(phi)=r_-(e-phi).

## 1. Explicit terminal hypothesis

Assume the upper and lower support arcs start at heights w/2 and -w/2 and finish at the SAME terminal vertex. There is no intervening segment on either terminal support line. Write

    J_+=integral_0^e r_+(s)sin s ds,
    J_-=integral_0^e r_-(s)sin s ds.

The vertical contact displacement gives

    J_++J_-=w.                                        (1)

Let D=h_+'(0)-h_-'(0) and I_+=integral r_+(s)sin(e-s)ds, with I_- similarly. The horizontal terminal matching condition is

    qD=d(w-2J_+)-I_++I_-.                             (2)

These conditions are not automatic for an arbitrary convex cap. They express the absence of terminal facets. Endpoint variation is a possible way to establish them for a suitable maximizer, but that argument must be supplied for the actual variational domain.

## 2. Eliminate the unknown endpoint slopes

For psi=e-phi, equations (1)-(2) and the support differential equation give

    q a(phi)=A
       - integral_phi^e r_+(s)sin(s+psi)ds
       - integral_psi^e r_-(s)sin(s-psi)ds,             (3)

    q b(phi)=A
       - integral_psi^e r_-(s)sin(s+phi)ds
       - integral_phi^e r_+(s)sin(s-phi)ds.             (4)

For example insert

    h_+(phi)=(w/2)cos phi+h_+'(0)sin phi
                +integral_0^phi r_+(s)sin(phi-s)ds

and its lower counterpart into the canonical-corner equations, differentiate, and use (1)-(2). All slope terms cancel. Every kernel displayed in (3)-(4) is nonnegative, since 0<e<pi/2.

It is important not to impose the wrong endpoint values. These formulas give

    A-q b(0)=J_+,  A-q a(e)=J_-,

not two endpoint values both equal to w. Their SUM equals w.

## 3. A uniform preliminary lower bound for the arms

Assume in addition the repaired interior curvature estimate gives

    0<=r_+,r_-<=R, R=1/(1-d).

The sum of the two kernels in (3) integrates to A-2d cos(psi). Therefore

    a(phi)>=d[2cos(psi)-A]/[(1-d)q]>=-d/q,             (5)

and similarly b(phi)>=-d/q. The usual opposite-support inequalities give a,b<=A/q.

A negative a can consequently occur only when cos(psi)<A/2, hence only in the first half of the angular interval. A negative b can occur only in the second half. This conclusion genuinely uses terminal matching and the density bound, unlike the earlier tangent observation.

## 4. A convex integral relaxation on the previously missing range

For e>=pi/3 one has d<=1/2 and -d/q>=-q/A. On the interval -q/A<=z<=A/q the corrected piecewise curvature ceiling satisfies

    k_e(z)<=1/2+A z/(2q).

The proof is elementary: for z<=0 the right side is nonnegative; for 0<z<=q/2 it exceeds 1/2; and for q/2<=z<=A/q its difference from z/q is [1-(1-d)z/q]/2>=0.

Put c=R/2 and define the positive integral operator

    (K r)_+(phi)=integral_phi^e r_+(s)sin(s-phi)ds
                  +integral_(e-phi)^e r_-(s)sin(s+phi)ds,

with (K r)_- obtained by interchanging + and -. Equations (3)-(4) convert the affine curvature bounds exactly to

    r+c K r <= R                                     (6)

componentwise, in addition to r>=0 and the moment constraint (1).

The L-infinity norm of cK on pairs, equipped with the maximum norm, is at most

    c[A-2d cos e]=1/2+d<1   when e>pi/3.              (7)

This makes the linear equality problem nonsingular. It does NOT make the inverse order preserving: (6) has I+cK, rather than the I-cK positive inverse used in PR #4. For example with L=[[0,1/2],[1/2,0]], the equality solution of (I+L)x=(1,1) is (2/3,2/3), but x=(1,0) is nonnegative and satisfies (I+L)x<=(1,1). Thus one cannot bound every subsolution by the equality solution componentwise.

## 5. A valid dual-certificate principle

The adjoint is

    (K*lambda)_+(s)=integral_0^s lambda_+(t)sin(s-t)dt
                 +integral_(e-s)^e lambda_-(t)sin(s+t)dt,

with the reflected formula for the other component. Suppose lambda>=0 and a target pair f satisfies

    f <= lambda+cK*lambda+eta(sin s,sin s).

Multiplying by r>=0, integrating, and using (6) gives

    integral f.r <= R integral(lambda_++lambda_-)+eta w.  (8)

If only w0<=w<=1 is known, replace eta w by eta when eta>=0 and by eta w0 when eta<0. Every proposed certificate must verify the functional inequality for ALL s; a linear program on sampled s is only a proposal mechanism.

The positive part of an approximate dual can be made feasible using an explicit uniform residual allowance: if f-lambda-cK*lambda-eta sin<=epsilon, then replacing lambda by lambda+epsilon in both components restores the inequality, because K* is positive. The corresponding integral cost must be retained.

## 6. An elementary moment certificate

Dropping the nonnegative cross-family term from (6) gives

    r(s)+c integral_s^e r(t)sin(t-s)dt<=R.

For k=sqrt(1+c), the function lambda(s)=sin(ks)/k satisfies

    lambda(s)+c integral_0^s lambda(t)sin(s-t)dt=sin s.

Whenever ke<pi, lambda>=0, so (8) proves the explicit bound

    integral_0^e r(s)sin s ds <= R[1-cos(ke)]/k^2.      (9)

This is an exact dual inequality, not a quadrature estimate. On e>=pi/3, c<=1 and ke<sqrt(2)pi/2<pi, so it applies throughout the currently relevant range. It may be too loose for full arm positivity; the cross-family terms in (8) retain additional information.

## Status

Equations (3)-(9) supply a precise global alternative to the failed local first-zero argument. To finish the all-obtuse theorem one still needs: the appropriate stationary-sequence construction, justified terminal matching, and a sufficient positive-arm or inside-strip crossing conclusion from the resulting constraints. Passing finite LPs would not by itself discharge the last item. The earlier optimum ranges are not enlarged here.
