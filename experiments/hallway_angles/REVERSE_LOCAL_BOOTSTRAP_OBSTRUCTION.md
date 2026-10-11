# Local curvature laws do not close the reverse-arm bootstrap

This is an exact counterexample to a proposed local proof strategy, not a feasible counterexample to reverse-sofa optimality. It also corrects an overstatement in the previous progress report.

## 1. A negative-arm excursion satisfying the local equations

Choose

    q=99/101, d=20/101, e=arccos(20/101),
    A0=(2+d)/(2q)=37/33,
    ell=2 arctan(33/148).

For 0<=t<=ell put

    a(t)=A0(1-cos t)-(sin t)/4,
    b(t)=q[a'(t)+1/2]+d a(t),
    rho_+(t)=1/2, rho_-(t)=0.

Then ell<e, a(0)=a(ell)=0, and a(t)<0 for 0<t<ell. Indeed

    a(t)=sin t [A0 tan(t/2)-1/4],

and tan(ell/2)=1/(4A0). The endpoint derivatives are a'(0)=-1/4 and a'(ell)=1/4, so

    b(0)=q/4=99/404, b(ell)=3q/4=297/404.

Since a''+a=A0, direct differentiation gives exactly

    a'=rho_+-1-d a/q+b/q,
    b'=1-rho_- -a/q+d b/q.

Throughout the excursion b>0: starting at b(0)>0, while a<0 and b>=0 its derivative is strictly positive. It increases to 3q/4. Thus the corrected local signed-curvature conditions hold: on a<0<b they require rho_+<=1/2 and rho_-=0, and this example saturates both. The opposite-support bounds a,b<=(1+d)/q also hold.

This is not merely a formal ODE example with impossible local contact heights. Define a corner by C'=( (cos(e-t)a-cos(t)b)/q, (sin(e-t)a+sin(t)b)/q ). Its two putative support contacts obey P_+'=(1/2)t1 and P_-'=0. Their initial height difference is

    D0=1+d-q^2/4=39083/40804<1.

At time t that difference is

    D(t)=D0-(1-cos t)/2,

which stays strictly between zero and one. A vertical translation therefore places these local contacts in a unit strip. The other differential and support-gap identities hold. The exact values sin(ell)=9768/22993 and cos(ell)=20815/22993 permit rational endpoint checks.

What is NOT supplied is a globally compatible convex cap on the full interval [0,e], the prescribed top and bottom endpoint contacts, a complete sofa motion, or maximality. Those global requirements may still exclude the excursion. The conclusion is that the local density laws plus a first-zero argument cannot do so on their own.

## 2. The earlier horizontal-tangent restriction was not new progress

At a horizontal tangent of the corner, y'=0 and X=x', the arm identities give

    a=sin(phi)X, b=-sin(e-phi)X.

The strip-contact inequality, without any maximality assumption, then gives

    q sin(2phi-e) X >= cos(phi)+cos(e-phi)-w >0.

Therefore a horizontal tangent in the first half must move left (X<0), and one in the second half must move right (X>0). At the midpoint no such tangent is possible.

REVERSE_PIECEWISE_CURVATURE.md instead highlighted exclusion of right-moving tangencies in the first half and left-moving tangencies in the second half. Those orientations were already excluded by the elementary strip constraint. They did not reduce the remaining geometric problem. In addition, an a.e. density inequality cannot automatically be evaluated at an isolated tangent as a classical second-derivative inequality.

This correction does not disprove the desired all-obtuse theorem. It retracts a claimed intermediate improvement and identifies the need for a genuinely global endpoint or integral argument.

## 3. Next usable direction

The terminal support faces couple the two arms over the whole angular interval. Under an explicit no-terminal-facet hypothesis their contact identities give positive-kernel integral formulas for both arms. Combining those global formulas with the repaired discrete curvature estimate is a different route; the local counterexample above does not satisfy or refute those additional conditions.

The existence of appropriate stationary polygonal approximants and the terminal-face condition must still be established for the correct maximization domain. No new optimality interval is claimed here. No CI or Lean build was used.
