# Every possible first-source excess ends before the endpoint tangencies

Written proof, independently checked within the research session, October 10, 2026. This uses the
[initial-floor argument](gate1-tilted-initial-floor-energy.md), together with
the already established same-sign spatial propagation. No first-source
unit-curvature hypothesis is imposed.

## Statement

For every remaining tilted canonical maximizer with

    2/3<C<37/50, 0<h<17/50,

the absolutely continuous first-source density u satisfies

    u(t)<=1 for a.e. t>=11/15.                         (ET1)

Moreover

    11/15<acos(37/50)<=acos C.                        (ET2)

Thus every possible u>1 episode ends before any positive right-window
endpoint tangency. Write d=3C, B=e_R-1+h and gamma0=acos(1-h).

## 1. The universal quadratic excess envelope

All possible u>1 lies in the initial positive-q component after its
first p=0 time alpha. Before that crossing u=0. If there is no crossing,
or if q(alpha)<=1, there is no first-source excess. Later positive-q
components have q<=1/8 and cannot generate u>1.

Put epsilon=(q(alpha)-1)_+. On the initial component after alpha,
while q>1, u<=q gives p'<=-1 and hence p(alpha+tau)<=-tau.
For 0<=tau<=1, the arm estimate for v then gives

    q'<=-(1+tau)/2,
    (u(alpha+tau)-1)_+
      <=[epsilon-tau/2-tau^2/4]_+.                     (ET3)

When -1<=p<0, use v<=(1-p)/2. When p<-1, the stronger q'<=-1
implies the stated bound as long as tau<=1. Therefore, provided
epsilon<3/4, all excess ends within the time

    ell(epsilon)=sqrt(1+4epsilon)-1<1                 (ET4)

after alpha. This is the same quadratic envelope used in the audited
horizontal leakage argument.

The endpoint box H(C)<1/3 and positive EP imply

    B>=-1/2+(5/4)h-(1/3-h)_+/4,
    B<=-1/4+(5/4)h,
    -7/12<B<7/40.                                    (ET5)

The lower bound uses the sharper low-wing box n_-<=(H(C)-h)_+.

## 2. The first p-zero precedes the floor crossing

Suppose alpha<=gamma0 and epsilon>0. Both densities vanish up to
alpha by the initial-floor theorem, so

    p-1=B cos t-d sin t,
    q+1=d cos t+B sin t,
    (q(alpha)+1)^2=d^2+B^2-1.

The positive excess therefore forces d^2+B^2>5. In view of
d<111/50 and B<7/40, this is impossible for B>=0. Thus B<0.
At alpha,

    d sin(alpha)=1+B cos(alpha)<=1,

so alpha<=pi/6<8/15. Also

    (q(alpha)+1)^2
      <(111/50)^2+(7/12)^2-1
       =384181/90000<(207/100)^2.

Hence epsilon<7/100. Since 1+4(7/100)=32/25<(17/15)^2,
ET4 gives ell(epsilon)<2/15. All excess ends before

    alpha+ell<8/15+2/15=2/3<11/15.                    (ET6)

## 3. The floor crossing precedes the first p-zero

Now suppose gamma0<alpha, with the initial q-positive component still
present. The exact initial solution gives

    p(gamma0)=1+B(1-h)-d sqrt(h(2-h))>0.               (ET7)

In this case necessarily h<1/8. To see this, use ET5 and d>2 to bound
the right side above by

    V(h)=1+[-1/4+(5/4)h](1-h)-2sqrt(h(2-h)).

On [1/8,17/50], V is convex: its second derivative is
-5/2+2/[h(2-h)]^(3/2)>0. Both endpoints are negative. At 1/8,

    V(1/8)=235/256-sqrt(15)/4<235/256-15/16<0.

At 17/50, use sqrt(1411)>75/2 to obtain

    V(17/50)=1+231/2000-sqrt(1411)/25<0.

Convexity excludes ET7 on that whole interval. Therefore h<1/8, and
the more precise interval from ET5 is

    -7/12+(3/2)h <=B<=-1/4+(5/4)h< -3/32.             (ET8)

The initial positive-positive energy, evaluated at the floor and then
propagated to alpha, gives

    (q(alpha)+1)^2
       <=Q(d,B,h)
        :=d^2+B^2+B(1-h)-d sqrt(h(2-h)).               (ET9)

### 3a. If 1/25<=h<1/8

The function Q increases with d. It is convex in B. At each of the
two affine endpoints of ET8 it is convex in h, since the quadratic
coefficient is respectively 3/4 or 5/16 and the negative square root
is convex. Thus it suffices to check d=111/50 and h=1/25 or 1/8.

At h=1/25 the square root is exactly 7/25, and the two B endpoints
are -157/300 and -1/5. The second endpoint gives the larger Q
because the sum of those endpoints plus 1-h is positive. Its value is

    Q(111/50,-1/5,1/25)=10387/2500.                   (ET10)

At h=1/8 both B endpoints are negative and B+1-h>0. Their contribution
B^2+B(1-h) is therefore negative. Using sqrt(15)>15/4 gives

    Q<(111/50)^2-(111/50)(15/32)<10387/2500.

Consequently

    (q(alpha)+1)^2<=10387/2500<(51/25)^2,
    epsilon<1/25,
    ell(epsilon)<2/25.                               (ET11)

To bound alpha, on the initial p,q-positive component q'>=-1 and
p'=-1-q<=-d+t. Since p(0)=1+B<29/32,

    p(t)<=29/32-dt+t^2/2.

The upper bound is negative at t=3/5 when d>=2. Thus alpha<3/5
unless the q-positive component ends earlier, in which case it has no
excess. Combining with ET11,

    alpha+ell<3/5+2/25=17/25<11/15.                   (ET12)

### 3b. If 0<h<1/25

Now -7/12<B<-1/5, so p(0)=1+B<4/5. The same quadratic estimate gives

    alpha<=d-sqrt(d^2-8/5).                           (ET13)

Also B(1-h)-d sqrt(h(2-h))<=B: since B<0, its excess over B is
|B|h-d sqrt(h(2-h))<0, using |B|<7/12, d>2 and
sqrt(h(2-h))>=h. The convex quadratic B^2+B is at most -4/25 on
[-7/12,-1/5]. Hence ET9 yields

    epsilon<=(sqrt(d^2-4/25)-2)_+.                   (ET14)

If the right side vanishes there is no excess. On its positive range,
d>=sqrt(104)/5, put

    W(d)=d-sqrt(d^2-8/5)
            +sqrt(4sqrt(d^2-4/25)-7)-1.

This is increasing for sqrt(104)/5<=d<=111/50. Indeed the derivative
of its first two terms is greater than -1/3, since

    d^2/(d^2-8/5)<=13/8<16/9.

The derivative of its square-root term is

    2d/[sqrt(d^2-4/25)*sqrt(4sqrt(d^2-4/25)-7)]>10/7,

using 4d-7<=47/25<49/25. Thus W'>0.

At d=111/50, the alpha term is strictly below 2/5 because
sqrt(8321)>91. Also

    sqrt(d^2-4/25)<219/100,
    epsilon<19/100,
    ell(epsilon)<1/3,

the last inequality following from 1+4(19/100)=44/25<16/9.
Therefore ET13-ET14 and monotonicity give

    alpha+ell<=W(d)<2/5+1/3=11/15.                    (ET15)

The three cases prove ET1.

## 4. The endpoint angle lies strictly later

The alternating Taylor lower bound for cosine at 11/15 gives

    cos(11/15)
       >=1-(11/15)^2/2+(11/15)^4/24-(11/15)^6/720
        =6093080189/8201250000
        >37/50.

The exact final gap is 24155189/8201250000>0. This proves ET2.

## 5. The resulting right endpoint estimate

The independently audited positive-corner confinement theorem implies
that any positive active angle at x=C uses its first wall with strict
companion slack. Its angular stationarity therefore gives B_x(t)=C.
The actual first source point is B+mu and lies at horizontal coordinate
at most 2C. Consequently cos(t)<=C and t>=acos C.

If the top endpoint is b=C+T, the exact backward support formula is

    R_t(C)=T cot t
        +(1/sin t) integral_t^L sin(s-t)(u(s)-1) ds.

By ET1-ET2 the integral is nonpositive at every possible positive
endpoint-active angle. Hence

    n(C)<=[C/sqrt(1-C^2)]T.                            (ET16)

Separately, for the positive first-wall intercept R0(t)=(f(t)-1)/cos t,
the same support formula gives

    R0(t)<=b+J_f,
    J_f:=integral_0^L (u(s)-1)_+ sin s ds.              (ET17)

Indeed sin(s-t)/cos t=sin s-cos s tan t<=sin s. Since the niche
is convex on the right wing and vanishes once every first wall does,

    integral_C^(2C) n <=(T+J_f)n(C)/2.                 (ET18)

If b+J_f exceeds the cap endpoint, using its larger width only weakens
the bound. ET16-ET18 are genuine endpoint and area bounds; they do not
identify limiting exposure with full graph arclength.

## 6. A uniform small exterior-leakage moment

The three cases above give epsilon<19/100 and ell<1/3 whenever excess occurs. Integrating ET3 gives

    integral (u-1)_+ <= ell^2/4+ell^3/6 <11/324.

All such angles are below 11/15, so sin(t)<11/15. Therefore

    J_f < (11/15)(11/324)=121/4860<1/40.               (ET19)

This is an exact integral bound for the proved quadratic envelope, not an angular sampling estimate.
