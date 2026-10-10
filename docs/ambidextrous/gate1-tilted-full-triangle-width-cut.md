# A sharper tilted width cut from three full niche triangles

Written proof, independently checked within the research session, October 10, 2026. This improves the
[preceding canonical cutoff](gate1-tilted-width-exclusions.md) C<4/5 to C<37/50. It uses actual
two-wall niche regions at pi/8, pi/4, and 3pi/8. The new ingredient is a
complete additional triangle together with an exact loss bound for the
positive floor. The final relaxation includes all 45-degree window
clipping, and a supporting plane controls its entire width range.

## Statement and standing notation

Let U be a downward convex cap of height one, with projection I=[-a,a]
and middle window J=[-a/2,a/2]. Its roof is affine on J and satisfies

    A(-a/2)=1-h, A(a/2)=1,
    37/25<=a<=8/5, 0<=h<=17/50.                         (FT1)

Write e_R=A(a), e_L=A(-a), n_+=n(a/2), n_-=n(-a/2), where n is the
full continuous-angle positive niche. Assume the actual endpoint laws

    e_R=1/2+h/4+(3n_+-n_-)/4,
    e_L=1/2-3h/4+(3n_--n_+)/4.                         (FT2)

Then

    P(U)<25811237/31500000<41/50.                       (FT3)

Consequently, combining this theorem with the already audited short,
wide, and intermediate-width bounds, every remaining canonical global
maximizer has

    1001/2000<C=W/4<37/50, 0<h<17/50.

Use the constants

    r=sqrt(2), k=r-1, c=cos(pi/8), s=sin(pi/8),
    A=1-k, b=2-k, d=3r-1,
    gamma=1-r/2, t=2c-r, d0=3/5-t.

Relevant exact identities are

    s/c=k, k+1/k=2r, 1+k=r, k^2=1-2k,
    1/s+1/c=4c, 1/(rc)=2s, 1/(rs)=2c,
    r/(4c^2)=k, 2d+b^2=9.

The letter A without an argument denotes the constant 1-k only in
scalar formulas; A(x) always denotes the cap roof.

## 1. Lift the low wing and retain a genuine 45-degree niche

Raise the left charged wing by h, put the middle roof at height one,
and retain the right wing. This gives the genuine concave roof Ahat of
a height-one cap Uhat. Concavity follows because the left wing has
slopes at least h/a, the inserted middle has slope zero, and the right
wing has nonpositive slopes since its initial endpoint already has
the global maximum height one. In particular

    O(U)=O(Uhat)-ah/2.                                  (FT4)

Set

    u=r H_Uhat(pi/4)-1, v=r H_Uhat(3pi/4)-1,
    M=(u+v)/2, C=a/2.

The actual middle endpoint points and the height bound give

    C<=u,v<=a.

The original first-quadrant support equals the lifted one: the point
(C,1) dominates every lifted point to its left in each such direction.
In the second 45-degree direction, the point (-C,1-h) beats (C,1)
by (a-h)/r>0. Hence the actual original parameter is exactly v-h.
Its 45-degree niche is therefore

    n45(x)=[min(u-k-x,v-h-k+x)]_+.

The apex x_d=(u-v+h)/2 lies in J, because |u-v|<=a/2 and h<=a/2.
Consequently its exact area, including both possible window clips, is

    N45=(M-h/2-k)^2
         -[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.             (FT5)

The apex height is positive throughout the enlarged square: it is at
least 37/50-17/100-k>0.

The lifted cap lies under

    A0(x)=min(1,1+u-x,1+v+x).

Let D be the charged exterior area between A0 and Ahat. Then D>=0,
and the exact exterior area of A0 together with (FT4) gives

    P(U)<=F_h(a,u,v)-D-[integral_J n-N45],                (FT6)

where

    F_h=a-[(a-u)^2+(a-v)^2]/2-ah/2
         -(M-h/2-k)^2
         +[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.             (FT7)

No mandatory tilt deficit is subtracted from F_h; ignoring that extra
nonnegative area is allowed.

## 2. Endpoint controls and two near-vertical support deficits

The unit-height box yields

    n(+-C)<=1-sqrt(1-C^2)<=2/5,

since C<=4/5. For example at x=C the first wall is at most
1+(C cos(theta)-1)/sin(theta), whose supremum over theta is
1-sqrt(1-C^2); the opposite endpoint follows by reflection. Combining
this with (FT2) gives

    e_R>=2/5+h/4, e_L>=2/5-3h/4,
    E:=e_R+e_L>=1-h/2.                                  (FT8)

Put w_R=a-u and w_L=a-v+h, the actual original 45-degree endpoint
deficits. Support containment at the endpoints gives

    e_R<=1-w_R, e_L<=1-w_L,
    w_R<=3/5-h/4, w_L<=3/5+3h/4,
    M-h/2>=a-1/2-h/4.                                  (FT9)

Define the nonnegative lifted support deficits

    delta_L=c+s v-H_Uhat(5pi/8),
    delta_R=c+s u-H_Uhat(3pi/8).

The actual lifted middle endpoints imply

    delta_L<=s(v-C), delta_R<=s(u-C).

On the flat part [-v,-C] the left support line cuts a triangle of
depth delta_L/c and slope k. It fits completely before -C and has
area delta_L^2/(2c^2 k)=r delta_L^2. The right flat part [C,u]
provides the analogous disjoint triangle. Thus

    D>=D0:=r(delta_L^2+delta_R^2).                       (FT10)

Only the flat portions are used, so there is no need to fit any
additional exterior triangle at either endpoint.

## 3. Full additional niche triangles fit the middle window

At angle pi/8 the actual niche dominates the positive part of

    f_R(x)=min(b_R+kx,B_R-x/k),
    b_R=1-1/c+k v-h-delta_L/c,
    B_R=e_R+a/k-1/s.

The first displayed wall follows from
H_U(5pi/8)>=H_Uhat(5pi/8)-ch. Indeed A(x)>=Ahat(x)-h on I,
so every translated upper point is dominated vertically by a point of U;
the support normal has positive vertical component. This argument also
covers a translated upper point falling below the floor. The companion
wall follows from the actual endpoint
(a,e_R). Equality of the actual support with either lower bound is
not assumed.

Against the right branch u-k-x of n45 set

    x_L=(u-k-b_R)/r,
    x_*=(B_R-b_R)/(2r),
    x_R=(B_R-u+k)/r,
    Z_R=(B_R+b_R)/2-u+k.

When Z_R>0, the signed gain f_R-(u-k-x) is a full triangle on
[x_L,x_R], with slopes r and -r and height Z_R. Its area is Z_R^2/r.
Its endpoints are x_*+-Z_R/r.

Reflection, in y=-x, gives the analogous left construction

    f_L(y)=min(b_L+ky,B_L-y/k),
    b_L=1-1/c+k u-delta_R/c,
    B_L=e_L+a/k-1/s,
    x_L^L=(v-h-k-b_L)/r,
    x_R^L=(B_L-v+h+k)/r,
    Z_L=(B_L+b_L)/2-v+h+k.

The right and reflected-left crossovers lie strictly beyond their
respective 45-degree apices:

    x_L-x_d=k(M+h/2)+2s-1+delta_L/(rc)>0,
    x_L^L+x_d=k(M-h/2)+2s-1+delta_R/(rc)>0.              (FT11)

Indeed M-h/2>=37/25-1/2-17/200=179/200, while k>2/5 and
2s>3/4. This also places the two gain regions on opposite sides
of the apex.

The outer zero of either signed triangle lies inside the window.
For the right one, using e_R<=1-w_R gives

    x_R<=1+a-2c,
    x_R-C<=1+C-2c<0.                                  (FT12)

Here C<=4/5 and c>9/10. The same calculation with w_L proves
x_R^L<C. Whenever Z_Q>0, its left endpoint is below its right
endpoint; (FT11)-(FT12) therefore fit the entire triangle in J.
There is no interval claim when Z_Q<=0, for which the zero gain
bound suffices.

## 4. An exact positive-floor loss

The preceding triangle describes signed gain above a linear baseline.
We now account for its possible continuation past the zero of that
baseline. Let

    z0=u-k, Delta_R=(x_R-z0)_+,
    Delta_L=(x_R^L-(v-h-k))_+.

The genuine positive niche gains obey

    integral_J n >=N45+(Z_R)_+^2/r+(Z_L)_+^2/r
                       -gamma(Delta_R^2+Delta_L^2).     (FT13)

Here is a one-dimensional proof of the required floor inequality.
Write Z>0 for one signed peak and q=x_R-x for the reversed coordinate
on its support. Then 0<=q<=2Z/r=rZ, the baseline is q-Delta, and
the signed triangular gain has height r q up to q=Z/r and height
2Z-rq afterwards. If Delta<=0, the baseline is everywhere
nonnegative and there is no loss.

If 0<Delta<=rZ, its zero lies in the triangle interval. The tent's
right zero has q=k Delta. Before that zero, the lost area is
integral_0^(k Delta) r q dq; between it and the baseline zero, the
lost area is integral_(k Delta)^Delta (Delta-q) dq. These sum to

    [r k^2+(1-k)^2]Delta^2/2=gamma Delta^2.

The tent remains positive throughout the latter interval, including
when that interval crosses its apex; its values at the apex and the
baseline zero are positive.

If Delta>rZ, the baseline is negative throughout the interval. The
remaining positive tent has area

    r[(1+1/r)Z-Delta]_+^2.

When the bracket is nonnegative, subtracting Z^2/r-gamma Delta^2
from this expression gives exactly

    (1+r/2)(Delta-rZ)^2>=0.

When the bracket is negative, Z^2/r-gamma Delta^2 is already
nonpositive, since
gamma(1+1/r)^2-1/r=gamma/2>0. This proves the same inequality
in every case. If Z<=0 its right-hand side is nonpositive and no
positive interval is needed. Applying the lemma on the two disjoint
regions in (FT11) proves (FT13).

The loss admits a simple uniform endpoint bound. Directly,

    Delta_R=[(e_R+1+w_R/k-1/s)/r]_+
           <=(w_R-t)_+,
    Delta_L<= (w_L-t)_+.

Use (FT9) and d0=3/5-t. On 0<=h<=17/50, d0-h/4>0: for example
c<15/16 and r>7/5 give d0>1/8>17/200. Thus

    gamma(Delta_R^2+Delta_L^2)<=L(h),
    L(h):=gamma[(d0-h/4)^2+(d0+3h/4)^2]
          =2gamma d0^2+gamma d0 h+(5/8)gamma h^2.        (FT14)

## 5. Combine exterior and niche payments without double counting

Write Z_R=Z_R^0-delta_L/(2c), Z_L=Z_L^0-delta_R/(2c).
Their undepleted sum satisfies

    Z_R^0+Z_L^0
      =E/2+a/k+(k-2)M+1-1/s-1/c+2k+h/2
      >=S(a,M,h),
    S(a,M,h):=a/k+(k-2)M+3/2+2k-4c+h/4.               (FT15)

Let G0=[(Z_R)_+^2+(Z_L)_+^2]/r. Cauchy-Schwarz, followed by
the elementary two-term square inequality, gives

    S_+<=sqrt(2r G0)+sqrt(r D0/(4c^2)),
    S_+^2<=[2r+r/(4c^2)](D0+G0)=d(D0+G0).             (FT16)

Combining (FT6), (FT10), and (FT13)-(FT16),

    P(U)<=G_h(a,u,v)+L(h),
    G_h:=F_h(a,u,v)-S(a,(u+v)/2,h)_+^2/d.               (FT17)

All niche payments in this calculation are true regions contained in
the original niche. Exterior payment is used once, through D0. The
positive-floor loss is added back explicitly.

## 6. Joint concavity controls all widths and all clipping patterns

Fix h in [0,17/50]. The function G_h is jointly concave in (a,u,v)
on the convex domain a>=37/25, u,v in [a/2,a]. To verify this,
use coordinates (a,M,Dv), where Dv=(u-v)/2. The Hessian of F_h
before clipping terms is

    [ -2,  2,  0 ]
    [  2, -4,  0 ].
    [  0,  0, -2 ]

Each active clip adds the outer product of (-1/2,1,+1) or
(-1/2,1,-1), respectively. Even with both clips active the Hessian is

    [ -3/2,  1, 0 ]
    [    1, -2, 0 ],
    [    0,  0, 0 ]

which is negative semidefinite. Every other clipping pattern subtracts
positive semidefinite outer products from this matrix. First derivatives
match at clipping boundaries. The subtraction of the convex function
S_+^2/d preserves concavity. Throughout this domain the apex is
positive, as checked after (FT5).

Set

    a0=37/25,
    B(a)=a-(a-k)^2/2,
    s0(a)=d a/2-(4c-2),
    m0(a)=(a+k)/2.

For u=v=M in the regime without window clipping and with S>=0,
put m'=M-h/4. Direct
completion of squares in (FT7) and (FT15) gives

    G_h=B(a)-kh/2-h^2/8-2[m'-m0(a)]^2
         -[s0(a)-b(m'-m0(a))-Ah/4]^2/d.                (FT18)

Since 2d+b^2=9, the stationary point at a=a0 is

    m'=m0(a0)+(b/9)[s0(a0)-Ah/4],
    u_*=v_*=m'+h/4.                                   (FT19)

We must check that this point is genuinely unclipped for every allowed
h, so that it is a global support critical point of the full function.
The elementary radical bounds

    140/99<r<99/70, 923/1000<c<231/250

imply

    703/1000<s0(a0)<71/100.                            (FT20)

Indeed the lower and upper intermediate bounds are respectively
5803/8250 and 2477/3500. The right clipping quantity at (FT19) is

    u_*-k-a0/2=-k/2+(b/9)s0(a0)+(1/4-bA/36)h.

Use k>41/99, b<8/5, bA>3/4, and h<=17/50. It is strictly below

    -41/198+(8/5)(71/100)/9+(11/48)(17/50)
      =-129/44000<0.                                  (FT21)

The left clipping quantity is smaller by h. Also s0(a0)-Ah/4>0
by (FT20), A<3/5, and h<=17/50; therefore u_*>a0/2.
Equation (FT21) implies u_*<a0/2+k<a0. Both supports are interior.
The affine S is positive there, because after (FT19) it equals
(2d/9)[s0(a0)-Ah/4]. Thus (FT19) is an actual interior critical
point in (u,v) of the full, differentiable G_h.

Its value is

    K(a0,h)=B(a0)-kh/2-h^2/8-(2/9)[s0(a0)-Ah/4]^2.     (FT22)

Its partial derivative in a, since the other two derivatives vanish,
equals the derivative of the same optimized expression:

    K_a(a0,h)=r-a0-(2d/9)[s0(a0)-Ah/4]<0.              (FT23)

Here a0>r and the bracket is positive. Joint concavity and the
supporting plane at (a0,u_*,v_*) now give

    G_h(a,u,v)<=K(a0,h)  for every a>=a0,              (FT24)

including configurations with one or both 45-degree clips. The
geometry was needed only up to a=8/5, but the supporting-plane
inequality itself holds on the entire enlarged convex domain.

## 7. The resulting scalar bound decreases with tilt

Expanding K(a0,h)+L(h) as a quadratic in h gives constant
B(a0)-(2/9)s0(a0)^2+2gamma d0^2, linear coefficient

    ell=-k/2+A s0(a0)/9+gamma d0,

and quadratic coefficient

    q=-1/8-A^2/72+5gamma/8.

The bounds k>2/5, A<3/5, gamma<3/10, (FT20), and

    d0<3/5-2(923/1000)+99/70=589/3500

yield

    A s0(a0)/9+gamma d0
      <(3/5)(71/100)/9+(3/10)(589/3500)
       =10271/105000<1/10.

Hence ell<-1/10, while q<1/16. On 0<=h<=17/50,

    ell+2qh<-1/10+h/8<=-1/10+17/400<0.                (FT25)

Thus the complete bound, including its positive-floor correction,
is maximized at h=0. Finally

    B(a0)=(62/25)k-72/625,
    2gamma d0^2<(3/5)(589/3500)^2<17/1000.

Use k<29/70 and s0(a0)>703/1000 to obtain

    P(U)<(62/25)(29/70)-72/625
           -(2/9)(703/1000)^2+17/1000
         =25811237/31500000<41/50.                     (FT26)

The final rational gap is 18763/31500000>0. This proves (FT3).

This is a scalar exclusion for actual canonical caps satisfying the
endpoint law. It assumes neither source unit curvature nor a finite
angle stationary optimizer. It lowers the remaining width ceiling
to C<37/50; it does not by itself establish the missing unit-curvature
condition below that ceiling.
