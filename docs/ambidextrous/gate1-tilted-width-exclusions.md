# Global tilted-cap width exclusions and the coupled width–height bound

**October 10, 2026. Written proofs, independently audited within this research session. Gate 1 remains open.**

This note excludes both extreme width ranges for a possible tilted canonical
maximizer of the actual spatial score. It also gives an exact joint restriction
on the remaining width and tilt. The argument uses ordinary charged exterior
area and three genuine niche angles; the niche being bounded is still the
**complete continuous-angle positive two-ray niche**.

Normalize the projection and its middle half as
\[
I=[-a,a],\qquad J=[-a/2,a/2],\qquad a=W/2=2C,
\]
and, after reflection, write
\[
A(-a/2)=1-h,\qquad A(a/2)=1.
\]
Here **a is the half-width**, and **h is the middle-endpoint height difference**.
The score is
\[
\mathcal P(U)=\int_{I\setminus J}A(x)\,dx-\int_Jn_U(x)\,dx.
\]
The global reductions [SD](gate1-spatial-dual-height-width-compactness.md),
[MID](gate1-global-middle-chord-canonicalization.md),
[TF](gate1-spatial-tilted-facet-pinning.md), and
[LH](gate1-global-positive-pressure-and-wing-identity.md) already supply a
canonical global maximizer of this form with a<3, h<1/2, and both endpoint
pressures strictly positive.

## Results and their precise hypotheses

| Result | Width range | Additional premises | Conclusion |
| --- | --- | --- | --- |
| TS1 and GAP1 | \(0<a\le1001/1000\) | Affine middle roof; higher endpoint height one | \(\mathcal P<41/50\) |
| TW2 | \(8/5\le a<3\) | \(0\le h<1/2\); exact positive-pressure endpoint laws | \(\mathcal P<41/50\) |
| INT1 | \(1\le a\le8/5\) | \(0\le h<1/2\); no endpoint law needed | Exact upper bound \(\mathcal P\le B_*(a,h)\) below |

Put r=\(\sqrt2\) and k=\(\sqrt2-1\). The intermediate bound is
\[
\boxed{B_*(a,h)
=1-\frac{(a-\sqrt2)^2}{2}
-\frac{2a}{4a-h}\left(\sqrt2-1+\frac h2\right)^2.}
\tag{INT1}
\]
Since the reference value satisfies \(M/2>41/50\), every remaining tilted
canonical global maximizer necessarily obeys
\[
\boxed{\frac{1001}{1000}<a<\frac85,\qquad0<h<\frac{17}{50},}
\]
\[
\boxed{(a-\sqrt2)^2+
\frac{4a}{4a-h}\left(\sqrt2-1+\frac h2\right)^2\le\frac9{25}.}
\tag{TW-INT}
\]
Equivalently, its full width lies in \(1001/500<W<16/5\), or
\(1001/2000<C<4/5\). This is a genuine global-domain reduction.
It does not prove the sharp score on the remaining domain.

The short proof extends [SW1](gate1-horizontal-short-width-exclusion.md)
while retaining both effects of tilt on the attached walls. The wide proof
extends the three-angle area payment in
[HW](gate1-horizontal-maximizer-sharp-value.md) while retaining the tilted
outer support constraint and the exact endpoint laws. Their estimates do
not assume symmetry, a prescribed contact chart, unit source curvature,
absence of a top overhang, or connectivity of the full niche.

## Part A. Short widths, including every tilted middle facet

### Statement

Let U be a downward convex cap of height one with projection I=[-a,a],
0<a<=1, and upper roof A affine on J=[-a/2,a/2]. Suppose the higher
middle endpoint has height one. After reflection write

    A(-a/2)=1-h, A(a/2)=1, 0<=h<1.

Let n be the actual full continuous-angle positive two-wall niche. Then

    P(U):=integral_(I\J) A - integral_J n <41/50.               (TS1)

Thus the entire short tilted canonical maximizing range C=W/4<=1/2
is excluded. The stronger assumed bound h<1/2 is not needed here.

Put

    k=sqrt(2)-1, r=sqrt(2), c=cos(pi/8), s=sin(pi/8),
    K=1/k, Gamma=1/[2k(1-k)]=K c^2=(4+3r)/4,
    t0=8/25, eta=2/25, L0=t0-k+eta/k=(12-23k)/25>0.

We use k^2=1-2k, s/c=k, 1/(kc)=1/s, K(1-k)=r,
2/5<k<29/70<3/7<1/2, and the two elementary inequalities

    1-1/c+k^2>eta,
    1/c+K eta<32/25.                                           (TS2)

For completeness, after squaring positive sides the first comparison
follows from r<1777/1249, and the second from r>231/167. The simpler
bounds r<99/70 and r>24/17 imply them.

### 1. Raise the left wing to a genuine horizontal-middle cap

Define a new roof

    Ahat(x)=A(x)+h for -a<=x<=-a/2,
    Ahat(x)=1      for -a/2<=x<=a/2,
    Ahat(x)=A(x)   for  a/2<=x<=a.

This is a concave height-one roof. The old left-wing slopes are at
least h/a, and the old right-wing slopes are nonpositive; replacing
the intervening slope h/a by zero preserves the required ordering.
All old left-wing heights are at most 1-h, so raising them by h
preserves the height bound. Let Uhat be this actual cap. Its charged
area satisfies the exact identity

    O(U)=O(Uhat)-a h/2.                                         (TS3)

The first-quarter supports f of U and Uhat are identical: the old
point (a/2,1) dominates every raised left-wing point for any upper
normal with nonnegative horizontal component. If ghat denotes Uhat's
companion support, the actual companion support of U is

    g_U(t)=max(ghat(t)-h cos t, cos t-(a/2)sin t).

Indeed the entire right wing is dominated by (a/2,1), while a linear
middle facet contributes only its endpoints. On J the wall associated
with the displayed high-point term has height

    1-sec t+(x-a/2)tan t<=0.

Consequently the distributive identity for min and max proves the
exact all-angle positive-niche formula

    n_U(x)=max(0,sup_t min(Rhat_t(x),Shat_t(x)-h)), x in J.       (TS4)

No assertion that raising the wing improves P is made or needed.

Define the lifted cap's actual 45-degree support parameters

    u=r H_Uhat(pi/4)-1, v=r H_Uhat(3pi/4)-1,
    M=(u+v)/2, d=(u-v+h)/2.

Since Uhat has height one on J,

    a/2<=u,v<=a.

It lies below A0=min(1,1+u-x,1+v+x), with exact charged area

    O0=a-[(a-u)^2+(a-v)^2]/2.

Write D=integral_(I\J)(A0-Ahat)>=0. Equation (TS4) gives the
actual 45-degree tent on J as

    n45(x)=[min(u-k-x,v-h-k+x)]_+.

### 2. Exact 45-degree concavity, with a shifted critical point

Assume for contradiction P>=41/50. The two charged wings have roof
bounded above by 1-h and 1 respectively, so P<=a(1-h/2). Hence

    a>=41/50, h<=9/25<a/2.

Thus the apex d lies in J for every (u,v) in [a/2,a]^2. Direct
integration gives

    N45=integral_J n45
       =(M-h/2-k)_+^2
          -[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.

Combining with (TS3),

    P<=F_h(a,u,v)-D,
    F_h=a-[(a-u)^2+(a-v)^2]/2-a h/2-(M-h/2-k)_+^2
          +[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.                 (TS5)

For fixed a,h this is concave in (u,v) on the whole square. When
M-h/2>k, its Hessian has diagonal entries -3/2 plus the corresponding
clipping indicator and off-diagonal entries -1/2, always nonpositive.
When M-h/2<=k the clipping terms vanish because the apex is in J,
and the Hessian is -Id. First derivatives match at the boundaries.

The critical point

    u=v=(a+k+h/2)/2

is interior to the square, has positive apex height, and has no
clipping. These facts follow already from a>=41/50 and h<=9/25.
Therefore

    F_h<=B(a)-k h/2-h^2/8,
    B(a):=a-(a-k)^2/2<=B(1)=2k.                              (TS6)

As in the horizontal short-width argument, B(9/10)<41/50, so
a>9/10. Also, if h>=1/24, then (TS6) gives

    P<=(95/48)k-1/4608<26441/32256<41/50.

Consequently every hypothetical high-score cap satisfies

    a>9/10, h<1/24,
    D<=2k-41/50-k h/2-h^2/8<3/350.                          (TS7)

#### 2a. The precise stability bounds needed for the two tail payments

In fact the high-score hypothesis forces

    u-a/2<t0+h/4, v-a/2<t0+h/4,
    m:=M-h/4>16/25.                                        (TS8)

For the first bound, maximize the concave F_h on the additional
half-square u>=a/2+t0+h/4. Its constrained critical point is

    u=a/2+t0+h/4,
    v=a/2+(2k-t0)/3+h/4.

Both clipping terms vanish there. The v derivative is zero and the
u derivative is (2k-4t0)/3<0, giving the global concave KKT conditions.
The maximum is

    B(a)-k h/2-h^2/8-(2/3)(t0-k/2)^2
       <=(9550k-881)/3750<41/50.                            (TS9)

The last strict comparison follows from r<577/408, or k<169/408.
The other bound follows by the same constrained KKT calculation with
u,v exchanged; the absence of clipping makes the local formulas equal,
even though F_h is not globally symmetric. All displayed KKT points
lie in the square because a>9/10 and h<1/24.

These bounds imply both actual 45-degree clipping terms vanish:
t0+h/4<1/3<k. Also M-h/2>=a/2-h/2>9/20-1/48>k.
Put x=u-h/4,y=v-h/4, whose mean is m. Then direct expansion of
(TS5), in this nonclipped regime, gives

    F_h=a-(a-m)^2-(m-k)^2-((x-y)/2)^2-k h/2-h^2/8.           (TS10)

If m<=1/2, the identity a-(a-m)^2=m+1/4-(a-m-1/2)^2 bounds
this by 3/4. If 1/2<m<=16/25, the symmetric part in (TS10)
increases first with a<=1 and then with m<=16/25. Its upper value
is (2050k-337)/625<41/50, using k<29/70. This proves the final
assertion of (TS8).

### 3. The ordinary exterior deficit pays for two complete cut triangles

Use the lifted cap's actual near-vertical deficits

    delta_L=c+s v-H_Uhat(5pi/8)>=0,
    delta_R=c+s u-H_Uhat(3pi/8)>=0.

The genuine height-one points at the J endpoints give

    delta_L<=s(v-a/2), delta_R<=s(u-a/2).

At (-v,1), a support cut by delta_L removes a triangle whose two
horizontal lengths are delta_L/s along the flat face and
delta_L/(c-s) along the outer 45-degree face. If the latter length
does not exceed a-v, the whole triangle is in the charged left wing
and has area

    delta_L^2/[2s(c-s)]=K delta_L^2.

This containment must hold. Otherwise cut only by
delta0=(c-s)(a-v)<delta_L. The resulting whole charged triangle
already gives

    D>=K delta0^2=(a-v)^2/r.

But (TS7)-(TS8) imply

    a-v>a/2-t0-h/4>13/100-1/96=287/2400>7/60,

so D>49/5400>3/350, a contradiction. The mirrored right cut
triangle obeys the same argument. They lie in opposite wings, hence

    D>=K(delta_L^2+delta_R^2).                              (TS11)

### 4. Two actual extra niche tails, with the tilt retained

Set

    eta_L=eta-(1-k)h>0,
    E_L=(eta_L-delta_L/c)_+,
    E_R=(eta-delta_R/c)_+.

#### Left additional tail

The actual pi/8 tent contains the lower second wall

    1-1/c+k v-delta_L/c-h+kx

by (TS4). At the left 45-degree zero x0=k-v+h, its height is

    1-1/c+k^2-delta_L/c-(1-k)h.

If E_L>0, (TS2) shows this dominates the line

    D_L(x)=E_L+k(x-x0).

If E_L=0, the claimed extra-area bound below is nonpositive and
already follows from nonnegativity; no wall assertion is needed.

An attaining point for u satisfies x+y=1+u and y<=1, hence x>=u.
It lies on the unchanged right portion of Uhat, so the actual first
wall has the lower bound

    R_pi/8(x)>=1-1/s+(u-x)/k.

At x_R=x0+E_L/(1-k), this dominates D_L exactly when

    2M-h>=1/c+K E_L.                                        (TS12)

The condition holds: 2M-h=2m-h/2>32/25-h/2, while
E_L<=eta-(1-k)h and K(1-k)=r>1/2. Thus (TS2) makes the
right side strictly smaller. For x<=x_R the companion gap only
increases.

The end x_R lies before the 45-degree apex d, since

    x_R-d=k-m+h/4+E_L/(1-k)
          <=k-m+eta/(1-k)-3h/4<0.

Here k+eta/(1-k)=(26k+3)/25<16/25. Therefore the extra niche
area contains the usual triangle with peak E_L at x0, left slope k
and right downward slope 1-k. Its full area is Gamma E_L^2.

#### Right additional tail and its actual companion wall

In the reflected coordinate y=-x the right 45-degree zero is
y0=k-u. The pi/8-type near-vertical wall on this side is unchanged,
so its analogous peak lower bound is E_R. Apply this wall construction
only when E_R>0; if E_R=0 the nonnegative extra-area bound suffices,
exactly as for the left tail. A point attaining v for
Uhat can be chosen on the left wing. Its reflected abscissa is at
least v; lowering it by h gives an actual point of U. Hence

    H_U(7pi/8)>=s(1-h)+c v.

This supplies the genuine reflected companion-wall bound

    R_ref(y)>=1-h-1/s+(v-y)/k.

At y_R=y0+E_R/(1-k), it dominates the near-vertical tail exactly
when

    2M-kh>=1/c+K E_R.                                       (TS13)

Indeed 2M-kh=2m+(1/2-k)h>32/25, while E_R<=eta. Equation
(TS2) applies. Also y_R lies before the reflected apex -d:

    y_R+d=k-m+h/4+E_R/(1-k)<0,

because k+eta/(1-k)<99/175, h/4<1/96, and
99/175+1/96<16/25. This tail is therefore disjoint from the left
tail, being on the opposite side of d.

#### Window clipping of the two tails

Both 45-degree zeros are in J, by (TS8):

    x0+a/2>k-t0+3h/4>0,
    y0+a/2>k-t0-h/4>0.

Only the outer tips of the two extra triangles can leave J. Their
omitted horizontal lengths are bounded respectively by

    (v-h-a/2-k+E_L/k)_+<=L0+h/4,
    (u-a/2-k+E_R/k)_+<=L0+h/4.

The slope of each omitted triangle is k, so the sum of the omitted
areas is at most k(L0+h/4)^2. We conclude that the actual full
positive niche satisfies

    integral_J n>=N45+Gamma(E_L^2+E_R^2)-k(L0+h/4)^2.          (TS14)

The zero-peak cases are covered by the same lower bound. No overlap
or angular-connectivity assertion concerning other niche pieces is used.

### 5. The final scalar upper bound strictly decreases with tilt

For every eta_i>=0 and delta>=0, Gamma=K c^2 gives

    K delta^2+Gamma(eta_i-delta/c)_+^2>=Gamma eta_i^2/2.

Apply this to eta_L and eta, using (TS11) and (TS14), then use
the sharp 45-degree maximum (TS6). It yields

    P<=H(h):=2k-kh/2-h^2/8
                -(Gamma/2)[(eta-(1-k)h)^2+eta^2]
                +k(L0+h/4)^2.

Its expansion is

    H(h)=H(0)+[(7/10)k-19/50]h
                   +[-1/8-Gamma(1-k)^2/2+k/16]h^2.          (TS15)

The linear coefficient is negative already from k<1/2, and the
quadratic coefficient is negative since k/16<1/8. Thus H(h)<=H(0)
for h>=0. The same exact simplification as in the horizontal proof is

    H(0)=2k-Gamma eta^2+k L0^2
         =(5140k-1617)/625<3587/4375<41/50,                  (TS16)

using k<29/70. This contradicts the assumed P>=41/50 and proves
(TS1).

The proof uses three genuine angles and ordinary exterior area only.
The lifting map is an explicit way of recording tilt, not a claim of
monotonicity for the original score. In particular it retains the
lower companion height on the right added tail and the moving 45-degree
zero on the left tail; both effects are included in (TS12)-(TS15).


## Part B. The exact positive width gap above two

### Statement

The short tilted theorem TS1 remains true with

    0<a<=a_max:=1001/1000,

under exactly the same geometric hypotheses. Consequently every remaining
canonical tilted global maximizer has

    C=W/4>1001/2000,   4C-2>1/500.                              (GAP1)

The original proof already treats a<=1. It is enough to check 1<=a<=a_max.
Keep k,r,c,s,K,Gamma,eta=2/25 from that proof, and change only

    t0=323/1000,  L0=t0-k+eta/k=(483-920k)/1000.

The computations below list every changed numerical premise. All geometric
and actual-niche arguments of TS3-TS16 are unchanged with these constants.

### 1. High-score stability in the extra interval

Suppose P>=41/50 and 1<=a<=1001/1000. The immediate outer-area bound
P<=a(1-h/2) gives

    h<=362/1001<a/2.

Thus the global concavity of the 45-degree relaxation still applies.
The same interior critical point has positive apex and no clipping, and

    F_h<=B(a)-kh/2-h^2/8,
    B(a)<=B(a_max)=(2001/1000)k-1/2000000.                    (GAP2)

The right side decreases with h. At h=1/23 it is, using k<29/70,

    <=6071014497/7406000000<41/50.

Therefore h<1/23. Also

    D<=B(a_max)-41/50
       <125793/14000000<9/1000.                              (GAP3)

The two shifted constrained KKT points are exactly those in TS9, with
t0=323/1000. Their largest possible value is

    B(a_max)-(2/3)(t0-k/2)^2
       =(7649/3000)k-1417319/6000000<41/50,                  (GAP4)

using k<169/408. All the points lie inside [a/2,a]^2 and have no
clipping: t0+h/4<17/50<k, and the other coordinate is smaller.
Thus a hypothetical high score forces

    u-a/2<t0+h/4,  v-a/2<t0+h/4.                             (GAP5)

Now the 45-degree tent is unclipped, with positive apex, and the shear
identity TS10 holds. Its symmetric part

    a-(a-m)^2-(m-k)^2

increases with m for m<=16/25 and a>=1. Set m=16/25 first; the resulting
expression increases with a<=a_max. Its maximum is

    a_max-(a_max-16/25)^2-(16/25-k)^2
       =(82/25)k-538921/1000000
       <5739553/7000000<41/50.                              (GAP6)

The strict rational bound uses k<29/70 and k^2=1-2k. Hence
m>16/25, as required by both genuine companion-wall checks.

### 2. Every triangle still fits

For the exterior cut triangles, (GAP5) gives

    a-v>a/2-t0-h/4>=1/2-323/1000-1/92>23/200,

and the same holds for a-u. A cut that reaches the vertical endpoint
would therefore force

    D>(23/200)^2/r>3703/400000>9/1000,

using r<10/7. This contradicts (GAP3). Therefore TS11's full two-cut
payment D>=K(delta_L^2+delta_R^2) still holds.

The left effective tail height eta_L=eta-(1-k)h remains positive,
since h<1/23<eta. The two actual companion inequalities TS12-TS13
are unchanged because m>16/25 and eta is unchanged. The right-tail
apex check uses

    k+eta/(1-k)<99/175,  h/4<1/92,
    99/175+1/92<16/25.

Both tail peaks remain inside J because

    k-t0-h/4>2/5-323/1000-1/92>0.

The two clipping lengths are again at most L0+h/4. Thus TS14 holds
with the updated L0.

### 3. The final scalar payment

With the new upper-width value B(a_max), the argument in TS15 yields

    P<=B(a_max)-kh/2-h^2/8
          -(Gamma/2)[(eta-(1-k)h)^2+eta^2]
          +k(L0+h/4)^2.

Its linear coefficient in h is

    (1403/2000)k-19/50<0,

and its quadratic coefficient is unchanged and negative. The maximum is
therefore at h=0. Exact use of k^2=1-2k gives

    P<=B(a_max)-Gamma eta^2+kL0^2
       =(8238929/1000000)k-5185441/2000000
       <334549037/408000000<41/50,                            (GAP7)

using k<169/408, a consequence of 577^2-2*408^2=1. The final strict
rational gap is

    41/50-334549037/408000000=10963/408000000>0.

This contradicts the high-score hypothesis, extending the global short
tilted theorem and proving GAP1. No endpoint-pressure or curvature premise
has been introduced.


## Part C. Wide widths with the actual endpoint law

### Statement and notation

Let U be a downward convex cap of height one, with projection
I=[-a,a], 8/5<=a<3, and upper roof A affine on J=[-a/2,a/2].
After reflection suppose

    A(-a/2)=1-h,   A(a/2)=1,   0<=h<1/2.

Let n be its full continuous-angle positive niche roof, and put
e_R=A(a), e_L=A(-a), n_+=n(a/2), n_-=n(-a/2). Assume the actual
positive-pressure endpoint laws

    e_R=1/2+h/4+(3n_+-n_-)/4,
    e_L=1/2-3h/4+(3n_--n_+)/4.                    (TW1)

Then

    P(U)=integral_(I\J) A - integral_J n <41/50.   (TW2)

More precisely, a hypothetical P(U)>=41/50 is forced below
261719/320000<41/50. For canonical global maximizers the premises
come from height/width compactness, the middle-affine reduction,
top localization, low-height exclusion, and positive EP. The theorem
therefore excludes the whole remaining canonical width range
C=W/4=a/2>=4/5, including tilted caps.

Write H_U(theta) for upper support, and use the constants

    r=sqrt(2), k=r-1, c=cos(pi/8), s=sin(pi/8).

We use

    s/c=k, k+1/k=2r, 1+k=r, k^2=1-2k,
    1/s+1/c=4c, 1/s-1/c=4s, 1/(rc)=2s,
    1/(2sc)=r,   2/5<k<29/70,   s>3/8.

### 1. The tilted 45-degree majorant

Set

    z=h/a,  L(x)=1-h/2+zx,
    u=r H_U(pi/4)-1,  v=r H_U(3pi/4)-1,
    m=(u+v)/2, d=(u-v)/2, w_R=a-u, w_L=a-v.

Concavity gives A<=L on all I, and the unit-height condition gives
A<=1. The actual J endpoint points and these two global upper
bounds imply

    a/2<=u<=a,  a/2-h<=v<=a-3h/2,
    u>=a+e_R-1, v>=a+e_L-1.                       (TW3)

For the bound on v, the function -x+min(1,L(x)) decreases on I
because z<1. Define

    q=(v+h/2)/(1-h/a),   a/2<=q<=a.

The line 1+v+x meets L at x=-q. The cap is below

    Abar(x)=min(1,L(x),1+u-x,1+v+x).

Its exact charged exterior area is

    Obar=a-(5/8)ah
           -1/2[(a-u)^2+(a-v-3h/2)^2/(1-h/a)].    (TW4)

Indeed, the right charged wing is the unit rectangle minus the
usual 45-degree triangle. The integral of L on the left charged
wing is a/2-5ah/8; the left triangle removed from it has height
a-v-3h/2 and base (a-v-3h/2)/(1-h/a).

The endpoint laws imply

    E:=e_R+e_L=1-h/2+(n_++n_-)/2>=1-h/2.

Since e_R<=1-w_R and e_L<=1-w_L, we obtain

    w_R>=0, w_L>=3h/2, w_R+w_L<=1+h/2,
    m>=a-1/2-h/4.                                 (TW5)

The 45-degree niche is the actual tent

    n45(x)=[min(u-k-x,v-k+x)]_+.

Its apex d lies in J: u-v<=1<=a follows from v>=a-1 and u<=a;
v-u<=a/2-3h/2<=a follows from (TW3). Also m>=a-5/8>=39/40>k.
Thus, writing b0=a/2-k,

    N45:=integral_J n45
      =(m-k)^2-1/2[(b0-w_R)_+^2+(b0-w_L)_+^2].     (TW6)

### 2. A perspective tangent pays both 45-degree clipping terms

For any t>=b0 with 3/2-t/a>=0, one has

    w^2-(b0-w)_+^2 >=2tw-t^2,

    (w-3h/2)^2/(1-h/a)-(b0-w)_+^2
        >=2tw-t^2+(-3t+t^2/a)h.                   (TW7)

For the second inequality use the exact identity

    (w-3h/2)^2/(1-h/a)
       =2tw-t^2+(-3t+t^2/a)h
          +[w-t-h(3/2-t/a)]^2/(1-h/a).

If w<b0<=t, the last nonnegative square is at least (b0-w)^2:
its numerator has absolute value at least t-w, and 1-h/a<=1.
If w>=b0 the clipping term is zero. The first inequality is the
same argument with h=0. In particular this handles clipping
without a symmetry assumption on u and v.

Let F=Obar-N45. Equations (TW4)-(TW7) give

    F<=a-2t(a-m)+t^2-(m-k)^2
           -[(5/8)a-(3/2)t+t^2/(2a)]h.             (TW8)

When a<=1+2k choose t=1/2. Then

    F<=m+1/4-(m-k)^2-D(a)h,
    D(a)=(5/8)a-3/4+1/(8a)>=21/64,                (TW9)

where D is increasing for a>=8/5.

#### 2a. Preliminary consequences of a hypothetical P>=41/50

All other niche portions and the deficit Abar-A have nonnegative
area, so P<=F. We now prove that a high-scoring cap must satisfy

    a<9/5,    h<1/4,    a+h<37/20.                (TW10)

First suppose 9/5<=a<=1+2k. The right side of (TW9) decreases
with m throughout m>=a-1/2-h/4, since m>k+1/2. Substitute this
lower bound for m. The resulting derivative with respect to h is

    -a/8+1/4-k/2-1/(8a)-h/8<0.

At h=0 its value is a-1/4-(a-1/2-k)^2, which decreases for a>=9/5.
Consequently

    P<=(23/5)k-57/50<134/175<41/50.               (TW11)

If instead 1+2k<=a<3, choose t=b0 in (TW8). This gives

    F<=a-(3/4)a^2+ak+am-m^2-[k+k^2/(2a)]h.

It decreases with m>=a-1/2-h/4 because a-2m<0 there. After that
substitution the upper bound becomes

    (3/2)a-(3/4)a^2+ak-1/4
      +[(a-1)/4-k-k^2/(2a)]h-h^2/16.

The h=0 part decreases for a>=1+2k, taking value 3k-1/2 at that
left endpoint. Since a<3 and h<1/2, the remaining part is at most
(1/2-k)/2. Therefore

    P<=(5/2)k-1/4<11/14<41/50.                    (TW12)

This proves a<9/5. We may use (TW9) and D>=21/64. Because its
right side decreases with m>=11/10-h/4, it gives

    P<=27/20-h/4-(11/10-h/4-k)^2-(21/64)h.

This expression has derivative -9/320-k/2-h/8<0. If h>=1/4,

    P<=(163/40)k-2787/3200
        <18307/22400<41/50.                       (TW13)

Finally, if a+h>=37/20 and h<1/4, (TW5) implies
m>=27/20-5h/4>=83/80>k+1/2. Hence (TW9) gives

    P<=8/5-(101/64)h-(27/20-k-5h/4)^2
      <=8/5-(101/80)(27/20-k)+10201/25600
      =7529/25600+(101/80)k
      <146431/179200<41/50.                       (TW14)

The middle inequality completes the square and is valid for all
real h. This proves (TW10). All rational comparisons in (TW11)-
(TW14) use only k<29/70.

For the rest of the proof assume P>=41/50 and thus (TW10).

### 3. Near-vertical support deficits have ordinary exterior payment

The right supporting direction 3pi/8 touches Abar at (u,1).
The left direction 5pi/8 touches Abar at (-q,L(-q)); here
z< (1/4)/(8/5)=5/32<k. Set

    Hbar_L=c(1-h/2)+(s-cz)q,
    delta_L=Hbar_L-H_U(5pi/8),
    delta_R=c+s u-H_U(3pi/8).

They are nonnegative. The actual J endpoint points yield

    delta_R<=s(u-a/2),
    delta_L<=(s-cz)(q-a/2).                        (TW15)

On the left affine segment x=-q+t, the new support line lies
below Abar by delta_L/c-(k-z)t. Equation (TW15) fits the entire
cut triangle in the charged interval [-q,-a/2]. Its area is

    delta_L^2/[2c^2(k-z)]>=r delta_L^2.

The right flat-piece triangle analogously has area r delta_R^2.
The two lie in opposite charged wings, so

    D:=integral_(I\J)(Abar-A)
          >=r(delta_L^2+delta_R^2).                (TW16)

For comparison with the horizontal formulas, define the exact
extra left support deficit

    tau=(c+s v-Hbar_L)/c
       =(1-k)h(1/2+q/a),
    0<=tau<=(3/2)(1-k)h.                          (TW17)

### 4. Two genuine niche half-triangles, truncated at baseline zeros

At the actual angle pi/8 the second wall is b_R+kx, with

    b_R=1-1/c+k v-delta_L/c-tau.

The actual endpoint (a,e_R) gives the companion-wall lower bound
B_R-x/k, where

    B_R=e_R+a/k-1/s.

Thus the full niche contains the positive part of
min(b_R+kx,B_R-x/k). Against the right branch u-k-x of n45, set

    x_L^R=(u-k-b_R)/r,
    x_*^R=(B_R-b_R)/(2r),
    Z_R=(B_R+b_R)/2-u+k=r(x_*^R-x_L^R).

Reflection, using the actual angle 3pi/8, gives the left-side
quantities in the coordinate y=-x:

    b_L=1-1/c+k u-delta_R/c,  B_L=e_L+a/k-1/s,
    x_L^L=(v-k-b_L)/r,
    x_*^L=(B_L-b_L)/(2r),
    Z_L=(B_L+b_L)/2-v+k=r(x_*^L-x_L^L).

The right and reflected-left 45-degree apices are d and -d.
Their crossover offsets are

    x_L^R-d=km+2s-1+(delta_L/c+tau)/r>0,
    x_L^L+d=km+2s-1+delta_R/(rc)>0.                (TW18)

Use m>=a-1/2-h/4>83/80, k>2/5, s>3/8 for the signs.

The actual low J point gives b_R>=1-h-1/c+k a/2. Consequently
x_*^R<=a/2 follows from

    e_R+h+alpha a<=1+4s,  alpha=(3-r)/2.

Indeed e_R<=1, and (TW10) gives

    h+alpha a<alpha*(37/20)+(1-alpha)/4
             =53/20-4r/5<4s.                     (TW19)

For the last comparison, both sides are positive and
16s^2-(53/20-4r/5)^2=(-121+96r)/400>0.
On the other side the actual high J point gives
b_L>=1-1/c+k a/2; thus x_*^L<=a/2 follows from
e_L+alpha a<=1+4s. This holds from e_L<=1,
alpha a<(4/5)(9/5)=36/25<3/2<4s.

The tentative half-triangle might extend past the zero of its
45-degree baseline. Retain only the part before that zero. Put

    F_R=r(u-k-x_L^R),   F_L=r(v-k-x_L^L),
    Zhat_R=min(Z_R,F_R), Zhat_L=min(Z_L,F_L).

If Zhat_R>0, integrate the linear gain r(x-x_L^R) from x_L^R
to min(x_*^R,u-k). Equations (TW18)-(TW19) place the interval in J,
to the right of d, and where the 45-degree baseline is positive.
The actual two-wall tent has the requisite ascending wall there.
This gives genuine niche gain Zhat_R^2/(2r). If Zhat_R<=0, the
zero lower bound requires no interval assertion. Reflection gives
the same statement on the left, disjoint from the right interval.
Therefore

    integral_J n >=N45+[(Zhat_R)_+^2+(Zhat_L)_+^2]/(2r). (TW20)

#### 4a. Bound the loss caused by the baseline truncation

Let ell_R=(Z_R-F_R)_+, ell_L=(Z_L-F_L)_+, so that
Zhat_R=Z_R-ell_R and Zhat_L=Z_L-ell_L exactly.
The actual J support bounds used in (TW19) also imply

    2ell_R <=[e_R+2r w_R+h-(3k/2)a-1-4s+2rk]_+,
    2ell_L <=[e_L+2r w_L  -(3k/2)a-1-4s+2rk]_+.   (TW21)

For example, 2(Z_R-F_R)=B_R-b_R-2r(u-k), and substitute
b_R>=1-h-1/c+k a/2. The coefficient of a is
1/k-k/2-2r=-3k/2. The left formula is its reflection, without h.

The unit-height box yields

    0<=n(+-C)<=1-sqrt(1-C^2),  C=a/2<9/10.

For completeness, at x=C the first wall is bounded by
1+(C cos(t)-1)/sin(t); its supremum is 1-sqrt(1-C^2),
and the other endpoint follows by reflection. This is below 2/3.
Together with (TW1), it gives

    e_R>=1/3+h/4, e_L>=1/3-3h/4,
    w_R<=2/3-h/4, w_L<=2/3+3h/4.                 (TW22)

The horizontal fitting constant is strictly negative:

    K:=(2r-1)*2/3-(12/5)k-4s+2rk<0.              (TW23)

An entirely rational verification uses r<10/7 and k<3/7 to bound
(2r-1)*2/3<26/21, whereas (12/5)k+4s-2rk>
3/2-48/245=639/490>26/21. Here 12/5-2r<0 and s>3/8.

Now use e_Q<=1-w_Q, a>=8/5, and (TW22) in (TW21). It follows that

    ell_R<=(5-2r)h/8,
    ell_L<=3(2r-1)h/8,
    ell_R+ell_L<=(1+2r)h/4<=h.                   (TW24)

The inequalities include h=0. No assumption on the sign of the
untruncated peak is made.

### 5. Combine exterior area and additional niche area

Write Z_R=Z_R^0-delta_L/(2c)-tau/2 and
Z_L=Z_L^0-delta_R/(2c). Direct addition gives

    Z_R^0+Z_L^0
       =E/2+a/k+(k-2)m+1-1/s-1/c+2k.

Use E>=1-h/2, (TW17), and

    1/k>12/5, k-2>-8/5, 3/2+2k-4c>-11/8.

The last inequality follows by squaring 4c<7/8+2r, since the
difference of the squared sides is 49/64-r/2>0. Thus, with

    S(a,m)=(12/5)a-(8/5)m-11/8,

we have

    Z_R+Z_L >= S(a,m)-(7/10)h-(delta_L+delta_R)/(2c).

The coefficient of h before the weakening to 7/10 is
1/4+3(1-k)/4=1-3k/4<7/10. By (TW24),

    Zhat_R+Zhat_L
       >=Q(a,m,h)-(delta_L+delta_R)/(2c),
    Q(a,m,h):=S(a,m)-(17/10)h.                    (TW25)

Set D0=r(delta_L^2+delta_R^2) and
G0=[(Zhat_R)_+^2+(Zhat_L)_+^2]/(2r). Cauchy-Schwarz yields

    Q_+<=sqrt(4r G0)+sqrt(r D0/(4c^2)),
    (Q_+)^2<=[4r+r/(4c^2)](D0+G0)<=8(D0+G0).

The last coefficient is strictly below 8, using r<3/2 and c^2>3/4;
the weak product inequality covers D0+G0=0. Equations (TW16),
(TW20), and (TW9) therefore imply

    P<=Gtilde(a,m,h)
       :=m+1/4-(m-k)^2-(21/64)h-[Q(a,m,h)_+]^2/8. (TW26)

### 6. One supporting plane closes the wide tilted range

The function Gtilde is jointly concave in (a,m,h), since it is a
linear function minus a square in m and the convex positive square
of an affine function. At

    (a0,m0,h0)=(8/5,11/10,0), Q=141/200>0,

its exact gradient is

    G_a=-423/1000,
    G_m=2k-459/500<0,
    G_h=-57/2000.

The feasible displacement furnished by (TW5) decomposes as

    (a-a0,m-m0,h)
       =(a-a0)(1,1,0)
          +(m-a+1/2+h/4)(0,1,0)
          +h(0,-1/4,1).

Each coefficient is nonnegative. The three directional derivatives
at the base point are strictly negative; for the tilt direction,

    G_h-G_m/4=201/1000-k/2<0,

using k>41/100 (equivalently sqrt(2)>141/100). Hence the supporting
plane of the concave Gtilde gives

    P<=Gtilde(a,m,h)<=Gtilde(a0,m0,0)
      =(21/5)k-295081/320000
      <261719/320000<41/50.                        (TW27)

This contradicts the high-score hypothesis and proves (TW2).

Every niche payment above is an ordinary region in one of the
three actual two-wall tents at pi/8, pi/4, 3pi/8. In particular,
the proof retains the possible high-side top overhang, includes
the full niche through its lower-bound direction, and does not
apply endpoint stationarity to an artificial finite-angle cap.

## Part D. Exact intermediate-width and tilt restriction

### Statement

Let U be a downward convex cap of height one with projection I=[-a,a],
1<=a<=8/5, and affine middle roof on J=[-a/2,a/2], with

    A(-a/2)=1-h, A(a/2)=1, 0<=h<1/2.

Then, for the full continuous-angle positive niche,

    P(U)<=B_*(a,h)
       :=a-(5/8)ah-2(a-3h/4-k)^2/(4-h/a)
        =1-(a-r)^2/2-[2a/(4a-h)](k+h/2)^2,                  (INT1)

where r=sqrt(2), k=r-1. No endpoint law or curvature assumption is used.

In particular any such cap with P>=41/50 satisfies

    (a-r)^2+[4a/(4a-h)](k+h/2)^2<=9/25,                     (INT2)
    h<17/50.                                                (INT3)

Combined with the already audited short positive-gap and wide theorems,
every remaining canonical global maximizer has

    1001/1000<a<8/5, 0<h<17/50,

and obeys the exact coupled inequality INT2.

### 1. The lifted cap and its mandatory extra exterior deficit

Use the exact lifted cap Uhat of the short tilted proof: raise the entire
left wing by h, make the middle roof height one, and retain the right wing.
It is a genuine downward convex cap of height one. Its first-quarter
supports agree with those of U, while on J the exact positive niche of U
is the all-angle maximum of

    min(Rhat_t(x),Shat_t(x)-h).

Let u,v be Uhat's 45-degree supports minus one in the normalization

    u=r H_Uhat(pi/4)-1, v=r H_Uhat(3pi/4)-1,
    M=(u+v)/2.

Then a/2<=u,v<=a. Concavity of the original tilted roof also imposes

    v<=a-h/2.                                                (INT4)

Indeed the original support parameter in the second 45-degree direction
is v-h; the global affine extension L(x)=1-h/2+(h/a)x bounds it above by
a-3h/2. Equivalently this follows directly by maximizing -x+Ahat(x)
under Ahat(x)<=1+h/2+(h/a)x on the left wing.

Put z=h/a. The lifted cap lies below the ordinary horizontal 45-degree
majorant

    A0=min(1,1+u-x,1+v+x).

But on the left wing it also lies below

    Lhat(x)=1+h/2+zx.

The lines Lhat and 1+v+x meet at x=-q, where

    q=(v-h/2)/(1-z),  a/2<=v<=q<=a.

The exact area by which this affine constraint cuts A0 on the charged
left wing is

    D_tilt=h(v-a/2)^2/[2(a-h)].                              (INT5)

To check it, on [-v,-a/2] the depth under the flat roof grows linearly
from zero to z(v-a/2), giving area z(v-a/2)^2/2. On [-q,-v] the
remaining triangle has base z(v-a/2)/(1-z) and the same depth, giving
z^2(v-a/2)^2/[2(1-z)]. Their sum is INT5. Both triangles are wholly
charged by INT4.

Consequently the true exterior area of U is at most

    a-[(a-u)^2+(a-v)^2]/2-ah/2-D_tilt.                       (INT6)

All additional exterior deficit is nonnegative.

### 2. A globally concave two-support relaxation, including clipping

Since h<a/2, the apex (u-v+h)/2 of the actual 45-degree tent lies in J
for every pair (u,v) in the square [a/2,a]^2. Hence its exact J-area is

    N45=(M-h/2-k)_+^2
        -[(u-k-a/2)_+^2+(v-h-k-a/2)_+^2]/2.                 (INT7)

Let F_h be the right side of INT6 minus N45 with D_tilt omitted. For
fixed a,h it is concave on that entire square, by exactly the TS5
piecewise-Hessian argument: diagonal entries -3/2 plus a clipping
indicator, off-diagonal -1/2 in the positive-apex region, and -Id
otherwise. The first derivatives match at all clipping boundaries.

Therefore

    Q_h(u,v):=F_h(a,u,v)-h(v-a/2)^2/[2(a-h)]

is also concave on the entire square. Its formula is a valid upper bound
on P for every actual cap satisfying INT4. We may maximize it on the
larger full square, even though the affine-area interpretation INT5 is
needed only on the actual cap's feasible subset.

### 3. The actual global critical point is unclipped

Put

    A_*=a-3h/4-k>0,
    D=2A_* /(4-h/a),
    u_*=a-D, v_*=a-h/2-(1-h/a)D.                            (INT8)

These are the stationary supports in the regime without clipping.
One can check this directly in the proper tilted variables:
w_R=a-u, w_L=a-v-h/2, so the proper exterior/niche expression is

    a-(5/8)ah
      -(w_R^2+w_L^2/(1-h/a))/2
      -[a-3h/4-(w_R+w_L)/2-k]^2.

Its stationary equations give w_R=D,w_L=(1-h/a)D.

Since D>0 and D<a/2, both u_*,v_* lie strictly inside [a/2,a], and
v_*<=a-h/2. The inequality D<a/2 follows at once from

    4(a-3h/4-k)<a(4-h/a).

Their apex height is D>0. The right clipping term vanishes because

    D-(a/2-k)=[2k-h(1+k/a)]/(4-h/a)>0.                       (INT9)

Indeed a>=1 and h<1/2 give
h(1+k/a)<(1+k)/2=r/2<2k, the last inequality being r>4/3.
For the left clipping term,

    v_*-h-k-a/2
      =(u_*-k-a/2)-3h/2+(h/a)D
      <=u_*-k-a/2-h<0.

Thus Q_h is differentiable and stationary at this interior point.
Concavity proves it is a global maximum of Q_h on the square,
including all configurations whose 45-degree tent is window-clipped.
Its value is the first expression in INT1.

For the second expression set b=a-h/4 and q0=k+h/2, expand the first,
and use r=1+k and k^2=1-2k. Equivalently,

    B_*=1-(a-r)^2/2-q0^2/2-h q0^2/[8(a-h/4)].

This proves INT1 and INT2.

### 4. A simple global rational tilt exclusion

For fixed a, the expression in INT1 strictly decreases with h, because
q0 increases and 4a-h decreases. For fixed positive h, the coefficient
2a/(4a-h) decreases as a increases. Dropping the nonpositive width square
therefore gives, uniformly for a<=8/5,

    B_*(a,h)<=1-[(16/5)/(32/5-h)](k+h/2)^2.                  (INT10)

If h>=17/50, the right side is bounded above by its value at h=17/50.
The rational lower bound k>41/99 follows from 140^2<2*99^2. Substituting
it gives

    P<1-[(16/5)/(32/5-17/50)](41/99+17/100)^2
      =304326697/371212875<41/50,

where the last rational gap is

    41/50-304326697/371212875=135721/742425750>0.

This proves INT3.

The estimate is global on the displayed geometric domain. It is a
finite-angle upper bound on the original spatial score, with the
mandatory tilt cut included as ordinary exterior area. It does not assume
a finite-angle optimizer satisfies EP, does not claim unit curvature, and
does not close the remaining tilted comparison.


## Remaining Gate 1 obligation and validation scope

The complete horizontal canonical-maximizer branch is proved in
[HW1](gate1-horizontal-maximizer-sharp-value.md). Together with this note,
the sole remaining alternative for an above-reference global scalar
maximizer is a tilted cap in the region TW-INT. It has positive end faces,
two strict central-facet corners at the endpoints of J, exact limiting
source-measure equality, and \(2\mathcal P=L_{\rm wing}\).

[CH7](gate1-spatial-maximizer-curvature-and-horizontal-value.md) proves
unit curvature on the regular quarter without the central-facet atom when
\(C\le2/3\). The companion [TU theorem](gate1-tilted-unit-wing-exclusion.md)
excludes every tilted canonical global maximizer with two unit-curvature
wings, including all orders of its floor and window contacts. The remaining
maximizer must therefore have a nonunit regular wing; excluding or sharply
bounding that branch is still required. No global claim that tilt can be
removed without score loss is used here.

The short, positive-gap, wide, and intermediate proofs received independent
adversarial mathematical checks within this research session. Their exact
rational comparisons and identities were checked directly. These are written
research arguments, not external refereeing or Lean verification. No Lean
source, Lake build, CI run, angular sampling, or numerical-search result is
part of the proof. Gate 1 remains ACTIVE and Gate 2 remains blocked.
