# Central short faces: three explicit ordinary-area extensions

**Scope.** This applies the six-point strip lemma SCG to a class not covered by LF1: both horizontal faces span the central interval, but their lengths may be less than one. Their alignment and full turns are derived rather than assumed. The sharp area step uses the existing written weighted theorem WV2 through SCG1. Labels CSF are local. Unrestricted optimality remains open.

## 1. The geometric class and threshold

Let S be compact, connected and ambidextrous in the common unit-height incoming strip. Write K=conv(S), its horizontal projection as [l,r], and W=r-l>2. Suppose both its top and bottom horizontal faces contain

$$[l+1,r-1].\tag{CSF.1}$$

This is an inclusion of intervals in the two exposed faces. It does not claim that their interiors belong to S. Choose actual extreme points P=(l,y_L), Q=(r,y_R). For some 0<=m<=1/2 suppose m<=y_L,y_R<=1-m. Define

$$w_m=2+\frac{\sqrt{1+(1-m)^2}-1}{1-m}.$$

**Theorem CSF1.** If W>w_m and CSF.1 holds, then

$$\boxed{|S|\le M.}\tag{CSF.2}$$

No curvature, smoothness, symmetry, full-turn or weighted-maximizer premise on S is used. The conclusion is conditional on the stated face and witness geometry.

| Extreme-height information | Sufficient width |
|---|---|
| None beyond 0<=y_L,y_R<=1 | W>1+sqrt(2) |
| Both extreme witnesses in [1/4,3/4] | W>7/3 |
| Both extreme witnesses at height 1/2 | W>sqrt(5) |

These are exact identities for w_m at m=0,1/4,1/2, not rounded thresholds.

## 2. Initial angles force a common left endpoint

For |S|<=8/5 the conclusion follows from M>8/5. Assume |S|>8/5, so the conventional initial turns are available from the earlier motion reduction. Write the top and bottom face intervals as [a_+,b_+], [a_-,b_-]. Their endpoints are extreme points of K and hence actual points of S. By CSF.1,

$$a_+,a_-\le l+1<r-1\le b_+,b_-.$$

The initial floor-trace exclusions OT3, also proved in LF Section 1, say that a_- is not in (a_+,r-1), and a_+ is not in (a_-,r-1). Since both are strictly below r-1 they coincide. Put

$$a=a_+=a_-,\qquad b=\min(b_+,b_-),\qquad T=b-a.$$

Then K contains [a,b] times [0,1], the points (a,0),(a,1) are retained, and

$$T\ge W-2,\qquad r-a\ge W-1,\qquad b-l\ge W-1.\tag{CSF.3}$$

At this stage b may be interior to one face. Its two points are only known to belong to K, and are not used as retained points before alignment is proved.

## 3. A strict strip test on the entire allowed T interval

If T>=1, the common rectangle contains a unit square and forces both reduced turns to be full, as in FL. Suppose 0<T<1. Then x=W-2 belongs to (0,1) and T in [x,1). Consider

$$H(T)=2T(W-1)+m(1-T^2)-(1+T^2).$$

It is concave in T, and

$$H(x)=(1-m)x^2+2x-(1-m),\qquad H(1)=2x>0.\tag{CSF.4}$$

The positive zero of the first quadratic is w_m-2. Thus W>w_m makes H(x)>0, and concavity gives H(T)>0 throughout [x,1]. Consequently

$$2T(r-a)+\min(y_R,1-y_R)(1-T^2)>1+T^2,$$

and the analogous left inequality follows from CSF.3. Also r-a,b-l>1.

Apply SCG.3 to the top point (b,1) of K and actual right extreme Q. With (a,0), it proves that the width of K in every possible lower outgoing interior normal exceeds one. Reflection proves the same for upper outgoing normals. Both reduced turns are full. This part requires (b,1) in K, not in S, since it is only a support-width estimate.

## 4. Full turns force the right endpoints to agree

Both b_+,b_- are at least r-1>l+1. The final floor-trace exclusions give b_->=b_+ and b_+>=b_-. Thus b_+=b_-=b, and all four corners at a,b are actual retained points. If T>=1, FL1 applies. If T<1, the two strict SCG inequalities proved above apply. SCG1 confines both positive niches to (a,b), gives zero clipping and proves the ordinary-area bound.

The order matters: a point in the interior of a hull face is not automatically in S. The width argument precedes the use of the right endpoints as retained forbidden-quadrant witnesses.

## 5. An actual feasible short-face example

To verify that the extension admits a nonempty geometric class, let E be the ellipse centered at the origin with horizontal semiaxis 7/10 and vertical semiaxis 1/2. Put

$$K=(0,1/2)+E+([-9/20,9/20]\times\{0\}).$$

Its width is 23/10, its top and bottom faces are [-9/20,9/20], of length 9/10, and its horizontal extreme points have height one half. Both faces contain the central interval [-3/20,3/20]. Thus W>sqrt(5) and the m=1/2 conditions hold. The two SCG margins are exactly 233/200.

It remains to verify that K is the actual hull of a feasible two-turn body, rather than merely a support-parameter example. For 0<t<pi/2 set c=cos t, s=sin t and

$$e(t)=\sqrt{(49/100)c^2+(1/4)s^2}.$$

The upper supports are f=s/2+e(t)+(9/20)c and g=c/2+e(pi/2-t)+(9/20)s. Because

$$ (1-s/2)^2-e(t)^2=(1-s)(51/100-(49/100)s)>0,$$

one has (f-1)/c<9/20. The reflected calculation gives (1-g)/s>-9/20. Hence every positive niche lies strictly between the face endpoints.

Its corner height is

$$c_y=1/2+s e(t)+c e(pi/2-t)+(9/10)sc-s-c.$$

Cauchy--Schwarz bounds the two e terms by sqrt(74)/10. Put z=s+c in [1,sqrt(2)]. Then

$$c_y\le1/20+\sqrt{74}/10+(9/20)z^2-z.$$

This convex quadratic is bounded above by its endpoint values. Both are less than 1/2: use sqrt(74)/10<87/100 and sqrt(2)>7/5 to get respective bounds 37/100 and 21/50. Thus the lower niche and its reflected upper counterpart stay strictly away from the common midline.

Let S be K minus the two canonical open forbidden sweeps. It is compact and has nonempty interval fibers through y=1/2, so it is connected. The canonical placements give both full turns. Outside the face interval neither niche removes material, and the four face endpoints survive. All extreme points of K therefore survive, proving conv(S)=K. This supplies an actual member of the new class with both face lengths below one.

The first draft's example W=12/5,T=2/5 was only a tuple passing the sufficient inequalities, not a verified realization. The later FAS flank bound shows that tuple cannot be a full-turn feasible hull. It is replaced here by the explicit realized ellipse construction rather than called a nonvacuous example.

## 6. Remaining scope

The theorem does not cover a point face, since W>2 makes the central interval have positive length. It does not cover all shifted, one-sided or very short faces, nor all widths between two and w_m. It gives no universal strict area gap on those remaining families.

The later FAS theorem covers all already full-turn aligned positive faces without these extra width/height thresholds. CSF remains useful because it derives full turns for its stated class. All the geometry above has hand proofs. A short rational checker is supplementary, not a continuum certificate. No long computation, CI, Lean/Lake compilation, dependency installation or manuscript build is used.
