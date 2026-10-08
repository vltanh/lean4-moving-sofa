# A unit vertical chord cannot have long flanks on both sides

**Scope.** This is a geometric obstruction independent of the weighted value theorem, area estimates and curvature. It eliminates the central point-face subcase left by the floor-trace tests. It does not exclude point faces in the unit end intervals. Labels UC are local.

## 1. Statement

Let a compact set S be contained in 0<=y<=1 and fit in its canonical supporting hallways for every angle of both conventional quarter turns. Suppose S contains (a,0),(a,1).

**Theorem UC1.** S cannot also contain a point with x<a-1 and a point with x>a+1.

Only the two endpoints of the vertical chord are required to lie in S. The whole chord need not be present, and connectedness is not needed for this particular obstruction.

## 2. The lower turn has a switching angle

Write h for the support of S, which equals that of its convex hull. At each angle t in [0,pi/2] define the closed safe-angle sets

$$A=\{t:h(t)-a\cos t\le1\},$$

$$B=\{t:h(t+pi/2)+a\sin t\le1\}.$$

The retained bottom point (a,0) must obey at least one inner-wall alternative at every interior angle. The same inequalities hold at the endpoints because S lies in the unit-height strip and touches both boundaries. Thus A union B is the entire closed quarter interval.

Suppose there are points P=(a-L,y_L), Q=(a+R,y_R) in S with L,R>1. At t=0, h(0)-a>=R>1, so 0 is not in A and is in B. At t=pi/2, h(pi)+a>=L>1, so the endpoint is not in B and is in A.

Continuity of support functions makes A,B closed. They cannot be disjoint nonempty closed sets partitioning a connected interval. Hence they intersect at some interior angle theta. Both inequalities hold there:

$$h(\theta)\le1+a\cos\theta,\qquad
h(\theta+pi/2)\le1-a\sin\theta.\tag{UC.1}$$

Apply the same argument to the reflection rho(x,y)=(x,1-y), using the retained top point. The upper motion supplies an interior angle phi with the analogous two bounds for h_(rho S).

The two angles are independent. No symmetry of S or equality of the two motions is assumed.

## 3. The right and left long flanks demand incompatible angle inequalities

Evaluate UC.1 at Q. Since R>1,

$$R\cos\theta+y_R\sin\theta\le1
\quad\Longrightarrow\quad
 y_R<\frac{1-\cos\theta}{\sin\theta}=\tan(\theta/2).$$

At the reflected switching angle, the same point gives

$$1-y_R<\tan(\phi/2).$$

Putting r=tan(theta/2), s=tan(phi/2), where 0<r,s<1, these two inequalities imply

$$r+s>1.\tag{UC.2}$$

Now evaluate the other supporting bound at P. Since L>1,

$$L\sin\theta+y_L\cos\theta\le1
\quad\Longrightarrow\quad
 y_L<\frac{1-\sin\theta}{\cos\theta}=
 \frac{1-r}{1+r}.$$

The reflected point similarly gives 1-y_L<(1-s)/(1+s). Hence

$$\frac{1-r}{1+r}+\frac{1-s}{1+s}>1.$$

Multiplying by the positive denominator (1+r)(1+s) gives

$$r+s+3rs<1,\tag{UC.3}$$

which contradicts UC.2. This proves UC1.

Every strict inequality comes from a flank strictly longer than one. The proof makes no assertion with both strict flank hypotheses replaced by equality.

## 4. A point face must lie in an end interval

Let K=conv(S) have unit vertical span and horizontal projection [l,r], with W>2, and assume both conventional turns are full. Put u=l+1 and v=r-1.

**Corollary UC2.** If the top or bottom horizontal face is a single point with abscissa a, then

$$\boxed{a\in[l,l+1]\cup[r-1,r].}\tag{UC.4}$$

**Proof.** Suppose the top face is the point (a,1), with u<a<v, and let [c,d] be the bottom face. Face endpoints are retained extreme points. The initial reflected floor exclusion says a is not in (c,v), so c>=a. The final reflected exclusion says a is not in (u,d), so d<=a. Thus c=d=a. Both (a,0),(a,1) belong to S.

Compactness supplies horizontal extreme points at l and r. Since a is strictly between u and v, both distances a-l and r-a exceed one. This contradicts UC1. Reflect vertically for a point bottom face. QED.

Consequently the point-face alternative in FD2 is now confined to the two unit end intervals. The central common-point possibility is excluded, not merely left as an unclassified degeneracy.

## 5. Boundary of the result

The theorem uses two full supporting-quarter families. It cannot be applied to an unhandled partial-turn body by extending its motion without proof. It is independent of WV2, the analytic width exclusion and the computer-assisted angle certificates.

Point faces at the left or right ends remain possible, including the previously known near-reference constructions. UC2 does not give an area bound for them. Opposite-end positive-face configurations also remain after FD2. Unrestricted optimality therefore remains unproved.

The proof is entirely algebraic/topological: a closed-set switching argument and two incompatible rational half-angle inequalities. No numerical computation, CI, Lean/Lake compilation, dependency installation or manuscript build is used.
