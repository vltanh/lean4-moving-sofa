# A universal height-sensitive bound from the two midpoint hallways

**Scope.** This extends MH's complete finite-relaxation calculation to incoming heights below one and to arbitrary continuous motions of either handedness. The result is an ordinary-area bound for the general ambidextrous problem:

$$|S|\le 2\sqrt2 H-H^2\le2\sqrt2-1,$$

where H<=1 is the actual height in the common incoming orientation. It does not attain the smaller reference value M. The proof does not complete partial turns, assume symmetry, or use a weighted-cap theorem. Labels GH are local. The geometric bound 2 sqrt(2)-1 was previously mentioned in the research conversation; no novelty claim is made for that constant. Here all placement and motion-sign steps are proved explicitly.

## 1. Extend the rectangle concentration formula to thin diagonal bands

Use the notation of `midpoint-hallways-global-bound.md`. For a 1-by-q rectangle, 0<=q<=1, and a diagonal band of width d in its sum coordinate, 0<d<=2, the centered band has the largest area. Its exact maximum is

$$H_d(q)=\begin{cases}
qd,&d\le1-q,\\
q-\tfrac14(1+q-d)_+^2,&d\ge1-q.
\end{cases} \tag{GH.1}$$

The sum-coordinate density is the symmetric trapezoid described in MH. If the band fits in its plateau, the area is qd. Otherwise the missing corners are two equal triangles, until the band covers the whole rectangle. These alternatives give GH.1 and agree at d=1-q.

The three placement cases in MH remain exhaustive. The narrow-rectangle case contributes at most d, and the two-square case contributes at most 2H_d(1)=2d-d^2/2. In the remaining case 1<Q<2, q=Q-1, the total upper bound is

$$f_d(q)=d(1-q)+2H_d(q).$$

It is nondecreasing in q on [0,1]. In the plateau regime q<=1-d, its derivative is d. In the partial-corner regime it is 1-q. In the whole-rectangle regime q<=d-1 (possible for d>=1), it is 2-d. All are nonnegative. Therefore f_d(q)<=f_d(1)=2d-d^2/2.

**Lemma GH1.** The exact maximum of the two opposing-midpoint-hallway envelope in a diagonal band of sum-coordinate width d is

$$\boxed{2d-d^2/2\quad(0<d\le2).} \tag{GH.2}$$

The two unit squares with P=Q=2 and the band centered at u+v=2 attain it. This is a statement about this finite relaxation, not a fully rotating equality body.

An actual incoming horizontal strip of height H has sum-coordinate width d=sqrt(2)H after the orthogonal transformation in MH. Thus any body visiting both proper midpoint frames has area at most

$$\boxed{B(H)=2\sqrt2 H-H^2.} \tag{GH.3}$$

## 2. A wrong-way midpoint has area at most sqrt(2) H

Consider the lower standard L-hallway in body coordinates, indexed by a continuous lifted angle theta starting at zero. Its frame normals are n_theta and n_(theta+pi/2). At theta=-pi/4 they are (1,-1)/sqrt(2) and (1,1)/sqrt(2), with the same positive horizontal component.

For arbitrary outer offsets a,b, a horizontal line at ordinate y has outer right endpoint

$$m(y)=\min(\sqrt2 a+y,\sqrt2 b-y).$$

The corresponding inner safe-half-plane alternatives require x to be at least one of those two expressions minus sqrt(2). Their union is exactly x>=m(y)-sqrt(2). Hence the full hallway section is

$$[m(y)-\sqrt2,m(y)],$$

of length sqrt(2), for every y. Its intersection with any incoming horizontal strip of height H has area at most sqrt(2)H. Reflecting the picture vertically gives the same bound for the upper hallway's wrong-way midpoint. The computation is independent of the hallway translations.

Therefore a body of area greater than sqrt(2)H cannot visit that wrong-way midpoint during either motion.

## 3. A large body must visit the proper midpoint in each motion

For the lower hallway, let theta(t) be the continuous lifted body-coordinate frame angle, theta(0)=0. Suppose its endpoint angle is omega. At the end the body fits an outgoing unit strip with normal n_omega. Together with the original incoming strip, normal n_(pi/2) and width H, this encloses the body in a parallelogram of area

$$H/|\cos\omega|$$

whenever cos(omega) is nonzero. If |S|>sqrt(2)H, then |cos(omega)|<1/sqrt(2). In particular the endpoint cannot lie in [-pi/4,pi/4]. If the path never visits +pi/4, continuity keeps it strictly below +pi/4; its endpoint must then lie below -pi/4, forcing it to pass through the wrong-way midpoint -pi/4. Section 2 rules that out.

Thus every such lower-turn motion visits +pi/4. There is no assumption of a monotone motion or a final angle at most pi/2. Full rotations or reversals along a continuous lift do not change the intermediate-value argument.

Reflect vertically to treat an upper-turn motion. In the original body coordinates its proper midpoint frame is the opposite pair -n_(pi/4), -n_(3pi/4), up to exchanging the two arms. Consequently a body of area greater than sqrt(2)H that negotiates both hallway handednesses from the same incoming orientation satisfies the two midpoint constraints used by GH1.

This argument concerns separate motions of the same rigid shape; their translations may differ. No common timing or matching of corner positions is assumed.

## 4. The universal area theorem and a necessary height of any counterexample

**Theorem GH2.** Let S be a compact ambidextrous sofa admitting continuous motions around both unit-width right-angle hallway corners from one common incoming orientation. Let its actual height in that orientation be H in (0,1]. Then

$$\boxed{|S|\le 2\sqrt2 H-H^2\le2\sqrt2-1.} \tag{GH.4}$$

**Proof.** If |S|<=sqrt(2)H, the result is immediate because B(H)-sqrt(2)H=H(sqrt(2)-H)>=0 for H<=1. Otherwise Section 3 forces both proper midpoint orientations and GH1 gives |S|<=B(H). The function B increases on [0,1], yielding the last inequality. QED.

Connectedness was not used in the area calculation. It remains part of the sofa definition, but disconnected finite envelopes are safely included in the upper relaxation.

With the explicit reference lower value M, a hypothetical counterexample must have, in every available common incoming orientation,

$$\boxed{H>H_M:=\sqrt2-\sqrt{2-M}.} \tag{GH.5}$$

Indeed B(H)=2-(sqrt(2)-H)^2 and B is increasing on this range. This bound applies in a transported minimum-width frame whenever the same-body transport has actually been justified. It does not authorize changing the frame of an arbitrary partial motion without proof.

At H<=H_M the sharp target |S|<=M is therefore settled without any curvature or face assumptions. The remaining high-height class still requires the genuinely sharp ordinary-area comparison. GH does not establish that comparison or any uniqueness statement.

## 5. Verification boundary

The expanded exact-rational midpoint checker includes d=1/2 and 3/4 as well as widths in [1,2], and checks GH.1 against exact polygon clipping. The proof above is analytic; the finite check is not a continuum motion verifier. No CI, Lean/Lake compilation, dependency installation, manuscript build, or long search was used. The general optimal value remains unproved.