# The complete midpoint-hallway relaxation has maximum 2 sqrt(2) - 1

**Scope.** This proves a universal ordinary-area bound, over **all placements** of the lower and upper 45-degree hallways and the common incoming unit strip. There is no remaining placement box, curvature assumption, convex-body feasibility assumption, symmetry assumption, or connectedness assumption. Its bound is not Romik's M: it is the exact maximum of this particular two-hallway relaxation. No novelty claim is made for the numerical constant, which was previously mentioned in the research discussion; the contribution here is a self-contained analytic proof, not reliance on that external claim. Labels MH are local. Baseline: `47fdd36ffffc54207e3c96a4cd268ac7e84eb3eb`.

## 1. Orthogonal coordinates expose the whole finite optimization

Put u=(x+y)/sqrt(2), v=(-x+y)/sqrt(2). This orthogonal change of coordinates preserves area. The two conventional midpoint hallway frames have normal pairs (u,v) and (-u,-v), with the order of the normals immaterial.

Write their four outer offsets as u<=a, v<=b, u>=c, v>=e. Translate the u,v origin to (c,e), and put P=a-c, Q=b-e. If either is nonpositive, the intersection has area zero. Otherwise every surviving point lies in the rectangle

$$R=[0,P]\times[0,Q]$$

and satisfies exactly

$$(u\ge P-1\ \text{or}\ v\ge Q-1),\qquad
(u\le1\ \text{or}\ v\le1). \tag{MH.1}$$

The incoming horizontal strip becomes a diagonal band

$$B_{z,d}=\{z\le u+v\le z+d\},\qquad d=\sqrt2.$$

Its position z is arbitrary. For the calculation below allow any d in [1,2]. Define F(P,Q,z,d) as the rectangle/band intersection after imposing both disjunctions MH.1. All boundary conventions are immaterial to area.

## 2. Concentration of a unit-by-q rectangle in a diagonal band

For 0<=q<=1 and 1<=d<=2, the largest possible area of the intersection of a 1-by-q axis-aligned rectangle with a band of the form B_(z,d) is

$$\boxed{H_d(q)=q-\frac14(1+q-d)_+^2.} \tag{MH.2}$$

**Proof.** Translating the rectangle changes only z. The density of the sum coordinate u+v on [0,1] times [0,q] is symmetric and nonincreasing away from its center (1+q)/2: it rises linearly to q, stays constant on [q,1], and then decreases linearly. A band of given width captures the most mass when centered there. This can also be seen by shifting an off-center band toward the center: the gained endpoint density is at least the lost endpoint density.

If d>=1+q, the centered band contains the rectangle. Otherwise each omitted corner has leg length (1+q-d)/2. Since d>=1, that leg length is at most q/2, so both omitted pieces are genuinely right triangles inside the rectangle. Their combined area is (1+q-d)^2/4. Subtract from q. QED.

In particular a unit square contributes at most H_d(1)=d-d^2/4.

## 3. Exhaustive placement cases

**Theorem MH1.** For all P,Q>0, all real z and every d in [1,2],

$$\boxed{|F(P,Q,z,d)|\le 2d-d^2/2.} \tag{MH.3}$$

**Case 1: min(P,Q)<=1.** The entire outer rectangle lies in a coordinate strip of thickness at most one. Its intersection with B_(z,d) has area at most d, by integrating in the thin coordinate. Since d<=2d-d^2/2 for 1<=d<=2, the bound follows without using the forbidden quadrants.

**Case 2: P,Q>=2.** Distributing the two alternatives in MH.1 leaves, up to zero-area line pieces, only the two unit corner squares

$$[P-1,P]\times[0,1],\qquad[0,1]\times[Q-1,Q].$$

Each contributes at most H_d(1). Their sum is at most 2d-d^2/2. The band need not be simultaneously centered on them; using each individual optimum is a valid upper bound.

**Case 3: one dimension is strictly between one and two.** Interchange u and v if necessary so 1<Q<2; Case 1 already disposed of P<=1. Put q=Q-1 in (0,1). Partition the allowed region by v into three disjoint horizontal layers. The lower layer 0<=v<=q permits only P-1<=u<=P, a 1-by-q rectangle. The upper layer 1<=v<=Q permits only 0<=u<=1, another 1-by-q rectangle. Between them, q<=v<=1, the disjunctions are both automatic; dropping the outer u bounds gives an infinite horizontal band of thickness 1-q.

The middle contribution inside B_(z,d) is at most d(1-q), and the two corners contribute at most 2H_d(q). Consequently

$$|F|\le f_d(q):=d(1-q)+2q-\tfrac12(1+q-d)_+^2.$$

For 0<=q<=1,

$$f_d'(q)=2-d-(1+q-d)_+\ge0.$$

Indeed below q=d-1 the derivative is 2-d; above it the derivative is 1-q. Thus f_d(q)<=f_d(1)=2d-d^2/2. These cases exhaust every positive P,Q. QED.

## 4. Sharpness and the actual sofa consequence

Take P=Q=2 and center the band at u+v=2, so z=2-d/2. The allowed set is the union of the two squares [1,2] times [0,1] and [0,1] times [1,2], intersected with that band. Each square attains MH.2, giving exactly

$$|F|=2d-d^2/2.$$

At d=sqrt(2), this set is compact and connected (the two pieces meet at (1,1)), and fits the incoming strip and the two midpoint hallways. Therefore

$$\boxed{\sup_{P,Q,z}|F(P,Q,z,\sqrt2)|=2\sqrt2-1.} \tag{MH.4}$$

**Corollary MH2.** Every body satisfying both conventional midpoint hallway positions in one common incoming unit strip has

$$\boxed{|S|\le2\sqrt2-1.} \tag{MH.5}$$

In particular this is a global upper bound for the full-turn problem. It also applies directly to a conventional partial-turn pair if both supplied angular intervals actually include 45 degrees. No partial-turn completion theorem is needed for that application. Merely having an arbitrary partial motion without those visited angles does not supply the hypothesis.

This bound concerns actual area and permits arbitrary measurable subsets and disconnected envelopes; it needs neither GC nor weighted-cap maximality. It does **not** show that the equality polygon can complete the full turns, and it does not establish the desired smaller bound M.

## 5. Verification and next boundary

The supporting script `computer-assisted/check_midpoint_hallways.py` checks the polygon/band area by exact Fraction clipping and inclusion-exclusion on a prescribed grid. It includes four sharp equality cases for rational d and checks the corner-concentration formula separately. These are finite regressions of this hand proof, not the reason MH1 covers all real parameters.

The first local checker run had a variable-name typo (`P-Q` with Q the Fraction constructor); it terminated with TypeError and yielded no mathematical output. After correction to `P-R` in the test list, the bounded replay passed. No optimization, CI, Lean/Lake compilation, dependency installation or manuscript build was used.

Unlike the earlier successful individual parameter boxes, MH1 solves this complete finite relaxation. Its exact maximum is strictly larger than the candidate value. More orientations or a continuum argument are indispensable; the full-turn sharp theorem remains unproved.