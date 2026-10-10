# An exact computer-assisted exclusion of width at most two

**Result.** The complete covering and its stateless replay establish the finite-position bound 411/250. Combined with the elementary motion reduction below, this gives:

> **Theorem CA-W.** Let S be a compact connected ambidextrous body in a common incoming horizontal orientation, normalized to vertical span one. If its horizontal width is at most two, then
> 
> `area(S) <= 411/250 = 1.644 < M`,
> 
> where M is Romik's candidate area.

No curvature, symmetry, contact order, full-quarter endpoint, or adaptive-functional enclosure hypothesis is used. This closes the **width gate**, not the unrestricted optimality proof. The geometric reduction and certificate algorithm are proved below. The executed complete tree is recorded in `RESULT.json`; it is not inferred from a floating-point optimizer's status. This is a computer-assisted proof with a written correctness argument and executed checks, not Lean verification or independent refereeing.

## 1. Four actually visited hallway positions

Use the two rational unit directions

\[
(c_1,s_1)=(4/5,3/5),\qquad
(c_2,s_2)=(481/769,600/769).
\]

Their squared coordinates sum to one. They arise from tan(t/2)=1/3 and 12/25, respectively, so 0<t_1<t_2<pi/2. Importantly,

\[
\cos t_2=481/769>5/8,
\]

because 8*481=3848>3845=5*769.

The canonical-angle reduction in Notes 8–10 can be checked without any optimizer hypothesis. For K=conv(S), tightening a hallway's two outer bounds to h_K never loses a point of S: both new inner thresholds move down along with their outer supports. The resulting placement is a continuous function of its angle and K. A continuous lifted angular motion visits every angle between its endpoints, so its backtracking can be erased. If it first reaches either signed quarter turn, the incoming width-one condition supplies the outgoing width at that point and the motion may stop there. Otherwise its original terminal width passes to the retained partial endpoint.

The wrong-sign cases have area at most sqrt(2): either the terminal magnitude is at most pi/4 and the two-strip bound gives area <=sec(pi/4), or the wrong diagonal is visited and every horizontal hallway section there has length sqrt(2). Thus a body of area greater than 8/5 has the conventional signs. The same two-strip bound implies each endpoint magnitude is greater than t_2, since sec(t_2)=769/481<8/5.

Consequently any body large enough to contradict CA-W visits **both t_1,t_2 for the lower turn and both -t_1,-t_2 for the upper turn**. We do not sample a position beyond an unproved endpoint. Both motions remain independent.

Translate S horizontally so its leftmost coordinate is zero. Under the theorem's width hypothesis it lies in R=[0,2] times [0,1]. It touches y=0, y=1, and x=0. The support values in the lower frame (c_j,s_j),(-s_j,c_j) therefore lie in

\[
A_j\in[s_j,2c_j+s_j],\qquad B_j\in[0,c_j].
\tag{CA.1}
\]

For example a point at y=1 gives A_j>=s_j; a point at x=0 gives B_j>=0. No contact with x=2 is assumed. Reflection in y=1/2 supplies the same bounds for the independent upper-turn values C_j,D_j. Parameterize these eight intervals by t in [0,1]^8, using A=s+2ct and B=ct for each pair.

## 2. A finite envelope that certainly contains S

For one lower hallway the outer inequalities are

\[
cx+sy\leq A,\qquad-sx+cy\leq B,
\]

and its inner condition is

\[
cx+sy\geq A-1\quad\text{or}\quad-sx+cy\geq B-1.
\]

The upper hallway has these same equations in (x,1-y) with C,D. Intersect all four hallways with R and call the result E(t). The original S is contained in E(t). The envelope need not be connected; its **total** area is still a valid upper bound for area(S).

At each x, its vertical section is an interval or empty. Its upper endpoint is the minimum of 1, the four lower-turn outer roof lines, and the two maxima of the upper-turn inner-wall lines. Its lower endpoint is the maximum of 0, the four upper-turn outer floor lines, and the two minima of the lower-turn inner-wall lines. These are exactly the 18 lines and the min/max operations in the code. Thus

\[
|E(t)|=\int_0^2\max(U_t(x)-L_t(x),0)\,dx.
\tag{CA.2}
\]

There is no subtraction of overlapping niche areas in this formula.

For a parameter box, replace every outer support by its **upper** endpoint and every inner threshold support by its **lower** endpoint. This relaxes all four hallways pointwise. The resulting interval envelope E_box contains E(t) for every t in the box. This is the spatial leaf bound used below.

## 3. Exact spatial integration with a proved fence error

All slopes of the 18 lines are among

\[
0,\quad\pm4/3,\quad\pm3/4,\quad\pm481/600,\quad\pm600/481.
\]

Their absolute values are at most 4/3. Minima and maxima preserve a common Lipschitz constant. Hence the nonnegative fiber-height function in (CA.2) is 8/3-Lipschitz and takes values in [0,1].

Let D=288600=lcm(3,4,600,481), let q be the largest dyadic denominator of the parameter box, and let G=2^14. Every line can be written exactly as

\[
a_i x+b_i=A_i x/D+B_i/(Dq),\qquad A_i,B_i\in\mathbb Z.
\]

The code derives these integers from the rational directions and parameter intervals. It does not store rounded trigonometric constants.

For every intersection of two nonparallel lines in (0,2), insert its floor and ceiling on the grid (1/G)Z. Include 0 and 2 and sort the resulting integer grid indices. An interval between successive indices of length greater than one grid unit contains **no line crossing** in its interior: otherwise the floor/ceiling of that crossing would occur between its endpoints. Therefore every min/max selection, and the positive-part selection, is affine on that interval. The trapezoidal integral is exact there.

On an interval of one grid unit, a crossing may occur. For any K-Lipschitz scalar function with endpoint values a,b on an interval of length h, the upper tent min(a+Kx,b+K(h-x)) gives

\[
\int f\leq (a+b)h/2+Kh^2/4.
\]

Indeed its excess over the endpoint trapezoid is (K^2h^2-(b-a)^2)/(4K), at most Kh^2/4. Apply this with K=8/3 and h=1/G.

At a grid point k/G, every line value has common denominator DqG and integer numerator A_i q k+B_i G. The min/max fiber height can consequently be evaluated **exactly by integer comparisons**, without divisions or floating-point rounding. If H_k denotes its numerator and N_small the number of unit-grid intervals, the returned bound is

\[
\boxed{|E_{\rm box}|\leq
\frac{\sum(H_{k_i}+H_{k_{i+1}})(k_{i+1}-k_i)
 +(4Dq/3)N_{\rm small}}{2DqG^2}.}
\tag{CA.3}
\]

This proves the spatial evaluator in both the arbitrary-precision and accelerated implementations. Grid fencing overestimates area; it never replaces a sampled value by an unjustified exact integral.

## 4. The second leaf bound is a verified polynomial majorant

The exact kernel lists a sequence of upper roof lines and a sequence of lower floor lines. The sequences were suggested by numerical exploration, but are not trusted as contact combinatorics.

Consecutive lines define affine-in-parameter intersection coordinates. The kernel generates all of the following linear conditions:

- those coordinates are ordered from 0 to 2;
- every chosen upper line stays at least 1/2 on its assigned interval;
- every chosen lower line stays at most 1/2;
- if an upper line comes from a max-pair, it dominates its companion throughout the interval;
- if a lower line comes from a min-pair, it is no larger than its companion.

It is enough to test each comparison at the two affine endpoints: the line difference is affine in x. Each endpoint comparison is affine in the parameters, so its minimum over a parameter box is evaluated exactly at the appropriate box endpoints.

Under these conditions the chosen upper function is an upper bound for the actual U, and the chosen lower function is a lower bound for L. Their difference is nonnegative. Integrating them separately therefore majorizes the positive fiber height, **even if the actual contact pattern is different**. No simultaneous ordering of upper and lower breakpoints is assumed.

The resulting integral is an explicit rational quadratic Q(t). Its matrix is reconstructed from the lines and intersections. The checker performs an exact rational LDL decomposition of its negative Hessian and rejects any nonpositive pivot. Solving the rational stationary system and evaluating the quadratic gives

\[
\max_{t\in\mathbb R^8}Q(t)
=\frac{189405071954415}{116319753199426}
<\frac{411}{250}.
\tag{CA.4}
\]

Thus a parameter box satisfying all the generated linear conditions can be discarded. The large integers in (CA.4) are reconstructed outputs of rational linear algebra, not unverified constants entered as assumptions. Independent rational polygon clipping also checks that the associated point actually attains this value in the **finite-position relaxation**. It is not asserted to describe a complete continuous motion.

## 5. Complete coverage, not a successful numerical search

The root is the entire cube [0,1]^8. A split bisects one coordinate interval exactly, with a deterministic axis choice. Both closed children cover their parent; common boundaries are harmless. Each terminal box must satisfy either (CA.3)<=411/250 or the polynomial-domain conditions of Section 4.

The certificate is a preorder byte stream: 0 means split, 1 means spatial leaf, 2 means polynomial leaf. The stateless verifier reconstructs every box from the root. It rejects unknown node types, unsupported depth, false leaf bounds, a premature end, and trailing data after complete coverage. It does **not** read a search checkpoint or trust the generator's claim that it finished.

The completed executed tree has:

- 11,697,975 visited nodes;
- 5,848,987 splits;
- 5,448,929 spatial leaves;
- 400,059 polynomial leaves;
- no open or unresolved boxes;
- maximum depth eight in any individual coordinate.

The leaf/split identity is 5,448,929+400,059=5,848,987+1. The raw tree SHA-256 is

`e41b83a31344e04b591b6d3f23473d3a8411a392b6647d7661aca8bac4d9e119`.

A fresh, stateless complete replay accepted every leaf and the full covering. The Python arbitrary-precision evaluator was cross-checked against the accelerated evaluator on 1,200 boxes, and an independent rational polygon-splitting algorithm checked 500 area bounds. Fourteen false/incomplete/malformed-tree checks were rejected. These tests supplement the correctness proof; the tests alone are not why the bound covers the continuum.

## 6. Fixed-width integer safety

The pure Python checker uses unbounded integers. The accelerated checker uses int64; this distinction matters because compiled machine integers can overflow (see the official Numba discussion of integer width: https://numba.readthedocs.io/en/0.61.0/reference/pysemantics.html ).

The checker rejects any coordinate depth above 13, so q<=8192. For the fixed directions and root intervals,

\[
|A_i|\leq(4/3)D,\qquad |B_i|\leq4Dq.
\]

All crossing numerators before division have absolute value at most 8DqG; line-evaluation numerators are bounded by 7DqG. The integrated trapezoid sum is nonnegative and at most 4DqG^2, because fiber height is in [0,1]. There are at most 306 unit-grid intervals. Therefore the numerator in (CA.3) is below

\[
4DqG^2+(4Dq/3)306<2^{62}<2^{63}.
\]

All earlier products are smaller. The denominator is 2DqG^2. Comparing it with 411/250 uses quotient/remainder arithmetic instead of the potentially overflowing product by 411. The largest derived template-row coefficient is less than 2^31, checked before compilation; its eight-coordinate box sum is bounded by 9*2^31*q. Split indices obey 0<=i<2^depth by induction. The DFS stack has at most 8*13+1 entries; the allocation has 106.

Thus no arithmetic used in a proof decision can overflow within the enforced input domain. The actual complete run used only q<=256. The optional `--pure` replay eliminates the machine-integer implementation from the trusted arithmetic at the cost of speed; the full executed replay used the guarded int64 implementation, not the pure mode.

## 7. Exact comparison with Romik's area

Let r=149/500. Then

\[
4r^3+3r-1=-4551/31250000<0,
\]

so the positive root Y of 4Y^3+3Y-1=0 satisfies Y>r. Also

\[
\arctan r>r-r^3/3+r^5/5-r^7/7,
\]

by integrating the identity that 1/(1+x^2) exceeds 1-x^2+x^4-x^6 for x>0. Since 1+4x^2+arctan(x) is increasing,

\[
M>\frac{269855742767652239353}{164062500000000000000}
>\frac{411}{250}.
\tag{CA.5}
\]

The certificate therefore leaves a strict gap below a feasible candidate, without floating-point comparison to its area.

## 8. Consequence and remaining proof boundary

If a normalized width-at-most-two sofa had area greater than 411/250, it would exceed 8/5, visit all four certified positions, and lie in one of the envelopes covered by the tree. Sections 2–5 contradict that area. Bodies of area at most 8/5 already satisfy the result. This proves CA-W.

Every sufficiently large ambidextrous body has a common incoming unit-span representative by the in-arm rotation argument of Note 15: vary the orientation until its vertical width first becomes one, keeping the intermediate widths at most one, and translate each pose inside the incoming arm. Reverse this in-arm motion before either original turn. This does not stretch the body or assume symmetry.

Hence every global maximizer, whose area is at least M, has horizontal width **greater than two** in every such incoming unit-span representative. The previous width gate is no longer an unproved structural requirement.

Combining CA-W with the existing wide curvature theorem CW4 gives the following precise remaining sufficient task: prove open-quarter curvature domination for an appropriate incoming unit-span hull of each unrestricted maximizer, or construct an equality-preserving sharp comparison that replaces it. The new computation does not prove that curvature statement and does not identify the unrestricted optimum by itself. A structural result for one maximizer would establish the value; uniqueness needs every maximizer or a recovery argument.

## Attribution and execution

The finite hallway-intersection / exact-rational branch-and-bound viewpoint is used in Kallus and Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630, Sections 2–3: https://arxiv.org/html/1706.06630v2 . This is a new two-turn implementation and certificate; no best-known or novelty claim is made.

Numerical discovery was used only to select the small relaxation and polynomial template. The completed decisions use exact arithmetic. No CI or Lean/Lake process was used. Numba did compile the local integer accelerator; this is disclosed and is not a Lean verification. The proof and implementation remain subject to independent mathematical/software review.
