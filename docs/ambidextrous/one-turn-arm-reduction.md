# The weighted one-turn bound is equivalent to two endpoint arm bounds

This note works on target O4 of the [roadmap](ROADMAP.md), the one-turn target named in the [handoff](HANDOFF.md): the sharp inequality Psi<=M/2 for the attained maximizer of [PA2](one-turn-penalized-attainment.md), with equality only at the candidate. It does **not** prove that inequality. It proves that, for the signed width-penalized problem, the inequality together with uniqueness is **equivalent** to an a priori bound on two horizontal distances of every maximizing cap (Theorems AR6 and AR6'). It also records floating-point examples showing that the local conclusions of [WR1](one-turn-weighted-regularity.md) cannot replace that bound by a comparison valid on their whole class.

Gate addressed: the missing curvature bound rho<=1 named in WR1 §5 is reduced to the endpoint arm inequality (EA) below. Nothing here concerns ambidextrous bodies, the clipping term G of OT1, full-turn admission, or the two-wing route.

Labels AR are local. Dependencies: the domain PA.1 and Lemma PA1; WP1–WP2 and WR1; [SR1](curvature-only-signed-roof.md); [AF1–AF3](adaptive-functional-global-calibration.md), including the case analysis of AF2; the explicit candidate profile of Note 14. The candidate formulas and their identification with Romik's construction are attributed there. No novelty claim is made.

## 1. Notation and the two endpoint arms

Use the domain PA.1. For a normalized cap U with upper support h write L=pi/2,

$$
f(t)=h(t),\quad g(t)=h(t+L),\quad p=f'-g+1,\quad q=g'+f-1,\quad \rho_f=f''+f,\quad \rho_g=g''+g
$$

on 0<t<L. Let `[x_L,x_R]` be the horizontal projection, `[x_tl,x_tr] x {1}` the top face (possibly a point), W=x_R-x_L and T=x_tr-x_tl.

For every maximizer, WR1 gives height one, W^(2,infinity) supports on each open quarter, and

$$
p(0)=\tfrac12,\qquad q(L)=-\tfrac12,\qquad \rho_f\le\kappa(q),\qquad \rho_g\le\kappa(p)\quad\text{a.e.},
\qquad \kappa(z)=\max\{|z|,(1+|z|)/2\}.
$$

These are WR.4 and WR.5. In particular p and q are Lipschitz on (0,L) with one-sided traces at both ends, and

$$
p'=\rho_f-1-q,\qquad q'=\rho_g-1+p\qquad\text{a.e.}
$$

Near the vertical normal the support points are the two ends of the top face. Hence h'(L-)=-x_tr and h'(L+)=-x_tl, while h(0)=x_R and h(pi)=-x_L. Substituting,

$$
\boxed{q(0)=x_R-x_{tl}-1,\qquad p(L)=1-(x_{tr}-x_L).}
\tag{AR.1}
$$

Thus 1+q(0) is the horizontal distance from the far end of the top face to the right end of the cap, and 1-p(L) is the mirror distance. These are Baek's two arms at the start and end of the turn. Also W+T=2+q(0)-p(L).

Put c=(f-1)mu+(g-1)nu, the inner corner, and

$$
C(f,g)=\frac12\int_0^L(f^2-f'^2+g^2-g'^2)\,dt,\qquad
I(f,g)=\frac12\int_0^L\det(c,c')\,dt,
$$

$$
S(f,g)=-I(f,g)+\frac12\int_0^L(p_-^2+q_+^2)\,dt .
$$

Since c'=p mu+q nu, direct expansion gives det(c,c')=(f-1)^2+(g-1)^2+(f-1)g'-(g-1)f'. Comparing with (A.1),

$$
F(f,g)=C+I-\frac12\int_0^L(p_-^2+q_+^2)\,dt=C(f,g)-S(f,g).
\tag{AR.2}
$$

S is the right side of SR1's identity (S.6). To avoid a clash with the functional F of (A.1), the signed roof of SR1 is written Lambda here; its negative-part magnitude is Lambda_-=max(-Lambda,0).

**Lemma AR0 (Baek's arms are nonnegative).** For every normalized cap whose quarter supports are C^1 on (0,L),

$$
p\le1,\qquad q\ge-1\qquad\text{on }(0,L).
$$

**Proof.** The support point f mu_t+f' nu_t lies in U, which lies in the half-plane z.nu_t<=g(t); hence f'<=g. The support point g nu_t-g' mu_t lies in z.mu_t<=f(t); hence -g'<=f. QED.

## 2. Cap area as a support integral

**Lemma AR1.** Every normalized cap satisfies

$$
\boxed{|U|=\frac12\int_0^\pi(h^2-h'^2)\,d\theta=C(f,g).}
\tag{AR.3}
$$

**Proof.** For a planar convex body, 2|U| is the integral of h against the length measure S_U on the circle. On the open lower half circle S_U is the bottom-edge atom at 3pi/2, where h=0; the two bottom corners carry no length. On [0,pi], S_U consists of the end-edge atoms e_R=h'(0+) and e_L=-h'(pi-), plus the measure h dtheta+d(h') on the open interval (0,pi). The latter includes the top-face atom at L.

The function h is Lipschitz and h' has bounded variation with one-sided limits. Hence

$$
\int_{(0,\pi)}h\,d(h')=h(\pi)h'(\pi-)-h(0)h'(0+)-\int_0^\pi h'^2\,d\theta .
$$

Adding h(0)e_R+h(pi)e_L cancels both endpoint products. QED.

## 3. The signed objective under unit curvature

**Proposition AR2.** Let U be a normalized cap whose quarter supports belong to W^(2,infinity)(0,L) with 0<=rho_f,rho_g<=1 a.e. Then

$$
\boxed{\mathcal A(U)=F(f,g)-\int_{\mathbb R}\Lambda_-\,dx\le F(f,g).}
\tag{AR.4}
$$

If W>=2, then Lambda>=0 almost everywhere and A(U)=F(f,g).

**Proof.** By PA.1 the vertical section of N(U) over x is the half-open interval from 0 to sup_t min(R_t(x),L_t(x)) over interior angles, or is empty. The axis quadrants included in SR1's roof only contribute the value zero. Hence Lambda_+ is the positive part of that interior supremum, and |N(U)|=integral Lambda_+.

Height one gives f(L)=g(0)=1, so SR1 applies and integral Lambda=S. Therefore |N(U)|=S+integral Lambda_-, and AR1 with AR.2 gives A(U)=C-S-integral Lambda_- = F-integral Lambda_-.

If W=f(0)+g(L)>=2, then x_0=f(0)-1>=1-g(L)=x_1. Every x except possibly one point satisfies x<x_0 or x>x_1. There an axis quadrant gives Lambda(x)>=0. QED.

This is the one-turn form of SR2. There is no clipping term because PA.1 subtracts the whole niche.

## 4. The candidate cap has value M/2

Recall AF2, Case 3. Y=tan(beta) is the root of 4Y^3+3Y-1=0, equivalently of (A.18). Then

$$
M=1+4Y^2+\arctan Y=\cot\beta-2+\beta,\qquad a_*=\frac1{3\sin\beta}.
$$

The centered candidate half (f_*,g_*) in X_(a_*) has momenta P(0)=1/2 and Q(0)=1/sin(beta)-2. Its orbit has three parts:

- an initial segment in {P,Q>=0} ending at (0,z), with z=cot(beta)-2;
- a rotation in {P<=0<=Q} from there to (-z,0);
- the mirror final segment, ending at (-Q(0),-1/2).

Use rho_f=p'+1+q and rho_g=q'+1-p, with P=p+p_- and Q=q+q_+. Then (A.9) becomes

$$
\begin{array}{lll}
\{p,q\ge0\}:&\rho_f=0,&\rho_g=\tfrac12;\\
\{p\le0\le q\}:&\rho_f=\tfrac{1+q}2,&\rho_g=\tfrac{1-p}2;\\
\{p,q\le0\}:&\rho_f=\tfrac12,&\rho_g=0.
\end{array}
\tag{AR.5}
$$

On the rotation, 0<=q<=z/2 and -z/2<=p<=0. On the first segment, q=Q/2<=Q(0)/2.

The cubic 4Y^3+3Y-1 is increasing and changes sign on (0.29,0.30). Hence sin(beta) lies in (0.277,0.288), cot(beta) in (3.33,3.45), and z in (1.33,1.45). Consequently

$$
0\le\rho_f,\rho_g\le\tfrac14\cot\beta<1,\qquad
W_*=2a_*=\frac2{3\sin\beta}>2 .
\tag{AR.6}
$$

The mirror symmetry (A.6) gives p(L)=-q(0). Hence the two arms and the top face are

$$
1+q(0)=1-p(L)=\frac1{2\sin\beta}\approx1.7506,\qquad T_*=2+2q(0)-W_*=a_*.
\tag{AR.7}
$$

Let U_* be the normalized cap with upper support h_*, the downward saturation of the candidate hull. It is a genuine cap: rho>=0 on both open quarters, the end-edge atoms are p(0)=1/2 and -q(L)=1/2, the top-face atom is T_*>0, and h_*(L)=1.

**Proposition AR3.** Psi(U_*)=M/2.

**Proof.** By AR.6 the hypotheses of AR2 hold and W_*>2, so A(U_*)=F(f_*,g_*). The adaptive value of h_* is M (Note 14). By the equality analysis in the proof of AF3, both halves of h_* are the unique fixed-width maximizer on X_(a_*). Hence M=2F(f_*,g_*)-2a_*, and Psi(U_*)=F(f_*,g_*)-a_*=M/2. QED.

## 5. Unit curvature forces the candidate

**Theorem AR4.** Let U be any global maximizer of Psi. If rho_f<=1 and rho_g<=1 almost everywhere on (0,L), then Psi(U)=M/2 and U is a horizontal translate of U_*.

**Proof.** By AR3 and maximality, Psi(U)>=M/2>1/2. Lemma PA1 then gives W>1. Translate so that h(0)=h(pi)=a=W/2>1/2; neither Psi nor F changes. By WR1 and the hypothesis, AR2 applies, so A(U)<=F(f,g). Since (f,g) lies in X_a, AF1 and (A.7) give F(f,g)<=max_(X_a) F=a+Phi(a)/2.

Let (f_a,g_a) be the fixed-width maximizer and let h_a be the profile whose upper half is (f_a,g_a) and whose lower half is

$$
h_a(-t)=f_a(t)-\sin t,\qquad h_a(-t-L)=g_a(t)-\cos t\qquad(0\le t\le L).
$$

The values agree at 0, -L and -pi because f_a(0)=g_a(L)=a and f_a(L)=g_a(0)=1. So h_a is an admissible profile for AF3, of width 2a>=1, with both halves of (A.2) equal to (f_a,g_a); hence its adaptive value (A.2) is Phi(a). AF3 gives Phi(a)<=M, with equality only if h_a is a translate of h_*, which has half-width a_*. Therefore

$$
\frac M2\le\Psi(U)=\mathcal A(U)-a\le F(f,g)-a\le\tfrac12\Phi(a)\le\frac M2 .
$$

All of these are equalities.

- Phi(a)=M forces a=a_*.
- F(f,g)=max over X_(a_*) then holds. AF1 uniqueness gives (f,g)=(f_*,g_*).
- A normalized cap equals the intersection of y>=0 with its upper supporting half-planes, so U=U_*.

QED.

**Corollary AR4.1.** If some maximizer satisfies rho<=1, then max Psi=M/2. If every maximizer does, U_* is the unique maximizer up to horizontal translation.

## 6. Arm propagation along the turn

**Lemma AR5 (arm propagation).** Let f,g in W^(2,infinity)(0,L) with rho_f,rho_g>=0 satisfy WR.4, WR.5, p<=1 and q>=-1. Then on (0,L)

$$
\boxed{q\le\max\{q(0)+\tfrac1{24},\ \tfrac23\},\qquad p\ge\min\{p(L)-\tfrac1{24},\ -\tfrac23\}.}
\tag{AR.8}
$$

**Proof.** Evaluating kappa, WR.5 and the kinematic equations give, almost everywhere:

- (K1) on {q>=0}, p'<=kappa(q)-1-q<=-1/2, because this equals -(1+q)/2 for q<=1 and -1 for q>=1;
- (K2) on {p<=0}, q'<=kappa(p)-1+p<=-1/2, by the same computation;
- (K3) on {0<=p<=1}, q'<=(3p-1)/2, because kappa(p)=(1+p)/2 there.

Fix t with q(t)>0; otherwise there is nothing to prove.

*Case p(t)>=0.* Let (t_A,t] be the maximal interval ending at t on which q>0. By K1, p decreases on it with slope at most -1/2; since p(t)>=0, p>0 on (t_A,t). By K3,

$$
q(t)\le q(t_A)+\int_{t_A}^t\Bigl(\frac{3p(s)-1}2\Bigr)_+ds .
$$

- If t_A=0, then p(s)<=1/2-s/2, the integrand is at most (1/4-3s/4)_+, and q(t)<=q(0)+1/24.
- If t_A>0, then q(t_A)=0 and p(s)<=1-(s-t_A)/2. The integrand is at most (1-3u/4)_+ with u=s-t_A, and q(t)<=2/3.

*Case p(t)<0.* Let s_0 be the last time before t with p(s_0)=0; it exists because p(0)=1/2. By K2, q decreases on [s_0,t], so q(s_0)>q(t)>0. The first case at s_0 bounds q(s_0), hence q(t).

For the second inequality use the reflection (f,g)(t) -> (g(L-t),f(L-t)), which is horizontal reflection of the cap. It sends (p,q) to (-q(L-t),-p(L-t)) and (rho_f,rho_g) to (rho_g(L-t),rho_f(L-t)). It preserves WR.5 because kappa is even, exchanges the two conditions of WR.4, and preserves p<=1, q>=-1. Apply the first inequality to the reflected pair. QED.

Thus wherever an arm exceeds 5/3, it exceeds the corresponding endpoint arm by at most 1/24. The lemma uses no maximality beyond WR.4–WR.5 and Lemma AR0.

**Theorem AR6 (reduction to the endpoint arms).** Let U be a maximizer of Psi. If

$$
x_R-x_{tl}\le\tfrac{47}{24}\qquad\text{and}\qquad x_{tr}-x_L\le\tfrac{47}{24},
\tag{EA}
$$

then Psi(U)=M/2 and U is a horizontal translate of U_*. Consequently the following are equivalent:

1. every maximizer satisfies (EA);
2. max Psi=M/2 and U_* is the only maximizer up to translation.

**Proof.** By AR.1, (EA) says q(0)<=23/24 and p(L)>=-23/24. By WR1 and Lemma AR0, AR5 applies and gives q<=1 and p>=-1. Together with AR0, |p|,|q|<=1, so kappa(p),kappa(q)<=1 and WR.5 gives rho<=1. Theorem AR4 concludes. Conversely, if (2) holds every maximizer is a translate of U_*, whose arms equal 1/(2 sin beta)<47/24 by AR.7. QED.

The equivalence is easy in the converse direction. Its content is the forward direction: a bound at two endpoint normals controls the curvature along the whole turn and then the global value. It does **not** make (EA) routine; Section 8 shows that WR1's local conclusions are compatible with long arms.

## 7. A sharper local law in the same-sign regimes

WR.5 bounds the exposed inner-wall length by the worst case of the neighboring-wall alternatives. In the two same-sign regimes one neighboring quadrant covers more, and the bound improves to the Euler–Lagrange values AR.5.

**Proposition AR7.** Every maximizer satisfies, almost everywhere,

$$
\boxed{\rho_f=0,\ \ \rho_g\le\tfrac12\ \text{ on }\{p>0,\ q>0\};\qquad
\rho_g=0,\ \ \rho_f\le\tfrac12\ \text{ on }\{p<0,\ q<0\}.}
\tag{AR.9}
$$

**Discrete lemma.** Use the grid polygons of WP1 with spacing delta and finite niche N_n, the union of open quadrants Q_i for 1<=i<n. Fix 2<=j<=n-2 and keep WR §1 and §4 notation: f=h_j, g=h_(j+n), c, s, T=tan(delta/2), mu=mu_(theta_j), nu=nu_(theta_j). Write

$$
d^\pm,\ d_\pm:\ \text{the one-sided derivatives of }h\text{ at }\theta_j\text{ and }\theta_{j+n},
$$

$$
p_\pm=d^\pm-g+1,\qquad q_\pm=f+d_\pm-1,\qquad \ell_j=d^+-d^-,\qquad \ell_{j+n}=d_+-d_- .
$$

For a grid polygon these are exact: between consecutive grid normals the support point is a fixed vertex. So d^+=(h_(j+1)-cf)/s, d_+=(h_(j+n+1)-cg)/s, and similarly for the left derivatives. Recall mu_(j±1)=c mu±s nu and nu_(j±1)=∓s mu+c nu.

(a) If p_+>T and q_+>T, the first inner-wall ray x(v)=(f-1)mu+v nu, v<=v_0=g-1, lies in the open quadrant Q_(j+1). Hence the exposed length tau_j of WP2 is zero.

(b) If p_+>T and q_-+T>=tan(delta)(p_-+T), the companion ray y(u)=(g-1)nu+u mu, u<=f-1, has exposed length

$$
\tau_{j+n}\le(2T-\ell_{j+n})_+ .
$$

*Proof of (a).* The two defining inequalities of Q_(j+1) on the first ray read

$$
v<d^+-T\quad(\text{and }d^+-T-v_0=p_+-T),\qquad
v<v_+\quad(\text{and }v_+-v_0=\tan\delta\,(q_+-T),\ \text{WR §4}).
$$

Both thresholds exceed v_0. The whole ray, including its corner, is therefore inside an open quadrant. Its points above the floor are interior points of N_n.

*Proof of (b).* On the companion ray the four inequalities are:

- Q_(j+1), first wall: u<f-1+tan(delta)(p_+-T);
- Q_(j+1), second wall: u>T-d_+;
- Q_(j-1), second wall: u<-d_--T;
- Q_(j-1), first wall: u<f-1-tan(delta)(p_-+T).

When p_+>T, Q_(j+1) covers T-d_+<u<=f-1. When q_-+T>=tan(delta)(p_-+T), the last threshold is at least -d_--T, so Q_(j-1) covers u<-d_--T. The exposed part lies in [-d_--T, T-d_+], of length (2T-ell_(j+n))_+. QED.

**Proof of AR7.** Let U_n be WP1's selected polygons for the given maximizer U_*. Support functions satisfy h''>=-h>=-B as measures, so h_n+B theta^2/2 is convex with a constant independent of n. The limit is C^1 on each open quarter (WR1). Uniform convergence of convex functions with differentiable limit implies locally uniform convergence of their one-sided derivatives (Rockafellar, *Convex Analysis*, Thm. 24.5; cf. Thm. 25.7). Hence the polygon quantities p_(n,±)(j) and q_(n,±)(j) converge to p and q uniformly over theta_j in any compact interval J of the open set {p>0, q>0}. Since T and tan(delta) tend to zero and p_(n,-) is uniformly bounded, for large n every grid normal theta_j in J has 2<=j<=n-2 and satisfies both hypotheses (a) and (b).

WP2 then gives, at those normals,

$$
\ell_j\le b_{n,j},\qquad
\ell_{j+n}\le(2T-\ell_{j+n})_++b_{n,j+n},
$$

the latter implying ell_(j+n)<=T+b_(n,j+n). Sum over grid normals in an open interval J0 inside J, and its translate by L:

$$
\sigma_{U_n}(J_0)\le\sum_jb_{n,j}\to0,\qquad
\sigma_{U_n}(J_0+L)\le\Bigl(\frac{|J_0|}\delta+1\Bigr)\tan\frac\delta2+\sum_jb_{n,j}\to\frac{|J_0|}2 .
$$

Lower semicontinuity of weakly converging measures on open sets, together with WR.2, gives rho_f=0 on J0 and integral of rho_g over J0 at most |J0|/2. Exhaust the open set by such intervals and use Lebesgue differentiation. The second regime follows by applying the same argument to the horizontally reflected maximizer, as in WR1. QED.

**Lemma AR5' (sharper propagation).** For every maximizer,

$$
q\le\max\{q(0),\ \tfrac18\},\qquad p\ge\min\{p(L),\ -\tfrac18\}.
\tag{AR.10}
$$

**Proof.** Repeat the first case of AR5 with AR.9. On (t_A,t) we are in {p>0,q>0}, so p'=-1-q<=-1 and q'<=p-1/2.

- If t_A=0, then p<=1/2 and q is nonincreasing, so q(t)<=q(0).
- If t_A>0, then q(t_A)=0, p(s)<=1-(s-t_A), and q(t)<= integral from 0 to 1/2 of (1/2-u) du = 1/8.

The second case of AR5 and the reflection are unchanged; AR.9 is reflection symmetric. QED.

**Theorem AR6' (sharp form).** A maximizer with

$$
x_R-x_{tl}\le2\qquad\text{and}\qquad x_{tr}-x_L\le2
\tag{EA_2}
$$

is a horizontal translate of U_*, and then Psi=M/2. In particular O4 holds if and only if every maximizer satisfies (EA_2): each end of a maximizing cap lies within horizontal distance two of the far end of its top face. The candidate's distances are 1/(2 sin beta)=1.7506.

**Proof.** As for AR6, with AR5' in place of AR5. QED.

## 8. Negative examples: WR1's local conclusions do not give A<=F

The following is a floating-point observation, not a theorem.

**Observation AR8.** There are caps satisfying every local conclusion of WR1 for which A(U)>F(f,g). Concretely, they have:

- height one and end edges exactly 1/2;
- the half-height rectangle and W^(2,infinity) quarters;
- 0<=rho_f<=kappa(q) and 0<=rho_g<=kappa(p);
- Baek arms nonnegative and T>0.

They are built from the contact-velocity system with the normalizations f(0)=1, g(0)=1, p(0)=1/2, using

$$
\rho_f=\begin{cases}0,&t<t_1,\\ \kappa(q),&t_1\le t<t_2,\\ \lambda_f\kappa(q),&t\ge t_2,\end{cases}
\qquad \rho_g=\lambda_g\kappa(p),
$$

with (lambda_f,lambda_g) in [0,1]^2 shot so that q(L)=-1/2 and f(L)=1. On [t_1,t_2) the standard regime p<0<q has q>1, so rho_f=q>1. This is an *active* fold of the envelope piece B=c+p nu, whose x-component then moves backwards.

| q(0), t_1, t_2 | lambda_f, lambda_g | W | T | arms | active fold | Psi | A-F (coarse) | A-F (fine) | B-loop area |
|---|---|---|---|---|---|---|---|---|---|
| 1.5, 0.2, 0.5 | 0.31679, 0.45696 | 2.8603 | 2.1664 | 2.500, 2.527 | 0.293 | 0.6235 | 6.2960e-5 | 6.2959e-5 | 1.2368e-4 |
| 1.3, 0.25, 0.45 | 0.65559, 0.52707 | 2.6940 | 1.8108 | 2.300, 2.205 | 0.200 | 0.7305 | 4.1780e-6 | 4.1783e-6 | 4.1795e-6 |

"Arms" are 1+q(0) and 1-p(L), and "active fold" is the measure of {p<0, rho_f>1}. A-F is computed with a refined maximization over angles at 20001 abscissae and 4001 angles (coarse) and at 40001 and 8001 (fine). Both examples have W>2, so integral Lambda_- = 0.

The same evaluator gives A-F=9e-15 and Psi-M/2=-2.3e-11 on the candidate. A fold-free control in the same class gives A-F=-2.7e-9, which is the evaluation error. It has q(0)=1, rho_f=0.6026 kappa(q), rho_g=0.6026 kappa(p), hence rho<=0.61 and SR1 applies.

**Mechanism.** With rho_f>1 on the active set, B has a swallowtail. SR1's formula counts the swallowtail region twice, while the actual roof counts it once. In the second example the whole loop lies in {p<0}, and A-F matches the loop area to within 2e-9. In the first example part of the loop has p>0, where B is not a roof piece, and the excess is smaller than the loop.

**What this does and does not show.**

- AR2 cannot be extended from rho<=1 to the WR.5 class.
- O4 cannot be obtained from a comparison A<=F valid on the whole class described by WR1. Some further consequence of global maximality, such as (EA_2), must enter.
- Both examples violate (EA_2), and their Psi is far below M/2. They are not counterexamples to the candidate.
- Both examples also violate AR.9: rho_g>0 on parts of {p<0,q<0} of measure 0.279 and 0.322, and the first also has rho_f>0 on a set of measure 0.007 in {p>0,q>0}.
- It is **not** decided here whether caps obeying both WR.5 and AR.9 can have A>F.

## 9. What remains, and one possible route

The remaining one-turn gate is (EA_2), or (EA), for **every** maximizer. Equivalently, both Baek arms at the endpoint normals are at most two. No proof is offered.

One route, recorded as a proposal only, is a global two-sided balance.

**Admissible variation.** For a maximizer with T>0 and s in [-T,infinity), the upper support h+s(cos theta)_+ defines a cap U_s. It translates the part of U to the right of a vertical line through the top face. It has |U_s|=|U|+s and W(U_s)=W+s, while every first inner wall moves by s cos t and the companion walls are fixed. Maximality gives

$$
\tfrac12s\le|N(U_s)|-|N(U)|\qquad(s\ge-T).
$$

**Proposed consequence.** If the niche area is differentiable at s=0 with derivative integral of tau_f cos t, where tau_f is the exposure density of the first walls, then

$$
\int_0^L\tau_f\cos t\,dt=\tfrac12=\int_0^L\rho_f\cos t\,dt .
$$

The right equality is the height rise 1-e_R. A pointwise inequality rho_f<=tau_f would then force rho_f=tau_f almost everywhere. Translating the left part instead gives the same for g, with weight sin t.

**The ODE step it would feed.** With exact exposure laws and the activity pattern of SR1, the contact-velocity system becomes the saturated piecewise-linear system: AR.5 in the same-sign and standard regimes, with rho_f=kappa(q), rho_g=kappa(p) in the standard regime (so rho_f=q on a fold), and rho_f=-q, rho_g=p in the reverse regime. The companion script integrates it from (1/2,q(0)). In floating point its first passage time to q=-1/2 is strictly increasing in q(0) on a 50-point grid of [0.05,2.5], rising from 0.84 to 3.00. Its crossing of L is at q(0)=0.7505747248, the candidate value to 3e-11.

**What is unproved.** This is evidence, not a proof. Unproved are:

- differentiability of the niche area;
- the identification of tau_f and the inequality rho_f<=tau_f in the limit;
- the activity pattern in the presence of folds;
- the ODE monotonicity.

## 10. Proof boundary and verification

**Proved here, self-reviewed:**

- AR0–AR2 and AR5, which are elementary;
- AR3 and AR4, which combine WR1, SR1 and AF1–AF3;
- AR6 and AR6';
- AR7, which combines exact polygon algebra with WR1's limit argument.

Together these reduce the sharp weighted one-turn theorem to (EA_2). AR8 is a numerical observation and Section 9 is a proposal. Nothing here proves (EA_2), the value of the one-turn maximum, or any statement about ambidextrous bodies. As the roadmap notes, even a completed O4 gives only |E|<=M+G; the positive clipping term G is untouched here.

The companion script [`check_one_turn_arm_reduction.py`](computer-assisted/one-turn-arms/check_one_turn_arm_reduction.py) and its executed record [`one-turn-arm-reduction-checks.json`](computer-assisted/one-turn-arms/one-turn-arm-reduction-checks.json) do the following in floating point:

- replay the candidate constants and AR.6–AR.7;
- sample the inequalities AR.8 and AR.10 on 218 and 134 admissible random trajectories, with no violation;
- test the discrete statements (a), (b) and the mirror of (a) on 66, 66 and 101 grid-polygon walls, with worst exposure excess 4e-15;
- reproduce AR8 and the Section 9 diagnostic.

These are floating-point checks of stated formulas and examples, not certificates.

No CI or Lean/Lake compilation was used. These are self-reviewed written arguments, not independent refereeing or kernel verification.
