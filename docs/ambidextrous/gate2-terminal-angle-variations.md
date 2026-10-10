# Gate 2: exact one-sided terminal-angle variations

Written proof, independently checked within the research session,
October 10, 2026. Gate 2 remains open. All statements below use the
actual partial one-cap spatial objective from
[PD](gate2-partial-cap-domain-reductions.md), including its whole first
outgoing wall. They do not differentiate the earlier weighted support
objective.

Let U be a downward convex cap of height at most one, with projection
I=[l,r], middle half J=[l+(r-l)/4,r-(r-l)/4], and roof A. Put L=pi/2,
mu_t=(cos t,sin t), nu_t=(-sin t,cos t), and

    f(t)=h_U(mu_t),   g(t)=h_U(nu_t),
    R_t(x)=(f(t)-1-x cos t)/sin t,
    D_t(x)=(g(t)-1+x sin t)/cos t,
    n_a(x)=max(0,sup_{0<t<a} min(R_t(x),D_t(x))),
    N_a(x)=max(n_a(x),R_a(x)),
    P_a(U)=integral_{I\J} A - integral_J N_a.

The outgoing strip is the first wall R_a. No horizontal-reflection
invariance at fixed a is assumed.

## 1. Exact right derivative in the terminal angle

Fix a in [pi/4,L). The support right derivative f'_+(a) exists. Let

    B_+(a)=(f(a)-1) mu_a + f'_+(a) nu_a.

Equivalently, B_+ is the upper/left endpoint of the outer mu_a supporting
face, translated inward by mu_a. Define disjoint measurable sets

    E={x in J: R_a(x)>n_a(x)},
    H={x in J: R_a(x)=n_a(x)}.

Then the exact pointwise right derivative is

    d_+ N_a(x)/da = (x-B_{+,x})/sin(a)^2              on E,
                    ((x-B_{+,x})/sin(a)^2)_+         on H,
                    0                              elsewhere.       (TV1)

Consequently

    d_+ P_a(U)/da
      = -1/sin(a)^2 [ integral_E (x-B_{+,x}) dx
                      + integral_H (x-B_{+,x})_+ dx ].               (TV2)

In particular every joint global maximizer (U,a) with a<L satisfies

    integral_E (x-B_{+,x}) dx
       + integral_H (x-B_{+,x})_+ dx >= 0.                            (TV3)

### Proof

Uniformly on compact x intervals,

    R_{a+h}(x)=R_a(x)+h (x-B_{+,x})/sin(a)^2+o(h).

The old n_a remains among the competitors defining n_{a+h}. Every
newly visited two-ray value at a+t is at most R_{a+t}. If R_a>n_a,
then min(R_a,D_a)<R_a; otherwise its limit from below would already
give n_a>=R_a. Continuity gives a strict gap for all sufficiently
nearby newly visited angles, so only R_{a+h} moves the maximum to
first order. This gives the first case of TV1.

If R_a<n_a, the strict gap makes the value locally constant to first
order, giving the last case. If R_a=n_a, the lower bound

    max(n_a,R_{a+h}) <= N_{a+h}

and the upper bound

    N_{a+h} <= max(n_a,sup_{0<=t<=h} R_{a+t})

have the same right derivative: the positive part of R'_+(a).
This gives the middle case. Local boundedness of the supports and
their one-sided derivatives makes these difference quotients
uniformly bounded on J, so dominated convergence proves TV2.
TV3 is the necessary one-sided derivative inequality at a maximum.

The formula is valid at an outer facet: it uses f'_+(a), not an
unjustified single f'(a).

### The corresponding exact left derivative

Suppose a>pi/4. Let B_-=(f(a)-1)mu_a+f'_-(a)nu_a, the lower/right
endpoint of the outer supporting face translated inward by mu_a.
Partition H further into H_old and H_new. Put x in H_old if R_a=0
(the fixed floor competitor) or if some t<a attains min(R_t,D_t)=R_a.
Put every other x in H_new. Then

    d_- N_a(x)/da = (x-B_{-,x})/sin(a)^2             on E or H_new,
                    min((x-B_{-,x})/sin(a)^2,0)      on H_old,
                    0                              elsewhere.       (TV1L)

Here d_- denotes [N_a-N_{a-h}]/h. On H_new, R_a>0 and the running
maximum is attained only at t=a, where min(R_a,D_a)=R_a. Write
R'_- for the left derivative of R and m'_- for that of min(R,D).
If R_a<D_a then m'_-=R'_-. If R_a=D_a then
m'_-=max(R'_-,D'_-). The terminal running maximum requires m'_->=0.
Its value at a-h is R_a-h m'_-+o(h): the elementary linear upper and
lower estimates near a prove this even without monotonicity of m.
Taking the maximum with R_{a-h}=R_a-h R'_-+o(h) leaves the derivative
R'_-. This proves the H_new case. On H_old a fixed earlier maximizing
competitor remains for every sufficiently small h, so the derivative
is min(R'_-,0). The strict cases are immediate. The same uniform local
angle-Lipschitz bound permits integration of TV1L.

Thus, in particular, if E is null and H_old is null, an interior-angle
maximum requires

    integral_H (x-B_{-,x}) dx <=0.                                 (TV3L)

For a genuine terminal-only first-wall tie, the absence of a larger
earlier R_t forces x>=B_{-,x}; any positive-length such H therefore
contradicts TV3L. This is a useful exclusion when all terminal charge
comes only from a new terminal ray. It does not replace the mixed
old-contact/strict-strip analysis for a general maximizing cap.

## 2. Exact positive-measure tie obstruction

Take U=[-1,1] x [0,1], J=[-1/2,1/2], and

    a=arctan(4/3),  cos a=3/5, sin a=4/5.

Here f(t)=cos t+sin t, so B_{+,x}=1-cos a=2/5.
For every x in [2/5,1/2] and every t<=a,

    partial_t R_t(x)=(x-1+cos t)/sin(t)^2 >=0.

Also D_a(x)>R_a(x)>0 on that entire interval. Thus

    n_a(x)=R_a(x),  [2/5,1/2] subset H.

Its contribution to the second term in TV2 is exactly

    integral_{2/5}^{1/2} (x-2/5)/(16/25) dx = 1/128.                (TV4)

Therefore a formula that differentiates only the strict outgoing-strip
set E omits a nonzero first-order term, even for a rectangle and an
interior terminal angle. This does not refute any sharp inequality;
it refutes that simplified first-variation formula.

## 3. Scope of terminal occupations and of this note

The fixed-angle [source theorem PS](gate2-partial-endpoint-source-and-green.md),
Section 9, constructs a terminal occupation chi in [0,1]. It is one on
the strict strip set E and on every positive terminal-only tie set H_new.
It may be fractional on H_old. Its integral is the horizontal length of
the charged outer terminal facet. PS proves the H_new statement by
localizing finite sources to the terminal angle and using the order-mesh
bound to exclude accumulation of adjacent nonterminal source mass.

These fixed-angle facts do not supply a shared occupation for a joint
facet offset and angle rotation, nor a first horizontal moment law. The
right derivative TV1–TV3 has its own exact positive-part tie term, which
must be retained when combining it with source mass. In particular one
must not differentiate only E, as TV4 demonstrates.

The [positive-tilt first-unit theorem](gate2-positive-tilt-first-unit-exclusion.md)
uses TV3 together with fixed-angle terminal mass and full occupation on
its terminal-only interval. Its proof requires no additional joint
moment identity. The universal partial-cap sharp value, the full
independent-angle spatial charge, and Gate 2 are not conclusions of
this terminal derivative note.
