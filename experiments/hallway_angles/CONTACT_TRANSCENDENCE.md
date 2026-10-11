# Transcendence obstructions for the forward contact equation

**Analytic result about the explicit contact equation.** It neither identifies the contact-model crossing with the global transition nor proves that the crossing angle has no elementary closed form. No Lean or CI verification is claimed. The result below is a deduction from classical Gelfond-Schneider and Lindemann-Weierstrass, not from unsuccessful numerical recognition.

Write Qbar for the algebraic numbers over Q. An angle has an algebraic direction when exp(i theta) belongs to Qbar. This includes all rational multiples of pi and all straightedge-and-compass constructible directions. It is different from the numerical angle, measured in radians, being algebraic.

## 1. Exponential form and nondegeneracy

Let 2pi/3<beta<pi and 0<T<pi, and define

    s=sin(beta/2), c=cos(beta/2),
    eta=sqrt((1-4c^2)/(3-4c^2)),
    mu=sqrt(3/[4sin(beta)^2]-1)>0.

The existing forward contact equation is

    F=eta(3s sin T-c cos T-1)
       +tanh(mu T)(s sin T-3c cos T-eta^2)=0.          (1)

Put z=exp(iT), w=exp(2mu T), and define quadratics

    a(z)=(-3is-c)z^2-2z+(3is-c),
    b(z)=(-is-3c)z^2-2eta^2 z+(is-3c),
    P(z)=eta a(z)+b(z), Q(z)=eta a(z)-b(z).

An exact expansion gives

    2z(w+1)F=P(z)w+Q(z).                             (2)

P and Q have no common root. Their values at z=0 are nonzero because c,s,eta>0 and eta<1. For a nonzero common root, a=b=0 would imply, writing v=(z-z^-1)/(2i), u=(z+z^-1)/2,

    3s v-c u=1,  s v-3c u=eta^2,
    v=s/(3-4c^2), u=c/(3-4c^2).

But u^2+v^2=1, whereas the last expressions give 1/(3-4c^2)^2. Since 0<c<1/2, one has 2<3-4c^2<3, a contradiction. In particular P,Q are nonproportional. At any solution, P(z) is nonzero and

    exp(2mu T)=-Q(exp(iT))/P(exp(iT)).                 (3)

Thus taking logarithms does not isolate T: its trigonometric exponential remains on the right.

## 2. Theorem: algebraic hallway direction forces transcendental contact data

Suppose additionally exp(i beta) is algebraic and (1) holds. Then all of

    T, exp(iT), exp(2mu T), sin T, cos T, tan T,
    tanh(mu T)

are transcendental. The tangent exists because cos T cannot be zero.

### exp(iT) is transcendental: Gelfond-Schneider

The hallway hypothesis makes s,c,eta,mu algebraic: exp(i beta/2) is a square root of exp(i beta), and the remaining quantities follow by field operations and square roots. Therefore P,Q have algebraic coefficients.

If z=exp(iT) were algebraic, (3) would make w algebraic. But z is neither zero nor one, and -2i mu is a nonreal algebraic number, hence not rational. Using the logarithm value log z=iT gives

    w=exp[(-2i mu)(iT)]=z^(-2i mu).

Gelfond-Schneider states that every such value is transcendental. This contradicts (3).

### The hyperbolic exponential and tangent are also transcendental

If w were algebraic, (2) would be a nonzero polynomial equation over Qbar for z. It is nonzero because P,Q are nonproportional. That would make z algebraic, contradicting the previous paragraph. Thus w is transcendental, and so is (w-1)/(w+1)=tanh(mu T).

If sin T or cos T were algebraic, the equations

    z^2-2i(sin T)z-1=0,
    z^2-2(cos T)z+1=0

respectively would make z algebraic. Similarly an algebraic finite tan T would make z^2=(1+i tan T)/(1-i tan T) algebraic. This proves the assertions for the circular functions.

### T is transcendental: Lindemann-Weierstrass

Suppose T were a nonzero algebraic number. Expand (2) as a linear combination of the exponentials at the six arguments

    (2mu+2i)T, (2mu+i)T, 2mu T, 2iT, iT, 0.

All six arguments are algebraic and pairwise distinct, since mu>0 and T>0. All coefficients are algebraic, and the combination is nonzero: for example the coefficient of exp((2mu+i)T) is -2eta(1+eta), which is not zero. This contradicts Lindemann-Weierstrass linear independence over Qbar. Hence T is transcendental.

## 3. Consequences for paired closed-form angle guesses

For a contact solution in the branch of the model, put alpha=beta/2-T. It is impossible for BOTH

    exp(i beta) and exp(i alpha)

to be algebraic: those hypotheses would also make exp(iT) algebraic. Thus beta and alpha cannot both have algebraic trigonometric coordinates. Equivalently at least one of cos beta, cos alpha is transcendental.

Consequences include:

- beta/pi and alpha/pi cannot both be rational.
- A construction producing both directions from algebraic coordinates by algebraic operations is excluded, including constructing both by straightedge and compass.
- For any rational multiple beta of pi in the stated domain, T/pi and alpha/pi are irrational, and the above switching-time and trigonometric transcendence conclusions apply.

**Crucial quantifier:** none of these consequences says beta itself is not a rational multiple of pi, nor that cos beta is transcendental at the crossing. Indeed the existing scalar branch has contact solutions at beta=3pi/4, an elementary angle; their switching data have the required transcendence. This is a counterexample to the inference 'nonalgebraic contact data imply a non-elementary hallway angle'.

## 4. A structural obstruction to direct polynomial substitution

For fixed beta in the hyperbolic regime, replacing exp(2mu T) by a function of z=exp(iT) gives the local function z^(-2i mu). It is not an algebraic function of z: one circuit around zero multiplies its value by exp(4pi mu)>1, yielding infinitely many distinct branches. An algebraic function has only finitely many branches at a nonsingular base point.

Consequently this direct exponential substitution does not convert (1) into a polynomial equation merely by adjoining algebraic functions of z. P and Q have no common factor to cancel the obstruction. This is a statement about that functional transformation, NOT about the elementary expressibility of an individual solution and NOT a theorem excluding all Lambert-W representations.

## 5. What these results do not establish

Transcendence is weaker than non-elementary expressibility: pi, log 2, and exp(pi) are familiar elementary-expression constants. The theorem supplies genuine exclusions in the algebraic-direction class, but it does not prove beta_model has no finite expression using exponentials, logarithms, radicals, and trigonometric functions. It does not prove beta_model irrational in units of pi, algebraic or transcendental in radians, or equal to the global beta_c.

The desired complete result remains either a verified explicit expression for the relevant angle, or nonmembership in a specified class of elementary constants. These narrower obstructions should not be presented as completion of that task.

## References for the invoked theorems

1. Michail Karatarakis and Freek Wiedijk, *A formalization of the Gelfond-Schneider theorem*, arXiv:2603.24823v1, Theorem 3.1 and Section 3.1: https://arxiv.org/html/2603.24823v1 . The statement permits a complex algebraic exponent not in Q and any specified logarithm value. This project does not import or run that formalization.
2. Jean-Paul Bezivin and Philippe Robba, *A new p-adic method for proving irrationality and transcendence results*, Annals of Mathematics 129 (1989), 151-160: https://annals.math.princeton.edu/1989/129-1/p05 . The stated Lindemann-Weierstrass theorem gives linear independence over the algebraic numbers.
3. Timothy Y. Chow, *What is a closed-form number?*, arXiv:math/9805045, Sections 2-3: https://arxiv.org/html/math/9805045 . Function-level non-elementarity, transcendence of a constant, and nonmembership in an exp/log expression field are distinct statements.
