# Prior work

[Back to the README](../README.md)

## The moving sofa problem

- Leo Moser posed the problem in 1966 (*SIAM Review* 8, Problem 66-11): the largest area of a
  connected planar shape that can be moved around the right-angled corner of a hallway of unit
  width.
- Hammersley found a sofa of area $\pi/2 + 2/\pi \approx 2.2074$ in 1968 and showed that the maximum is
  at most $2\sqrt2 \approx 2.83$.
- Gerver (*Geometriae Dedicata* 42, 1992) found a sofa of area $2.21953\ldots$, bounded by 18 curves
  and segments, and conjectured that it is optimal. Gerver's Theorem 1 states a balance condition that a
  maximum sofa satisfies, and Gerver's Theorem 2 that this sofa satisfies it.
- Romik (*Experimental Mathematics* 27, 2018) derived Gerver's sofa from a system of differential
  equations that balance the sides of the sofa, and solved it explicitly; the Challenge's definition
  of Gerver's sofa follows this description.
- Kallus and Romik (*Advances in Mathematics* 340, 2018) proved, with a computer-assisted method,
  that the maximum is at most $2.37$.
- Baek's preprint *Optimality of Gerver's Sofa* (arXiv:2411.19826, 2024, 119 pages) proves that
  Gerver's sofa is optimal. This repository formalizes version 1 of it, still the only one.
- Concurrent work, in 2024: Baek's [conditional upper bound](https://arxiv.org/abs/2406.10725)
  1 + π²/8 = 2.2337… for sofas with the injectivity condition, which the paper supersedes; Leng, Bi,
  Cha, Pinilla and Thiyagalingam's [numerical evidence](https://arxiv.org/abs/2407.11106), by neural
  networks, that Gerver's sofa is the global maximum, with an improvement of the five-angle bound of
  Kallus and Romik from 2.37 to 2.3337; and Deng's
  [calculus of variations approach](https://arxiv.org/abs/2407.02587), which recovers Gerver's sofa
  as a solution of the Euler–Lagrange equations under convexity assumptions.
- Later work is in the report's [What's next](../baek/REPORT.md#10-whats-next).
- That Gerver's sofa is the only optimal sofa, up to rigid motions, is not proved in Baek's paper.
  Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
  states it as `volume_eq_sofaConstant_iff_congruent_gerversSofa`, in its category `research open`;
  this repository proves that statement. We know of no earlier proof, but have not searched the
  literature systematically.

## Formalizations of the same proof

Two Lean 4 formalizations of Baek's proof appeared shortly before this one:
[deancureton/MovingSofa](https://github.com/deancureton/MovingSofa), written by AI agents directed by Dean Cureton, and
[RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal), written with Claude under the direction of Ruifeng Cao. Both prove the statement of
Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean),
`sofaConstant = volume gerversSofa`, and neither proves the uniqueness of the optimal sofa.
[Formalizations of Baek's proof](../baek/formalizations.md) compares the three: what each proves, their
definitions, how closely each follows the paper, how each treats Gerver's sofa, the errors each found
in the paper, how each is checked, and how each was made.

Like the earlier two, this repository proves the facts about Gerver's sofa that the paper states
without proof or takes from Gerver and Romik (Theorems 6.1.2, 8.4.1 and 8.4.2). For the niche,
Theorem 8.4.1(2), the proof reduces a two-parameter family of inequalities to one-variable
inequalities verified by interval arithmetic.

## References

- L. Moser, Problem 66-11, Moving furniture through a hallway, *SIAM Review* 8 (1966), 381.
- J. L. Gerver, [On moving a sofa around a corner](https://doi.org/10.1007/BF02414066), *Geometriae Dedicata* 42 (1992), 267–283.
- D. Romik, [Differential equations and exact solutions in the moving sofa problem](https://doi.org/10.1080/10586458.2016.1270858), *Experimental Mathematics* 27 (2018), 316–330.
- Y. Kallus, D. Romik, [Improved upper bounds in the moving sofa problem](https://doi.org/10.1016/j.aim.2018.10.022), *Advances in Mathematics* 340 (2018), 960–982.
- J. Baek, [Optimality of Gerver's sofa](https://arxiv.org/abs/2411.19826), arXiv:2411.19826v1 (2024).
- R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd edition, Cambridge University Press, 2013.
