# Romik's description of Gerver's sofa

**Source.** D. Romik, *Differential equations and exact solutions in the moving sofa problem*,
Experimental Mathematics 27 (2018), Section 4. Gerver's sofa is the shape of a rotation path 𝐱
glued from five explicit families (SOL1)–(SOL5), whose 22 parameters satisfy Romik's equations
(27)–(44). Romik solves the system numerically (his Table 1: φ = 0.0391773…, θ = 0.6813015…) and
states without proof that the solution with 0 < φ < θ < π/4 is unique.

**Use in the paper.** Definition 8.1.2 defines Gerver's sofa G from this solution, and
Definitions 8.4.1–8.4.3 and Theorem 8.4.2 use Romik's formulas.

**Lean.** The system, the parameters and the sofa are defined in `MovingSofa/Gerver/Defs.lean`
(`GerverParams`, `GerverParams.IsSolution`, `GerverParams.InBox`, `gerverSofa`). This directory
proves, in `MovingSofa/External/Romik.lean`:

```lean
theorem romik_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox
theorem romik_unique {P Q : GerverParams} (hP : P.IsSolution) (hPb : P.InBox) (hQ : Q.IsSolution)
    (hQb : Q.InBox) : P = Q
theorem romik_bounds {P : GerverParams} (hP : P.IsSolution) (hb : P.InBox) : P.Bounds
```

(all in the namespace `MovingSofa.GerverParams`). The box is φ ∈ [0.039, 0.04], θ ∈ [0.68, 0.69];
the paper quotes φ ∈ [0.039, 0.040]. `romik_bounds` gives enclosures of width 2·10⁻⁷ of all
parameters, which the numerical verifications of Theorem 8.4.1 use.

**Proof.**
- The parameters that enter Romik's system linearly are eliminated symbolically (`rom_mk`), leaving
  two equations H(φ, θ) = 0.
- `Num.lean` encloses H and its partial derivatives on the box by interval arithmetic. It is generated
  by `scripts/romik/mk_num.py`; every step is an explicit inequality checked by `norm_num`.
- `Fix.lean` shows that z ↦ z − M·H(z) maps a small box to itself and is a ½-contraction. Banach's
  fixed point theorem then gives a zero within 10⁻¹⁰ of (0.0391773648, 0.6813015094), and the
  contraction gives that it is the only zero in the box.
- `Calc.lean` holds the interval arithmetic and the Taylor bounds for sin and cos.
