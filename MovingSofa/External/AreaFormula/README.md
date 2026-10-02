# The area of a planar convex body

**Source.** R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
Press 2013, Remark 5.1.2 and Equation (5.19): for a convex body K in the plane,

  |K| = ½ ∫_{S¹} h_K dσ_K,

where h_K is the support function and σ_K the surface area measure of K.

**Use in the paper.** Theorem 7.1.3 cites it, and Chapter 8 computes the areas of caps with it
(Lemma 8.3.5, Theorems 8.2.4, 8.3.8, 8.5.7).

**Lean.** `area_eq_half_integral_supp` in `MovingSofa/External/AreaFormula.lean`:

```lean
theorem area_eq_half_integral_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    area K = (1 / 2) * ∫ t in Ico 0 (2 * π), supp K t ∂(sigma K)
```

Here σ_K (`sigma K`) is the surface area measure as defined in `MovingSofa/Basic/SurfaceArea.lean`, a
2π-periodic measure on ℝ, and S¹ is represented by [0, 2π). `theorem7_1_3` is this statement.

**Proof.** `Param.lean` builds the arc-length parametrization γ of ∂K from the generalized inverse τ
of the distribution function of σ_K. γ is Lipschitz, γ(y) lies on the edge with normal angle τ(y),
γ′ = v_{τ(y)} outside a countable set, and τ pushes Lebesgue measure forward to σ_K (Schneider's
Theorem 4.2.3 in arc-length form). For K with nonempty interior, the map (y, λ) ↦ c + λ(γ(y) − c) from
an interior point c is injective, its image is K up to a null set, and the change of variables formula
gives the area. If K has empty interior, both sides are 0.
