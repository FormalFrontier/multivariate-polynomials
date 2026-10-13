# Results and examples

This guide gives the full result inventory, hypotheses and boundary cases.
For dependency setup, imports and build commands, see the
[README](../README.md#use-and-check).

## Result inventory

- **Finite collections of polynomial fractions have one finite-variable origin.**
  [`MvPolynomial.exists_finset_fractionRing_map_range`](../MultivariatePolynomials/FractionRingFiniteVariables.lean)
  captures any finite set in any fraction-ring representation of `MvPolynomial σ R`
  over an integral domain `R` in the range of one coefficient-preserving finite-variable
  fraction-ring map. The variables may be infinite and the three universes are independent;
  no field structure on the coefficients or abstract target is assumed. The empty-variable
  stage is a fraction ring of `R`, not generally `R` itself.
- **Subsemirings of polynomial fraction rings are bounded by their stage traces.**
  [`MvPolynomial.ringKrullDim_subsemiring_le_iSup_comap_fractionRing`](../MultivariatePolynomials/PolynomialFractionTrace.lean)
  bounds the Krull dimension of any subsemiring `A` in any fraction-ring
  representation of `MvPolynomial σ R`, for an integral domain `R` and arbitrary
  variables `σ`, by the supremum of the dimensions of its preimages under the
  canonical finite-variable fraction maps. The dimensions are those of the
  preimages, not of the whole stage fields. No one stage need contain all of `A`,
  and `A` need not contain the coefficients. A subring uses its underlying subsemiring.
- **Zeros are closed points of polynomial quotients.** For any ideal `I` in
  `MvPolynomial σ K` with `K` algebraically closed and `σ` finite, the
  [canonical point-set equivalence](../MultivariatePolynomials/QuotientClosedPoints.lean)
  identifies `MvPolynomial.zeroLocus K I` with closed points of the spectrum
  of `MvPolynomial σ K ⧸ I`. The forward prime is the kernel of descended
  evaluation; polynomial membership and inverse coordinates have explicit
  laws. The field and variables may inhabit different universes, and `I` may
  be the unit ideal or define a nonreduced quotient. This point-set result
  itself does not assert a topological or sheaf equivalence.
- **Polynomial coordinate zero loci have their quotient topology.** For any
  field and variable type, the [coordinate topology](../MultivariatePolynomials/ZariskiTopology.lean)
  induced by the evaluation point in the prime spectrum has exactly polynomial
  zero loci as closed sets, with polynomial nonvanishing sets as an open basis.
  Evaluation embeds coordinate tuples; polynomial substitution is continuous.
  Every ideal's zero locus embeds in the closed-point subspace of its quotient
  spectrum, without assuming finiteness or algebraic closure. For an
  algebraically closed field and finitely many variables, the existing
  coordinate equivalence is a homeomorphism onto that inherited subspace,
  including the unit ideal and nonradical ideals. A parabola has inverse
  polynomial-coordinate parametrizations; over the rationals a closed quotient
  point need not arise from a rational zero. No sheaf equivalence is claimed.
- **Separated polynomial point quotients are square-zero extensions.** Over
  any commutative ring, including the zero ring, and any index type, the
  [generator-prescribed forward map](../MultivariatePolynomials/PointSquareZeroPresentation.lean)
  from the quotient by coordinate squares and point relations is bijective
  when differences of distinct evaluation points are units. The resulting
  [polynomial-algebra equivalence](../MultivariatePolynomials/PointSquareZeroQuotient.lean)
  has forward coordinate laws and an inverse law on the evaluation summands;
  no mixed-product relations are added to the defining ideal. See the
  [API guide](../docs/API.md) for the two modules and their boundary examples.
- **Subset-weight-one valuations have full rational residue fields.** For any
  field, any variable type and subset containing a chosen pivot, the
  [weight-one construction](../MultivariatePolynomials/WeightOneValuation.lean)
  identifies the multivariate function field birationally with a univariate
  rational function field over the field of unweighted variables and pivot
  ratios. Minimum subset weight gives a surjective rank-one discrete valuation;
  its pivot is a uniformizer, and its entire residue field is the rational
  function field in those unweighted variables and ratios. The equal-order
  fraction law computes residues from initial coefficients. For the empty
  subset, the separate trivial valuation has no discrete-valuation claim.
- **Weight-one valuations and full residues respect embeddings.** An injective
  coefficient map and variable embedding preserve minimum support weight,
  including at zero, over arbitrary commutative semirings when source weights
  are pulled back from target weights. Over fields the induced maps of fraction
  fields, valuation rings and full residue fields preserve valuations under the
  exact inverse-image condition on weighted variables. Source and target pivots
  may differ: the coordinate change fixes constants and unweighted variables
  and transforms weighted ratios by division by the new pivot ratio. If every
  source variable maps to an unweighted target variable, the *source function
  field* instead embeds into the target residue field without a source pivot;
  an additional weighted target ratio lies outside this image. These results
  require no finite-variable assumption or surjectivity of the variable
  embedding. See the [naturality module](../MultivariatePolynomials/WeightOneNaturality.lean)
  and its [examples](../MultivariatePolynomialsTests/WeightOneNaturality.lean).
- **Coordinate differences identify evaluation kernels.** The
  [coordinate-difference ideal](../MultivariatePolynomials/EvaluationIdeal.lean)
  at any point over a commutative ring equals the evaluation
  kernel, with a membership criterion and a bridge to the singleton vanishing
  ideal over any field. The variable type may be infinite or empty, and the
  coefficient ring may have zero divisors or be the zero ring.
- **Evaluation ideals commute with substitution.** Polynomial algebra
  homomorphisms contract evaluation kernels to evaluation kernels at the
  substituted coordinates over any commutative semiring and coefficient algebra.
  For commutative rings this contracts coordinate-difference ideals; over fields,
  contraction of the associated prime-spectrum points works also for points
  valued in a field extension. See the [evaluation-ideal module](../MultivariatePolynomials/EvaluationIdeal.lean).
- **Hilbert basis theorem for left-Noetherian rings.**
  [`Polynomial.isNoetherianRing_of_isNoetherianRing`](../MultivariatePolynomials/Noetherian.lean)
  proves `IsNoetherianRing (Polynomial R)` for any `R : Type u` with
  `[Ring R]` and `[IsNoetherianRing R]`. The polynomial variable is central;
  coefficient commutativity, nontriviality and absence of zero divisors are
  not required. On commutative rings,
  `Polynomial.isNoetherianRing_of_isNoetherianRing_eq_isNoetherianRing`
  identifies this proof with Mathlib's `Polynomial.isNoetherianRing`.
  Here `IsNoetherianRing R` means `IsNoetherian R R` for the canonical left
  self-action. It does not assume `IsNoetherian R (Polynomial R)`: that
  coefficient-module property is false for every nontrivial coefficient ring.
  The [examples](../MultivariatePolynomialsTests/Noetherian.lean) include the
  noncommutative 16-element ring `Matrix (Fin 2) (Fin 2) (ZMod 2)`, whose
  polynomial ring is infinite but left-Noetherian, the zero ring `ZMod 1`,
  and `ZMod 4` with its nonzero nilpotent `2`.
- **Trivial additive units obstruct polynomial Noetherianity.** For any
  nontrivial semiring `R` whose only additive unit is zero,
  [`Polynomial.not_isNoetherianRing_of_subsingleton_addUnits`](../MultivariatePolynomials/Noetherian.lean)
  proves that `Polynomial R` is not Noetherian as a left module over itself.
  Coefficient multiplication need not be commutative, and zero divisors are
  allowed. In particular, `Polynomial ℕ` is not Noetherian although `ℕ` is.
  The [clients](../MultivariatePolynomialsTests/PolynomialAddUnits.lean) include
  natural, product and noncommutative matrix coefficients and transport to
  multivariate polynomials with a unique variable. The zero ring and integers
  show why the nontriviality and additive-unit hypotheses matter.
- **Coefficient-module Noetherianity requires empty variables or zero coefficients.**
  [`MvPolynomial.isNoetherian_iff`](../MultivariatePolynomials/Noetherian.lean)
  proves, for any commutative semiring `R` and variable type `σ`,
  `IsNoetherian R (MvPolynomial σ R) ↔
  IsNoetherianRing R ∧ (IsEmpty σ ∨ Subsingleton R)`.
  The scalar action is the canonical coefficient action, not the polynomial
  self-action. The coefficient and variable universes are independent; no ring,
  domain, field, nontriviality or finite-variable assumption is required.
  Empty variables recover precisely coefficient Noetherianity, while zero
  coefficients give a Noetherian module for every variable type. For nontrivial
  coefficients even one variable obstructs coefficient-module Noetherianity,
  unlike the finite-variable polynomial-ring criterion below. The
  [examples](../MultivariatePolynomialsTests/Noetherian.lean) include the genuine
  non-ring semiring `ℕ`, the Boolean ring `ZMod 2`, and `ℤ × ZMod 2` with zero
  divisors, and contrast finite-variable integer self-Noetherianity with failure
  for its coefficient module.
- **Noetherian polynomial-ring criteria.** The
  [Noetherian module](../MultivariatePolynomials/Noetherian.lean) proves the
  coefficient-and-variable characterization over arbitrary commutative rings:
  `MvPolynomial σ R` is Noetherian for its self-action exactly when `R` is
  Noetherian and either
  `σ` is finite or `R` is the zero ring. For nontrivial commutative semirings,
  Noetherianity of the polynomial semiring forces `σ` to be finite; no
  semiring Hilbert-basis sufficiency is asserted. The nontrivial-ring form
  removes the zero-ring alternative without imposing a domain hypothesis.
  The coefficient and variable universes are independent. The
  [examples](../MultivariatePolynomialsTests/Noetherian.lean) distinguish empty,
  finite and infinite variables over the integers, `ZMod 6`, and `ZMod 1`.
- **Artinian polynomial-semiring criterion.** For any commutative semiring
  and arbitrary variable type, the [Artinian module](../MultivariatePolynomials/Artinian.lean)
  proves the complete characterization:

  ```lean
  MvPolynomial.isArtinianRing_iff
      {σ : Type u} {R : Type v} [CommSemiring R] :
      IsArtinianRing (MvPolynomial σ R) ↔
        IsArtinianRing R ∧ (IsEmpty σ ∨ Subsingleton R)
  ```

  Here Artinianity uses polynomial multiplication on the canonical left
  self-module, not the coefficient `R`-module action. The coefficient and
  variable universes are independent. No ring, domain, field, reducedness,
  Noetherianity, nontriviality or finite-variable hypothesis is required.
  Empty variables recover exactly coefficient Artinianity; trivial coefficients
  work for every variable type. With nontrivial coefficients, even one variable
  prevents polynomial self-Artinianity.
  The [examples](../MultivariatePolynomialsTests/ArtinianCriterion.lean) include
  empty and single variables over `ℝ≥0` with its usual semiring operations.
  These coefficients are Artinian despite having an infinite carrier, and are
  not a ring: `1` has no additive inverse. Their Artinianity comes from a
  two-element ideal lattice, not a finite carrier. The empty-variable polynomial
  semiring is Artinian, whereas the one-variable polynomial semiring is not.
  The proof reuses Mathlib's `Mathlib.RingTheory.Artinian.Module` for surjective
  descent and regular elements being units in Artinian semirings,
  `Mathlib.Algebra.MvPolynomial.Basic` and `Mathlib.Algebra.MvPolynomial.Equiv`
  for constant coefficients, regular variables and the empty-variable equivalence,
  and its unit-map and zero-unit APIs to force trivial coefficients when a
  variable is present.
- **Coefficient-and-variable ideals have an exact finite-generation criterion.**
  For any commutative semiring `R`, coefficient ideal `I`, and variable subset `S`,
  [`MvPolynomial.ideal_map_C_sup_span_X_image_fg_iff`](../MultivariatePolynomials/IdealOfVars.lean)
  characterizes finite generation of `Ideal.map C I ⊔ Ideal.span (X '' S)`:
  `I` must be finitely generated, and either `S` is finite or `I` is the unit ideal.
  The coefficient and variable universes are independent; no ring, domain,
  subtractivity or finite-ambient-variable hypothesis is required. The
  [examples](../MultivariatePolynomialsTests/CoefficientVariableIdeal.lean) include
  a proper nonsubtractive ideal over `ℕ`, coefficient zero divisors, and the
  zero-ring boundary.
- **Variable ideals are finitely generated exactly for finite subsets.** Over
  any nontrivial commutative semiring,
  [`MvPolynomial.ideal_span_X_image_fg_iff`](../MultivariatePolynomials/IdealOfVars.lean)
  characterizes finite generation of `Ideal.span (MvPolynomial.X '' S)` in the
  full ambient polynomial semiring by finiteness of `S`. No domain, Noetherian
  or finite-ambient-variable assumption is needed. Finite subsets, including
  the empty subset, give finitely generated ideals even with infinitely many
  ambient variables; the converse fails over the zero semiring. Mathlib supplies
  the characteristic membership API `MvPolynomial.mem_ideal_span_X_image`;
  this library supplies the finite-generation iff. The
  [examples](../MultivariatePolynomialsTests/IdealOfVarsSubset.lean) include a proper
  infinite even-variable ideal over `ZMod 6` and the zero-ring boundary `ZMod 1`.
- **The variable ideal is not finitely generated.** For a nontrivial
  commutative semiring and infinitely many variables,
  [`MvPolynomial.idealOfVars_not_fg`](../MultivariatePolynomials/IdealOfVars.lean)
  proves non-finite generation. A finite union of polynomial supports misses
  some variable; evaluation separating that variable gives a contradiction.
  Mathlib supplies the complementary *finite*-variable ideal theorem. This
  library does not prove the motivating complete short exact sequence.
- **Homogeneous evaluation scales predictably.** The
  [weighted and ordinary scaling laws](../MultivariatePolynomials/HomogeneousEvaluation.lean)
  hold over arbitrary commutative semirings with the coefficient homomorphism
  held fixed; the scalar may be zero. See the
  [evaluation guide](../docs/homogeneous-polynomial-evaluation.md).
- **Disjoint-block substitution preserves appropriate zero loci.**
  [`blockSubst` and its laws](../MultivariatePolynomials/BlockSubstitution.lean)
  distinguish forward-only vanishing from vanishing *iff* the input tuple is
  zero. Structural [renaming, association, unit and iteration laws](../MultivariatePolynomials/BlockSubstitutionLaws.lean)
  hold even for noninjective renaming over arbitrary commutative semirings.
  See the [substitution](../docs/block-substitution.md) and
  [structural laws](../docs/block-substitution-laws.md) guides.
- **Iterates have conditional attained degrees.**
  [`iteratedBlockSubst`](../MultivariatePolynomials/IteratedBlockSubstitution.lean)
  uses tuple indices `Fin r → ι`. For a homogeneous base of degree `d`, its
  nominal degree is `d ^ r`; nontrivial coefficients, nonempty indices and a
  forward-only vanishing condition give the exact total degree. With `1 < d`,
  the attained degrees exceed every bound. Neither a base form nor every
  sufficiently large degree is asserted. See the [iteration guide](../docs/iterated-block-substitution.md).
- **Exact degree of disjoint-block substitution.**
  [`totalDegree_blockSubst`](../MultivariatePolynomials/BlockSubstitutionDegree.lean)
  handles arbitrary inputs, including zero, constants and empty indices, over
  a commutative semiring without zero divisors. See the
  [degree guide](../docs/block-substitution-degree.md).
- **Polynomial-parameter coefficient extraction preserves a homogeneous
  label.** The [interchange theorem](../MultivariatePolynomials/PolynomialCoefficientHomogeneity.lean)
  works over any commutative semiring, including zero coefficients; it does not
  imply equality of actual degrees. See the
  [coefficient guide](../docs/polynomial-coefficient-homogeneity.md).
- **Linear coefficient functionals commute with base-valued evaluation.**
  [`eval_addMonoidAlgebraMap_of_linearMap`](../MultivariatePolynomials/LinearCoefficientEvaluation.lean)
  needs only an `R`-linear coefficient map, not a multiplicative one, and
  evaluates at points in `R`. See the
  [linear-evaluation guide](../docs/linear-coefficient-evaluation.md).
- **Fixed linear division preserves coefficient ideals.** Given arbitrary
  variable and divisor-index types over a commutative ring, and unit leading
  coefficients, [chosen `R`-linear quotient and remainder maps](../MultivariatePolynomials/LinearDivision.lean)
  reconstruct every input. Actual remainder exponents avoid *every*
  componentwise leading cone; every coefficient ideal is preserved, including
  in each quotient coordinate. The choices are not canonical; no Gröbner
  basis is assumed or established, and no finite-variable or domain
  condition is imposed. See the
  [division guide](../docs/linear-division.md).
- **Monic lifts preserve literal leading exponents.**
  [`MonomialOrder.exists_monic_lift`](../MultivariatePolynomials/MonicLift.lean)
  gives an existential lift along a surjective coefficient map for arbitrary
  variables and commutative rings, including a zero target. Support equality
  is used only in the nontrivial-target proof; the zero-target case takes
  `q = 1`. No injectivity, finite-variable or blanket nontriviality condition
  is needed. See the [lift guide](../docs/monic-lift.md).

- **A scalar top first-variable coefficient fixes the maximum lex monomial.**
  [`MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top`](../MultivariatePolynomials/FirstVariableLex.lean)
  works over any commutative semiring when the separated polynomial has natural
  degree `d` and its degree-`d` coefficient is a nonzero scalar. The `Fin 0`
  tail and `d = 0` are included. A distinct [pointwise cone lemma](../MultivariatePolynomials/FirstVariableLex.lean)
  characterizes exponents above the pure first-variable monomial; it is not a
  lexicographic inequality. See the [lex guide](../docs/first-variable-lex.md).

The [localized coordinate quotient](../MultivariatePolynomials/LocalizedCoordinateQuotient.lean)
has a coefficient-annihilation kernel law and algebra equivalence from
the localization of `R[X] / ⟨C r * X⟩` at the image of `r` to `R[1/r]`,
for any commutative ring and any `r`. Evaluation at zero on the quotient
and its representative law supply the map; its localization has forward and
inverse fraction laws, a variable-to-zero law, and a chosen-inverse law. The
[ordinary-import clients](../MultivariatePolynomialsTests/LocalizedCoordinateQuotient.lean)
exercise nonconstant fractions, a separately justified nonzero variable,
and degenerate coefficient choices.

These results are mathematical interfaces, not source-coverage certifications.
The [API map](../docs/API.md) gives declaration names, modules and hypotheses;
[documentation navigation](../docs/README.md) links each focused guide and
explains the archived six-module native API snapshot.

## Fraction origins and traces in use

For fraction origins, import `MultivariatePolynomials.FractionRingFiniteVariables`
(or the aggregate) and apply `MvPolynomial.exists_finset_fractionRing_map_range hE`
to `hE : E.Finite`. The resulting common `J` and range inclusion give a preimage
for each member through Mathlib's `IsFractionRing.map`. The
[examples](../MultivariatePolynomialsTests/FractionRingFiniteVariables.lean) capture
`X₀ / 2`, `1 / (X₁ + 1)`, and zero simultaneously over integer coefficients and
infinitely many variables, and include empty collections and empty ambient variables.

For the dimension bound, import `MultivariatePolynomials.PolynomialFractionTrace`
(or the aggregate) and apply
`MvPolynomial.ringKrullDim_subsemiring_le_iSup_comap_fractionRing A`. The
[integer-trace examples](../MultivariatePolynomialsTests/PolynomialFractionTrace.lean)
use the aggregate: the integer image in the fraction field of `ℚ[ℕ]` and every
finite-stage preimage have dimension one, whereas whole stage fields have
dimension zero. The missing element `1/2` makes both image and traces proper.
Every integer already comes from the empty stage; this is not a failure of
uniform stage capture. Both subsemiring and subring clients use the bound.

## Further reading

See the [API map](API.md) for selected declaration names and the
[focused guides](README.md) for longer explanations. Return to the
[library README](../README.md) for the bibliography and credits.
