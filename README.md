# Multivariate polynomials

This Lean library provides reusable results about variable ideals, homogeneous
evaluation, substitution into disjoint blocks, coefficient extraction, linear
evaluation and division, monic lifts, first-variable lexicographic degrees,
and subset-weight-one valuations and their naturality on multivariate
function fields. Polynomial point quotients at pairwise unit-separated points
are canonically equivalent to square-zero extensions of evaluation modules.
For any ideal of a finite-variable polynomial algebra over an algebraically
closed field, its zeros also give precisely the closed points of the quotient
spectrum, even for nonreduced quotients.
The polynomial Zariski topology on field-valued coordinates makes the
evaluation map an embedding and identifies zero loci with inherited
closed-point subspaces under the same finite-variable algebraic-closure
hypotheses.
It builds on mathlib and [Coherent Modules](https://github.com/FormalFrontier/coherent-modules)
for the square-zero action. [Algebraic Direct Limits](https://github.com/FormalFrontier/algebraic-direct-limits)
supplies the generic finite-capture preimage dimension bound used for polynomial
fraction-stage traces. Import `MultivariatePolynomials` for the
aggregate, or a [producer module](docs/API.md) for a smaller import. The
library has twenty-three production leaves and thirty-five test/example modules.
The [hand-maintained API map](docs/API.md) highlights selected public
declarations, including the localized-coordinate-quotient and
weight-one-valuation naturality interfaces.

## Headline results

- **Fraction-ring variable images are exactly the renamed variables.** Over
  any integral domain `R`, an injective index map `ρ : τ → σ` induces a
  [canonical fraction-ring map](MultivariatePolynomials/FractionRingFiniteVariables.lean)
  between arbitrary commutative-ring fraction-ring realizations. The image of
  `X i` belongs to its range exactly when `i ∈ Set.range ρ`; coefficient,
  variable and realization universes are independent. A finite-variable stage
  missing `i` is not surjective, so with infinitely many variables **every**
  finite stage is nonsurjective, although each finite family of fractions has
  a common finite stage. See the [API guide](docs/API.md#multivariatepolynomialsfractionringfinitevariables).
- **Zeros are closed points of polynomial quotients.** For any ideal `I` in
  `MvPolynomial σ K` with `K` algebraically closed and `σ` finite, the
  [canonical point-set equivalence](MultivariatePolynomials/QuotientClosedPoints.lean)
  identifies `MvPolynomial.zeroLocus K I` with closed points of the spectrum
  of `MvPolynomial σ K ⧸ I`. The forward prime is the kernel of descended
  evaluation; polynomial membership and inverse coordinates have explicit
  laws. The field and variables may inhabit different universes, and `I` may
  be the unit ideal or define a nonreduced quotient. This point-set result
  itself does not assert a topological or sheaf equivalence.
- **Separated polynomial point quotients are square-zero extensions.** Over
  any commutative ring, including the zero ring, and any index type, the
  [generator-prescribed forward map](MultivariatePolynomials/PointSquareZeroPresentation.lean)
  from the quotient by coordinate squares and point relations is bijective
  when differences of distinct evaluation points are units. The resulting
  [polynomial-algebra equivalence](MultivariatePolynomials/PointSquareZeroQuotient.lean)
  has forward coordinate laws and an inverse law on the evaluation summands;
  no mixed-product relations are added to the defining ideal. See the
  [API guide](docs/API.md) for the two modules and their boundary examples.
- **Subset-weight-one valuations have full rational residue fields.** For any
  field, any variable type and subset containing a chosen pivot, the
  [weight-one construction](MultivariatePolynomials/WeightOneValuation.lean)
  identifies the multivariate function field birationally with a univariate
  rational function field over the field of unweighted variables and pivot
  ratios. Minimum subset weight gives a surjective rank-one discrete valuation;
  its pivot is a uniformizer, and its entire residue field is the rational
  function field in those unweighted variables and ratios. The equal-order
  fraction law computes residues from initial coefficients. For the empty
  subset, the separate trivial valuation has no discrete-valuation claim.
- **Hilbert basis theorem for left-Noetherian rings.**
  [`Polynomial.isNoetherianRing_of_isNoetherianRing`](MultivariatePolynomials/Noetherian.lean)
  proves `IsNoetherianRing (Polynomial R)` for any `R : Type u` with
  `[Ring R]` and `[IsNoetherianRing R]`. The polynomial variable is central;
  coefficient commutativity, nontriviality and absence of zero divisors are
  not required. On commutative rings,
  `Polynomial.isNoetherianRing_of_isNoetherianRing_eq_isNoetherianRing`
  identifies this proof with Mathlib's `Polynomial.isNoetherianRing`.
  Here `IsNoetherianRing R` means `IsNoetherian R R` for the canonical left
  self-action. It does not assume `IsNoetherian R (Polynomial R)`: that
  coefficient-module property is false for every nontrivial coefficient ring.
  The [examples](MultivariatePolynomialsTests/Noetherian.lean) include the
  noncommutative 16-element ring `Matrix (Fin 2) (Fin 2) (ZMod 2)`, whose
  polynomial ring is infinite but left-Noetherian, the zero ring `ZMod 1`,
  and `ZMod 4` with its nonzero nilpotent `2`.
- **Noetherian polynomial-ring criteria.** The
  [Noetherian module](MultivariatePolynomials/Noetherian.lean) proves the
  coefficient-and-variable characterization over arbitrary commutative rings:
  `MvPolynomial σ R` is Noetherian for its self-action exactly when `R` is
  Noetherian and either
  `σ` is finite or `R` is the zero ring. For nontrivial commutative semirings,
  Noetherianity of the polynomial semiring forces `σ` to be finite; no
  semiring Hilbert-basis sufficiency is asserted. The nontrivial-ring form
  removes the zero-ring alternative without imposing a domain hypothesis.
  The coefficient and variable universes are independent. The
  [examples](MultivariatePolynomialsTests/Noetherian.lean) distinguish empty,
  finite and infinite variables over the integers, `ZMod 6`, and `ZMod 1`.
- **Artinian polynomial-semiring criteria.** For any `R : Type u` with
  `[Semiring R]`, including noncommutative coefficients,
  [`Polynomial.isArtinianRing_iff`](MultivariatePolynomials/Artinian.lean)
  proves `IsArtinianRing (Polynomial R) ↔ Subsingleton R`.
  For arbitrary variable types `σ : Type u` and coefficients `R : Type v`
  with `[CommSemiring R]`,
  [`MvPolynomial.isArtinianRing_iff`](MultivariatePolynomials/Artinian.lean)
  proves `IsArtinianRing (MvPolynomial σ R) ↔ IsArtinianRing R ∧
  (IsEmpty σ ∨ Subsingleton R)`. Both use polynomial multiplication on the
  canonical left self-module, not the coefficient `R`-module action.
  All universes are arbitrary; the multivariate universes are independent.
  No ring or finite-variable hypothesis is imposed. Empty multivariate
  variables recover coefficient Artinianity; trivial coefficients make every
  polynomial zero. The [univariate applications](MultivariatePolynomialsTests/PolynomialArtinianClient.lean)
  include the usual non-ring semiring `ℝ≥0`, the noncommutative 16-element
  matrix ring over `ZMod 2`, and the zero ring `ZMod 1`.
- **Univariate coefficient-module Noetherianity and Artinianity each characterize trivial coefficients.**
  For any `R : Type u` with `[Semiring R]`,
  [`Polynomial.isNoetherian_iff`](MultivariatePolynomials/Noetherian.lean) and
  [`Polynomial.isArtinian_iff`](MultivariatePolynomials/Artinian.lean) give
  `IsNoetherian R (Polynomial R) ↔ Subsingleton R` and
  `IsArtinian R (Polynomial R) ↔ Subsingleton R`, respectively.
  Both use the canonical left coefficient action
  `r • p = Polynomial.C r * p`, not polynomial multiplication as a self-module.
  The universe is arbitrary; no commutativity, ring, domain or field hypothesis
  is required. The [coefficient-module examples](MultivariatePolynomialsTests/PolynomialCoefficientModules.lean)
  distinguish these properties from coefficient self-Noetherianity and
  self-Artinianity, even for the infinite non-ring semiring `ℝ≥0` with finitely
  many ideals.
- **Coefficient-and-variable ideals have an exact finite-generation criterion.**
  For any commutative semiring `R`, coefficient ideal `I`, and variable subset `S`,
  [`MvPolynomial.ideal_map_C_sup_span_X_image_fg_iff`](MultivariatePolynomials/IdealOfVars.lean)
  characterizes finite generation of `Ideal.map C I ⊔ Ideal.span (X '' S)`:
  `I` must be finitely generated, and either `S` is finite or `I` is the unit ideal.
  The coefficient and variable universes are independent; no ring, domain,
  subtractivity or finite-ambient-variable hypothesis is required. The
  [examples](MultivariatePolynomialsTests/CoefficientVariableIdeal.lean) include
  a proper nonsubtractive ideal over `ℕ`, coefficient zero divisors, and the
  zero-ring boundary.
- **The variable ideal is not finitely generated.** For a nontrivial
  commutative semiring and infinitely many variables,
  [`MvPolynomial.idealOfVars_not_fg`](MultivariatePolynomials/IdealOfVars.lean)
  proves non-finite generation. A finite union of polynomial supports misses
  some variable; evaluation separating that variable gives a contradiction.
  Mathlib supplies the complementary *finite*-variable ideal theorem. This
  library does not prove the motivating complete short exact sequence.

The [full results guide](docs/Results.md) also covers simultaneous finite-fraction
origins and their preimage dimension bounds, polynomial Zariski topology,
valuation naturality, evaluation kernels, coefficient-module Noetherianity and
Artinianity, polynomial self-Artinianity, and the substitution, degree, division
and lifting interfaces, with all their hypotheses and boundary cases.
Its [fraction examples](docs/Results.md#fraction-origins-and-traces-in-use)
explain how to use the common finite stage and why whole stage fields do not
provide the subsemiring dimension bound.

## Use and check

To use this library as a dependency, add it to your `lakefile.toml`:

```toml
[[require]]
name = "multivariate-polynomials"
git = "https://github.com/FormalFrontier/multivariate-polynomials.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves a release when you
add or update the dependency; `lake-manifest.json` retains that commit until you
update again. To pin a particular release, use a full commit from that branch's
history instead of `main`.

For the Noetherian criteria and the left-Noetherian Hilbert basis theorem,
import `MultivariatePolynomials.Noetherian` directly. The matrix-ring example
obtains coefficient self-Noetherianity from finiteness and applies the theorem:

```lean
import MultivariatePolynomials.Noetherian
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic

example :
    IsNoetherianRing (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) := by
  let B : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)
  let : IsNoetherianRing B := isNoetherian_of_finite B B
  exact Polynomial.isNoetherianRing_of_isNoetherianRing (R := B)
```

The aggregate import exposes the other producer modules; direct imports such
as `MultivariatePolynomials.IdealOfVars`,
`MultivariatePolynomials.LinearDivision`, `MultivariatePolynomials.MonicLift`
and `MultivariatePolynomials.FirstVariableLex`
work independently. For example, the following is checked in
[`MultivariatePolynomialsTests/ReadmeExample.lean`](MultivariatePolynomialsTests/ReadmeExample.lean):

```lean
import MultivariatePolynomials.IdealOfVars

private theorem readmeRationals : ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ
```

Read the [toolchain file](lean-toolchain), [Lake configuration](lakefile.toml)
and [resolved manifest](lake-manifest.json) for the checkout's versions.
Libraries used together must share one Mathlib revision; Lake resolves one
revision of each package, so do not try to use multiple revisions of this
library in the same project.

For a source checkout, run the following commands from its root directory.
The repository pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` (eleven pinned package records in
`lake-manifest.json`). Install the pinned toolchain and **successfully fetch
the matching precompiled mathlib cache before building**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build
```

The default Lake build includes both the production and test/example targets.
`LEAN_NUM_THREADS=1` can set Lean's runtime task-worker count; it is **not** a
whole-build process or memory limit. The pinned Lake does **not** use
`LAKE_JOBS` as an effective concurrency limit. Allow about 8 GiB
available RAM and several GiB free disk as *planning allowances*, not measured
minima or current aggregate peaks; host and concurrent load matter. Fetch the
matching cache rather than falling back to a Mathlib source rebuild.

## Contents

Each leaf may be imported individually. The aggregate imports twenty-two of
these twenty-three leaves; `MultivariatePolynomials.Noetherian` is direct-only.
Tests and examples are not re-exported. The [API map](docs/API.md) is selective,
not a complete declaration inventory.

| Module (`MultivariatePolynomials.`) | Main interfaces |
| --- | --- |
| [`FractionRingFiniteVariables`](MultivariatePolynomials/FractionRingFiniteVariables.lean) | Simultaneous finite-variable origins for polynomial fractions |
| [`PolynomialFractionTrace`](MultivariatePolynomials/PolynomialFractionTrace.lean) | Krull dimension bounds through finite-stage preimages |
| [`IdealOfVars`](MultivariatePolynomials/IdealOfVars.lean) | Finite-generation criteria for coefficient and variable ideals |
| [`Noetherian`](MultivariatePolynomials/Noetherian.lean) | Left-Noetherian Hilbert basis theorem; univariate coefficient-module Noetherianity iff subsingleton coefficients; multivariate self and coefficient-module criteria (direct import) |
| [`Artinian`](MultivariatePolynomials/Artinian.lean) | Univariate left self- and coefficient-module Artinianity iff subsingleton coefficients over any semiring, including noncommutative ones; multivariate self-module criterion over commutative semirings: Artinian coefficients and empty variables or trivial coefficients |
| [`HomogeneousEvaluation`](MultivariatePolynomials/HomogeneousEvaluation.lean) | Weighted and ordinary homogeneous evaluation laws |
| [`BlockSubstitution`](MultivariatePolynomials/BlockSubstitution.lean) | Disjoint-block substitution and zero-locus laws |
| [`IteratedBlockSubstitution`](MultivariatePolynomials/IteratedBlockSubstitution.lean) | Tuple-indexed iterates and conditional attained degrees |
| [`BlockSubstitutionLaws`](MultivariatePolynomials/BlockSubstitutionLaws.lean) | Renaming, association, unit and iteration laws |
| [`BlockSubstitutionDegree`](MultivariatePolynomials/BlockSubstitutionDegree.lean) | Exact total degree under no zero divisors |
| [`PolynomialCoefficientHomogeneity`](MultivariatePolynomials/PolynomialCoefficientHomogeneity.lean) | Homogeneous labels under polynomial coefficient extraction |
| [`LinearCoefficientEvaluation`](MultivariatePolynomials/LinearCoefficientEvaluation.lean) | Linear coefficients and base-valued evaluation |
| [`LinearDivision`](MultivariatePolynomials/LinearDivision.lean) | Chosen linear division preserving coefficient ideals |
| [`MonicLift`](MultivariatePolynomials/MonicLift.lean) | Monic lifts along surjective coefficient maps |
| [`FirstVariableLex`](MultivariatePolynomials/FirstVariableLex.lean) | First-variable scalar coefficients and lexicographic degree |
| [`EvaluationIdeal`](MultivariatePolynomials/EvaluationIdeal.lean) | Evaluation kernels and contraction under substitution |
| [`QuotientClosedPoints`](MultivariatePolynomials/QuotientClosedPoints.lean) | Closed points of polynomial quotient spectra |
| [`ZariskiTopology`](MultivariatePolynomials/ZariskiTopology.lean) | Polynomial coordinate topology and zero-locus homeomorphisms |
| [`LocalizedCoordinateQuotient`](MultivariatePolynomials/LocalizedCoordinateQuotient.lean) | Localized coordinate quotients and evaluation at zero |
| [`PointSquareZeroPresentation`](MultivariatePolynomials/PointSquareZeroPresentation.lean) | Point quotient presentation and its forward map |
| [`PointSquareZeroQuotient`](MultivariatePolynomials/PointSquareZeroQuotient.lean) | Equivalence with a square-zero extension |
| [`WeightOneValuation`](MultivariatePolynomials/WeightOneValuation.lean) | Subset-weight-one valuations and full residue fields |
| [`WeightOneNaturality`](MultivariatePolynomials/WeightOneNaturality.lean) | Valuation and residue maps under embeddings |

## References

- Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5: rational-function constructions motivate the
  finite-variable fraction-origin theorem. Its algebraic proof uses Mathlib's
  polynomial-support, renaming and localization-representative APIs; it asserts
  no valuation or dimension result.
- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
  2025 draft: §§3.2.5–6 and Exercise 3.2.F (p. 107) motivate coordinate
  differences; Exercise 3.2.L (p. 109) gives the complex-axes localization
  generalized here; Exercise 3.2.P (pp. 110–111) motivates substitution of
  points; Exercise 6.7.E (PDF p. 199) motivates the infinite-variable ideal
  theorem. These are not claims of exact source correspondence or of a proof
  of the full exercises.
- [Mathlib](https://github.com/leanprover-community/mathlib4) supplies the
  multivariate-polynomial, ideal, homogeneity, substitution, localization,
  monomial-order, and linear-map APIs used throughout the library. The leaf
  modules identify the specific formalized dependencies.
- [Algebraic Direct Limits](https://github.com/FormalFrontier/algebraic-direct-limits/tree/5959888b3d648cf1f72038459f63d804093d6c54)
  supplies the generic finite-capture bound for subsemiring preimage dimensions.
  The polynomial-fraction application and integer boundary examples are original
  Formal Frontier formalizations using that bound, this library's simultaneous
  finite-fraction origins, and Mathlib's integer, field and ring-equivalence APIs.
- [Coherent Modules](https://github.com/FormalFrontier/coherent-modules)
  supplies the canonical opposite-module and central-scalar action used by the
  polynomial point quotient's trivial square-zero extension.
- Stefan Schröer, *A simple proof for Hochster's Theorem*,
  arXiv:2606.20016v1, §2, motivates the
  subset-weight-one valuation on polynomial function fields and indirectly
  credits Y. Ershov's earlier specialization construction. The rational
  coordinate and full-residue arguments use independent corrections to the
  presentation.
- Riccardo Brasca's Mathlib theorem
  `Polynomial.lifts_and_natDegree_eq_and_monic` is a univariate analogue
  informing the distinct multivariate monic-lift result.
- Antoine Chambert-Loir's Mathlib monomial-order infrastructure supplies
  `MonomialOrder.div` for fixed linear division and the leading-exponent API
  used by the monic lift.

## Credits and license

The library is released under [Apache-2.0](LICENSE) with collective
formalization authorship credited to **Formal Frontier Agents**. The original
mathematical motivation, project expositions, contributors, third-party
infrastructure and AI involvement are described in [CREDITS.md](CREDITS.md).
