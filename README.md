# Multivariate polynomials

This Lean library provides reusable results about variable ideals, homogeneous
evaluation, substitution into disjoint blocks, coefficient extraction, linear
evaluation and division, monic lifts, first-variable lexicographic degrees,
and subset-weight-one valuations and their naturality on multivariate
function fields.
It builds on mathlib and has no other
Formal Frontier library dependency. Import `MultivariatePolynomials` for the
aggregate, or a [producer module](docs/API.md) for a smaller import. The
[hand-maintained API map](docs/API.md) highlights the public declarations
across fifteen production leaves and the aggregate, including the
localized-coordinate-quotient and weight-one-valuation naturality interfaces.
The project registers nineteen test/example modules.

## Headline results

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
  embedding. See the [naturality module](MultivariatePolynomials/WeightOneNaturality.lean)
  and its [examples](MultivariatePolynomialsTests/WeightOneNaturality.lean).
- **Coordinate differences identify evaluation kernels.** The
  [coordinate-difference ideal](MultivariatePolynomials/EvaluationIdeal.lean)
  at any point over a commutative ring equals the evaluation
  kernel, with a membership criterion and a bridge to the singleton vanishing
  ideal over any field. The variable type may be infinite or empty, and the
  coefficient ring may have zero divisors or be the zero ring.
- **Evaluation ideals commute with substitution.** Polynomial algebra
  homomorphisms contract evaluation kernels to evaluation kernels at the
  substituted coordinates over any commutative semiring and coefficient algebra.
  For commutative rings this contracts coordinate-difference ideals; over fields,
  contraction of the associated prime-spectrum points works also for points
  valued in a field extension. See the [evaluation-ideal module](MultivariatePolynomials/EvaluationIdeal.lean).
- **The variable ideal is not finitely generated.** For a nontrivial
  commutative semiring and infinitely many variables,
  [`MvPolynomial.idealOfVars_not_fg`](MultivariatePolynomials/IdealOfVars.lean)
  proves non-finite generation. A finite union of polynomial supports misses
  some variable; evaluation separating that variable gives a contradiction.
  Mathlib supplies the complementary *finite*-variable ideal theorem. This
  library does not prove the motivating complete short exact sequence.
- **Homogeneous evaluation scales predictably.** The
  [weighted and ordinary scaling laws](MultivariatePolynomials/HomogeneousEvaluation.lean)
  hold over arbitrary commutative semirings with the coefficient homomorphism
  held fixed; the scalar may be zero. See the
  [evaluation guide](docs/homogeneous-polynomial-evaluation.md).
- **Disjoint-block substitution preserves appropriate zero loci.**
  [`blockSubst` and its laws](MultivariatePolynomials/BlockSubstitution.lean)
  distinguish forward-only vanishing from vanishing *iff* the input tuple is
  zero. Structural [renaming, association, unit and iteration laws](MultivariatePolynomials/BlockSubstitutionLaws.lean)
  hold even for noninjective renaming over arbitrary commutative semirings.
  See the [substitution](docs/block-substitution.md) and
  [structural laws](docs/block-substitution-laws.md) guides.
- **Iterates have conditional attained degrees.**
  [`iteratedBlockSubst`](MultivariatePolynomials/IteratedBlockSubstitution.lean)
  uses tuple indices `Fin r → ι`. For a homogeneous base of degree `d`, its
  nominal degree is `d ^ r`; nontrivial coefficients, nonempty indices and a
  forward-only vanishing condition give the exact total degree. With `1 < d`,
  the attained degrees exceed every bound. Neither a base form nor every
  sufficiently large degree is asserted. See the [iteration guide](docs/iterated-block-substitution.md).
- **Exact degree of disjoint-block substitution.**
  [`totalDegree_blockSubst`](MultivariatePolynomials/BlockSubstitutionDegree.lean)
  handles arbitrary inputs, including zero, constants and empty indices, over
  a commutative semiring without zero divisors. See the
  [degree guide](docs/block-substitution-degree.md).
- **Polynomial-parameter coefficient extraction preserves a homogeneous
  label.** The [interchange theorem](MultivariatePolynomials/PolynomialCoefficientHomogeneity.lean)
  works over any commutative semiring, including zero coefficients; it does not
  imply equality of actual degrees. See the
  [coefficient guide](docs/polynomial-coefficient-homogeneity.md).
- **Linear coefficient functionals commute with base-valued evaluation.**
  [`eval_addMonoidAlgebraMap_of_linearMap`](MultivariatePolynomials/LinearCoefficientEvaluation.lean)
  needs only an `R`-linear coefficient map, not a multiplicative one, and
  evaluates at points in `R`. See the
  [linear-evaluation guide](docs/linear-coefficient-evaluation.md).
- **Fixed linear division preserves coefficient ideals.** Given arbitrary
  variable and divisor-index types over a commutative ring, and unit leading
  coefficients, [chosen `R`-linear quotient and remainder maps](MultivariatePolynomials/LinearDivision.lean)
  reconstruct every input. Actual remainder exponents avoid *every*
  componentwise leading cone; every coefficient ideal is preserved, including
  in each quotient coordinate. The choices are not canonical; no Gröbner
  basis is assumed or established, and no finite-variable or domain
  condition is imposed. See the
  [division guide](docs/linear-division.md).
- **Monic lifts preserve literal leading exponents.**
  [`MonomialOrder.exists_monic_lift`](MultivariatePolynomials/MonicLift.lean)
  gives an existential lift along a surjective coefficient map for arbitrary
  variables and commutative rings, including a zero target. Support equality
  is used only in the nontrivial-target proof; the zero-target case takes
  `q = 1`. No injectivity, finite-variable or blanket nontriviality condition
  is needed. See the [lift guide](docs/monic-lift.md).

- **A scalar top first-variable coefficient fixes the maximum lex monomial.**
  [`MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top`](MultivariatePolynomials/FirstVariableLex.lean)
  works over any commutative semiring when the separated polynomial has natural
  degree `d` and its degree-`d` coefficient is a nonzero scalar. The `Fin 0`
  tail and `d = 0` are included. A distinct [pointwise cone lemma](MultivariatePolynomials/FirstVariableLex.lean)
  characterizes exponents above the pure first-variable monomial; it is not a
  lexicographic inequality. See the [lex guide](docs/first-variable-lex.md).

The [localized coordinate quotient](MultivariatePolynomials/LocalizedCoordinateQuotient.lean)
has a coefficient-annihilation kernel law and algebra equivalence from
the localization of `R[X] / ⟨C r * X⟩` at the image of `r` to `R[1/r]`,
for any commutative ring and any `r`. Evaluation at zero on the quotient
and its representative law supply the map; its localization has forward and
inverse fraction laws, a variable-to-zero law, and a chosen-inverse law. The
[ordinary-import clients](MultivariatePolynomialsTests/LocalizedCoordinateQuotient.lean)
exercise nonconstant fractions, a separately justified nonzero variable,
and degenerate coefficient choices.

These results are mathematical interfaces, not source-coverage certifications.
The [API map](docs/API.md) gives declaration names, modules and hypotheses;
[documentation navigation](docs/README.md) links each focused guide and
explains the archived six-module native API snapshot.

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

The aggregate import exposes the current producer modules; direct imports such
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

The repository pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` (nine resolved packages in
`lake-manifest.json`). Install the pinned toolchain and **successfully fetch
the matching precompiled mathlib cache before building**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

The default Lake build includes both the production and test/example targets.
`LEAN_NUM_THREADS=1` can set Lean's runtime task-worker count; it is **not** a
whole-build process or memory limit. The pinned Lake does **not** use
`LAKE_JOBS` as an effective concurrency limit. After-cache two-target project
builds on comparable CI runners took 16.967 and 19.234 seconds, with matching
cache fetches of 39.349 and 41.061 seconds; complete workflows with setup and
private-inclusive axiom auditing took 229 and 240 seconds. Roughly 20–30
seconds for the after-cache project build and 4–5 minutes for the whole
workflow are *planning estimates*, not guaranteed timings. Allow about 8 GiB
available RAM and several GiB free disk as *planning allowances*, not measured
minima or current aggregate peaks; host and concurrent load matter. These
figures do not describe a full mathlib source rebuild. The archived six-module
snapshot's child-process RSS does not measure the expanded current project.

## References

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
