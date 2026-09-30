# Multivariate polynomials

This Lean library provides reusable results about variable ideals, homogeneous
evaluation, substitution into disjoint blocks, coefficient extraction, linear
evaluation and division, and monic lifts. It builds on mathlib and has no other
Formal Frontier library dependency. Import `MultivariatePolynomials` for the
aggregate, or a [producer module](docs/API.md) for a smaller import. The
[hand-maintained API map](docs/API.md) lists **39 selected public declarations**
across 11 producer modules (including the aggregate); fixed linear division has
six additional public helpers. The project also registers 13 test/example modules.

## Headline results

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

These results are mathematical interfaces, not source-coverage certifications.
The [API map](docs/API.md) gives declaration names, modules and hypotheses;
[documentation navigation](docs/README.md) links each focused guide and
explains the archived six-module native API snapshot.

## Use and check

The aggregate import exposes the current producer modules; direct imports such
as `MultivariatePolynomials.IdealOfVars`,
`MultivariatePolynomials.LinearDivision` and `MultivariatePolynomials.MonicLift`
work independently. For example, the following is checked in
[`Test/ReadmeExample.lean`](Test/ReadmeExample.lean):

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
snapshot's child-process RSS does not measure the current 24-module aggregate.

## Credits and license

The library is released under [Apache-2.0](LICENSE) with collective
formalization authorship credited to **Formal Frontier Agents**. The original
mathematical motivation, project expositions, contributors, third-party
infrastructure and AI involvement are described in [CREDITS.md](CREDITS.md).
Formal Frontier's source-specific correspondence and working review records
are maintained separately; they are not needed to use this library.
