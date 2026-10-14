# Multivariate polynomials

This Lean library provides reusable results about variable ideals, homogeneous
evaluation, substitution into disjoint blocks, coefficient extraction, linear
evaluation and division, monic lifts, first-variable lexicographic degrees,
and subset-weight-one valuations and their naturality on multivariate
function fields. It also gives exact injectivity and recovery criteria for
finite coefficient aggregation. Polynomial point quotients at pairwise
unit-separated points are canonically equivalent to square-zero extensions
of evaluation modules.
For any ideal of a finite-variable polynomial algebra over an algebraically
closed field, its zeros also give precisely the closed points of the quotient
spectrum, even for nonreduced quotients.
The polynomial Zariski topology on field-valued coordinates makes the
evaluation map an embedding and identifies zero loci with inherited
closed-point subspaces under the same finite-variable algebraic-closure
hypotheses.
Variable renaming also has exact finite-type and module-finiteness criteria
relative to the source polynomial semiring. Its finite-presentation interface
over commutative rings also accounts for all source indices participating in collisions.
It builds on mathlib and [Coherent Modules](https://github.com/FormalFrontier/coherent-modules)
for the square-zero action. [Algebraic Direct Limits](https://github.com/FormalFrontier/algebraic-direct-limits)
supplies the generic finite-capture preimage dimension bound used for polynomial
fraction-stage traces. Import `MultivariatePolynomials` for the
aggregate, or a [producer module](docs/API.md) for a smaller import. The
library has 32 production leaves and 58 test/example modules.
The [hand-maintained API map](docs/API.md) highlights selected public
declarations, including the localized-coordinate-quotient and
weight-one-valuation naturality interfaces.

## Headline results

- **Injectivity and surjectivity of variable renaming.** For any commutative
  semiring `R` and any map `f : σ → τ`, with the coefficient, source-variable
  and target-variable types in independent universes, the canonical renaming
  map from the full polynomial semiring `MvPolynomial σ R` to the full
  polynomial semiring `MvPolynomial τ R` is injective exactly when `f` is
  injective or `R` is subsingleton
  ([`MvPolynomial.injective_rename_iff`](MultivariatePolynomials/Rename.lean)),
  and is surjective exactly when `f` is surjective or `R` is subsingleton
  ([`MvPolynomial.surjective_rename_iff`](MultivariatePolynomials/Rename.lean)).
- **Integrality of polynomial variable renaming.**
  [`MvPolynomial.isIntegral_rename_iff`](MultivariatePolynomials/RenameIntegral.lean)
  states that renaming between the full polynomial rings is integral exactly
  when the variable map is surjective or the coefficient ring is subsingleton.
  See the [integrality section](#integrality-of-polynomial-variable-renaming)
  for the precise map, generality and independent models.
- **Algebraicity of polynomial variable renaming.**
  [`MvPolynomial.isAlgebraic_rename_iff`](MultivariatePolynomials/RenameAlgebraic.lean)
  states that the full target polynomial ring is algebraic over the full source
  via the specified renaming exactly when the coefficients are nontrivial and
  the variable map is surjective or noninjective. A collision gives a nonzero
  constant annihilator, even when a target variable is missed; zero coefficients
  give no such polynomial, even for identity renaming. This is weak algebraicity,
  not integrality or module finiteness. The coefficient and both variable types
  have independent universes, with no additional ring or finiteness hypotheses.
  [Criterion applications](MultivariatePolynomialsTests/RenameAlgebraicType.lean)
  use the public result; the [positive](MultivariatePolynomialsTests/RenameAlgebraicPositive.lean)
  and [negative](MultivariatePolynomialsTests/RenameAlgebraicNegative.lean) models
  independently use stock Mathlib only.
- **Finite presentation of commutative-ring variable renaming.**
  [`MvPolynomial.finitePresentation_rename_iff`](MultivariatePolynomials/RenameFinitePresentation.lean)
  states the relative finite-presentation criterion: subsingleton coefficients,
  or finitely many missed target variables together with finitely many source
  collision participants. Both collision endpoints are counted. See the
  [finite-presentation section](#relative-finite-presentation-of-variable-renaming)
  for the coefficient-ring boundary and infinite-variable examples.
- **Variable renaming has an exact relative finite-type criterion.**
  [`MvPolynomial.finiteType_rename_iff`](MultivariatePolynomials/RenameFiniteType.lean)
  characterizes finite generation of the target polynomial algebra over the
  source polynomial semiring: the coefficients are subsingleton or the set of
  missed target variables is finite. See the
  [relative finite-type section](#relative-finite-type-of-variable-renaming)
  for the algebra structure, generality and infinite-variable applications.
- **Module finiteness of variable renaming has a sharper criterion.** For any
  commutative semiring `R` and any map `f : σ → τ`, with all three types in
  independent universes,
  [`MvPolynomial.moduleFinite_rename_iff`](MultivariatePolynomials/RenameModuleFinite.lean)
  states that the full target polynomial semiring is a finite module over the
  full source polynomial semiring under `p • q = MvPolynomial.rename f p * q`
  exactly when `f` is surjective or `R` is subsingleton. This is stronger than
  finite type: over nontrivial coefficients, `Nat.succ : ℕ → ℕ` misses only
  `0`, so its renaming is of finite type but is not module-finite. These are
  source-polynomial scalars, not coefficient-`R` scalars. See the
  [criterion applications](MultivariatePolynomialsTests/RenameModuleFiniteCriterion.lean).
- **Finite coefficient aggregation has an exact injectivity criterion.** For
  types `α`, `β` and `M` in independent universes, an additive commutative
  monoid `M`, and any index map `f : α → β`,
  [`Finsupp.mapDomain_injective_iff`](MultivariatePolynomials/FiniteSupport.lean)
  characterizes injectivity of `Finsupp.mapDomain f : (α →₀ M) → (β →₀ M)`:
  it holds exactly when `f` is injective **or** `M` is subsingleton. The map
  adds coefficients whose indices have the same image; cancellation, a ring
  structure and nontrivial coefficients are not required. The
  [applications](MultivariatePolynomialsTests/FiniteSupport.lean) contrast the
  identity and a constant index map with natural-number coefficients.
- **Joint degree-and-support profiles recover bivariate coefficients only for trivial coefficients.**
  For any additive commutative monoid `M` in an arbitrary universe,
  [`Finsupp.mapDomain_degree_support_hasLeftInverse_iff`](MultivariatePolynomials/FiniteSupport.lean)
  proves that pushing coefficients along
  `d ↦ (d.degree, d.support.card)`, for `d : Fin 2 →₀ ℕ`, admits a total left
  inverse exactly when `M` is subsingleton. The profile groups coefficients
  jointly by total degree and the number of variables with positive exponent.
  The decoder may be **any total function**: no additive, multiplicative or
  linear structure is required. The
  [applications](MultivariatePolynomialsTests/FiniteSupport.lean) exclude every
  decoder over `ℕ` and obtain recovery over the zero ring `ZMod 1`.
- **Variable-renaming kernels have an exact presentation and finite-generation criterion.**
  For any commutative ring `R` and any map `f : σ → τ`, with all three types in
  independent universes,
  [`MvPolynomial.ker_rename_eq_span_X_sub_X`](MultivariatePolynomials/RenameKernel.lean)
  identifies the kernel of `MvPolynomial.rename (R := R) f` with the ideal
  generated by `X i - X j` for pairs satisfying `f i = f j`. Moreover,
  [`MvPolynomial.ker_rename_fg_iff`](MultivariatePolynomials/RenameKernel.lean)
  says that this ideal is finitely generated exactly when `R` is subsingleton
  or the set `{i : σ | ∃ j : σ, i ≠ j ∧ f i = f j}` is finite. This counts
  **both endpoints** of every collision, not just chosen representatives;
  finiteness of individual fibres is not enough. Finite generation is as an
  ideal of the **source polynomial ring** `MvPolynomial σ R`, not as an
  `R`-module. No surjectivity or finite-variable hypothesis is required. See
  the [applications](MultivariatePolynomialsTests/RenameKernelCriterion.lean).
- **Fraction-ring renaming is surjective, equivalently integral, exactly when
  it covers all variables.**
  For any integral domain `R` (`[CommRing R] [IsDomain R]`) and injective
  `ρ : τ → σ`,
  [`MvPolynomial.surjective_fractionRing_map_rename_iff`](MultivariatePolynomials/FractionRingFiniteVariables.lean)
  characterizes surjectivity of the induced fraction-ring map by
  `Function.Surjective ρ`. Its source `L` and target `K` may be any
  commutative-ring fraction-ring realizations with their `Algebra` and
  `IsFractionRing` instances, without `Field` instances. The five universes
  of `R`, `τ`, `σ`, `L` and `K` are independent. For this same map,
  [`MvPolynomial.isIntegral_fractionRing_map_rename_iff`](MultivariatePolynomials/FractionRingFiniteVariables.lean)
  characterizes integrality by the same condition `Function.Surjective ρ`.
  [`MvPolynomial.surjective_fractionRing_map_finset_iff`](MultivariatePolynomials/FractionRingFiniteVariables.lean)
  and
  [`MvPolynomial.isIntegral_fractionRing_map_finset_iff`](MultivariatePolynomials/FractionRingFiniteVariables.lean)
  specialize these criteria to a finite-variable stage `S : Finset σ`: the
  stage map is surjective, equivalently integral, exactly when
  `∀ i : σ, i ∈ S`, with no finiteness hypothesis on the ambient variable
  type. The variable-image criterion identifies the image of `X i` in the
  range exactly when `i ∈ Set.range ρ`. When `i ∉ Set.range ρ`,
  [`MvPolynomial.not_isIntegralElem_fractionRing_map_rename_X`](MultivariatePolynomials/FractionRingFiniteVariables.lean)
  shows that the localized variable `X i` in `K` is not integral over the
  image of the fraction-ring map. Thus every finite stage in infinitely
  many variables is neither surjective nor integral, although each finite
  family of fractions has a common finite stage. See the
  [API guide](docs/API.md#multivariatepolynomialsfractionringfinitevariables).
- **Omitted variables are algebraically independent over the source fraction ring.**
  For a commutative domain `R`, an injective map `ρ : τ → σ`, and arbitrary
  commutative-ring fraction rings `L` of `MvPolynomial τ R` and `K` of
  `MvPolynomial σ R`,
  [`MvPolynomial.algebraicIndependent_fractionRing_map_rename_compl`](MultivariatePolynomials/FractionRingAlgebraicIndependence.lean)
  proves that the images of `X i` in `K`, indexed by
  `{i : σ // i ∉ Set.range ρ}`, are algebraically independent over `L`.
  The `L`-algebra structure on `K` must be induced by the same canonical
  fraction-ring map of `MvPolynomial.rename ρ`, not an arbitrary scalar action.
  The five universes of `R`, `τ`, `σ`, `L` and `K` are independent;
  no `Field` instances or finite index types are required.
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

## Relative finite type of variable renaming

For any map `f : σ → τ` and any commutative semiring `R`,
[`MvPolynomial.finiteType_rename_iff`](MultivariatePolynomials/RenameFiniteType.lean)
states

```lean
@Algebra.FiniteType (MvPolynomial σ R) (MvPolynomial τ R) _ _
  (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra ↔
  Subsingleton R ∨ Set.Finite ((Set.range f)ᶜ)
```

The displayed algebra structure is induced by the renaming homomorphism:
a source polynomial `p` acts on a target polynomial `q` by
`MvPolynomial.rename f p * q`. The base is the **source polynomial semiring**,
not the coefficient semiring. The types `R`, `σ` and `τ` may lie in three
independent universes. Neither variable type need be finite, and `f` need not
be injective or surjective. Empty variable types, non-ring commutative
semirings such as `ℕ`, the zero semiring, and nonreduced rings such as `ZMod 4`
are all allowed.

Finitely many variables outside the image of `f` supply relative algebra
generators. For nontrivial coefficients, finite polynomial support prevents a
finite family of generators from supplying infinitely many missed variables.
For subsingleton coefficients the target polynomial semiring is itself
subsingleton, even if the set of missed variables is infinite. This is a
criterion for finite **algebra** generation, not finite presentation,
coefficient-module finiteness, or finite generation of the source polynomial
kernel ideal.

The [infinite-variable applications](MultivariatePolynomialsTests/RenameFiniteTypeCriterion.lean)
show that shifting natural-number indices by one or two is of finite type,
whereas the even-index embedding `n ↦ 2 * n` is of finite type exactly when
`R` is subsingleton. Its missed variables include the infinite injective image
of `n ↦ 2 * n + 1`. This index embedding sends `X n` to `X (2 * n)`; it is not
the substitution `X n ↦ (X n)²`. The criterion uses Mathlib's polynomial
renaming, finite-support and algebra-adjoin APIs.

## Relative finite presentation of variable renaming

For any map `f : σ → τ` and any commutative ring `R`,
[`MvPolynomial.finitePresentation_rename_iff`](MultivariatePolynomials/RenameFinitePresentation.lean)
has the interface

```lean
@Algebra.FinitePresentation (MvPolynomial σ R) (MvPolynomial τ R) _ _
  (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra ↔
  Subsingleton R ∨ (Set.Finite ((Set.range f)ᶜ) ∧
    Set.Finite {i : σ | ∃ j : σ, i ≠ j ∧ f i = f j})
```

The base is the source polynomial ring with the same renaming-induced action
as in the finite-type criterion. The coefficient and two variable universes
are independent. No Noetherian, domain, reducedness, injectivity, surjectivity
or finite-variable hypothesis is imposed. The collision set contains all
source participants, not one representative per fibre. Subsingleton rings
allow infinitely many missed variables and collisions.

The [integer-coefficient applications](MultivariatePolynomialsTests/RenameFinitePresentationCriterion.lean)
use this interface for successor and predecessor renaming and for the negative
paired projection `ℕ × Bool → ℕ`. Separate
[ring examples](MultivariatePolynomialsTests/RenameFinitePresentationModels.lean)
construct finite presentations from Mathlib's APIs, including empty variable
types in different universes, the zero ring `ZMod 1`, non-Noetherian sources,
and the nonzero nilpotent `2` in `ZMod 4`.

The commutative-ring hypothesis is substantive. In the
[natural-number example](MultivariatePolynomialsTests/RenameFinitePresentationSemiring.lean),
paired projection has bottom ideal kernel and a zero-variable finite presentation
in Mathlib's existing class, although all infinitely many source indices collide.
Bottom ideal kernel does not imply injectivity over this semiring. This
ideal-kernel definition is distinct from a congruence-based finite-presentation
notion for semirings.

## Integrality of polynomial variable renaming

For any commutative ring `R` and any map `f : σ → τ`,
[`MvPolynomial.isIntegral_rename_iff`](MultivariatePolynomials/RenameIntegral.lean)
has the statement

```lean
RingHom.IsIntegral ((MvPolynomial.rename (R := R) f).toRingHom) ↔
  Function.Surjective f ∨ Subsingleton R
```

This is Mathlib's existing predicate for the canonical ring homomorphism
`MvPolynomial σ R →+* MvPolynomial τ R`. Integrality is relative to the
**full source polynomial ring**, with the full target polynomial ring as
codomain. It is not coefficient-`R` integrality, integrality of a fraction-ring
map, or integrality after restricting the codomain to the image. In particular,
when `σ = τ` the displayed renaming map still determines the question; it is
not replaced by the identity map or a default algebra structure.

The types `R : Type u`, `σ : Type v` and `τ : Type w` have three independent
universes. No injectivity, finiteness, domain, reducedness, Noetherian or
nontriviality hypothesis is imposed. Noninjective surjections are allowed.
Subsingleton coefficients account for nonsurjective maps over the zero ring,
and empty source or target variable types are included.

The named
[criterion applications](MultivariatePolynomialsTests/RenameIntegralCriterion.lean)
derive their integrality conclusions from this equivalence. They include
surjections, subsingleton coefficients, the noninjective
projection `ℕ × Bool → ℕ`, empty-to-empty renaming, and successor renaming,
which is integral exactly when the coefficients are subsingleton. They also
include the noninjective, nonsurjective map `(n, b) ↦ n + 1`, whose renaming
is nonintegral over nontrivial coefficients.

Two separate independent model files are included:
`MultivariatePolynomialsTests/RenameIntegralPositive.lean` and
`MultivariatePolynomialsTests/RenameIntegralNegative.lean`. They give direct
positive examples (including infinite and noninjective surjections, a nonzero
nilpotent coefficient in `ZMod 4`, zero-ring boundaries and three independent
lifted universes) and negative examples over
nontrivial, possibly nonreduced rings, without applying the displayed equivalence.
The negative controls include the noninjective, nonsurjective shifted projection
`(n, b) ↦ n + 1`; its proof factors through successor rather than asserting
transcendence over the full source ring. These models do not prove the headline.

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

For finite coefficient aggregation, import `MultivariatePolynomials.FiniteSupport`
and use `Finsupp.mapDomain_injective_iff` or
`Finsupp.mapDomain_degree_support_hasLeftInverse_iff`. The
[finite-support applications](MultivariatePolynomialsTests/FiniteSupport.lean)
show both criteria with concrete coefficient monoids.

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

For variable subsets, `MvPolynomial.idealOfVars_map_rename` identifies the
image of the all-variable ideal under any renaming `f` with
`Ideal.span (MvPolynomial.X '' Set.range f)`. Taking `f` to be the inclusion
of `S` gives the span of the selected variables. Mathlib's `killCompl` for
that inclusion **retains `S`** and kills variables outside it; to **eliminate
`S` by setting its variables to zero**, use the inclusion of `Sᶜ` instead. See the
[subset examples](MultivariatePolynomialsTests/IdealOfVarsSubset.lean).

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

Each leaf may be imported individually. The aggregate imports 31 of
these 32 leaves; `MultivariatePolynomials.Noetherian` is direct-only.
Tests and examples are not re-exported. The [API map](docs/API.md) is selective,
not a complete declaration inventory.

| Module (`MultivariatePolynomials.`) | Main interfaces |
| --- | --- |
| [`FiniteSupport`](MultivariatePolynomials/FiniteSupport.lean) | Exact injectivity criterion for coefficient aggregation; total bivariate degree-and-support recovery iff subsingleton coefficients |
| [`Rename`](MultivariatePolynomials/Rename.lean) | Injectivity and surjectivity of the full polynomial renaming map iff the variable map has the corresponding property or the coefficient semiring is subsingleton |
| [`RenameKernel`](MultivariatePolynomials/RenameKernel.lean) | Over commutative rings, kernel presentation by equal-image variable differences; finite generation iff subsingleton coefficients or finitely many collision participants |
| [`RenameFiniteType`](MultivariatePolynomials/RenameFiniteType.lean) | Finite type over the source polynomial semiring under the explicit renaming algebra iff subsingleton coefficients or finitely many missed target variables |
| [`RenameFinitePresentation`](MultivariatePolynomials/RenameFinitePresentation.lean) | Finite-presentation interface over the source polynomial ring: subsingleton coefficients or finite missed target variables and all source collision participants |
| [`RenameModuleFinite`](MultivariatePolynomials/RenameModuleFinite.lean) | Finiteness of the full target module over the full source polynomial semiring under the explicit renaming action iff surjective variable map or subsingleton coefficients |
| [`RenameIntegral`](MultivariatePolynomials/RenameIntegral.lean) | Integrality criterion for canonical renaming between full polynomial rings over any commutative ring: surjective variables or subsingleton coefficients |
| [`RenameAlgebraic`](MultivariatePolynomials/RenameAlgebraic.lean) | Algebraicity of the full target over the full source under the specified renaming iff nontrivial coefficients and a surjective or noninjective variable map; arbitrary commutative rings and three independent universes |
| [`FractionRingFiniteVariables`](MultivariatePolynomials/FractionRingFiniteVariables.lean) | Finite-variable origins, variable-image, surjectivity and integrality criteria for polynomial fraction rings |
| [`FractionRingAlgebraicIndependence`](MultivariatePolynomials/FractionRingAlgebraicIndependence.lean) | Over a commutative domain, variables omitted by an injective renaming are algebraically independent over the source fraction ring under the same fraction-renaming scalar action |
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
