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
aggregate, or a [producer module](docs/API.md) for a smaller import.
The module index below lists the producer interfaces; tests and examples use
`MultivariatePolynomialsTests` as their module root.
The [hand-maintained API map](docs/API.md) highlights selected public
declarations, including the localized-coordinate-quotient and
weight-one-valuation naturality interfaces.

## Headline results

- **Radicals of coefficient-ideal extensions.** For any commutative ring `R`,
  arbitrary variable type `σ` and ideal `I : Ideal R`,
  [`MvPolynomial.radical_map_C`](MultivariatePolynomials/IdealExtension.lean)
  says that extending `I` along the constant-polynomial map commutes with radicals.
  [`MvPolynomial.mem_radical_map_C_iff`](MultivariatePolynomials/IdealExtension.lean)
  characterizes radical membership coefficientwise: a polynomial lies in the
  radical of the extended ideal exactly when every coefficient lies in `I.radical`.

- **Scalar annihilators and non-zero-divisors.** For any commutative semiring
  `R` and arbitrary variable type `σ`,
  [`MvPolynomial.mem_nonZeroDivisors_iff`](MultivariatePolynomials/Regularity.lean)
  characterizes non-zero-divisors by the absence of a nonzero scalar in the
  original coefficient semiring annihilating every coefficient. No individual
  coefficient need be a non-zero-divisor.
  [`MvPolynomial.eq_zero_of_mul_eq_zero_of_smul`](MultivariatePolynomials/Regularity.lean)
  shows that a polynomial with no nonzero scalar annihilator has no nonzero
  polynomial annihilator. The results allow empty or infinite variable types,
  independent universes and trivial coefficient semirings. The interpretation
  in terms of `IsRegular` is asserted only over commutative rings.

- **The degree-zero homogeneous component.** For any commutative semiring
  `R` and arbitrary variable type `σ`,
  [`MvPolynomial.gradeZeroAlgEquiv`](MultivariatePolynomials/GradeZero.lean)
  identifies `R` as an `R`-algebra with Mathlib's original degree-zero homogeneous
  component. Its forward map is the inherited coefficient algebra map, with
  ambient polynomial `C r`; its inverse is `constantCoeff`. The construction uses
  independent universes and commutes with coefficient homomorphisms in the
  ambient polynomial algebras, without finiteness or nontriviality hypotheses.
- **Coefficient ideals over commutative semirings.** For any commutative
  semiring `R`, ideal `I` and arbitrary variable type `σ`,
  [`MvPolynomial.coeffsIn_eq_restrictScalars_map_C`](MultivariatePolynomials/CoefficientIdeal.lean)
  identifies the extension `Ideal.map C I`, restricted to the canonical
  coefficient action, with Mathlib's coefficient submodule `coeffsIn σ I`.
  Polynomial membership is therefore coefficientwise membership, and
  contraction along `C` recovers `I`.
  [`MvPolynomial.ker_map_eq_map_C`](MultivariatePolynomials/CoefficientIdeal.lean)
  identifies the kernel of a coefficient map with the extension of its kernel.
  Coefficients, target coefficients and variables have independent universes;
  no ring, finiteness or nontriviality hypothesis is needed. The
  [natural-number example](MultivariatePolynomialsTests/CoefficientIdeal.lean)
  separates `2 * X` from `X` for the proper extended ideal `(2)` and for
  coefficient reduction modulo two.
- **Powers of augmented coefficient ideals.** For any commutative semiring
  `R`, ideal `I`, natural number `n`, arbitrary variable type `σ`, and polynomial
  `p`, [`MvPolynomial.mem_pow_comap_constantCoeff_iff_coeff_mem_pow`](MultivariatePolynomials/AugmentedIdealPowers.lean)
  characterizes membership in `(I.comap constantCoeff) ^ n`: the coefficient
  at each exponent `d` belongs to `I ^ (n - d.sum (fun _ k => k))`.
  Subtraction is truncated in `ℕ`, so degrees at least `n` impose no
  restriction, rather than vanishing. Coefficients and variables have
  independent universes; empty or infinite variables and trivial coefficient
  semirings are allowed. The bottom coefficient ideal recovers Mathlib's
  variable-ideal power criterion. The
  [integer and boundary examples](MultivariatePolynomialsTests/CoefficientVariableIdeal.lean)
  apply the criterion to `2 * X ∈ (2, X)²`, contrast the constant `2`, and
  include the zeroth power and empty variables.
- **Primary coefficient ideals.** For any commutative ring `R`, ideal `I`
  and arbitrary variable type `σ`,
  [`MvPolynomial.isPrimary_map_C_iff`](MultivariatePolynomials/Primary.lean)
  states that `I.map C` is primary exactly when `I` is primary, using
  Mathlib's `Ideal.IsPrimary`. Coefficients and variables have independent
  universes; empty variable types and the unit ideal are included, with no
  Noetherian or nontriviality hypothesis. The
  [integer example](MultivariatePolynomialsTests/Primary.lean) extends the
  primary, nonradical ideal `(4)`.
- **Supplied primary families and deletion irredundance.** For any commutative
  ring `R`, ideal `I`, family `Q : ι → Ideal R` and variable type `σ`,
  [`MvPolynomial.primary_family_map_C_iff`](MultivariatePolynomials/PrimaryDecomposition.lean)
  says that `I.map C = ⨅ i, (Q i).map C` with every mapped component primary
  exactly when `I = ⨅ i, Q i` with every component primary. Over any commutative
  semiring, [`MvPolynomial.irredundant_iInf_map_C_iff`](MultivariatePolynomials/PrimaryDecomposition.lean)
  preserves and reflects the condition that, for every index, the intersection
  of all other components is not contained in that component. The index may
  be any sort; coefficient, variable and index universes are independent.
  Empty families and variable types are allowed, with no finiteness or
  Noetherian hypothesis. These are transport statements, not existence or
  uniqueness results. The [integer model](MultivariatePolynomialsTests/PrimaryDecomposition.lean)
  uses both for `(12) = (4) ∩ (3)`.

- **Nilpotent coefficients and irreducible polynomial spectra.** For any
  commutative semiring `R` and arbitrary variable type `σ`,
  [`MvPolynomial.isNilpotent_iff_coeff`](MultivariatePolynomials/Nilpotent.lean)
  characterizes nilpotent polynomials by nilpotence of every coefficient.
  [`PrimeSpectrum.irreducibleSpace_mvPolynomial_iff`](MultivariatePolynomials/PrimeSpectrum.lean)
  states that `PrimeSpectrum (MvPolynomial σ R)` is irreducible exactly when
  `PrimeSpectrum R` is irreducible. Coefficients and variables have independent
  universes; empty or infinite variables and trivial coefficients are allowed.
- **Jacobson radicals of coefficient ideals.** For any commutative ring `R`,
  ideal `I` and nonempty variable type `σ`,
  [`Ideal.jacobson_map_mvPolynomial_C`](MultivariatePolynomials/Jacobson.lean)
  identifies `Ideal.jacobson (I.map C)` with `I.radical.map C`.
  In particular, the Jacobson radical of zero in `MvPolynomial σ R` is its
  nilradical. Coefficient and variable universes are independent; no
  Jacobson-ring, Noetherian, properness or nontriviality hypothesis is needed.
  The [integer example](MultivariatePolynomialsTests/Jacobson.lean) separates
  the extended ideal `(4)` from its proper Jacobson radical using `2 * X`.
- **Integral elements over coefficient rings.** For any commutative ring `R`
  and arbitrary variable type `σ`,
  [`MvPolynomial.isIntegral_iff_coeff_isNilpotent`](MultivariatePolynomials/IntegralCoefficients.lean)
  characterizes `IsIntegral R p` by nilpotence of every nonconstant coefficient.
  For reduced `R`,
  [`MvPolynomial.isIntegral_iff_eq_C_coeff_zero`](MultivariatePolynomials/IntegralCoefficients.lean)
  specializes this to `p = C (p.coeff 0)`.
  The coefficient and variable universes are independent; trivial coefficient
  rings and empty or infinite variable types are allowed. Over `ZMod 4`,
  `C 2 * X ()` is a nonconstant square-zero integral polynomial.
- **Integral closure in arbitrarily many variables.** For every integrally closed
  commutative domain `R` and arbitrary variable type `ι`,
  [`MvPolynomial.isIntegrallyClosed`](MultivariatePolynomials/IntegrallyClosed.lean)
  makes the ordinary polynomial ring `MvPolynomial ι R` integrally closed.
  The coefficient and variable universes are independent, and the variables may
  be empty or infinite. No Noetherian or unique-factorization hypothesis is
  imposed on `R`.
- **Flatness of commutative-ring variable renaming.** For every commutative
  ring `R` and arbitrary `f : σ → τ`, with coefficient and variable types in
  independent universes,
  [`MvPolynomial.rename_flat_iff`](MultivariatePolynomials/RenameFlatness.lean)
  characterizes flatness of the full ring homomorphism
  `MvPolynomial.rename (R := R) f` by injectivity of `f` or subsingleton
  coefficients. The scalar action is induced by this original polynomial-ring
  map, not just by `R` or by its image. Injective maps give free polynomial
  extensions after complementary variables are separated; a collision kills
  the regular difference of two distinct variables. The
  [regularity API](MultivariatePolynomials/Regularity.lean) works over every
  commutative ring, including the zero ring. The
  [independent models](MultivariatePolynomialsTests/RenameFlatnessModels.lean)
  and [criterion applications](MultivariatePolynomialsTypeTests/RenameFlatness.lean)
  include a proper inclusion over the integers, a collision over the nonreduced
  ring `ZMod 4`, and the same collision over `ZMod 1`.
  The same module also gives
  [`MvPolynomial.comap_rename_surjective_iff`](MultivariatePolynomials/RenameFlatness.lean)
  for commutative semirings and
  [`MvPolynomial.rename_faithfullyFlat_iff`](MultivariatePolynomials/RenameFlatness.lean)
  for commutative rings: each uses the same injectivity-or-subsingleton condition
  for the original full polynomial map. Their criterion applications include
  the strict inclusion over `ℤ`, prime-spectrum surjectivity over the non-ring
  semiring `ℕ`, an empty source, and a collision over the zero ring.
- **Canonical unique-variable degree.** For any commutative semiring `R`,
  unique variable type `σ` (`[Unique σ]`), and `p : MvPolynomial σ R`,
  [`MvPolynomial.natDegree_uniqueAlgEquiv`](MultivariatePolynomials/UniqueAlgEquiv.lean)
  identifies `Polynomial.natDegree (MvPolynomial.uniqueAlgEquiv R σ p)`
  with `p.totalDegree`. The coefficient and variable universes are independent.
  No nonzero-polynomial or nontrivial-coefficient premise is needed:
  both natural-number degrees assign zero to the zero polynomial.
- **Injectivity and surjectivity of variable renaming.** For any commutative
  semiring `R` and any map `f : σ → τ`, with the coefficient, source-variable
  and target-variable types in independent universes, the canonical renaming
  map from the full polynomial semiring `MvPolynomial σ R` to the full
  polynomial semiring `MvPolynomial τ R` is injective exactly when `f` is
  injective or `R` is subsingleton
  ([`MvPolynomial.injective_rename_iff`](MultivariatePolynomials/Rename.lean)),
  and is surjective exactly when `f` is surjective or `R` is subsingleton
  ([`MvPolynomial.surjective_rename_iff`](MultivariatePolynomials/Rename.lean)).
- **Formal smoothness of variable renaming.** Over any commutative ring `R`,
  [`MvPolynomial.rename_formallySmooth_iff_injective`](MultivariatePolynomials/RenameFormalSmoothness.lean)
  characterizes formal smoothness of the full source polynomial-ring
  homomorphism by injectivity of that homomorphism. Equivalently,
  [`MvPolynomial.rename_formallySmooth_iff`](MultivariatePolynomials/RenameFormalSmoothness.lean)
  says that the variable map is injective or the coefficients are subsingleton.
  The scalar action is induced by the original renaming, not just by `R`.
  The coefficient and variable types have independent universes, with no
  finiteness or nontriviality hypotheses. Complementary variables give the
  polynomial-extension direction; a square-zero lifting obstruction detects
  collisions over nontrivial coefficients.
- **Smoothness of variable renaming.** Over any commutative ring `R`,
  [`MvPolynomial.rename_smooth_iff`](MultivariatePolynomials/RenameSmooth.lean)
  says that the canonical homomorphism on full polynomial rings is smooth
  exactly when the variable map is injective with finite complement, or `R`
  is subsingleton. This is stock `RingHom.Smooth`, including finite
  presentation, for the source-polynomial action induced by renaming.
  Coefficients and both variable types have independent universes; no
  finiteness or nontriviality hypothesis is imposed on them.
- **Formal unramifiedness of variable renaming.** Over any commutative ring
  `R`, [`MvPolynomial.formallyUnramified_rename_iff_surjective`](MultivariatePolynomials/RenameUnramified.lean)
  says that `MvPolynomial.rename f`, as a homomorphism from the full source
  polynomial ring, is formally unramified exactly when it is surjective:
  equivalently, when `f` is surjective or `R` is subsingleton. The coefficient
  and variable types may lie in independent universes, and neither variable
  type must be finite or inhabited. The [boundary examples](MultivariatePolynomialsTests/RenameUnramifiedModels.lean)
  include a collision of variables over the integers, an omitted variable over
  the integers, and an omitted variable over `ZMod 1`.
- **Integrality of polynomial variable renaming.**
  Over any commutative ring `R`,
  [`MvPolynomial.isIntegral_rename_iff`](MultivariatePolynomials/RenameIntegral.lean)
  states that renaming between the full polynomial rings is integral exactly
  when the variable map is surjective or the coefficient ring is subsingleton.
  See the [integrality section](#integrality-of-polynomial-variable-renaming)
  for the precise map, generality and independent models.
- **Algebraicity of polynomial variable renaming.**
  Over any commutative ring `R`,
  [`MvPolynomial.isAlgebraic_rename_iff`](MultivariatePolynomials/RenameAlgebraic.lean)
  states that the full target polynomial ring is algebraic over the full source
  via the specified renaming exactly when the coefficients are nontrivial and
  the variable map is surjective or noninjective. A collision gives a nonzero
  constant annihilator, even when a target variable is missed; zero coefficients
  give no such polynomial, even for identity renaming. This is weak algebraicity,
  not integrality or module finiteness. The coefficient and both variable types
  have independent universes, with no additional ring or finiteness hypotheses.
  [Criterion applications](MultivariatePolynomialsTests/RenameAlgebraicType.lean)
  use the public result. The four weak-algebraicity proofs in the
  [positive models](MultivariatePolynomialsTests/RenameAlgebraicPositive.lean)
  and the proofs in the [negative models](MultivariatePolynomialsTests/RenameAlgebraicNegative.lean)
  use stock Mathlib directly. The positive models also include a shifted-projection
  contrast over `ZMod 4`, whose missing-variable nonintegrality proof uses
  [`MvPolynomial.isIntegral_X_rename_iff`](MultivariatePolynomials/RenameIntegral.lean).
- **Finite presentation of commutative-ring variable renaming.**
  [`MvPolynomial.finitePresentation_rename_iff`](MultivariatePolynomials/RenameFinitePresentation.lean)
  states the relative finite-presentation criterion: subsingleton coefficients,
  or finitely many missed target variables together with finitely many source
  collision participants. Both collision endpoints are counted. See the
  [finite-presentation section](#relative-finite-presentation-of-variable-renaming)
  for the coefficient-ring boundary and infinite-variable examples.
- **Zero-variable presentations and semiring renaming.**
  [`Algebra.FinitePresentation.of_surjective_algebraMap`](MultivariatePolynomials/FinitePresentation.lean)
  gives a zero-variable presentation for a surjective scalar map from a
  commutative semiring to any semiring, with finitely generated ideal kernel.
  For commutative-semiring coefficients with subsingleton additive units,
  [renaming reflects zero](MultivariatePolynomials/RenameFinitePresentationSemiring.lean)
  and every surjective variable map is finitely presented over its full source
  polynomial semiring. No cancellation, order, or finiteness assumption is needed.
  This is Mathlib's ideal-kernel convention, not congruence-based semiring
  finite presentation; a bottom ideal kernel need not imply injectivity.
- **Variable renaming has an exact relative finite-type criterion.**
  [`MvPolynomial.finiteType_rename_iff`](MultivariatePolynomials/RenameFiniteType.lean)
  characterizes finite generation of the target polynomial algebra over the
  source polynomial semiring: the coefficients are subsingleton or the set of
  missed target variables is finite. See the
  [relative finite-type section](#relative-finite-type-of-variable-renaming)
  for the algebra structure, generality and infinite-variable applications.
- **Variable renaming has an exact relative essentially finite-type criterion.**
  [`MvPolynomial.essFiniteType_rename_iff`](MultivariatePolynomials/RenameEssentialFiniteType.lean)
  characterizes `RingHom.EssFiniteType` of renaming for arbitrary `f : σ → τ`
  over a commutative ring `R`, with independent coefficient and variable
  universes: `R` is subsingleton or `Set.Finite ((Set.range f)ᶜ)`. Scalars are
  `MvPolynomial σ R`, acting on `MvPolynomial τ R` by `p • q = rename f p * q`.
  Essential finite type is distinct from finite type, but their criteria
  coincide for these maps. The
  [worked applications](MultivariatePolynomials/RenameEssentialFiniteType.lean)
  contrast successor renaming over `ℤ` (only `0` is missed), `Empty → ℕ`
  with subsingleton coefficients (infinitely many missed variables), and
  even-index renaming over `ℤ`, which is not essentially of finite type.
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
- **Quasi-finiteness of commutative-ring variable renaming.** For any
  commutative ring `R` and arbitrary `f : σ → τ`, with all three types in
  independent universes,
  [`MvPolynomial.rename_quasiFinite_iff`](MultivariatePolynomials/RenameQuasiFinite.lean)
  states that the original full polynomial-ring map is quasi-finite exactly
  when `f` is surjective or `R` is subsingleton. It uses Mathlib's
  residue-field-fiber convention, without a `FiniteType` hypothesis, and
  the full source-polynomial action. Module finiteness supplies the positive
  direction; an omitted target variable gives a surjective evaluation onto
  `R[X]`, reducing the converse to Mathlib's polynomial local obstruction. The
  comparison `MvPolynomial.rename_quasiFinite_iff_finite` identifies
  quasi-finiteness with finiteness of that same ring homomorphism. The
  [independent boundary data and API contract](MultivariatePolynomialsTests/RenameQuasiFiniteModels.lean)
  contrast an omitted variable and a noninjective surjection over `ℤ`, and
  include the zero-coefficient boundary. The three data proofs use Mathlib
  directly, independently of the renaming criteria; the module also imports
  the comparison API for a final private verification contract.
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
- **Omitted variables form a transcendence basis over the source fraction ring.**
  In the same five-universe commutative-domain setting and under the full
  canonical fraction-renaming scalar action,
  [`MvPolynomial.isAlgebraic_adjoin_fractionRing_map_rename_compl`](MultivariatePolynomials/FractionRingTranscendenceBasis.lean)
  proves that `K` is algebraic over the `L`-subalgebra generated by the
  complementary localized variables, and
  [`MvPolynomial.isTranscendenceBasis_fractionRing_map_rename_compl`](MultivariatePolynomials/FractionRingTranscendenceBasis.lean)
  identifies that family as a transcendence basis over `L`. Under the same
  hypotheses,
  [`MvPolynomial.isFractionRing_adjoin_fractionRing_map_rename_compl`](MultivariatePolynomials/FractionRingTranscendenceBasis.lean)
  makes `K` the fraction ring of that generated `L`-subalgebra, for its canonical
  inclusion into `K`. The adjoin is over
  the source **fraction ring**, not the coefficient ring. Neither fraction-ring
  realization needs a `Field` instance, and neither variable type need be finite.
  The [direct-import examples](MultivariatePolynomialsTests/FractionRingTranscendenceBasis.lean)
  include the nonempty complement of `Unit → Bool`, `() ↦ false`, over `ℤ`,
  as well as arbitrary fraction-ring realizations.
- **Zeros are closed points of polynomial quotients.** For any ideal `I` in
  `MvPolynomial σ K` with `K` algebraically closed and `σ` finite, the
  [canonical point-set equivalence](MultivariatePolynomials/QuotientClosedPoints.lean)
  identifies `MvPolynomial.zeroLocus K I` with closed points of the spectrum
  of `MvPolynomial σ K ⧸ I`. The forward prime is the kernel of descended
  evaluation; polynomial membership and inverse coordinates have explicit
  laws. The field and variables may inhabit different universes, and `I` may
  be the unit ideal or define a nonreduced quotient. This point-set result
  itself does not assert a topological or sheaf equivalence.
- **Finite simultaneous polynomial evaluation has an exact surjectivity criterion.**
  For any commutative ring `R`, arbitrary variable type `σ`, finite point-index
  type `ι` and family `a : ι → σ → R`,
  [`MvPolynomial.surjective_eval_family_iff`](MultivariatePolynomials/EvaluationIdeal.lean)
  states that `p ↦ (i ↦ MvPolynomial.eval (a i) p)` is surjective exactly when
  the coordinate differences `a i s - a j s`, for all `s : σ`, generate the
  unit ideal for every pair of distinct indices `i ≠ j`. The three types have
  independent universes. Empty families, empty or infinite variable types,
  repeated points and the zero ring are included; no field hypothesis is needed.
- **Evaluation-kernel powers are detected by translated coefficients.** For any
  commutative semiring `R` and point `a : σ → AddUnits R`,
  [`MvPolynomial.mem_pow_ker_eval_addUnits_iff`](MultivariatePolynomials/EvaluationIdeal.lean)
  characterizes membership in every `n`th evaluation-kernel power by vanishing
  of all coefficients of total degree `< n` after the translation `p(X + a)`.
  Over a commutative ring,
  [`MvPolynomial.mem_pow_ker_eval_iff`](MultivariatePolynomials/EvaluationIdeal.lean)
  allows arbitrary points `a : σ → R`. Both results allow arbitrary variable
  types, independent coefficient/variable universes, and every `n : ℕ`, including zero.
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
- **Radical coefficient-ideal extensions force subtractivity.** For any
  commutative semiring `R`, ideal `I`, and nonempty variable type `σ`,
  [`MvPolynomial.mem_of_add_mem_of_isRadical_map_C`](MultivariatePolynomials/CoefficientIdealSubtractive.lean)
  shows that radicality of `I.map C` forces `b ∈ I` whenever `a ∈ I` and
  `a + b ∈ I`. The coefficient and variable universes are independent; no
  properness, ring, domain or finiteness hypothesis is needed. The original
  prime-extension theorem is a corollary, and the
  [examples](MultivariatePolynomialsTests/CoefficientIdealSubtractive.lean)
  apply both statements to the zero ideal over the natural numbers.
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
- **Antichain coefficients of monomial ideals.** For any commutative semiring
  `R`, arbitrary variable type `σ` and antichain `S : Set (σ →₀ ℕ)`,
  [`MvPolynomial.monomialIdealCoeffMap`](MultivariatePolynomials/MonomialIdeal.lean)
  restricts coefficients from the stock ideal generated by the monic monomials
  with exponents in `S` to `S →₀ R`. It is surjective and semilinear over
  `constantCoeff`, for the full polynomial-semiring action on the ideal and
  the coefficient action on the target. Its coordinate and monomial laws give
  the original coefficients and the corresponding single functions.
  Coefficients and variables have independent universes; empty or infinite
  antichains and variable types, and trivial coefficients, are allowed. The
  [coordinate-axes example](MultivariatePolynomialsTests/MonomialIdealGenerators.lean)
  records the three exponents of `(xy, xz, yz)` over `ℂ`, their antichain and
  monomial presentation, and the ideal's nonzeroness and properness. This is
  a coefficient-map interface, not a minimum-generator formula.
- **Variable classes form the augmentation cotangent basis.** For any
  `(σ : Type u)` and `(R : Type v) [CommRing R]`,
  [`MvPolynomial.idealOfVarsCotangentBasis`](MultivariatePolynomials/Cotangent.lean)
  is a `σ`-indexed `R`-basis of the stock variable-ideal cotangent `I/I²`.
  Its vectors are the classes of `X i`, with inherited coefficient action
  `r • [p] = [C r * p]`. The `_apply` and `_repr_X` lemmas characterize those
  vectors, and `idealOfVarsCotangentBasis_repr_toCotangent` computes each
  coordinate as `(x : MvPolynomial σ R).coeff (Finsupp.single i 1)` for any
  representative `x` in the variable ideal. Quadratic and higher terms do not
  contribute. The variable and coefficient universes are independent; empty
  or infinite variable types, zero rings and nilpotent coefficients are allowed.
  This is an indexed basis, not a numerical rank assertion over the zero ring.

- **Degree-controlled finite interpolation.** Over any commutative ring `R`,
  let `s : Finset ι` select points `a : ι → σ → R`. If, for every distinct
  `i, j ∈ s`, the coordinate differences `a i x - a j x` span the unit ideal,
  then any prescribed values `v : ι → R` are attained on `s` by a polynomial
  of total degree at most `s.card - 1`
  ([`MvPolynomial.exists_eval_eq_totalDegree_le_of_pairwise_span_eq_top`](MultivariatePolynomials/Interpolation.lean)).
  Both the variable type and ambient label type may be infinite; no field or
  domain hypothesis is needed. The theorem asserts existence, not uniqueness.

- **Comparison with Lagrange interpolation.** Over a field, for a unique
  variable type, a polynomial taking prescribed values at distinct nodes and
  having total degree strictly below the number of nodes maps to Mathlib's
  Lagrange interpolant under the canonical single-variable equivalence
  ([`MvPolynomial.uniqueAlgEquiv_eq_interpolate_of_eval_eq`](MultivariatePolynomials/LagrangeComparison.lean)).
  The univariate degree bound follows from the total-degree bound. On a
  nonempty selection, the bound `s.card - 1` also suffices, so the comparison
  applies to any bounded witness supplied by the commutative-ring existence
  theorem. Zero agrees with the empty interpolant separately; an arbitrary
  degree-zero witness need not do so.

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
[ring models](MultivariatePolynomials/RenameFinitePresentationModels.lean)
include the predecessor quotient equivalence identifying `X 0` and `X 1`,
with explicit forward and inverse formulas, uniqueness, and coefficient
naturality. Its equivalence is over the coefficient ring, while its finite
presentation uses the full source polynomial ring. The examples retain empty
variable types in different universes, the zero ring `ZMod 1`, non-Noetherian
sources, and the nonzero nilpotent `2` in `ZMod 4`.

[Empty-variable evaluation](MultivariatePolynomials/FinitePresentation.lean)
identifies surjectivity and ideal-kernel finite generation with those of the
scalar map. A surjective scalar map with finitely generated ideal kernel gives
a zero-variable presentation, even for a noncommutative semiring target.

The commutative-ring hypothesis is substantive. The
[semiring renaming API](MultivariatePolynomials/RenameFinitePresentationSemiring.lean)
assumes only that the additive units of the commutative coefficient semiring
are subsingleton. It gives zero-reflection, bottom ideal kernel, and finite
presentation for surjective variable maps. In its natural-number example,
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

For a target index `j`,
[`MvPolynomial.isIntegral_X_rename_iff`](MultivariatePolynomials/RenameIntegral.lean)
states that `X j` is integral over the full source through the specified
renaming-induced algebra structure exactly when `j ∈ Set.range f` or
`Subsingleton R`. It applies to arbitrary variable maps over commutative rings,
with the same three independent universes. In particular, a collision may make
the full-source algebra algebraic while a missing target variable remains
nonintegral; the shifted-projection example over `ZMod 4` exhibits this contrast.

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

Each producer module may be imported individually. The aggregate's
[public import list](MultivariatePolynomials.lean) records its re-exports;
`MultivariatePolynomials.Noetherian` is direct-only.
The aggregate also re-exports `MultivariatePolynomials.Regularity` through
its public import of `MultivariatePolynomials.RenameFlatness`.
Tests and examples are not re-exported. The [API map](docs/API.md) is selective,
not a complete declaration inventory.

| Module (`MultivariatePolynomials.`) | Main interfaces |
| --- | --- |
| [`FiniteSupport`](MultivariatePolynomials/FiniteSupport.lean) | Exact injectivity criterion for coefficient aggregation; total bivariate degree-and-support recovery iff subsingleton coefficients |
| [`Rename`](MultivariatePolynomials/Rename.lean) | Injectivity and surjectivity of the full polynomial renaming map iff the variable map has the corresponding property or the coefficient semiring is subsingleton |
| [`RenameKernel`](MultivariatePolynomials/RenameKernel.lean) | Over commutative rings, kernel presentation by equal-image variable differences; finite generation iff subsingleton coefficients or finitely many collision participants |
| [`RenameFiniteType`](MultivariatePolynomials/RenameFiniteType.lean) | Finite type over the source polynomial semiring under the explicit renaming algebra iff subsingleton coefficients or finitely many missed target variables |
| [`RenameEssentialFiniteType`](MultivariatePolynomials/RenameEssentialFiniteType.lean) | Essential finite type over the source polynomial ring under renaming iff subsingleton coefficients or finitely many missed target variables |
| [`RenameComplement`](MultivariatePolynomials/RenameComplement.lean) | Complementary-variable algebra equivalence over a commutative semiring, with the retained-variable action bridge and evaluation laws |
| [`Regularity`](MultivariatePolynomials/Regularity.lean) | Differences of distinct variables are regular over every commutative ring, including the zero ring |
| [`RenameFlatness`](MultivariatePolynomials/RenameFlatness.lean) | Full polynomial-ring renaming over a commutative ring is flat exactly when the variable map is injective or the coefficients are subsingleton |
| [`RenameFinitePresentation`](MultivariatePolynomials/RenameFinitePresentation.lean) | Finite-presentation interface over the source polynomial ring: subsingleton coefficients or finite missed target variables and all source collision participants |
| [`FinitePresentation`](MultivariatePolynomials/FinitePresentation.lean) | Empty-variable evaluation API and zero-variable finite presentation from a surjective scalar map with finitely generated ideal kernel over a commutative semiring |
| [`RenameFinitePresentationModels`](MultivariatePolynomials/RenameFinitePresentationModels.lean) | Predecessor principal kernel and quotient equivalence, full-source finite presentation, and infinite-product projection obstruction over nontrivial commutative rings |
| [`RenameFinitePresentationSemiring`](MultivariatePolynomials/RenameFinitePresentationSemiring.lean) | Zero-reflection and full-source finite presentation of surjective renaming for commutative semirings with subsingleton additive units; paired natural-number boundary example |
| [`RenameModuleFinite`](MultivariatePolynomials/RenameModuleFinite.lean) | Finiteness of the full target module over the full source polynomial semiring under the explicit renaming action iff surjective variable map or subsingleton coefficients |
| [`RenameIntegral`](MultivariatePolynomials/RenameIntegral.lean) | Integrality criterion for canonical renaming between full polynomial rings over any commutative ring: surjective variables or subsingleton coefficients |
| [`RenameQuasiFinite`](MultivariatePolynomials/RenameQuasiFinite.lean) | Quasi-finiteness criterion for the original full polynomial-ring map over a commutative ring: surjective variables or subsingleton coefficients, without a finite-type hypothesis |
| [`RenameAlgebraic`](MultivariatePolynomials/RenameAlgebraic.lean) | Algebraicity of the full target over the full source under the specified renaming iff nontrivial coefficients and a surjective or noninjective variable map; arbitrary commutative rings and three independent universes |
| [`FractionRingFiniteVariables`](MultivariatePolynomials/FractionRingFiniteVariables.lean) | Finite-variable origins, variable-image, surjectivity and integrality criteria for polynomial fraction rings |
| [`FractionRingAlgebraicIndependence`](MultivariatePolynomials/FractionRingAlgebraicIndependence.lean) | Over a commutative domain, variables omitted by an injective renaming are algebraically independent over the source fraction ring under the same fraction-renaming scalar action |
| [`FractionRingTranscendenceBasis`](MultivariatePolynomials/FractionRingTranscendenceBasis.lean) | Algebraicity over the source-fraction adjoin of omitted variables and the corresponding transcendence basis for injective renaming |
| [`PolynomialFractionTrace`](MultivariatePolynomials/PolynomialFractionTrace.lean) | Krull dimension bounds through finite-stage preimages |
| [`IdealOfVars`](MultivariatePolynomials/IdealOfVars.lean) | Finite-generation criteria for coefficient and variable ideals |
| [`IdealFiniteGeneration`](MultivariatePolynomials/IdealFiniteGeneration.lean) | Ideal extension along a semiring homomorphism with a retraction preserves and reflects finite generation; arbitrary semirings and independent universes |
| [`CoefficientIdeal`](MultivariatePolynomials/CoefficientIdeal.lean) | Coefficient submodule and extended-ideal identification over commutative semirings; membership, contraction and coefficient-map kernels |
| [`AugmentedIdealPowers`](MultivariatePolynomials/AugmentedIdealPowers.lean) | Coefficient criterion for all powers of constant-coefficient pullback ideals over commutative semirings, with truncated total-degree deficits and agreement with the variable-ideal criterion |
| [`Cotangent`](MultivariatePolynomials/Cotangent.lean) | Prescribed variable-class basis of the augmentation cotangent over arbitrary commutative coefficient rings; coordinates from linear coefficients |
| [`Noetherian`](MultivariatePolynomials/Noetherian.lean) | Left-Noetherian Hilbert basis theorem; univariate coefficient-module Noetherianity iff subsingleton coefficients; multivariate self and coefficient-module criteria (direct import) |
| [`Artinian`](MultivariatePolynomials/Artinian.lean) | Univariate left self- and coefficient-module Artinianity iff subsingleton coefficients over any semiring, including noncommutative ones; multivariate self-module criterion over commutative semirings: Artinian coefficients and empty variables or trivial coefficients |
| [`IntegrallyClosed`](MultivariatePolynomials/IntegrallyClosed.lean) | Integral closure of polynomial rings over integrally closed commutative domains, with arbitrary variable types and independent universes |
| [`UniqueAlgEquiv`](MultivariatePolynomials/UniqueAlgEquiv.lean) | Over any commutative semiring and unique variable type, the canonical univariate equivalence identifies natural degree with total degree, including zero and trivial coefficients |
| [`HomogeneousEvaluation`](MultivariatePolynomials/HomogeneousEvaluation.lean) | Weighted and ordinary homogeneous evaluation laws |
| [`GradeZero`](MultivariatePolynomials/GradeZero.lean) | The coefficient algebra equivalence with the original degree-zero homogeneous component over arbitrary commutative semirings |
| [`BlockSubstitution`](MultivariatePolynomials/BlockSubstitution.lean) | Disjoint-block substitution and zero-locus laws |
| [`IteratedBlockSubstitution`](MultivariatePolynomials/IteratedBlockSubstitution.lean) | Tuple-indexed iterates and conditional attained degrees |
| [`BlockSubstitutionLaws`](MultivariatePolynomials/BlockSubstitutionLaws.lean) | Renaming, association, unit and iteration laws |
| [`BlockSubstitutionDegree`](MultivariatePolynomials/BlockSubstitutionDegree.lean) | Exact total degree under no zero divisors |
| [`PolynomialCoefficientHomogeneity`](MultivariatePolynomials/PolynomialCoefficientHomogeneity.lean) | Homogeneous labels under polynomial coefficient extraction |
| [`LinearCoefficientEvaluation`](MultivariatePolynomials/LinearCoefficientEvaluation.lean) | Linear coefficients and base-valued evaluation |
| [`LinearDivision`](MultivariatePolynomials/LinearDivision.lean) | Chosen linear division preserving coefficient ideals |
| [`MonicLift`](MultivariatePolynomials/MonicLift.lean) | Monic lifts along surjective coefficient maps |
| [`FirstVariableLex`](MultivariatePolynomials/FirstVariableLex.lean) | First-variable scalar coefficients and lexicographic degree |
| [`EvaluationIdeal`](MultivariatePolynomials/EvaluationIdeal.lean) | Evaluation kernels; two-point kernel images, sums and comaximality; contraction under substitution |
| [`Interpolation`](MultivariatePolynomials/Interpolation.lean) | Finite interpolation over commutative rings with a total-degree bound, under pairwise coordinate-difference ideals equal to the unit ideal |
| [`LagrangeComparison`](MultivariatePolynomials/LagrangeComparison.lean) | Identification of bounded unique-variable field polynomials with Mathlib's Lagrange interpolant; comparison for finite-interpolation witnesses and the empty-zero choice |
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
