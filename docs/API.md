# Public API map

This is a hand-maintained map of selected public interfaces, **not** freshly
generated native documentation, a build record or proof certification. Import
`MultivariatePolynomials` for all production families, or the named leaf for
one family. The localized quotient and weight-one valuation leaves also have
their evaluation, equivalence and characteristic laws. The weight-one
naturality leaf describes embeddings of valuation rings and their full
residue fields, including independent choices of pivot.
This selection does not count every public helper. [README](../README.md)
explains how to build the library. The
[initial native snapshot](API-initial-snapshot.md) and its
[unchanged manifest](api-manifest.json) cover only the original six-module
revision, not this expanded interface.

## `MultivariatePolynomials.EvaluationIdeal`

For arbitrary types of variables `σ` and a commutative ring `R`,
`MvPolynomial.ideal_span_X_sub_C_eq_ker_eval` identifies the span of
`X i - C (x i)` for `i : σ` with `RingHom.ker (MvPolynomial.eval x)`.
`MvPolynomial.mem_ideal_span_X_sub_C_iff` characterizes membership by
`MvPolynomial.eval x p = 0`. Over any field `k`,
`MvPolynomial.ideal_span_X_sub_C_eq_vanishingIdeal_singleton` identifies
the same span with `MvPolynomial.vanishingIdeal k {x}` without requiring
algebraic closure or finitely many variables. The kernel equality follows by
comparing the quotient map with evaluation followed by the constant map;
membership and the singleton bridge follow from that equality.

`MvPolynomial.ker_aeval_comap` contracts evaluation kernels along polynomial
algebra homomorphisms, with arbitrary source and target variable types and
points valued in any commutative coefficient algebra. Over a commutative ring,
`MvPolynomial.ideal_span_X_sub_C_comap` specializes this to coordinate-difference
spans, using Mathlib's `MvPolynomial.comap` for the induced point.
`MvPolynomial.pointToPoint_comap` identifies contraction of the corresponding
prime with the point obtained by evaluating images of source coordinates, even
when the points take values in a larger field; `pointToPoint_comap_self` uses
`MvPolynomial.comap` in the same-field case. The
[evaluation-naturality clients](../MultivariatePolynomialsTests/EvaluationIdealNaturality.lean)
include a quotient evaluation square requiring vanishing on the target ideal
and an independent counterexample when vanishing fails.

## `MultivariatePolynomials.QuotientClosedPoints`

[Producer](../MultivariatePolynomials/QuotientClosedPoints.lean) and
[ordinary-import clients](../MultivariatePolynomialsTests/QuotientClosedPoints.lean).
For a field `K` and arbitrary variable type `σ`, `zeroLocusQuotientEval I a`
is the canonical `K`-algebra homomorphism from `MvPolynomial σ K ⧸ I` to `K`
for a zero `a`. Its `_comp`, `_mk` and `_X` laws give its values without
unfolding the definition. For every field and any variable type,
`zeroLocusClosedPoint I a` is the closed point whose ideal is the kernel of
this evaluation; its `_asIdeal` and `_mem_iff` laws characterize that point.
If `K` is algebraically closed and `σ` is finite,
`zeroLocusEquivClosedPoints I` identifies the zero locus of every ideal,
including the unit ideal, with the closed quotient-spectrum points. Its
`_apply` and `_symm_apply` laws identify its maps with the standalone
`zeroLocusClosedPoint` and `closedPointZeroLocus`. The inverse map's `_ideal`,
`_mem_iff` and `_coordinate` laws characterize its coordinates directly;
the equivalence's `_asIdeal`, `_mem_iff`, `_symm_mem_iff`, `_symm_coordinate`
and round-trip laws follow from these. Independent universes and nonreduced
quotients require no extra hypotheses. This is a point-set equivalence, not an
equivalence of spaces or schemes.

## `MultivariatePolynomials.ZariskiTopology`

[Producer](../MultivariatePolynomials/ZariskiTopology.lean) and
[ordinary-import examples](../MultivariatePolynomialsTests/ZariskiTopology.lean).
`MvPolynomial.ZariskiSpace K σ` wraps tuples of field-valued coordinates and
has the topology induced by `pointToPoint` into the polynomial prime spectrum,
not a topology on `K` or on the function type. `coordinatesEquiv`, `ext`,
`pointToPoint_asIdeal`, and `mem_zeroLocus_iff_mem_spectrum_zeroLocus`
characterize its coordinates and evaluation prime. For any ideal,
`isClosed_iff` characterizes closed sets by `zeroLocus`; `isOpen_iff`,
`basicOpen_eq_preimage`, and `isTopologicalBasis_basicOpen` give the
nonvanishing-set basis. `isEmbedding_pointToPoint` and
`continuous_substitution` hold over arbitrary fields and variable types, with
`substitution_apply`, `substitution_id`, and `substitution_comp` governing the
contravariant coordinate action. `zeroLocusClosedPoint_mem_iff` computes
quotient membership by evaluation, and `isEmbedding_zeroLocusClosedPoint`
embeds each zero locus in the inherited closed-point subspace without
finiteness or algebraic closure. With algebraic closure and finite variables,
`zeroLocusHomeomorphClosedPoints` upgrades the existing coordinate equivalence
to a homeomorphism; its forward and inverse coordinate laws agree with the
point-set correspondence. The unit ideal and nonradical quotients are included;
arbitrary-field surjectivity and a scheme/sheaf equivalence are not claimed.

## `MultivariatePolynomials.LocalizedCoordinateQuotient`

[Producer](../MultivariatePolynomials/LocalizedCoordinateQuotient.lean) and
[ordinary-import client](../MultivariatePolynomialsTests/LocalizedCoordinateQuotient.lean).
For arbitrary `{R : Type u} [CommRing R] (r : R)`,
`Polynomial.quotientSpanCMulX_mul_mk_eq_zero_of_eval_zero` states that an
element represented by a polynomial vanishing at zero is annihilated by the
image of `r` in `R[X] / ⟨C r * X⟩`. The quotient evaluation map
`Polynomial.quotientSpanCMulXEval` and its `_mk` law evaluate at zero.
`Polynomial.quotientSpanCMulXAwayAlgEquiv` points from
`Localization.Away (algebraMap R (R[X] ⧸ Ideal.span {C r * X}) r)` to
`Localization.Away r` as an `R`-algebra equivalence. Evaluation at zero
specifies its action on quotient representatives. Its inverse sends localized
coefficients to constant-polynomial classes. The two power-denominator laws
specify both maps on every fraction via `IsLocalization.mk'`, without an
implicit regularity or nonzero premise. A chosen-inverse law uses
`IsLocalization.Away.invSelf`; the variable-to-zero law follows from the
representative law.

The independent nonzero-variable witness in the rational-polynomial client
does not use the equivalence. The zero, unit, zero-ring, zero-divisor and
nilpotent boundary examples do not add assumptions to the equivalence statement.

## `MultivariatePolynomials.IdealOfVars`

[Producer](../MultivariatePolynomials/IdealOfVars.lean):
`MvPolynomial.idealOfVars_not_fg` says

```lean
theorem MvPolynomial.idealOfVars_not_fg
    (k : Type*) (σ : Type*) [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG
```

The types `k` and `σ` may be in different universes. The claim concerns the
ideal of variables, not an arbitrary ideal or a complete short exact sequence.

## `MultivariatePolynomials.HomogeneousEvaluation`

[Producer](../MultivariatePolynomials/HomogeneousEvaluation.lean) and
[standalone usage guide](homogeneous-polynomial-evaluation.md). With arbitrary
`ι`, `[CommSemiring B]`, `[CommSemiring R]`, fixed `σ : B →+* R`, weights
`w : ι → ℕ`, degree `d : ℕ`, polynomial `p : MvPolynomial ι B`, variable values
`v : ι → R` and scalar `a : R`:

```lean
theorem MvPolynomial.IsWeightedHomogeneous.eval₂Hom_scaleVariables
    (w : ι → ℕ) (d : ℕ) (p : MvPolynomial ι B)
    (hp : p.IsWeightedHomogeneous w d) (σ : B →+* R) (v : ι → R) (a : R) :
    MvPolynomial.eval₂Hom σ (fun i => a ^ w i * v i) p =
      a ^ d * MvPolynomial.eval₂Hom σ v p

theorem MvPolynomial.IsHomogeneous.eval₂Hom_mul_left
    (d : ℕ) (p : MvPolynomial ι B) (hp : p.IsHomogeneous d)
    (σ : B →+* R) (v : ι → R) (a : R) :
    MvPolynomial.eval₂Hom σ (fun i => a * v i) p =
      a ^ d * MvPolynomial.eval₂Hom σ v p
```

These excerpts display the exact named arguments and conclusions under the
module's type variables; they are not a native Lean signature print. Neither
law requires a unit, domain, field, nonzero polynomial, finite/inhabited indices
or positive degree. Both hold for the zero polynomial and preserve the same
coefficient homomorphism on both sides.

## `MultivariatePolynomials.BlockSubstitution`

[Producer](../MultivariatePolynomials/BlockSubstitution.lean),
[standalone guide](block-substitution.md), and
[ordinary-import client](../MultivariatePolynomialsTests/BlockSubstitution.lean). With arbitrary
`{ι : Type u}`, `{κ : Type v}`, `{R : Type w}` and `[CommSemiring R]`,
the producer declares one definition and four theorems (the following manual
display is not a native Lean signature print):

```lean
MvPolynomial.blockSubst (p : MvPolynomial ι R) (q : MvPolynomial κ R) :
  MvPolynomial (ι × κ) R

MvPolynomial.eval_blockSubst (p : MvPolynomial ι R) (q : MvPolynomial κ R)
    (x : ι × κ → R) :
  eval x (blockSubst p q) = eval (fun i => eval (fun j => x (i, j)) q) p

MvPolynomial.eval_blockSubst_eq_zero_imp (p : MvPolynomial ι R)
    (q : MvPolynomial κ R)
    (hp : ∀ y : ι → R, eval y p = 0 → y = 0)
    (hq : ∀ z : κ → R, eval z q = 0 → z = 0)
    (x : ι × κ → R) : eval x (blockSubst p q) = 0 → x = 0

MvPolynomial.eval_blockSubst_eq_zero_iff (p : MvPolynomial ι R)
    (q : MvPolynomial κ R)
    (hp : ∀ y : ι → R, eval y p = 0 ↔ y = 0)
    (hq : ∀ z : κ → R, eval z q = 0 ↔ z = 0)
    (x : ι × κ → R) : eval x (blockSubst p q) = 0 ↔ x = 0

MvPolynomial.ne_zero_of_eval_eq_zero_imp [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R) (hp : ∀ y : ι → R, eval y p = 0 → y = 0) : p ≠ 0
```

The structural substitution uses tagged copies, not identification by
pointwise agreement (which fails over finite fields). The forward zero-locus
implication does **not** assume vanishing at zero; only the iff result requires
each input's full equivalence. The separate nonzero theorem alone adds
`[Nontrivial R] [Nonempty ι]`. Empty indices and zero rings remain valid for
the first four declarations. This generic block leaf alone adds no homogeneous
degree or arbitrary-iteration theorem: its private client reuses mathlib's
homogeneity and nonzero-conditional total-degree results. The separate degree
leaf below proves exact degree for arbitrary inputs; the iterator provides
finite iteration and conditional degree-power theorems.

## `MultivariatePolynomials.IteratedBlockSubstitution`

[Producer](../MultivariatePolynomials/IteratedBlockSubstitution.lean),
[standalone guide](iterated-block-substitution.md), and
[ordinary-import private client](../MultivariatePolynomialsTests/IteratedBlockSubstitution.lean).
For arbitrary `{ι : Type u}`, `{R : Type v}` and `[CommSemiring R]`, with
`p : MvPolynomial ι R`, this is a manual declaration/signature map, not a
native Lean print:

```lean
MvPolynomial.iteratedBlockSubst (p : MvPolynomial ι R) (r : ℕ) :
  MvPolynomial (Fin r → ι) R

MvPolynomial.iteratedBlockSubst_zero (p : MvPolynomial ι R) :
  iteratedBlockSubst p 0 = X Fin.elim0

MvPolynomial.iteratedBlockSubst_succ (p : MvPolynomial ι R) (r : ℕ) :
  iteratedBlockSubst p (r + 1) =
    rename (Fin.consEquiv (fun _ : Fin (r + 1) => ι))
      (blockSubst p (iteratedBlockSubst p r))

MvPolynomial.eval_iteratedBlockSubst_zero (p : MvPolynomial ι R)
    (x : (Fin 0 → ι) → R) : eval x (iteratedBlockSubst p 0) = x Fin.elim0

MvPolynomial.eval_iteratedBlockSubst_succ (p : MvPolynomial ι R) (r : ℕ)
    (x : (Fin (r + 1) → ι) → R) :
  eval x (iteratedBlockSubst p (r + 1)) =
    eval (fun i => eval (fun t => x (Fin.cons i t)) (iteratedBlockSubst p r)) p

MvPolynomial.eval_iteratedBlockSubst_eq_zero_imp (p : MvPolynomial ι R)
    (hp : ∀ y : ι → R, eval y p = 0 → y = 0) (r : ℕ)
    (x : (Fin r → ι) → R) : eval x (iteratedBlockSubst p r) = 0 → x = 0

MvPolynomial.eval_iteratedBlockSubst_eq_zero_iff (p : MvPolynomial ι R)
    (hp : ∀ y : ι → R, eval y p = 0 ↔ y = 0) (r : ℕ)
    (x : (Fin r → ι) → R) : eval x (iteratedBlockSubst p r) = 0 ↔ x = 0

MvPolynomial.isHomogeneous_iteratedBlockSubst (p : MvPolynomial ι R)
    (d : ℕ) (hp : p.IsHomogeneous d) (r : ℕ) :
  (iteratedBlockSubst p r).IsHomogeneous (d ^ r)

MvPolynomial.iteratedBlockSubst_ne_zero [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R)
    (hp : ∀ y : ι → R, eval y p = 0 → y = 0) (r : ℕ) :
  iteratedBlockSubst p r ≠ 0

MvPolynomial.iteratedBlockSubst_totalDegree [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d)
    (hz : ∀ y : ι → R, eval y p = 0 → y = 0) (r : ℕ) :
  (iteratedBlockSubst p r).totalDegree = d ^ r

MvPolynomial.exists_iteratedBlockSubst_totalDegree_gt
    [Nontrivial R] [Nonempty ι] (p : MvPolynomial ι R) (d : ℕ)
    (hp : p.IsHomogeneous d)
    (hz : ∀ y : ι → R, eval y p = 0 → y = 0)
    (hd : 1 < d) (bound : ℕ) :
  ∃ r : ℕ, bound < (iteratedBlockSubst p r).totalDegree
```

These eleven selected declarations comprise one definition and ten theorems.
Structural tuple recursion never infers polynomial equality from evaluation
equality over finite fields. Homogeneity is nominal even for zero; exact total
degree needs the nonzero hypotheses, and `1 < d` yields attained degrees beyond
each bound, **not** every sufficiently large degree. The private client checks
zero steps, finite fields, empty indices, zero rings, a forward-only constant
and conditional cardinality powers. No base polynomial is constructed.

## `MultivariatePolynomials.BlockSubstitutionLaws`

[Producer](../MultivariatePolynomials/BlockSubstitutionLaws.lean),
[standalone guide](block-substitution-laws.md), and
[eight-theorem private client](../MultivariatePolynomialsTests/BlockSubstitutionLaws.lean). Import this
leaf directly or import the aggregate. With arbitrary `{I : Type u}`,
`{J : Type v}`, `{K : Type w}`, `{L : Type x}`, `{R : Type t}` and
`[CommSemiring R]`, the following seven declarations are a **manual**
statement map, not a native signature print:

```lean
theorem MvPolynomial.rename_blockSubst (f : I → K) (g : J → L)
    (p : MvPolynomial I R) (q : MvPolynomial J R) :
    rename (Prod.map f g) (blockSubst p q) =
      blockSubst (rename f p) (rename g q)

theorem MvPolynomial.blockSubst_assoc (p : MvPolynomial I R)
    (q : MvPolynomial J R) (r : MvPolynomial K R) :
    rename (Equiv.prodAssoc I J K) (blockSubst (blockSubst p q) r) =
      blockSubst p (blockSubst q r)

theorem MvPolynomial.blockSubst_X_left (p : MvPolynomial I R) :
    rename (Prod.snd : PUnit × I → I) (blockSubst (X PUnit.unit) p) = p

theorem MvPolynomial.blockSubst_X_right (p : MvPolynomial I R) :
    rename (Prod.fst : I × PUnit → I) (blockSubst p (X PUnit.unit)) = p

theorem MvPolynomial.iteratedBlockSubst_one (p : MvPolynomial I R) :
    iteratedBlockSubst p 1 = rename (fun i : I => Fin.cons i Fin.elim0) p

theorem MvPolynomial.iteratedBlockSubst_add (p : MvPolynomial I R) (m n : ℕ) :
    iteratedBlockSubst p (m + n) =
      rename (fun pair : (Fin m → I) × (Fin n → I) =>
        Fin.append pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p m) (iteratedBlockSubst p n))

theorem MvPolynomial.iteratedBlockSubst_snoc (p : MvPolynomial I R) (m : ℕ) :
    iteratedBlockSubst p (m + 1) =
      rename (fun pair : (Fin m → I) × I => Fin.snoc pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p m) p)
```

`rename_blockSubst` permits noninjective maps. Associativity uses the forward
product associator, and the unit laws erase a single `PUnit` index. The word
laws include zero lengths and preserve positions under the required `Fin`
casts: the additive decomposition is not merely an equality of cardinalities,
and the snoc successor is different from the iterator's cons recursion.
No theorem in this leaf requires a field, nontrivial coefficient semiring,
nonempty index type, degree or homogeneity premise. The private client tests
finite-field constants, mixed/empty indices, noninjective maps and a zero ring;
it does not restrict the arbitrary-commutative-semiring statements.

## `MultivariatePolynomials.BlockSubstitutionDegree`

[Producer](../MultivariatePolynomials/BlockSubstitutionDegree.lean),
[standalone guide](block-substitution-degree.md) and
[ordinary-import client](../MultivariatePolynomialsTests/BlockSubstitutionDegree.lean). With arbitrary
`{I : Type u}`, `{J : Type v}`, `{R : Type w}`, `[CommSemiring R]` and
`[NoZeroDivisors R]`, the one new public theorem is (manual statement map,
not a native Lean signature print):

```lean
theorem MvPolynomial.totalDegree_blockSubst
    (p : MvPolynomial I R) (q : MvPolynomial J R) :
    (blockSubst p q).totalDegree = p.totalDegree * q.totalDegree
```

This equality needs no separate `Nontrivial`, nonzero-polynomial, homogeneous,
positive-degree, field, additive-cancellation or finite/nonempty-index premise;
it includes zeros and constants. It does not claim substitution injectivity.
The proof's auxiliary degree and block-profile facts are private, not new API.

## `MultivariatePolynomials.PolynomialCoefficientHomogeneity`

[Producer](../MultivariatePolynomials/PolynomialCoefficientHomogeneity.lean),
[standalone guide](polynomial-coefficient-homogeneity.md), and
[ordinary-import finite-parameter client](../MultivariatePolynomialsTests/PolynomialCoefficientHomogeneity.lean).
For arbitrary `{R σ : Type*}` and `[CommSemiring R]`, with `R[X]` denoting
`Polynomial R`, the one public theorem is (manual statement map, not a native
Lean signature print):

```lean
theorem MvPolynomial.IsHomogeneous.coeff_polynomial_interchange
    (p : MvPolynomial σ R[X]) (degree index : ℕ)
    (hp : p.IsHomogeneous degree) :
    ((((MvPolynomial.optionEquivRight R σ).symm.trans
      (MvPolynomial.optionEquivLeft R σ)) p).coeff index).IsHomogeneous degree
```

The native interchange places the polynomial parameter in a separate
weight-zero variable: each coefficient retains the *label* `degree` in the
multivariate variables. Zero coefficients satisfy every label. No finiteness,
domain, field, nontriviality or actual-degree-equality premise is required.
The interchange helpers are private, not additional public definitions.

## `MultivariatePolynomials.LinearCoefficientEvaluation`

[Producer](../MultivariatePolynomials/LinearCoefficientEvaluation.lean),
[standalone guide](linear-coefficient-evaluation.md) and
[ordinary-import client](../MultivariatePolynomialsTests/LinearCoefficientEvaluation.lean).
With arbitrary universes for `{R : Type u}`, `{S : Type v}` and `{V : Type w}`,
`[CommSemiring R]`, `[CommSemiring S]`, `[Algebra R S]`, the sole public theorem is
(manual statement map, not a native Lean signature print):

```lean
theorem MvPolynomial.eval_addMonoidAlgebraMap_of_linearMap
    (lambda : S →ₗ[R] R) (F : MvPolynomial V S) (y : V → R) :
    lambda (MvPolynomial.eval (algebraMap R S ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom F)
```

The evaluation point is valued in the **base semiring `R`**, not arbitrary `S`.
The map `lambda` is only linear, not a ring homomorphism or necessarily
multiplicative; `AddMonoidAlgebra.map` is mathlib's native additive map.
There is no finite-variable/basis, field, domain, nontriviality or injectivity
assumption. The basis-coordinate, nonmultiplicative Nat-pair sum, zero-map and
`Empty` clients do not reconstruct polynomials from coordinates, preserve
homogeneous labels or prove a common-zero or full source theorem.

## `MultivariatePolynomials.LinearDivision`

[Producer](../MultivariatePolynomials/LinearDivision.lean),
[standalone guide](linear-division.md), and
[ordinary-import private client](../MultivariatePolynomialsTests/LinearDivision.lean). For arbitrary
variable and family-index types `{σ ι R : Type*}`, `[CommRing R]`,
`m : MonomialOrder σ`, `b : ι → MvPolynomial σ R` and
`hb : ∀ i, IsUnit (m.leadingCoeff (b i))`, the nine selected public results
are (manual statements under these types, not native Lean output):

```lean
noncomputable def MonomialOrder.linearDivisionQuotient (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    MvPolynomial σ R →ₗ[R] (ι →₀ MvPolynomial σ R)

noncomputable def MonomialOrder.linearDivisionRemainder (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R

theorem MonomialOrder.linearDivision_decomposition (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) :
    p = Finsupp.linearCombination (MvPolynomial σ R) b (linearDivisionQuotient m b hb p) +
      linearDivisionRemainder m b hb p

theorem MonomialOrder.linearDivision_remainder_support (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) :
    ∀ α ∈ (linearDivisionRemainder m b hb p).support,
      ∀ i, ¬ m.degree (b i) ≤ α

theorem MonomialOrder.linearMap_preserves_coeffsIn (J : Ideal R)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (p : MvPolynomial σ R) (hp : p ∈ coeffsIn σ (J : Submodule R R)) :
    F p ∈ coeffsIn σ (J : Submodule R R)

theorem MonomialOrder.linearDivision_remainder_coeffsIn (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (J : Ideal R) (p : MvPolynomial σ R)
    (hp : p ∈ coeffsIn σ (J : Submodule R R)) :
    linearDivisionRemainder m b hb p ∈ coeffsIn σ (J : Submodule R R)

theorem MonomialOrder.linearDivision_quotient_coeffsIn (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (J : Ideal R) (p : MvPolynomial σ R)
    (hp : p ∈ coeffsIn σ (J : Submodule R R)) (i : ι) :
    (linearDivisionQuotient m b hb p) i ∈ coeffsIn σ (J : Submodule R R)

theorem MonomialOrder.linearDivision_remainder_of_reduced (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) (hp : ∀ α ∈ p.support, ∀ i, ¬ m.degree (b i) ≤ α) :
    linearDivisionRemainder m b hb p = p

theorem MonomialOrder.linearDivision_quotient_of_reduced (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p : MvPolynomial σ R) (hp : ∀ α ∈ p.support, ∀ i, ¬ m.degree (b i) ≤ α) :
    linearDivisionQuotient m b hb p = 0
```

The *six additional public helpers*, not extra selected results or private
theorems, are `MonomialOrder.basisDivision`, `monomial_eq_smul_one`,
`linearDivisionQuotient_monomial`, `linearDivisionRemainder_monomial`,
`reducedSubmodule` and `basisDivision_reduced`. Quotients are finitely
supported in the divisor-family index; the reconstruction weights are
polynomials, while the chosen operators are linear over `R`.
The remainder's **actual** support avoids leading cones in *componentwise*
exponent order, not the monomial-order comparison. The ideal laws apply to
every `J : Ideal R` (in particular `J ^ n`) and every quotient coordinate.
The fixed choice of basis-monomial witnesses does not give uniqueness or
canonical independence, a Gröbner basis, a field/domain premise, finite
indices or restricted-series division. Eight private client theorems cover
generic and finite families, an empty family, zero input, the zero ring,
the nonzero proper ideal `(2)` in `ZMod 4`, and reduced input.

## `MultivariatePolynomials.MonicLift`

[Producer](../MultivariatePolynomials/MonicLift.lean),
[standalone guide](monic-lift.md), and
[ordinary-import private client](../MultivariatePolynomialsTests/MonicLift.lean). For arbitrary
`{σ R S : Type*}`, `[CommRing R]`, `[CommRing S]`, a monomial order
`m : MonomialOrder σ`, surjective coefficient homomorphism `φ : R →+* S`,
`p : MvPolynomial σ S` and `hp : m.Monic p`, the one selected public theorem is
(a manual statement, not native Lean output):

```lean
theorem MonomialOrder.exists_monic_lift (m : MonomialOrder σ) (φ : R →+* S)
    (hφ : Function.Surjective φ) (p : MvPolynomial σ S) (hp : m.Monic p) :
    ∃ q : MvPolynomial σ R,
      MvPolynomial.map φ q = p ∧ m.Monic q ∧ m.degree q = m.degree p
```

Degree equality is literal in `σ →₀ ℕ`, not just monomial-order equivalence.
The nontrivial-target proof agrees on actual supports; the zero-target proof
takes `q = 1` and does not assert support equality. No finiteness, injectivity,
field, domain or unconditional nontriviality is required. The existential
choice is not canonical. Five private client theorems cover generic use,
a noninjective quotient, empty variables and zero target/source rings.

## `MultivariatePolynomials.FirstVariableLex`

[Producer](../MultivariatePolynomials/FirstVariableLex.lean),
[guide](first-variable-lex.md), and
[ordinary-import private client](../MultivariatePolynomialsTests/FirstVariableLex.lean). The three
selected public theorems concern the usual `Fin` order and pointwise order on
exponents (the latter is separate from the monomial order):

```lean
Finsupp.cons_zero_le_cons_iff (β : Fin n →₀ ℕ) :
    ((0 : Fin n →₀ ℕ).cons d) ≤ β.cons i ↔ d ≤ i

MonomialOrder.lex_le_cons_zero_of_le (β : Fin n →₀ ℕ)
    (hi : i ≤ d) (heq : i = d → β = 0) :
    β.cons i ≼[MonomialOrder.lex] (0 : Fin n →₀ ℕ).cons d

MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top [CommSemiring K]
    (n d : ℕ) (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hdegree : (MvPolynomial.finSuccEquiv K n p).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv K n p).coeff d = MvPolynomial.C c)
    (hc : c ≠ 0) :
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).degree p =
      (0 : Fin n →₀ ℕ).cons d
```

The scalar-top condition rules out extra tail exponents at the maximal first
degree; a nonzero scalar ensures that the pure first-variable exponent belongs
to the support. The coefficient ring need not have subtraction. `Fin 0` and
degree zero are valid, and the client includes a non-scalar-top boundary.

## `MultivariatePolynomials.WeightOneValuation`

For any field `k`, variable type `σ`, subset `S : Set σ` and chosen pivot
`i : S`, `MvPolynomial.weightOneOrder` is the *minimum* subset weight of a
polynomial (with zero assigned `⊤`), and `weightOneNatOrder` gives its finite
order when nonzero. `weightOneExpansion` substitutes the pivot by `X`, the
remaining weighted variables by `X` times independent ratio variables, and
unweighted variables by coefficient variables. `weightOneCoordinates` proves
the corresponding birational ring equivalence with a univariate rational
function field over the rational function field of coefficient variables.

`weightOneValuation` pulls back the `X`-adic valuation. Its polynomial and
fraction laws use minimum weights and integer subtraction, and it is
surjective and rank-one discrete. `weightOneUniformizer` is the chosen pivot
in the valuation ring and generates its maximal ideal. The
`weightOneCoefficientSection` lifts every rational coefficient, while
`weightOneResidueEquiv` identifies the *entire* residue field with the
rational function field in unweighted variables and weighted-variable ratios.
Its section and generator laws and `weightOneResidueEquiv_div` describe
equal-order fractions via their initial coefficients. The independent
[client](../MultivariatePolynomialsTests/WeightOneValuation.lean) checks
characteristic-independent finite-variable examples, infinite variables,
and the empty-subset boundary using Mathlib's trivial valuation.

## `MultivariatePolynomials.WeightOneNaturality`

[Producer](../MultivariatePolynomials/WeightOneNaturality.lean) and
[ordinary-import client](../MultivariatePolynomialsTests/WeightOneNaturality.lean).
Let `e : σ ↪ τ` embed arbitrary variable types and let `g : R →+* A` be an
injective map of commutative semirings. `weightOnePolynomialMap` maps
coefficients and renames variables. `weightOneOrder_map` identifies the target
minimum support weight with the source weight for `e ⁻¹' T`, *including zero*
(whose order is `⊤`); `weightOneNatOrder_map` gives the corresponding equality
of finite natural-number orders for all polynomials, including zero. When
every image variable is outside `T`, a nonzero polynomial image has target
order zero.

For independent fields `k` and `l`, every field homomorphism `g : k →+* l` and
embedding `e` induce `weightOneFractionMap` and its polynomial, identity,
composition and division laws. Given `S : Set σ`, `T : Set τ`,
`h : ∀ j, e j ∈ T ↔ j ∈ S`, a source pivot `i : S` and *any* target pivot
`t : T`, `weightOneValuation_map` identifies the two valuations. The restricted
`weightOneValuationRingMap` is local and respects identity and composition;
`weightOneResidueMap` acts on the **entire** residue fields, commutes with
reduction and has corresponding identity and composition laws. Neither
surjectivity nor finiteness of `e` is required: the target may have additional
weighted and unweighted variables.

For the aligned target pivot `e i`, `weightOneCoefficientFieldMap` takes
constants, unweighted generators and pivot-ratio generators to their embedded
counterparts. `weightOneCoefficientSection_map` and
`weightOneResidueEquiv_map` commute with this coefficient map. For an arbitrary
target pivot, `weightOneResidueEquiv_map_changePivot` inserts the coordinate
equivalence `weightOneCoefficientChangePivot`. This equivalence preserves
constants and unweighted variables, is the identity at equal pivots, and
composes across pivot choices. For distinct pivots `t` and `t'`, it sends
`t'/t` to `(t/t')⁻¹` and `j/t` to `(j/t')/(t/t')` when `j` is distinct from both
pivots. These ratios are coefficient-field coordinates, not identities of
their differently indexed polynomial rings.

Under the separate condition `∀ j, e j ∉ T`, only a **target** pivot is needed.
Each nonzero source fraction has target valuation one, and
`weightOneZeroResidueMap` embeds the entire source function field into the
target full residue field. `weightOneZeroResidueMap_coordinates` identifies it
with `weightOneZeroCoefficientFieldMap` in rational coefficient coordinates.
An additional weighted target ratio is not in this image; the client exhibits
the strict `ℚ(z) ⊂ ℚ(z, y/x)` case, a nonconstant `RatFunc.X` coefficient
extension with no source variables, infinite/proper embeddings and both
directions of weight-mismatch and noninjective-variable boundaries. No
surjectivity onto the target residue field is asserted.

## `MultivariatePolynomials.PointSquareZeroPresentation`

[Producer](../MultivariatePolynomials/PointSquareZeroPresentation.lean). For
any commutative ring `R`, including the zero ring, and arbitrary index type
`ι`, `pointSquareZeroIdeal a` is generated **only** by `X (some i) ^ 2` and
`(X none - C (a i)) * X (some i)` in `MvPolynomial (Option ι) R`; mixed
products are not defining relations. `pointSquareZeroQuotient a` is the
quotient, with an `R[X]`-algebra structure sending `X` to `[X none]` and
agreeing with its coefficient `R`-algebra structure. `pointSquareZeroModule a`
is the direct sum of `R[X] / ker (Polynomial.evalRingHom (a i))`, with the
polynomial action determined separately by each evaluation point.

`pointSquareZeroDelta` gives canonical summand coordinates and their
annihilation law. `pointSquareZeroLift` constructs an `R[X]`-algebra map to a
commutative target from square-zero elements annihilated by `X - C (a i)`;
its generator laws, `pointSquareZeroAlgHom_ext` and
`pointSquareZeroLift_unique` characterize this map. `pointSquareZeroForward`
is the prescribed lift into the canonical trivial square-zero extension; it
needs no separation hypothesis.

## `MultivariatePolynomials.PointSquareZeroQuotient`

[Producer](../MultivariatePolynomials/PointSquareZeroQuotient.lean). If
`a i - a j` is a unit for every pair of distinct indices,
`pointSquareZeroForward_bijective` proves that the same prescribed map is
bijective, and `pointSquareZeroAlgEquiv` applies `AlgEquiv.ofBijective` to
that map. The equivalence has forward laws on indexed coordinates, the
distinguished coordinate and constants, and an inverse law on
`pointSquareZeroDelta`. The two defining relations and unit separation
force all mixed coordinate products to vanish. Multiplication by each
coordinate then descends along its polynomial evaluation kernel; the direct
sum and the square-zero universal property yield an inverse in both
directions. Neither a converse nor noninjectivity upon failed unit separation
is proved.

## Aggregate and tests

[Aggregate](../MultivariatePolynomials.lean) publicly imports all seventeen leaves.
Twenty-one test/example modules are registered as literal roots under
`MultivariatePolynomialsTests`: [evaluation-ideal client](../MultivariatePolynomialsTests/EvaluationIdeal.lean),
[evaluation-naturality client](../MultivariatePolynomialsTests/EvaluationIdealNaturality.lean),
[aggregate ideal client](../MultivariatePolynomialsTests/IdealOfVars.lean),
[selected ideal-only axiom print](../MultivariatePolynomialsTests/Axioms.lean),
[direct ideal clients](../MultivariatePolynomialsTests/LeafImport.lean),
[README ideal example](../MultivariatePolynomialsTests/ReadmeExample.lean),
[direct homogeneous-evaluation client](../MultivariatePolynomialsTests/HomogeneousEvaluation.lean),
[direct block-substitution client](../MultivariatePolynomialsTests/BlockSubstitution.lean),
[direct finite-iteration client](../MultivariatePolynomialsTests/IteratedBlockSubstitution.lean),
[structural-law client](../MultivariatePolynomialsTests/BlockSubstitutionLaws.lean),
[exact-degree client](../MultivariatePolynomialsTests/BlockSubstitutionDegree.lean),
[coefficient-homogeneity client](../MultivariatePolynomialsTests/PolynomialCoefficientHomogeneity.lean), and
[linear-coefficient-evaluation client](../MultivariatePolynomialsTests/LinearCoefficientEvaluation.lean), and
[linear-division client](../MultivariatePolynomialsTests/LinearDivision.lean), and
[monic-lift client](../MultivariatePolynomialsTests/MonicLift.lean), and
[first-variable lex client](../MultivariatePolynomialsTests/FirstVariableLex.lean), and
[localized quotient client](../MultivariatePolynomialsTests/LocalizedCoordinateQuotient.lean), and
[presentation-only fixtures](../MultivariatePolynomialsTests/PointSquareZeroFixtures.lean), and
[headline equivalence clients](../MultivariatePolynomialsTests/PointSquareZeroHeadline.lean), and
[weight-one valuation client](../MultivariatePolynomialsTests/WeightOneValuation.lean), and
[weight-one naturality client](../MultivariatePolynomialsTests/WeightOneNaturality.lean).
The presentation-only fixtures import only the presentation leaf;
the headline clients import the separated-equivalence leaf. The tests are not re-exported as production
API. These eighteen production modules (including the aggregate) plus
twenty-one test modules total thirty-nine Lean modules.
