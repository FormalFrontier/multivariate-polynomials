# Public API map

This is a hand-maintained map of the current public interface, **not** freshly
generated native documentation, a build record or proof certification. Import
`MultivariatePolynomials` for all twenty-eight selected declarations, or the named leaf for one
family. [README](../README.md) explains how to build the library. The
[initial native snapshot](API-initial-snapshot.md) and its
[unchanged manifest](api-manifest.json) cover only the original six-module
revision, not this expanded interface.

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
[ordinary-import client](../Test/BlockSubstitution.lean). With arbitrary
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
[ordinary-import private client](../Test/IteratedBlockSubstitution.lean).
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
[eight-theorem private client](../Test/BlockSubstitutionLaws.lean). Import this
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
[ordinary-import client](../Test/BlockSubstitutionDegree.lean). With arbitrary
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
[ordinary-import finite-parameter client](../Test/PolynomialCoefficientHomogeneity.lean).
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

## Aggregate and tests

[Aggregate](../MultivariatePolynomials.lean) publicly imports all seven leaves.
Ten test/example modules are registered as literal roots under
`MultivariatePolynomialsTests`: [aggregate ideal client](../Test/IdealOfVars.lean),
[selected ideal-only axiom print](../Test/Axioms.lean),
[direct ideal clients](../Test/LeafImport.lean),
[README ideal example](../Test/ReadmeExample.lean),
[direct homogeneous-evaluation client](../Test/HomogeneousEvaluation.lean),
[direct block-substitution client](../Test/BlockSubstitution.lean),
[direct finite-iteration client](../Test/IteratedBlockSubstitution.lean),
[structural-law client](../Test/BlockSubstitutionLaws.lean), and
[exact-degree client](../Test/BlockSubstitutionDegree.lean), and
[coefficient-homogeneity client](../Test/PolynomialCoefficientHomogeneity.lean).
The tests are not re-exported as production API. These eight production plus
ten test modules total eighteen Lean modules; a private-inclusive transitive
standard-axiom audit remains a separate revision-specific acceptance gate.
