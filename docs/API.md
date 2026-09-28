# Public API map

This is a hand-maintained map of the current public interface, **not** freshly
generated native documentation, a build record or proof certification. Import
`MultivariatePolynomials` for all eight selected declarations, or the named leaf for one
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
the first four declarations. No homogeneous degree or iteration theorem is
added: the private client reuses mathlib's homogeneity and nonzero-conditional
total-degree results.

## Aggregate and tests

[Aggregate](../MultivariatePolynomials.lean) publicly imports all three leaves.
Six test/example modules are registered as literal roots under
`MultivariatePolynomialsTests`: [aggregate ideal client](../Test/IdealOfVars.lean),
[selected ideal-only axiom print](../Test/Axioms.lean),
[direct ideal clients](../Test/LeafImport.lean),
[README ideal example](../Test/ReadmeExample.lean), and
[direct homogeneous-evaluation client](../Test/HomogeneousEvaluation.lean), and
[direct block-substitution client](../Test/BlockSubstitution.lean).
The tests are not re-exported as production API. These four production plus
six test modules total ten Lean modules; a private-inclusive transitive
standard-axiom audit remains a separate revision-specific acceptance gate.
