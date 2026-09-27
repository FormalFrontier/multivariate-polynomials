# Public API map

This is a hand-maintained map of the current public interface, **not** freshly
generated native documentation, a build record or proof certification. Import
`MultivariatePolynomials` for all three results, or the named leaf for one
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

## Aggregate and tests

[Aggregate](../MultivariatePolynomials.lean) publicly imports both leaves.
Five test/example modules are registered as literal roots under
`MultivariatePolynomialsTests`: [aggregate ideal client](../Test/IdealOfVars.lean),
[selected ideal-only axiom print](../Test/Axioms.lean),
[direct ideal clients](../Test/LeafImport.lean),
[README ideal example](../Test/ReadmeExample.lean), and
[direct homogeneous-evaluation client](../Test/HomogeneousEvaluation.lean).
The tests are not re-exported as production API. These three production plus
five test modules total eight Lean modules; a private-inclusive transitive
standard-axiom audit remains a separate revision-specific acceptance gate.
