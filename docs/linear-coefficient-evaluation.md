<!-- SPDX-License-Identifier: Apache-2.0 -->

# Base-valued linear coefficient evaluation

Import `MultivariatePolynomials.LinearCoefficientEvaluation` directly, or
`MultivariatePolynomials` for the complete public interface. The leaf imports
`Mathlib.Algebra.MvPolynomial.Eval` and exposes one theorem:

```lean
MvPolynomial.eval_addMonoidAlgebraMap_of_linearMap
    {R : Type u} {S : Type v} {V : Type w}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (lambda : S →ₗ[R] R) (F : MvPolynomial V S) (y : V → R) :
    lambda (MvPolynomial.eval (algebraMap R S ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom F)
```

The point `y` **must have values in the base semiring `R`**. There is no
`Fintype V`, field, domain, nontriviality, injective algebra map, homogeneous
polynomial, positive-degree or multiplicativity assumption on `lambda`.
`AddMonoidAlgebra.map` is the native additive coefficient map; no ring-hom
structure is demanded. It is useful, for example, with arbitrary-index
`Module.Basis.coord` maps, and with the nonmultiplicative sum map
`(ℕ × ℕ) →ₗ[ℕ] ℕ`. The ordinary-import examples (also a zero map and `Empty`
variables) are in [`MultivariatePolynomialsTests/LinearCoefficientEvaluation.lean`](../MultivariatePolynomialsTests/LinearCoefficientEvaluation.lean).
The proof expands the finite monomial sum, transports each monomial's
base-valued product through `algebraMap R S`, applies linearity to the resulting
scalar multiplication, and reassembles the native additive map.

This statement does not construct a ring homomorphism from an arbitrary
coefficient-linear map, reconstruct a polynomial from basis coordinates,
prove preservation of homogeneity, descend a finite extension, or assert a
common-zero or full source theorem. The finite-basis coordinate example
requires no finite basis because it only applies one coordinate functional.

Using this project's pinned Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and exact
`lake-manifest.json`, fetch the matching precompiled mathlib cache **before**
building both default targets and the ordinary-import client:

```sh
lake exe cache get
lake --wfail build MultivariatePolynomials MultivariatePolynomialsTests
lake env lean -DwarningAsError=true MultivariatePolynomialsTests/LinearCoefficientEvaluation.lean
```

The independent linear-evaluation theorem and clients build on mathlib; a separate project finite-basis exposition is background, not a proof of full coordinate reconstruction. See [CREDITS.md](../CREDITS.md).
