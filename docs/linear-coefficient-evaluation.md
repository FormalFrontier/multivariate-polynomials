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
variables) are in [`Test/LinearCoefficientEvaluation.lean`](../Test/LinearCoefficientEvaluation.lean).
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
lake env lean -DwarningAsError=true Test/LinearCoefficientEvaluation.lean
```

The original producer, client and incubator guide were authored by
`formalization-worker-b` Hive Task
`hive-request-1e84b7dbd24453b4c56079d2af61fc9a6c164c79`
(UID `1cfcdc7e-2006-4a03-8da1-e73d97d820c1`) in accepted isolated
`FormalFrontier/incubator@960964368c62af2bedd331c6798eccdab3636424`;
the native research probe was authored by `formalization-worker-b` Hive Task
`hive-request-e0e5d4898e89eb2ea5c8cb7b88a53638dc6a3130`
(UID `0aa6aebb-1fc5-41d4-9aea-c44e7f941221`). The separate
project-authored finite-basis mathematical exposition is recorded at
`FormalFrontier/source-nsw@8dac6b7744339ec6e9313003b53982d839cb93d4:
expositions/finite-basis-polynomial-coordinate-expansion.md`, with independent
source review at `d62fa7308095968d551a08223c76274ba836a5b4`;
it supplies background, not a dependency or the full-source formalization.
Independent isolated-code reviewer `formalization-worker-a` Hive Task
`hive-request-e76c950e3a979d10e409fb4b0cd2e71972deca44`
(UID `bae49ddb-8977-4562-bc3c-a3947c3de5c2`) approved that exact donor in
`004806390540e3930cf57cf78eb121bb2c1bd759`. Beacon accepted only the
isolated scope in incubator issue #196/comment 62346. The independent
destination transfer (not proof authorship or independent review) is by
`formalization-worker-b` Hive Task
`hive-request-59885bc6e40d66807f5e417d29e18f3ec497405f`
(UID `65442cf3-e7a6-4314-8ad9-107a116d4df2`). The preceding
polynomial-coefficient-homogeneity addition reached reviewed official release
`330f46ba71e3230c4eec5f8d17c6b10927cf6dbe` on September 29, 2026.
At the initial code-only static-transfer snapshot that day, before native
run 1002 or destination review, this **new** addition was an unreleased
candidate requiring its own both-target/private-inclusive native check,
fresh independent review, maintainer acceptance, protected integration and
separately verified official publication. Later revision-specific decisions
are recorded in PR #38 and incubator issue #196, not inferred from the donor
or this dated snapshot. The candidate does not retroactively change the older
release or establish source coverage.

At the release-readiness snapshot following code integration on September 29,
2026, before separate release review, the evidence was as follows. Later
revision-specific release decisions belong to PR #39 and incubator issue #196.
Native destination run 1002 checked both default targets and
the complete 134-origin, 97-private, twenty-module transitive standard-axiom
graph at `752bdd058deaf81c745d4b82332ee8d862ddb2ba`; its successful
exact-main documentary successor run 1003 and fresh independent worker-a
review `9f28eacf997e768da3af91bf2824024810d268cc` apply to accepted
`d996f56195589eb9a3a388b3e2e916eacd8cfeeb`. Beacon accepted and
protected-integrated that code/API in PR #38 at 08:18:43 UTC on September
29, 2026. At that snapshot, its own independent release review, acceptance,
protected promotion and verified private GitHub publication remained pending. Static release
readiness is prepared by `formalization-worker-b` Hive Task
`hive-request-22d6061a1d4098d03a837f79783c36552c554bb6` (UID
`d4bc5e89-cd8d-4ec4-bdd5-64bc5b038bf6`), not the proof author or release
reviewer/acceptor. The previously published coefficient release is unchanged.

Authors: Formal Frontier Agents; Apache-2.0 (`LICENSE`).
