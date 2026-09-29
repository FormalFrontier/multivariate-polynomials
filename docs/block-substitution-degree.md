# Exact total degree of disjoint-block substitution

Import `MultivariatePolynomials.BlockSubstitutionDegree` to use
`MvPolynomial.totalDegree_blockSubst`:

```lean
import MultivariatePolynomials.BlockSubstitutionDegree

example {I J R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (p : MvPolynomial I R) (q : MvPolynomial J R) :
    (MvPolynomial.blockSubst p q).totalDegree = p.totalDegree * q.totalDegree :=
  MvPolynomial.totalDegree_blockSubst p q
```

The index types need not be finite, inhabited, or equal. Neither polynomial needs
to be nonzero or homogeneous; the inner polynomial need not have positive degree.
For instance, with coefficients in `ℕ`, take
`p = X (0 : Fin 2) ^ 2 + X 1` and
`q = X (0 : Fin 3) ^ 2 + X 1`: both have terms of different degrees, and
`(blockSubst p q).totalDegree = 4`. The ordinary-import client also checks a
nonhomogeneous example over `ZMod 5` of degrees three and two, zero and
constant inputs, empty and unequal index types, and the trivial ring `ZMod 1`.
For a zero polynomial, `totalDegree` is zero, as in mathlib.

The proof first bounds the degree by expanding the outer finite monomial support.
For the reverse bound, it projects onto the highest homogeneous degree and
replaces each inner polynomial by its nonzero highest component. The products
coming from distinct top outer monomials are nonzero because the polynomial
ring has no zero divisors; their distinct block-degree profiles prevent
cancellation, including over semirings without additive cancellation. The
argument does not infer polynomial equality from pointwise evaluation.

This theorem does **not** assert injectivity of substitution or require a
coefficient field. Without the no-zero-divisors hypothesis, the exact-degree
claim need not hold. The proof's auxiliary degree, component, and profile
lemmas are private implementation details; no source-specific wrapper or
structural substitution law is duplicated.

The destination project pins Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and nine resolved external
packages; it has no incubator or other Formal Frontier library dependency.
From the pinned `multivariate-polynomials` checkout, fetch the matching
precompiled mathlib cache **before** building the default targets or the
individual modules:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build MultivariatePolynomials MultivariatePolynomialsTests
lake --wfail build MultivariatePolynomials.BlockSubstitutionDegree
lake --wfail build Test.BlockSubstitutionDegree
```

Both modules set `warningAsError true`. The original isolated incubator donor
`f1411fc45c46dd90521b08212f3057ac0b7fe6ec` was independently reviewed
and accepted for isolated scope only. The distinct destination transfer at
`a298692e9515cd264f64b1650d916e7325f22dae` passed native run 923's
both-root build and complete private-inclusive standard-axiom audit, received
fresh independent worker-a review, and was accepted and protected-integrated
by Beacon in PR #30 on September 29, 2026. Official release and GitHub
publication require separate recorded decisions; this guide makes no claim
of source coverage. Original implementation and client: worker-b Hive Task
`hive-request-c655e17355d47e3745bfb5dfa4546c236c22cf1e`, UID
`e8bed61b-ec43-4ac5-867e-419700dd255f`. Destination transfer: worker-b
Hive Task `hive-request-2568fec3a496ab8d743f4b71ca03e04f1e3dfcfd`,
UID `c9cbe957-98d8-4679-a26a-ed417bcaf65f`. Destination reviewer: worker-a
Task `hive-request-259a8fa2891a9f2ccb3b7768e6a5e3721e4f2b7d`, UID
`b333f69a-1e1a-421a-b47e-bcc7ff670df4`. Static release-readiness preparer:
worker-b Task `hive-request-545ac40599943c4846985bcbecc9773af7867eb4`,
UID `f1111607-8c9c-40cd-a138-8b0dc8737447`. This work is supplied under
the repository's Apache-2.0 `LICENSE`; its mathematical dependency is mathlib,
with no original source assets copied.
