# Polynomial-coefficient homogeneity

Import `MultivariatePolynomials.PolynomialCoefficientHomogeneity` to use
`MvPolynomial.IsHomogeneous.coeff_polynomial_interchange`. For any type of
variables `σ`, commutative semiring `R`, polynomial
`p : MvPolynomial σ (Polynomial R)` and naturals `d k`, its signature is:

```lean
p.IsHomogeneous d →
  ((((MvPolynomial.optionEquivRight R σ).symm.trans
    (MvPolynomial.optionEquivLeft R σ)) p).coeff k).IsHomogeneous d
```

This is the native composition of mathlib algebra equivalences, not a new
interchange operator. The variable of `Polynomial R` has weight **zero**: the
degree label `d` measures only the `σ`-variables, not the parameter's degree.
This is about homogeneous *labels*, not necessarily the actual total degree;
zero coefficients satisfy every label. No finite-variable, integral-domain,
field or nontriviality hypothesis is needed. The private proof establishes
the coefficient identity after interchange; coefficient extraction is additive,
not a ring homomorphism.

The ordinary-import client in
`Test/PolynomialCoefficientHomogeneity.lean` tests a finite
parameter substitution: for each `i : σ`, replace `X i` by
`∑ j : Fin (s + 1), C (Polynomial.X ^ j.val) * X (i, j)`.
The native `IsHomogeneous.eval₂` gives degree `d` for the substituted
polynomial, and the bridge gives the same label to *each* polynomial
coefficient. The client also checks zero, degree zero, `s = 0`, `ZMod 1` and
`ZMod 6` without strengthening the general assumptions. This theorem does
not assert actual-degree equality, recover a nonzero input from a coefficient,
or descend to finite bases.

**Provenance and lifecycle (September 29, 2026):** The isolated addition at
incubator commit `e5c756838bb3d454bfdd6cf83aa3e4146554b760` was based on
the native interchange probe at incubator commit
`32ac38b114a272e25da0d76e241112b0006ae57b`, contributed by worker-b
Hive Task `hive-request-5f7de283751dacfb71124e88a895d681f2d82b67`
(UID `9e51bb9e-d6f0-4407-a73b-d277ee8afd78`). The isolated Lean proof and
client were authored by worker-b Task
`hive-request-35ae3e5f432d81c2ab9b9ffc5cf35185702d8590` (UID
`368216ac-2105-4165-9a38-ef1c5c72e807`), independently reviewed by
worker-a Task `hive-request-d91b835baed2bddb31bd4e5e4809f1948084c296`
(UID `f9e28345-0411-4bdc-9c82-1b347209fc6c`) in incubator review commit
`bcb348fabccda2692785b2f41283ea7e823f98ef`, and accepted *only for the
isolated donor* by Beacon in incubator issue #195/comment 62204. The donor's
matching-cache, warning-fatal producer/client build and complete scoped
actual-origin standard-axiom evidence are in its evidence-only child
`0aa15e0b5433e4471fcb8803e1756221c03d873e`. This destination transfer
is by worker-b Task `hive-request-9214c009238fd6c0c6b9be23a591519a5c2de117`
(UID `9b3a6959-ad8e-4db6-8103-efe641aeeaab`); it is not original proof
authorship or independent destination review. For the destination, a
new both-target/private-inclusive native check and fresh
author-distinct exact-candidate review were required: native run 994/UI25
passed for the eighteen-module destination at
`6e74a6874269bd340775a4b6d6ff9facf118fce3` on September 29, 2026,
auditing all 127 actual-origin declarations including 91 private declarations
with only the permitted foundational axioms. Worker-a Task
`hive-request-4f49b2d86e2f5399552c92df167b0dd8766fac02` (UID
`1a57e9b8-ba94-49ec-ae8b-295709051759`) independently approved that
exact code/API candidate in review `558e6f1e0dab8081d1aa24bc18c3c33be8e8dc93`
and PR #34/native review 4838. Beacon accepted and protected-integrated
the code/API in PR #34/comment 62345 on September 29, 2026. The donor's
scoped evidence alone did not certify the destination aggregate or client
origins. Separate release acceptance, verified GitHub publication and
source-coverage decisions are not established here. Static release-readiness
preparation by formalization-worker-b Task
`hive-request-7597826593b11e7296f06dea2eed7512fbaa96d5` (UID
`e43cd759-475e-4c61-9c5d-0b9eae171d49`) is not mathematical
authorship or independent release review. No source repository is needed
to understand or use this API.

To reproduce checks from this destination project root with Lean
`leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build MultivariatePolynomials.PolynomialCoefficientHomogeneity
lake --wfail build MultivariatePolynomialsTests
lake env lean -DwarningAsError=true Test/PolynomialCoefficientHomogeneity.lean
```

These are reproduction instructions, not a claim of a new execution by this
documentation update. Native run 994/UI25 passed both default build targets
and the full private-inclusive standard-axiom audit at the accepted code/API
revision above; the listed focused commands are not separately claimed as
results of that run. Consult its ordinary PR/CI and review record for exact
scope and the independent later release decision.
