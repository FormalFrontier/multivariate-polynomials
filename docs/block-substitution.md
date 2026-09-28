# Substitution into disjoint variable blocks

Import `MultivariatePolynomials.BlockSubstitution` (the [producer](../MultivariatePolynomials/BlockSubstitution.lean)) to use
`MvPolynomial.blockSubst`. Given arbitrary index types `ι`, `κ`, a commutative
semiring `R`, and polynomials `p : MvPolynomial ι R` and
`q : MvPolynomial κ R`, the resulting polynomial has variables indexed by
`ι × κ`. Its `i`-th block is a copy of `q` with variable `j` renamed to
`(i, j)`:

```lean
MvPolynomial.blockSubst p q =
  MvPolynomial.bind₁ (fun i => MvPolynomial.rename (Prod.mk i) q) p
```

The operation is structural: it does not identify polynomials merely because
they agree on coefficient-ring points, which would be invalid over finite
fields. `MvPolynomial.eval_blockSubst` gives its evaluation formula:

```lean
MvPolynomial.eval x (MvPolynomial.blockSubst p q) =
  MvPolynomial.eval (fun i =>
    MvPolynomial.eval (fun j => x (i, j)) q) p
```

For example, substituting `q` into the two separate blocks of `X 0 + X 1`
evaluates to the sum of the two block evaluations. Repeating the operation
once more gives a polynomial on `(ι × κ) × υ`; the consumer
[`Test.BlockSubstitution`](../Test/BlockSubstitution.lean) tests both evaluations
and the two-stage vanishing implications. This block client itself does not
provide arbitrary iteration; the separate
[iterated-block module and guide](iterated-block-substitution.md) define and
explain finite iteration over disjoint tuple-indexed blocks. The separate
[structural-law guide](block-substitution-laws.md) gives renaming, forward
associativity, singleton units and the iterator's word-concatenation laws;
none of these is asserted by this generic leaf alone.

Two preservation statements have **different hypotheses and conclusions**:

- `MvPolynomial.eval_blockSubst_eq_zero_imp` assumes separately that an
  evaluation of each of `p` and `q` can be zero *only* at the zero tuple, and
  concludes the same one-way implication for `blockSubst p q`.
- `MvPolynomial.eval_blockSubst_eq_zero_iff` assumes separately that each
  evaluation is zero *exactly when* its tuple is zero, and concludes the
  corresponding equivalence. Its reverse implication needs the extra
  zero-at-zero information; it does not follow from the one-way hypotheses.

Neither result assumes finite or inhabited variable types, decidable equality,
positivity, a nontrivial semiring, or a field. A nonzero constant over `ZMod 2`
has the one-way property vacuously but fails the equivalence at zero. Conversely,
the zero polynomial over a zero ring can satisfy the equivalence; likewise the
empty-index examples need no fictitious variable. The consumer exercises these
cases using an ordinary import of the producer.

`MvPolynomial.ne_zero_of_eval_eq_zero_imp` is a separate useful consequence:
over a nontrivial commutative semiring and a nonempty variable type, the
one-way property proves the polynomial is nonzero. Evaluate at the constant
tuple `1`; if the polynomial were zero, that nonzero tuple would violate the
implication. This requires neither vanishing at zero nor finite support.

For homogeneous inputs of nominal degrees `d` and `e`, reuse mathlib's
`MvPolynomial.IsHomogeneous.aeval` and `.rename_isHomogeneous` to show that
`blockSubst p q` is homogeneous of nominal degree `e * d`; the native
`aeval_eq_bind₁` identifies substitution with `aeval`. Exact
`MvPolynomial.totalDegree = e * d` also requires the substituted polynomial
to be **nonzero**: mathlib's `IsHomogeneous.totalDegree` takes that hypothesis,
and the zero polynomial is homogeneous in every nominal degree. The ordinary
consumer applies the one-way consequence to supply nonzeroness when its
indices are nonempty and the coefficients nontrivial. This module introduces
no duplicate homogeneous-substitution or variable-scaling theorem.

The implementation uses mathlib's `eval₂Hom_bind₁` and
`eval_rename_prod_mk`; its only declared producer dependency is mathlib.
The original isolated incubator contribution at
`65119111a365a3b28bf5803e64a4a1c880948d6d` was independently reviewed
and accepted for **isolated readiness only** on September 28, 2026; at that
stage it was not registered on incubator main. The destination code/API commit
`0000be8ab382b047dfe93bb43ec2941b625fc9e7` completed both default-target
native builds and the complete transitive standard-axiom audit in run 740,
received fresh independent code/API review and was accepted and integrated by
Beacon on September 28, 2026. At that earlier code-acceptance checkpoint,
neither the acceptance nor this guide established a separately reviewed
official deliverable release or verified publication. The block/headline
release was subsequently completed at official commit
`fb22a0a31ff464de6f82d2f94ac6d37f837eb519` (issue 20/comment 57713)
on September 28, 2026. Neither the historical code review nor this guide
establishes incubator conversion, source correspondence or source coverage;
the separate iterator's later official publication is recorded in its own
[guide](iterated-block-substitution.md). The newly transferred structural laws
passed complete destination native CI checks (run 866), independent review
and Beacon's protected-main code/API acceptance at commit
`5179b6042154397e09c9047e24fb42dddc07ae15` on September 28, 2026;
separate release and publication decisions are recorded externally, not
certified by this generic-block guide.

Responsible maintainer and destination integration owner: Beacon. Original
contributor: worker-b Hive Task
`hive-request-7b6e0f04fc7e294c99c77638da5d6abb97b4be03`
(UID `0068e189-b29d-4cf7-9b0c-63cb34dab472`). Destination transfer:
worker-b Hive Task
`hive-request-54ffdbad98fe154f75224b39e0f7a253b50fde7c`
(UID `11eb8d82-791b-41fe-a9bf-e15eea2ba73a`). Independent destination
reviewer: worker-a Hive Task
`hive-request-446f2cfe616e290ac265715dbd9879143a7dda4c`
(UID `aa259428-f3d3-4e77-b017-91fa3c1d15de`). Documentation-only release
preparer: worker-b Hive Task
`hive-request-70e6e11667d1a57d588854eb0cc9806dab89b9c1`
(UID `d5157618-a9d2-4b99-9a6b-c21ea017878b`). The unchanged Lean toolchain
is `v4.34.0-rc2`, with mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
