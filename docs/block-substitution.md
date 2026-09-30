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
The separately developed [iteration](iterated-block-substitution.md) and [structural laws](block-substitution-laws.md) have their own guides. Project authorship and mathlib credit appear in [CREDITS.md](../CREDITS.md).
