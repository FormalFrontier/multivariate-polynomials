# Iterated disjoint-block polynomial substitution

Import `MultivariatePolynomials.IteratedBlockSubstitution` to use
`MvPolynomial.iteratedBlockSubst`. For a commutative semiring `R`, any variable
type `ι` and `p : MvPolynomial ι R`, its `r`-th iterate has variables indexed by
`Fin r → ι`. An index is an ordered tuple of `r` original variable names;
there is one empty tuple when `r = 0`.

The construction is **structural**, not an identification by evaluation:

```lean
iteratedBlockSubst p 0 = X Fin.elim0
iteratedBlockSubst p (r + 1) =
  rename (Fin.consEquiv (fun _ : Fin (r + 1) => ι))
    (blockSubst p (iteratedBlockSubst p r))
```

Thus the successor places a copy of the preceding iterate in each disjoint
block of `p`. The head of a successor tuple chooses a block and its tail chooses
a variable of the preceding iterate. The defining equations and
`eval_iteratedBlockSubst_zero` / `eval_iteratedBlockSubst_succ` expose the
corresponding evaluation identities; no polynomial equality is inferred from
equality of pointwise evaluations, which would be unsound over finite fields.

For every `r`, `eval_iteratedBlockSubst_eq_zero_imp` carries the hypothesis
`∀ y, eval y p = 0 → y = 0` to the tuple variables of the iterate. Separately,
`eval_iteratedBlockSubst_eq_zero_iff` carries the strictly stronger hypothesis
`∀ y, eval y p = 0 ↔ y = 0` to an equivalence. The reverse direction does **not**
follow from the forward-only property: a nonzero constant over `ZMod 2` is a
counterexample. Neither core theorem needs finite or inhabited variable types,
nontrivial coefficients, positive degree or a field. They also cover zero rings,
empty variable types and `r = 0`.

If `p.IsHomogeneous d`, then `isHomogeneous_iteratedBlockSubst` makes every
iterate homogeneous of **nominal degree** `d ^ r`. This uses native
`IsHomogeneous.aeval` and `rename_isHomogeneous` on the local generic
`blockSubst`; the result does not require `p ≠ 0`. In particular, at `r = 0`
the degree is `1` even when `d = 0`, and degrees `0` or `1` do not give
unbounded growth. With `[Nontrivial R]` and `[Nonempty ι]`, a forward-only base
property gives `iteratedBlockSubst_ne_zero`, so
`iteratedBlockSubst_totalDegree` identifies the actual total degree with
`d ^ r`. The nonzero premise is essential for this identification;
`IsHomogeneous 0 d` holds for multiple nominal degrees.

For a compact use with a base homogeneous polynomial satisfying the
forward-only property, `exists_iteratedBlockSubst_totalDegree_gt` additionally
assumes `1 < d` and gives, for every `bound : ℕ`, some `r` with
`bound < (iteratedBlockSubst p r).totalDegree`. It asserts **attained degrees
beyond every bound**, not that every sufficiently large degree occurs. The
private ordinary-import client
`Test.IteratedBlockSubstitution` exercises this
with the native finite arity equation
`Fintype.card (Fin r → ι) = (Fintype.card ι) ^ r`; if the base arity is
`d ^ m`, the tuple arity is `d ^ (m * r)`, equivalently the iterate's exact
total degree to the power `m`. These are conditional results: this library does
not construct a base polynomial over an arbitrary field.

`blockSubst` and its evaluation/zero/nonzero results are supplied by the
[local generic-block module](../MultivariatePolynomials/BlockSubstitution.lean);
see its [independent guide](block-substitution.md). The public iterator is in
[the iteration producer](../MultivariatePolynomials/IteratedBlockSubstitution.lean),
and [its ordinary-import client](../Test/IteratedBlockSubstitution.lean) remains
private to the test target. The separate
[structural-law guide](block-substitution-laws.md) gives `iteratedBlockSubst_one`,
`iteratedBlockSubst_add` using `Fin.append` and `iteratedBlockSubst_snoc` using
`Fin.snoc`. This opposite successor appends the original polynomial at the end
of the tuple; it is not the `Fin.consEquiv` recursion that defines the iterator.
The iteration was originally developed as an
isolated incubator candidate `c916ced0230520b33e1a519174be4020324708d0`,
independently reviewed and accepted only for isolated mathematical/API
readiness (incubator issue 153/comments 58032 and 58041). That was an
earlier checkpoint; destination integration and the reviewed official release
subsequently completed at commit `ec4906268f2a65a54e320ce9f3f44562e9d78c1e`
on September 28, 2026. The new structural-law transfer passed destination
native CI checks (run 866), independent review and protected-main code/API
integration at `5179b6042154397e09c9047e24fb42dddc07ae15` on that date;
its separate release and publication require their own external decisions.
Source correspondence remains separate, not certified by this guide.

Original generic-block author: worker-b Task
`hive-request-7b6e0f04fc7e294c99c77638da5d6abb97b4be03` (UID
`0068e189-b29d-4cf7-9b0c-63cb34dab472`). Original finite-iteration
contributor: worker-a Task `hive-request-48b8f568eaec9f747a0528cb5fe8ae07ff507397`
(UID `580b0679-5109-43e3-8af0-05470fe31187`). Destination transfer:
worker-b Task `hive-request-2deb4fea21bdf1e8bfd734175d5bf8c681d288c7`
(UID `f641b493-3b74-49f4-bc2d-bb46824a4fa5`). Collective project authorship
and Apache-2.0 terms are retained. This guide does not construct a base form,
assert all sufficiently large degrees, or claim source coverage.
