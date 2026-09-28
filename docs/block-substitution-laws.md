# Structural laws for disjoint-block substitutions

Import `MultivariatePolynomials.BlockSubstitutionLaws` directly (the
[producer](../MultivariatePolynomials/BlockSubstitutionLaws.lean)), or import
`MultivariatePolynomials` for the aggregate API. For polynomials
`p : MvPolynomial I R`, `q : MvPolynomial J R`, `r : MvPolynomial K R` and
`[CommSemiring R]`, `MvPolynomial.blockSubst p q` has variables
`I × J`. Its copies of `q` are indexed by the variables of `p`.

- `rename_blockSubst f g p q` says that renaming the pair `(i,j)` to
  `(f i,g j)` is the same as separately renaming `p` and `q`. The functions
  can identify variables; no injectivity is required.
- `blockSubst_assoc p q r` identifies the two bracketings by **forward**
  renaming of `((i,j),k)` to `(i,(j,k))`, using `Equiv.prodAssoc I J K`.
- `blockSubst_X_left p` and `blockSubst_X_right p` use the one-variable
  polynomial `X PUnit.unit` as a unit. Their renamings erase its respectively
  left and right `PUnit` tags. The zero-length word variable below is also a
  *single* variable, not an empty variable set.

`iteratedBlockSubst p n` from the
[local iterator](../MultivariatePolynomials/IteratedBlockSubstitution.lean)
has variables `(Fin n → I)`, including the empty-word variable at `n = 0`.
`iteratedBlockSubst_one p` renames `p` by one-letter words. The additive law
`iteratedBlockSubst_add p m n` identifies the `(m+n)`-fold iterate with
`blockSubst (iteratedBlockSubst p m) (iteratedBlockSubst p n)` after renaming
`(a,b)` to `Fin.append a b`. The proof uses the native cons successor and the
position-preserving length cast
`Nat.add_right_comm m 1 n : m+1+n = m+n+1`; it never chooses an equivalence
merely from equal cardinalities. `iteratedBlockSubst_snoc p m` is the opposite
successor, substituting the original `p` at the end of each word and renaming
`(a,i)` to `Fin.snoc a i`.

These are polynomial equalities proved using mathlib's `bind₁_bind₁`,
`rename_bind₁`, `bind₁_rename`, and `rename_rename` and its finite-tuple
concatenation laws. They do **not** use equality of evaluations at
coefficient-ring points, which would be insufficient over finite fields. They
require no finiteness, nonemptiness, nontriviality, field, degree, or
homogeneity hypothesis; zero polynomials, constants, empty index types,
zero iterations, and zero semirings are included. The private ordinary-import
client [`Test.BlockSubstitutionLaws`](../Test/BlockSubstitutionLaws.lean) exercises
mixed variable types, noninjective maps and these boundary cases. This abstract
API by itself establishes no correspondence with a particular source's
numbered-variable recurrence.

Responsible maintainer: Beacon. Original contributor of these structural
laws and the ordinary-import client: worker-b Hive Task
`hive-request-b3d4d6e3a78dc53efdabae39dcafd0f770d8c0c4` (UID
`12c22dfd-831c-4fa3-a82a-d6e0a88a8a5d`). The underlying block and
iterator authors are separately credited in the [README](../README.md);
their previous release is complete at official commit
`ec4906268f2a65a54e320ce9f3f44562e9d78c1e`. The isolated laws donor
`b21228137f1cb0b644817628a3cc29c696b6156f` passed independent review
`52304b237d071945221c80a19f94b7a4c5c84202`, with applicable isolated
build/axiom evidence `56b0bb6dd7645635589e3999068e136a2d7e6cb7`;
Beacon accepted only that isolated contribution (incubator issue 171/comment
59495). The new destination transfer is by worker-b Hive Task
`hive-request-dcfc7155e1b8f1e339a4db2a5f323981d29793e3` (UID
`50067b60-ca63-4a90-bbcf-6e81453fd6a1`). Exact destination commit
`5179b6042154397e09c9047e24fb42dddc07ae15` passed the complete native
CI build/standard-axiom checks (run 866), received independent worker-a
review `bacb7cb13e1ef0d82c7599027015976dfa42f76a` (Task
`hive-request-32a5395f2a6b985f54aec6698f4988e3d00b81bf`, UID
`f02d75a9-fc5e-4044-ac63-a130c00c09e8`), and was accepted and
protected-integrated by Beacon on September 28, 2026 (PR #26).
Documentation-only release preparation is by worker-b Task
`hive-request-8f84e6612202ac883d6b0bbd46bbd1ee4a5c7d49` (UID
`fa2f833c-131c-4cc7-acc0-99d96bb5a71c`). The distinct official release
and verified publication require separate revision-specific decisions; this
guide does not certify them. Source correspondence and coverage are separate.
