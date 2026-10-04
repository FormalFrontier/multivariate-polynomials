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
client [`MultivariatePolynomialsTests.BlockSubstitutionLaws`](../MultivariatePolynomialsTests/BlockSubstitutionLaws.lean) exercises
mixed variable types, noninjective maps and these boundary cases. This abstract
API by itself establishes no correspondence with a particular source's
numbered-variable recurrence.

The structural laws and their Lean clients are original project work distinct
from Beacon's block-substitution exposition; see [CREDITS.md](../CREDITS.md).
