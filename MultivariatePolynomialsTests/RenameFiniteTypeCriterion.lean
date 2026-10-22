/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFiniteType
import Mathlib.Data.ZMod.Basic

/-!
# Relative finite type for infinite variable renaming

Shifting the natural-number variables by one or two gives a finite-type algebra
relative to the source polynomial semiring, although both variable types are
infinite. In contrast, renaming each variable index `n` to `2 * n` gives a
finite-type algebra exactly when the coefficient semiring is subsingleton:
the infinitely many odd target indices are missed. This renaming sends `X n`
to `X (2 * n)`, not to the square of `X n`.

These applications specialize the public shift and even-index API, without
constructing algebra generators or a scalar tower. The shift-by-two example
allows arbitrary commutative semiring coefficients. The even-index examples
compare the nontrivial semiring `ℕ` with the zero semiring `ZMod 1`, showing why
the negative result requires nontriviality. The algebra structure in each
statement is induced by the displayed renaming homomorphism, not merely the
coefficient algebra structure.

## References

* `MultivariatePolynomials.RenameFiniteType`: the relative finite-type criterion
  and its natural-number shift and even-index applications.
* Mathlib, `Mathlib.Data.ZMod.Basic`: the zero semiring `ZMod 1`.
-/

universe u

namespace MultivariatePolynomialsTests

private theorem finiteType_rename_succ :
    @Algebra.FiniteType (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) _ _
      (MvPolynomial.rename (R := ℕ) Nat.succ).toRingHom.toAlgebra :=
  MvPolynomial.finiteType_rename_succ

private theorem finiteType_rename_add_two {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (MvPolynomial.rename (R := R) (fun n : ℕ => n + 2)).toRingHom.toAlgebra :=
  MvPolynomial.finiteType_rename_add 2

private theorem not_finiteType_rename_even_nat :
    ¬ @Algebra.FiniteType (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) _ _
      (MvPolynomial.rename (R := ℕ) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra :=
  MvPolynomial.not_finiteType_rename_even

private theorem finiteType_rename_even_zero :
    @Algebra.FiniteType (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) _ _
      (MvPolynomial.rename (R := ZMod 1) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra :=
  (MvPolynomial.finiteType_rename_even_iff (R := ZMod 1)).mpr inferInstance

end MultivariatePolynomialsTests
