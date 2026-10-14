/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFiniteType
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Relative finite type for infinite variable renaming

Shifting the natural-number variables by one or two gives a finite-type algebra
relative to the source polynomial semiring, although both variable types are
infinite. In contrast, renaming each variable index `n` to `2 * n` gives a
finite-type algebra exactly when the coefficient semiring is subsingleton:
the infinitely many odd target indices are missed. This renaming sends `X n`
to `X (2 * n)`, not to the square of `X n`.

These applications use the variable-renaming criterion directly, without
constructing algebra generators or a scalar tower. The coefficients can be any
commutative semiring. The algebra structure in each statement is the one induced
by the displayed renaming homomorphism, not merely the coefficient algebra
structure.

## References

* `MultivariatePolynomials.RenameFiniteType`: the relative finite-type criterion.
* Mathlib, `Mathlib.Data.Set.Finite.Basic`: finite subsets and infinite ranges of
  injective maps.
* Mathlib, `Mathlib.Data.Nat.Init`: separation of even and odd natural-number indices.
-/

universe u

namespace MultivariatePolynomialsTests

private theorem finiteType_rename_succ {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (MvPolynomial.rename (R := R) Nat.succ).toRingHom.toAlgebra := by
  apply (MvPolynomial.finiteType_rename_iff (R := R) Nat.succ).mpr
  right
  refine (Set.finite_singleton (0 : ℕ)).subset ?_
  intro n hn
  cases n with
  | zero => exact Set.mem_singleton 0
  | succ n => exact (hn ⟨n, rfl⟩).elim

private theorem finiteType_rename_add_two {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (MvPolynomial.rename (R := R) (fun n : ℕ => n + 2)).toRingHom.toAlgebra := by
  apply (MvPolynomial.finiteType_rename_iff (R := R) (fun n : ℕ => n + 2)).mpr
  right
  refine (Set.Finite.insert 0 (Set.finite_singleton (1 : ℕ))).subset ?_
  intro n hn
  cases n with
  | zero => exact Set.mem_insert 0 _
  | succ n =>
    cases n with
    | zero => exact Set.mem_insert_of_mem 0 (Set.mem_singleton 1)
    | succ n => exact (hn ⟨n, rfl⟩).elim

private theorem finiteType_rename_even_iff {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (MvPolynomial.rename (R := R) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra ↔
      Subsingleton R := by
  have hodd_injective : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro m n h
    exact Nat.mul_left_cancel Nat.zero_lt_two (Nat.add_right_cancel h)
  have hodd_subset : Set.range (fun n : ℕ => 2 * n + 1) ⊆
      (Set.range (fun n : ℕ => 2 * n))ᶜ := by
    rintro _ ⟨n, rfl⟩ ⟨m, hm⟩
    exact Nat.two_mul_ne_two_mul_add_one hm
  have hmissed : ((Set.range (fun n : ℕ => 2 * n))ᶜ).Infinite :=
    (Set.infinite_range_of_injective hodd_injective).mono hodd_subset
  rw [MvPolynomial.finiteType_rename_iff]
  exact ⟨fun h => h.resolve_right hmissed, Or.inl⟩

end MultivariatePolynomialsTests
