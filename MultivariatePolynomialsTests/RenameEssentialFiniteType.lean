/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFiniteType
import Mathlib.RingTheory.RingHom.EssFiniteType

@[expose] public section

/-!
# Standard models of essentially finite type renaming

Successor renaming over the integers adjoins the single missed variable `X 0`
to the full source polynomial ring. The essential-finite-type witness below
comes from finite type and the canonical ring-homomorphism bridge.
-/

universe u

private theorem rename_succ_int_essFiniteType :
    RingHom.EssFiniteType ((MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom) := by
  have h : RingHom.FiniteType
      ((MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom) :=
    MvPolynomial.finiteType_rename_succ (R := ℤ)
  exact h.essFiniteType

-- Subsingleton coefficients allow infinitely many missed variables.
private theorem rename_empty_essFiniteType_of_subsingleton {R : Type u} [CommRing R] [Subsingleton R] :
    RingHom.EssFiniteType
      ((MvPolynomial.rename (R := R) (Empty.elim : Empty → ℕ)).toRingHom) := by
  apply RingHom.FiniteType.essFiniteType
  exact (MvPolynomial.finiteType_rename_iff (R := R)
    (Empty.elim : Empty → ℕ)).mpr (Or.inl inferInstance)

-- This refutes only the proposed right-hand side, not essential finite type.
private theorem not_subsingleton_or_finite_compl_range_even_int :
    ¬ (Subsingleton ℤ ∨
      Set.Finite ((Set.range (fun n : ℕ => 2 * n))ᶜ)) := by
  intro h
  exact MvPolynomial.not_finiteType_rename_even (R := ℤ)
    ((MvPolynomial.finiteType_rename_iff (R := ℤ) (fun n : ℕ => 2 * n)).mpr h)
