/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.AddUnits
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Prod

/-!
# Additive-unit factorization and operation coherence

The homomorphism `ℤ →ₙ+* ℕ × ℤ`, `z ↦ (0, z)`, has nonzero image but does not
preserve the ambient identity. Its factorization needs neither a ring target nor
a multiplicative identity in the additive units. The remaining checks cover the
zero cases and definitional agreement of the inherited operations.
-/

private def intToNatProdInt : ℤ →ₙ+* ℕ × ℤ :=
  (0 : ℤ →ₙ+* ℕ).prod (NonUnitalRingHom.id ℤ)

example (z : ℤ) : (AddUnits.liftNonUnitalRingHom intToNatProdInt z).val = (0, z) := rfl

example : AddUnits.coeNonUnitalRingHom.comp
    (AddUnits.nonUnitalRingHomEquiv.symm intToNatProdInt) = intToNatProdInt := by
  simp

example (g : ℤ →ₙ+* AddUnits (ℕ × ℤ))
    (h : AddUnits.coeNonUnitalRingHom.comp g = intToNatProdInt) :
    g = AddUnits.nonUnitalRingHomEquiv.symm intToNatProdInt :=
  AddUnits.liftNonUnitalRingHom_unique intToNatProdInt g h

example : (AddUnits.liftNonUnitalRingHom intToNatProdInt 1).val ≠ (1 : ℕ × ℤ) := by
  intro h
  exact Nat.zero_ne_one (congrArg Prod.fst h)

example : AddUnits.liftNonUnitalRingHom intToNatProdInt 1 ≠ 0 := by
  intro h
  exact Int.one_ne_zero (congrArg (fun a : AddUnits (ℕ × ℤ) => a.val.2) h)

example (a : AddUnits ℕ) : a = 0 :=
  AddUnits.ext (Nat.add_eq_zero_iff.mp a.val_neg).1

example {R : Type*} [NonUnitalNonAssocSemiring R] [Subsingleton R] (a : AddUnits R) :
    a = 0 := AddUnits.ext (Subsingleton.elim _ _)

-- Agreement of this whole structure checks addition, zero, negation, nsmul and zsmul.
example {R : Type*} [NonUnitalNonAssocSemiring R] :
    (inferInstance : NonUnitalNonAssocRing (AddUnits R)).toAddCommGroup =
      (inferInstance : AddCommGroup (AddUnits R)) := rfl

-- The stronger structures retain the same multiplication as well as additive data.
example {R : Type*} [NonUnitalSemiring R] :
    (inferInstance : NonUnitalRing (AddUnits R)).toNonUnitalNonAssocRing =
      (inferInstance : NonUnitalNonAssocRing (AddUnits R)) := rfl

example {R : Type*} [NonUnitalCommSemiring R] :
    (inferInstance : NonUnitalCommRing (AddUnits R)).toNonUnitalRing =
      (inferInstance : NonUnitalRing (AddUnits R)) := rfl
