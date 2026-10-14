/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.NormNum

/-!
# Integral renaming: independent positive models

These models concern
`RingHom.IsIntegral ((MvPolynomial.rename (R := R) f).toRingHom)`: the canonical
renaming ring homomorphism from the full source polynomial ring to the full
target polynomial ring. Integrality here is over the source polynomial ring
through that map, not over the coefficient ring.

With coefficient ring `ℤ`, the identity on natural-number variables and the
projection from `ℕ × Bool` induce integral polynomial-ring homomorphisms;
projection is surjective but not injective. The same projection is integral
with coefficients `ZMod 4`, where `2` is nonzero and has square zero.
With zero coefficients, even the
nonsurjective map from `Empty` to `ℕ` induces an integral renaming. Empty source
and target variable types give another integral renaming with coefficients `ℤ`.

The lifted model places coefficients, source variables, and target variables
in three independent universes. Each integrality proof uses Mathlib's
`MvPolynomial.rename_surjective` and `RingHom.isIntegral_of_surjective`, or
surjectivity onto a subsingleton target for the zero-coefficient model.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: renaming and its surjectivity.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`:
  surjective ring homomorphisms are integral.
* Mathlib, `Mathlib.Algebra.Algebra.Defs`: algebras over subsingleton rings.
-/

private theorem integer_coefficients_nontrivial : (0 : ℤ) ≠ 1 :=
  zero_ne_one

private theorem nat_variables_infinite : Infinite ℕ :=
  inferInstance

private theorem nat_identity_surjective : Function.Surjective (id : ℕ → ℕ) := by
  intro n
  exact ⟨n, rfl⟩

private theorem nat_identity_integral :
    RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom) := by
  exact RingHom.isIntegral_of_surjective _
    (MvPolynomial.rename_surjective (R := ℤ) _ nat_identity_surjective)

private theorem projection_surjective :
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) := by
  intro n
  exact ⟨(n, false), rfl⟩

private theorem projection_not_injective :
    ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) := by
  intro h
  have hpair : ((0 : ℕ), false) = (0, true) := h rfl
  cases congrArg Prod.snd hpair

private theorem projection_integral :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom) := by
  exact RingHom.isIntegral_of_surjective _
    (MvPolynomial.rename_surjective (R := ℤ) _ projection_surjective)

private theorem zmod_four_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  intro h
  have hval := congrArg ZMod.val h
  norm_num [ZMod.val_two_eq_two_mod, ZMod.val_zero] at hval

private theorem zmod_four_two_sq_zero : (2 : ZMod 4) ^ 2 = 0 := by
  calc
    (2 : ZMod 4) ^ 2 = (4 : ZMod 4) := by norm_num
    _ = 0 := ZMod.natCast_self 4

private theorem zmod_four_projection_integral :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := ZMod 4) (Prod.fst : ℕ × Bool → ℕ)).toRingHom) := by
  exact RingHom.isIntegral_of_surjective _
    (MvPolynomial.rename_surjective (R := ZMod 4) _ projection_surjective)

private theorem zero_coefficients_subsingleton : Subsingleton (ZMod 1) :=
  inferInstance

private theorem empty_to_nat_not_surjective :
    ¬ Function.Surjective (Empty.elim : Empty → ℕ) := by
  intro h
  obtain ⟨i, _⟩ := h 0
  exact Empty.elim i

private theorem zero_coefficients_target_subsingleton :
    Subsingleton (MvPolynomial ℕ (ZMod 1)) := by
  letI : Subsingleton (ZMod 1) := zero_coefficients_subsingleton
  exact Algebra.subsingleton (ZMod 1) (MvPolynomial ℕ (ZMod 1))

private theorem zero_empty_to_nat_rename_surjective :
    Function.Surjective
      ((MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom) := by
  letI : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    zero_coefficients_target_subsingleton
  exact Function.surjective_to_subsingleton _

private theorem zero_empty_to_nat_integral :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom) := by
  exact RingHom.isIntegral_of_surjective _ zero_empty_to_nat_rename_surjective

private theorem empty_to_empty_surjective :
    Function.Surjective (Empty.elim : Empty → Empty) := by
  intro i
  exact Empty.elim i

private theorem empty_to_empty_integral :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := ℤ) (Empty.elim : Empty → Empty)).toRingHom) := by
  exact RingHom.isIntegral_of_surjective _
    (MvPolynomial.rename_surjective (R := ℤ) _ empty_to_empty_surjective)

universe u v w

private theorem ulift_coefficients_nontrivial : (0 : ULift.{u} ℤ) ≠ 1 := by
  intro h
  exact integer_coefficients_nontrivial (congrArg ULift.down h)

private theorem ulift_nat_surjective :
    Function.Surjective
      (fun n : ULift.{v} ℕ => (ULift.up n.down : ULift.{w} ℕ)) := by
  intro n
  exact ⟨ULift.up n.down, rfl⟩

private theorem ulift_nat_integral :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := ULift.{u} ℤ)
        (fun n : ULift.{v} ℕ => (ULift.up n.down : ULift.{w} ℕ))).toRingHom) := by
  exact RingHom.isIntegral_of_surjective _
    (MvPolynomial.rename_surjective (R := ULift.{u} ℤ) _
      ulift_nat_surjective)
