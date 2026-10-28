/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

/-!
# Polynomial renaming: coercion and boundary contracts

These contracts concern the renaming homomorphism from the full source
polynomial semiring to the full target polynomial semiring. Natural-number
coefficients allow infinitely many variables without requiring a coefficient
ring. Projection from paired variables is surjective despite identifying
variables. The same surjective maps work over the nonreduced ring `ZMod 4`.

With coefficients `ZMod 1`, polynomial renaming is both injective and surjective
even for a variable map which is neither. Empty variable types are also allowed.
The lifted identity transport separates the coefficient, source-variable and
target-variable universes. These formalizations by Formal Frontier Agents use
Mathlib’s renaming theorems and subsingleton instances.
-/

universe u v w

namespace MvPolynomial

private def natProjection : ℕ × Bool → ℕ := Prod.fst

private theorem nat_projection_surjective : Function.Surjective natProjection := by
  intro n
  exact ⟨(n, false), rfl⟩

private theorem nat_projection_not_injective : ¬ Function.Injective natProjection := by
  intro h
  have hpair : (0, false) = (0, true) := h (a₁ := (0, false)) (a₂ := (0, true)) rfl
  have hbool : false = true := congrArg Prod.snd hpair
  cases hbool

private theorem nat_projection_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ℕ) natProjection :
      MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) :=
  MvPolynomial.rename_surjective _ nat_projection_surjective

private theorem nat_projection_ringHom_surjective :
    Function.Surjective ((MvPolynomial.rename (R := ℕ) natProjection).toRingHom :
      MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) :=
  nat_projection_rename_surjective

private theorem nat_projection_coercions :
    ((MvPolynomial.rename (R := ℕ) natProjection).toRingHom :
      MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) =
    (MvPolynomial.rename (R := ℕ) natProjection :
      MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) := rfl

private theorem zmod_four_two_ne_zero : (2 : ZMod 4) ≠ 0 := by decide

private theorem zmod_four_two_sq_zero : (2 : ZMod 4) ^ 2 = 0 := by decide

private theorem zmod_four_identity_rename_injective :
    Function.Injective (MvPolynomial.rename (R := ZMod 4) (id : ℕ → ℕ) :
      MvPolynomial ℕ (ZMod 4) → MvPolynomial ℕ (ZMod 4)) :=
  MvPolynomial.rename_injective _ (fun _ _ h => h)

private theorem zmod_four_identity_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ZMod 4) (id : ℕ → ℕ) :
      MvPolynomial ℕ (ZMod 4) → MvPolynomial ℕ (ZMod 4)) :=
  MvPolynomial.rename_surjective _ (fun n => ⟨n, rfl⟩)

private theorem zmod_four_projection_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ZMod 4) natProjection :
      MvPolynomial (ℕ × Bool) (ZMod 4) → MvPolynomial ℕ (ZMod 4)) :=
  MvPolynomial.rename_surjective _ nat_projection_surjective

private def pairSuccessor (x : ℕ × Bool) : ℕ := x.1 + 1

private theorem pair_successor_not_injective : ¬ Function.Injective pairSuccessor := by
  intro h
  have hpair : (0, false) = (0, true) := h (a₁ := (0, false)) (a₂ := (0, true)) rfl
  have hbool : false = true := congrArg Prod.snd hpair
  cases hbool

private theorem pair_successor_not_surjective : ¬ Function.Surjective pairSuccessor := by
  intro h
  obtain ⟨⟨n, b⟩, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

private theorem zmod_one_coefficients_subsingleton : Subsingleton (ZMod 1) :=
  inferInstance

@[instance_reducible] private def zmod_one_pair_polynomials_unique :
    Unique (MvPolynomial (ℕ × Bool) (ZMod 1)) := inferInstance

@[instance_reducible]
private def zmod_one_nat_polynomials_unique : Unique (MvPolynomial ℕ (ZMod 1)) :=
  inferInstance

private theorem zmod_one_pair_successor_rename_injective :
    Function.Injective (MvPolynomial.rename (R := ZMod 1) pairSuccessor :
      MvPolynomial (ℕ × Bool) (ZMod 1) → MvPolynomial ℕ (ZMod 1)) := by
  have : Subsingleton (MvPolynomial (ℕ × Bool) (ZMod 1)) := inferInstance
  exact Function.injective_of_subsingleton _

private theorem zmod_one_pair_successor_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ZMod 1) pairSuccessor :
      MvPolynomial (ℕ × Bool) (ZMod 1) → MvPolynomial ℕ (ZMod 1)) := by
  have : Nonempty (MvPolynomial (ℕ × Bool) (ZMod 1)) := ⟨0⟩
  exact Function.surjective_to_subsingleton _

private theorem empty_identity_rename_injective :
    Function.Injective (MvPolynomial.rename (R := ℕ) (id : Empty → Empty) :
      MvPolynomial Empty ℕ → MvPolynomial Empty ℕ) :=
  MvPolynomial.rename_injective _ (fun _ _ h => h)

private theorem empty_identity_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ℕ) (id : Empty → Empty) :
      MvPolynomial Empty ℕ → MvPolynomial Empty ℕ) :=
  MvPolynomial.rename_surjective _ (fun e => ⟨e, rfl⟩)

private def emptyToNat : Empty → ℕ := Empty.elim

private theorem empty_to_nat_not_surjective : ¬ Function.Surjective emptyToNat := by
  intro h
  obtain ⟨e, _⟩ := h 0
  exact e.elim

private theorem zmod_one_empty_to_nat_rename_injective :
    Function.Injective (MvPolynomial.rename (R := ZMod 1) emptyToNat :
      MvPolynomial Empty (ZMod 1) → MvPolynomial ℕ (ZMod 1)) := by
  have : Subsingleton (MvPolynomial Empty (ZMod 1)) := inferInstance
  exact Function.injective_of_subsingleton _

private theorem zmod_one_empty_to_nat_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ZMod 1) emptyToNat :
      MvPolynomial Empty (ZMod 1) → MvPolynomial ℕ (ZMod 1)) := by
  have : Nonempty (MvPolynomial Empty (ZMod 1)) := ⟨0⟩
  exact Function.surjective_to_subsingleton _

private def liftedIdentity (x : ULift.{v} ℕ) : ULift.{w} ℕ := ⟨x.down⟩

private theorem lifted_identity_injective :
    Function.Injective (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ) := by
  rintro ⟨a⟩ ⟨b⟩ h
  have hab : a = b := congrArg ULift.down h
  cases hab
  rfl

private theorem lifted_identity_surjective :
    Function.Surjective (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ) := by
  rintro ⟨n⟩
  exact ⟨⟨n⟩, rfl⟩

private theorem lifted_identity_rename_injective :
    Function.Injective (MvPolynomial.rename (R := ULift.{u} ℕ)
      (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ) :
      MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ) →
        MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) :=
  MvPolynomial.rename_injective _ lifted_identity_injective

private theorem lifted_identity_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ULift.{u} ℕ)
      (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ) :
      MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ) →
        MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) :=
  MvPolynomial.rename_surjective _ lifted_identity_surjective

end MvPolynomial
