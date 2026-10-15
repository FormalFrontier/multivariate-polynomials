/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameComplement
import MultivariatePolynomials.Regularity
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Independent boundary models for flatness of variable renaming

Retaining one of two variables gives a flat, nonsurjective renaming over `ℤ`.
Collapsing two variables gives a nonflat renaming over `ZMod 4`, whose nonzero
nilpotent coefficient witnesses that no domain assumption is hidden in this
example. Over `ZMod 1`, the same collision is flat. None of these proofs imports
or uses the flatness classification. The regularity step uses the general
variable-difference API.

The natural-number calculation also exercises the complementary-variable
construction outside the category of commutative rings.
-/

namespace MultivariatePolynomialsTests.RenameFlatnessModels

open MvPolynomial

private def retained : Set Bool := {false}

private theorem retained_injective :
    Function.Injective (Subtype.val : retained → Bool) :=
  Subtype.val_injective

private theorem retained_not_surjective :
    ¬ Function.Surjective (Subtype.val : retained → Bool) := by
  intro h
  obtain ⟨i, hi⟩ := h true
  have ht : true ∈ retained := hi ▸ i.property
  simp [retained] at ht

private theorem retained_rename_flat :
    RingHom.Flat (rename (R := ℤ) (Subtype.val : retained → Bool)).toRingHom := by
  let e := splitComplAlgEquiv (R := ℤ) retained
  have hcomp : e.symm.toRingEquiv.toRingHom.comp
      (C : MvPolynomial retained ℤ →+*
        MvPolynomial (retainedᶜ : Set Bool) (MvPolynomial retained ℤ)) =
      (rename (R := ℤ) (Subtype.val : retained → Bool)).toRingHom := by
    apply RingHom.ext
    intro p
    apply e.injective
    change e (e.symm (C p)) = e (rename (Subtype.val : retained → Bool) p)
    rw [AlgEquiv.apply_symm_apply, splitComplAlgEquiv_rename_subtypeVal]
  have hC : RingHom.Flat
      (C : MvPolynomial retained ℤ →+*
        MvPolynomial (retainedᶜ : Set Bool) (MvPolynomial retained ℤ)) := by
    change RingHom.Flat (algebraMap (MvPolynomial retained ℤ)
      (MvPolynomial (retainedᶜ : Set Bool) (MvPolynomial retained ℤ)))
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  rw [← hcomp]
  exact hC.comp (RingHom.Flat.of_bijective e.symm.bijective)

private theorem complement_over_naturals :
    splitComplAlgEquiv (R := ℕ) retained
      (X true * rename (Subtype.val : retained → Bool)
        (X (⟨false, by simp [retained]⟩ : retained))) =
      X (⟨true, by simp [retained]⟩ : (retainedᶜ : Set Bool)) *
        C (X (⟨false, by simp [retained]⟩ : retained)) := by
  rw [map_mul, splitComplAlgEquiv_rename_subtypeVal]
  congr 1
  exact splitComplAlgEquiv_X_compl (R := ℕ) retained
    (⟨true, by simp [retained]⟩ : (retainedᶜ : Set Bool))

private def collision : Bool → Unit := fun _ => ()

private theorem collision_not_injective : ¬ Function.Injective collision := by
  intro h
  have hft : false = true := h (show collision false = collision true from rfl)
  cases hft

private theorem coefficient_nonzero_nilpotent :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  decide

private abbrev CollisionSource := MvPolynomial Bool (ZMod 4)
private abbrev CollisionTarget := MvPolynomial Unit (ZMod 4)

private theorem collision_difference_regular :
    IsSMulRegular CollisionSource (X false - X true : CollisionSource) :=
  (isRegular_X_sub_X (R := ZMod 4) (i := false) (j := true) (by decide)).1

/-- Collapsing two variables over `ZMod 4` gives a nonflat polynomial-ring map. -/
public theorem collision_rename_not_flat :
    ¬ RingHom.Flat (rename (R := ZMod 4) (fun _ : Bool => ())).toRingHom := by
  intro hflat
  let f : CollisionSource →+* CollisionTarget :=
    (rename (R := ZMod 4) collision).toRingHom
  let : Algebra CollisionSource CollisionTarget := f.toAlgebra
  let : Module.Flat CollisionSource CollisionTarget := hflat
  have hreg : IsSMulRegular CollisionTarget
      (algebraMap CollisionSource CollisionTarget
        (X false - X true : CollisionSource)) :=
    collision_difference_regular.of_flat
  have hz : algebraMap CollisionSource CollisionTarget
      (X false - X true : CollisionSource) = 0 := by
    change f (X false - X true) = 0
    simp [f, collision]
  rw [hz] at hreg
  have h10 : (1 : CollisionTarget) = 0 :=
    hreg (show (0 : CollisionTarget) • (1 : CollisionTarget) =
      (0 : CollisionTarget) • 0 by simp)
  have hcoeff : (1 : ZMod 4) = 0 := by
    simpa using congrArg (fun p : CollisionTarget => constantCoeff p) h10
  exact (by decide : (1 : ZMod 4) ≠ 0) hcoeff

private theorem zero_coefficients_subsingleton : Subsingleton (ZMod 1) :=
  inferInstance

private theorem collision_rename_flat_zero :
    RingHom.Flat (rename (R := ZMod 1) collision).toRingHom := by
  unfold RingHom.Flat
  infer_instance

end MultivariatePolynomialsTests.RenameFlatnessModels
