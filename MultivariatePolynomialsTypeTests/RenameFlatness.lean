/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameFlatness
import Mathlib.Data.ZMod.Basic

/-!
# Clients of the flatness criterion for renaming

These clients use the full polynomial-ring homomorphism: a proper inclusion
of variables over the integers, a collision over `ZMod 4`, and the same
collision over the zero ring. The independent boundary models remain separate.
-/

namespace MultivariatePolynomialsTests.RenameFlatness

open MvPolynomial

/-- The proper one-variable inclusion into two-variable integer polynomials is flat. -/
public theorem unit_bool_rename_flat :
    RingHom.Flat (rename (R := ℤ) (fun _ : Unit => false)).toRingHom :=
  (rename_flat_iff (R := ℤ) (fun _ : Unit => false)).mpr
    (Or.inl (fun _ _ _ => Subsingleton.elim _ _))

private theorem unit_bool_inclusion_not_surjective :
    ¬ Function.Surjective (fun _ : Unit => false) := by
  intro h
  obtain ⟨i, hi⟩ := h true
  cases hi

private theorem unit_bool_rename_X :
    rename (R := ℤ) (fun _ : Unit => false) (X ()) = X false := by
  simp

private theorem bool_unit_collision_kills_difference :
    rename (R := ZMod 4) (fun _ : Bool => ())
      (X false - X true : MvPolynomial Bool (ZMod 4)) = 0 := by
  simp

private theorem bool_unit_rename_not_flat :
    ¬ RingHom.Flat (rename (R := ZMod 4) (fun _ : Bool => ())).toRingHom := by
  intro hflat
  rcases (rename_flat_iff (R := ZMod 4) (fun _ : Bool => ())).mp hflat with hf | hR
  · have hft : false = true := hf rfl
    cases hft
  · have h01 : (0 : ZMod 4) = 1 := @Subsingleton.elim _ hR 0 1
    exact (by decide : (0 : ZMod 4) ≠ 1) h01

private theorem bool_unit_rename_flat_zero :
    RingHom.Flat (rename (R := ZMod 1) (fun _ : Bool => ())).toRingHom :=
  (rename_flat_iff (R := ZMod 1) (fun _ : Bool => ())).mpr (Or.inr inferInstance)

end MultivariatePolynomialsTests.RenameFlatness
