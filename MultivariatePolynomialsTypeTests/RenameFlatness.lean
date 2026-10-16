/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameFlatness
import Mathlib.Data.ZMod.Basic

/-!
# Clients of the flatness and prime-spectrum criteria for renaming

These clients use the full polynomial-ring homomorphism: a proper inclusion
of variables over the integers, a collision over `ZMod 4`, and the same
collision over the zero ring. The independent boundary models remain separate.
The faithful-flatness and prime-spectrum clients below use the two
criteria; they also include natural-number coefficients and an empty source
variable type.
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

/-- The strict one-variable inclusion over `ℤ` is surjective on prime spectra. -/
public theorem unit_bool_comap_rename_surjective_int :
    Function.Surjective
      (PrimeSpectrum.comap (rename (R := ℤ) (fun _ : Unit => false)).toRingHom) :=
  (comap_rename_surjective_iff (R := ℤ) (fun _ : Unit => false)).mpr
    (Or.inl (fun _ _ _ => Subsingleton.elim _ _))

/-- The strict one-variable inclusion over `ℤ` is faithfully flat on full polynomial rings. -/
public theorem unit_bool_rename_faithfullyFlat :
    RingHom.FaithfullyFlat (rename (R := ℤ) (fun _ : Unit => false)).toRingHom :=
  (rename_faithfullyFlat_iff (R := ℤ) (fun _ : Unit => false)).mpr
    (Or.inl (fun _ _ _ => Subsingleton.elim _ _))

/-- Prime-spectrum surjectivity also holds for the strict inclusion over the
commutative semiring `ℕ`, which is not a ring. -/
public theorem unit_bool_comap_rename_surjective_nat :
    Function.Surjective
      (PrimeSpectrum.comap (rename (R := ℕ) (fun _ : Unit => false)).toRingHom) :=
  (comap_rename_surjective_iff (R := ℕ) (fun _ : Unit => false)).mpr
    (Or.inl (fun _ _ _ => Subsingleton.elim _ _))

/-- Over the zero ring, even the collision of two variables is faithfully flat
and surjective on prime spectra. -/
public theorem bool_unit_rename_zero_boundaries :
    RingHom.FaithfullyFlat (rename (R := ZMod 1) (fun _ : Bool => ())).toRingHom ∧
      Function.Surjective
        (PrimeSpectrum.comap (rename (R := ZMod 1) (fun _ : Bool => ())).toRingHom) :=
  ⟨(rename_faithfullyFlat_iff (R := ZMod 1) (fun _ : Bool => ())).mpr
      (Or.inr inferInstance),
    (comap_rename_surjective_iff (R := ZMod 1) (fun _ : Bool => ())).mpr
      (Or.inr inferInstance)⟩

/-- Adding variables to an empty variable family over `ℤ` is faithfully flat
and surjective on prime spectra. -/
public theorem empty_bool_rename_boundaries :
    RingHom.FaithfullyFlat (rename (R := ℤ) (Empty.elim : Empty → Bool)).toRingHom ∧
      Function.Surjective
        (PrimeSpectrum.comap (rename (R := ℤ) (Empty.elim : Empty → Bool)).toRingHom) := by
  have hf : Function.Injective (Empty.elim : Empty → Bool) :=
    fun i => nomatch i
  exact ⟨(rename_faithfullyFlat_iff (R := ℤ) (Empty.elim : Empty → Bool)).mpr (Or.inl hf),
    (comap_rename_surjective_iff (R := ℤ) (Empty.elim : Empty → Bool)).mpr (Or.inl hf)⟩

/-- The collision over the nonreduced ring `ZMod 4` is not faithfully flat. -/
public theorem bool_unit_rename_not_faithfullyFlat :
    ¬ RingHom.FaithfullyFlat (rename (R := ZMod 4) (fun _ : Bool => ())).toRingHom :=
  fun h => bool_unit_rename_not_flat h.flat

end MultivariatePolynomialsTests.RenameFlatness
