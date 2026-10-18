/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameKernelProperties
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Applications of the prime and radical renaming-kernel criteria

Identifying two variables over the integers gives a nonzero prime radical
kernel. The same criteria apply over the natural-number semiring. Over `ZMod 4`,
the nonzero square-zero constant `2` obstructs both properties. Over the zero
ring, the kernel is radical but not prime, even between empty variable types in
different universes.

The collision and coefficient data below use polynomial renaming, variable
injectivity, and closed modular arithmetic independently of the kernel criteria.

## References

* `MultivariatePolynomials.RenameKernelProperties`: prime and radical criteria.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic` and
  `Mathlib.Algebra.MvPolynomial.Rename`: variables and their renaming.
* Mathlib, `Mathlib.Data.ZMod.Basic`: modular coefficient rings.
-/

open MvPolynomial

namespace MultivariatePolynomialsTests

private theorem int_collision :
    (X false - X true : MvPolynomial Bool ℤ) ≠ 0 ∧
      X false - X true ∈ RingHom.ker
        (rename (R := ℤ) (fun _ : Bool => ())).toRingHom := by
  constructor
  · intro h
    have hvars : false = true := X_injective (sub_eq_zero.mp h)
    cases hvars
  · apply RingHom.mem_ker.mpr
    change rename (R := ℤ) (fun _ : Bool => ()) (X false - X true) = 0
    simp only [map_sub, rename_X, sub_self]

private theorem nat_collision :
    (X false : MvPolynomial Bool ℕ) ≠ X true ∧
      rename (R := ℕ) (fun _ : Bool => ()) (X false) =
        rename (R := ℕ) (fun _ : Bool => ()) (X true) := by
  constructor
  · intro h
    have hvars : false = true := X_injective h
    cases hvars
  · simp only [rename_X]

private theorem zmod_four_data :
    ¬ (⊥ : Ideal (ZMod 4)).IsPrime ∧ ¬ IsReduced (ZMod 4) := by
  have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  constructor
  · intro h
    have hmul : (2 : ZMod 4) * 2 = 0 := by simpa only [pow_two] using hsq
    rcases h.mem_or_mem (Ideal.mem_bot.mpr hmul) with hmem | hmem <;>
      exact hne (Ideal.mem_bot.mp hmem)
  · intro h
    letI := h
    exact hne (show IsNilpotent (2 : ZMod 4) from ⟨2, hsq⟩).eq_zero

private theorem zmod_one_data :
    ¬ (⊥ : Ideal (ZMod 1)).IsPrime ∧ IsReduced (ZMod 1) := by
  letI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  constructor
  · intro h
    exact h.one_notMem (Ideal.mem_bot.mpr (Subsingleton.elim _ _))
  · infer_instance

example :
    (RingHom.ker (rename (R := ℤ) (fun _ : Bool => ())).toRingHom).IsPrime ∧
      (RingHom.ker (rename (R := ℤ) (fun _ : Bool => ())).toRingHom).IsRadical ∧
      ∃ p : MvPolynomial Bool ℤ, p ≠ 0 ∧
        p ∈ RingHom.ker (rename (R := ℤ) (fun _ : Bool => ())).toRingHom := by
  refine ⟨(isPrime_ker_rename_iff _).mpr inferInstance,
    (isRadical_ker_rename_iff _).mpr inferInstance, ?_⟩
  exact ⟨X false - X true, int_collision.1, int_collision.2⟩

example :
    (RingHom.ker (rename (R := ℕ) (fun _ : Bool => ())).toRingHom).IsPrime ∧
      (RingHom.ker (rename (R := ℕ) (fun _ : Bool => ())).toRingHom).IsRadical ∧
      (X false : MvPolynomial Bool ℕ) ≠ X true ∧
      rename (R := ℕ) (fun _ : Bool => ()) (X false) =
        rename (R := ℕ) (fun _ : Bool => ()) (X true) := by
  exact ⟨(isPrime_ker_rename_iff _).mpr inferInstance,
    (isRadical_ker_rename_iff _).mpr inferInstance, nat_collision⟩

example :
    ¬ (RingHom.ker (rename (R := ZMod 4) (fun _ : Bool => ())).toRingHom).IsPrime ∧
      ¬ (RingHom.ker (rename (R := ZMod 4) (fun _ : Bool => ())).toRingHom).IsRadical := by
  constructor
  · intro h
    exact zmod_four_data.1 ((isPrime_ker_rename_iff _).mp h)
  · intro h
    exact zmod_four_data.2 ((isRadical_ker_rename_iff _).mp h)

example :
    ¬ (RingHom.ker (rename (R := ZMod 1)
      (Empty.elim : Empty → PEmpty.{2})).toRingHom).IsPrime ∧
      (RingHom.ker (rename (R := ZMod 1)
        (Empty.elim : Empty → PEmpty.{2})).toRingHom).IsRadical := by
  constructor
  · intro h
    exact zmod_one_data.1 ((isPrime_ker_rename_iff _).mp h)
  · exact (isRadical_ker_rename_iff _).mpr zmod_one_data.2

end MultivariatePolynomialsTests
