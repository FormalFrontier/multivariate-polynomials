/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameUnramified
import Mathlib.Data.ZMod.Basic

/-!
# Models of formally unramified variable renaming

Over the integers, the constant map from `Bool` to `Unit` gives a formally
unramified renaming despite identifying two variables. The finite-module comparison
also applies to this surjection, with scalars from the full source polynomial ring.
The map from `Empty` to `Unit` does not give a formally unramified renaming over
the integers, but does over the zero coefficient ring `ZMod 1`. In the zero-ring
case, failure of injectivity of a variable map would not imply failure of
injectivity of its polynomial renaming.

## References

* `MultivariatePolynomials.RenameUnramified`: the variable-level formal
  unramifiedness criterion and its finite-module comparison.
* `MultivariatePolynomials.RenameModuleFinite`: the finite-module criterion.
* Mathlib, `Mathlib.Data.ZMod.Basic`: the zero coefficient ring `ZMod 1`.
-/

private theorem integer_collision_formallyUnramified :
    (¬ Function.Injective (fun _ : Bool => ())) ∧
      RingHom.FormallyUnramified
        (MvPolynomial.rename (R := ℤ) (fun _ : Bool => ())).toRingHom := by
  constructor
  · intro h
    have hfalse : (false : Bool) = true := h rfl
    cases hfalse
  · apply (MvPolynomial.formallyUnramified_rename_iff_moduleFinite
      (R := ℤ) (fun _ : Bool => ())).2
    apply (MvPolynomial.moduleFinite_rename_iff (R := ℤ) (fun _ : Bool => ())).2
    left
    intro t
    exact ⟨false, Subsingleton.elim _ _⟩

private theorem integer_omitted_variable_not_formallyUnramified :
    ¬ RingHom.FormallyUnramified
      (MvPolynomial.rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom := by
  intro h
  have hs := (MvPolynomial.formallyUnramified_rename_iff (R := ℤ)
    (Empty.elim : Empty → Unit)).1 h
  rcases hs with hs | hR
  · obtain ⟨e, _⟩ := hs ()
    exact Empty.elim e
  · exact zero_ne_one (hR.elim 0 1)

private theorem zero_coefficients_omitted_variable_formallyUnramified :
    RingHom.FormallyUnramified
      (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → Unit)).toRingHom :=
  (MvPolynomial.formallyUnramified_rename_iff
    (R := ZMod 1) (Empty.elim : Empty → Unit)).2
      (Or.inr (ZMod.subsingleton_iff.mpr rfl))
