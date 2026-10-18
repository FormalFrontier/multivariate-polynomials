/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import MultivariatePolynomials.Jacobson

/-!
# Nilpotent constants and polynomial Jacobson radicals

In `MvPolynomial Unit (ZMod 4)`, `C 2` is nonzero and square-zero. Its second
power witnesses radical membership, and `Ideal.radical_le_jacobson` gives
Jacobson membership. Both ideals therefore contain a nonzero element. Over
the zero coefficient ring both ideals are zero.
-/

@[expose] public section

example :
    Ideal.jacobson (⊥ : Ideal (MvPolynomial Unit (ZMod 1))) =
      (⊥ : Ideal (MvPolynomial Unit (ZMod 1))).radical :=
  Subsingleton.elim _ _

example :
    ∃ p : MvPolynomial Unit (ZMod 4), p ≠ 0 ∧ p ^ 2 = 0 ∧
      p ∈ (⊥ : Ideal (MvPolynomial Unit (ZMod 4))).radical ∧
      p ∈ Ideal.jacobson (⊥ : Ideal (MvPolynomial Unit (ZMod 4))) :=
  let p : MvPolynomial Unit (ZMod 4) := MvPolynomial.C 2
  have hne : p ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (show (2 : ZMod 4) ≠ 0 from by decide)
  have hsquare : p ^ 2 = 0 := by
    simpa only [p, map_pow, map_zero] using
      congrArg (MvPolynomial.C : ZMod 4 →+* MvPolynomial Unit (ZMod 4))
        (show (2 : ZMod 4) ^ 2 = 0 from by decide)
  have hradical : p ∈ (⊥ : Ideal (MvPolynomial Unit (ZMod 4))).radical :=
    Ideal.mem_radical_iff.mpr
      ⟨2, by simpa only [Ideal.mem_bot] using hsquare⟩
  ⟨p, hne, hsquare, hradical, Ideal.radical_le_jacobson hradical⟩

example :
    Ideal.jacobson (⊥ : Ideal (MvPolynomial Unit (ZMod 4))) =
      (⊥ : Ideal (MvPolynomial Unit (ZMod 4))).radical :=
  Ideal.jacobson_bot_mvPolynomial
