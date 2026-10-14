/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Nonintegral variable-renaming maps

Successor on the natural-number variables gives a nonintegral ring homomorphism
between the full polynomial rings, both over the integers and over `ZMod 4`.
The latter coefficient ring has a nonzero element whose square is zero. The
unique map from `Empty` to `Unit` gives another nonintegral renaming map.
The shifted projection `(n, b) ↦ n + 1` is both noninjective and nonsurjective,
and also induces a nonintegral map over the integers. A lifted successor separates
the universes of the coefficients, source variables, and target variables.

In each case a target variable omitted by the renaming evaluates to the
univariate indeterminate, while the renamed source evaluates through its
augmentation to the coefficient ring. An integral witness for that target
variable would therefore make the univariate indeterminate integral over the
coefficients.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename` and
  `Mathlib.Algebra.MvPolynomial.Eval`: canonical renaming and evaluation maps.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` and
  `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`:
  `RingHom.IsIntegralElem.map`, `RingHom.IsIntegralElem.of_comp`, and
  `RingHom.IsIntegral.tower_top`.
* Mathlib, `Mathlib.RingTheory.Algebraic.Basic` and
  `Mathlib.RingTheory.Algebraic.Integral`: `Polynomial.transcendental_X` and
  `IsIntegral.isAlgebraic`.
-/

universe u v w

noncomputable section

namespace MvPolynomialRenameIntegralNegative

/-- The zero variable is not in the image of successor. -/
private theorem natSucc_not_surjective : ¬ Function.Surjective Nat.succ := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

/-- For the fixed successor map, any nontrivial commutative coefficient ring
leaves the zero variable nonintegral over the full renamed source. -/
private theorem natSucc_not_isIntegral (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := R) Nat.succ).toRingHom) := by
  intro h
  let ψ : MvPolynomial ℕ R →+* Polynomial R :=
    MvPolynomial.eval₂Hom Polynomial.C (fun n => if n = 0 then Polynomial.X else 0)
  let ε : MvPolynomial ℕ R →+* R :=
    MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)
  have hcomp : ψ.comp (MvPolynomial.rename (R := R) Nat.succ).toRingHom =
      Polynomial.C.comp ε := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, ε, MvPolynomial.rename_C]
    · intro n
      simp [ψ, ε]
  have hx := (h (MvPolynomial.X 0)).map ψ
  rw [hcomp] at hx
  have hX : IsIntegral R (Polynomial.X : Polynomial R) := by
    simpa [IsIntegral, ψ] using hx.of_comp
  exact (Polynomial.transcendental_X R) hX.isAlgebraic

/-- Successor over the integers is nonintegral as a map of full polynomial rings. -/
private theorem int_natSucc_not_isIntegral :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom) :=
  natSucc_not_isIntegral ℤ

/-- A fixed shifted projection forgets the Boolean coordinate. -/
private def pairSucc : ℕ × Bool → ℕ := fun p => p.1 + 1

/-- Two distinct source variables have the same image under the shifted projection. -/
private theorem pairSucc_collision :
    ((0, false) : ℕ × Bool) ≠ (0, true) ∧
      pairSucc (0, false) = pairSucc (0, true) := by
  refine ⟨?_, rfl⟩
  intro h
  have h' : false = true := congrArg Prod.snd h
  cases h'

/-- The shifted projection is not injective. -/
private theorem pairSucc_not_injective : ¬ Function.Injective pairSucc := by
  intro h
  exact pairSucc_collision.1 (h pairSucc_collision.2)

/-- The zero target variable is omitted by the shifted projection. -/
private theorem pairSucc_misses_zero (p : ℕ × Bool) : pairSucc p ≠ 0 := by
  simp [pairSucc]

/-- The shifted projection is not surjective. -/
private theorem pairSucc_not_surjective : ¬ Function.Surjective pairSucc := by
  intro h
  obtain ⟨p, hp⟩ := h 0
  exact pairSucc_misses_zero p hp

/-- Noninjectivity does not make the shifted projection integral. Factoring through
successor avoids any claim of nonalgebraicity over the full source ring. -/
private theorem int_pairSucc_not_isIntegral :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) pairSucc).toRingHom) := by
  intro h
  have hcomp : (MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom.comp
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom =
      (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom := by
    change ((MvPolynomial.rename (R := ℤ) Nat.succ).comp
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ))).toRingHom = _
    exact congrArg AlgHom.toRingHom
      (MvPolynomial.rename_comp_rename (R := ℤ)
        (Prod.fst : ℕ × Bool → ℕ) Nat.succ)
  apply int_natSucc_not_isIntegral
  apply RingHom.IsIntegral.tower_top
    (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom
    (MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom
  simpa only [hcomp] using h

/-- The coefficient ring of order four has a genuinely nonzero element `2`. -/
private theorem zmodFour_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  decide

/-- That same nonzero element has square zero. -/
private theorem zmodFour_two_sq_eq_zero : (2 : ZMod 4) ^ 2 = 0 := by
  decide

/-- Thus this coefficient model has a nonzero nilpotent element. -/
private theorem zmodFour_has_nonzero_square_zero :
    ∃ a : ZMod 4, a ≠ 0 ∧ a ^ 2 = 0 :=
  ⟨2, zmodFour_two_ne_zero, zmodFour_two_sq_eq_zero⟩

/-- The nonzero coefficient supplies a nontriviality witness. -/
private theorem zmodFour_nontrivial : Nontrivial (ZMod 4) :=
  ⟨⟨2, 0, zmodFour_two_ne_zero⟩⟩

/-- Nilpotents in the coefficients do not make successor renaming integral. -/
private theorem zmodFour_natSucc_not_isIntegral :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ZMod 4) Nat.succ).toRingHom) := by
  letI : Nontrivial (ZMod 4) := zmodFour_nontrivial
  exact natSucc_not_isIntegral (ZMod 4)

/-- The unique function from no variables to one variable is not surjective. -/
private theorem empty_unit_not_surjective :
    ¬ Function.Surjective (Empty.elim : Empty → Unit) := by
  intro h
  obtain ⟨i, _⟩ := h ()
  exact Empty.elim i

/-- Even an empty source variable set leaves the full target variable nonintegral. -/
private theorem int_empty_unit_not_isIntegral :
    ¬ RingHom.IsIntegral
      ((MvPolynomial.rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom) := by
  intro h
  let ψ : MvPolynomial Unit ℤ →+* Polynomial ℤ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X)
  let ε : MvPolynomial Empty ℤ →+* ℤ :=
    MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun _ => 0)
  have hcomp : ψ.comp
      (MvPolynomial.rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom =
      Polynomial.C.comp ε := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, ε, MvPolynomial.rename_C]
    · intro i
      exact Empty.elim i
  have hx := (h (MvPolynomial.X ())).map ψ
  rw [hcomp] at hx
  have hX : IsIntegral ℤ (Polynomial.X : Polynomial ℤ) := by
    simpa [IsIntegral, ψ] using hx.of_comp
  exact (Polynomial.transcendental_X ℤ) hX.isAlgebraic

/-- Successor lifted between two independently chosen variable universes. -/
private def liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨n.down.succ⟩

/-- The lifted zero variable is still omitted. -/
private theorem liftedSuccessor_not_surjective :
    ¬ Function.Surjective (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ) := by
  intro h
  obtain ⟨n, hn⟩ := h ⟨0⟩
  have hn' : n.down.succ = 0 := congrArg ULift.down hn
  exact Nat.succ_ne_zero n.down hn'

/-- Lifting the integer coefficients preserves their nontriviality. -/
private theorem liftedInt_nontrivial : Nontrivial (ULift.{u} ℤ) := by
  refine ⟨⟨⟨0⟩, ⟨1⟩, ?_⟩⟩
  intro h
  have h' : (0 : ℤ) = 1 := congrArg ULift.down h
  exact zero_ne_one h'

/-- The full renaming map remains nonintegral with three independent universes. -/
private theorem liftedInt_liftedSuccessor_not_isIntegral :
    ¬ RingHom.IsIntegral
      ((MvPolynomial.rename (R := ULift.{u} ℤ)
        (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom) := by
  letI : Nontrivial (ULift.{u} ℤ) := liftedInt_nontrivial
  intro h
  let ψ : MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ) →+* Polynomial (ULift.{u} ℤ) :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun n => if n.down = 0 then Polynomial.X else 0)
  let ε : MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ) →+* ULift.{u} ℤ :=
    MvPolynomial.eval₂Hom (RingHom.id (ULift.{u} ℤ)) (fun _ => 0)
  have hcomp : ψ.comp
      (MvPolynomial.rename (R := ULift.{u} ℤ)
        (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom =
      Polynomial.C.comp ε := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, ε, MvPolynomial.rename_C]
    · intro n
      simp [ψ, ε, liftedSuccessor]
  have hx := (h (MvPolynomial.X (⟨0⟩ : ULift.{w} ℕ))).map ψ
  rw [hcomp] at hx
  have hX : IsIntegral (ULift.{u} ℤ) (Polynomial.X : Polynomial (ULift.{u} ℤ)) := by
    simpa [IsIntegral, ψ] using hx.of_comp
  exact (Polynomial.transcendental_X (ULift.{u} ℤ)) hX.isAlgebraic

end MvPolynomialRenameIntegralNegative
