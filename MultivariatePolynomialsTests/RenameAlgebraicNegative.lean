/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nonalgebraic variable-renaming algebras

The inclusion `some : PUnit → Option PUnit` is injective and omits `none`.
Over the integers and over `ZMod 4`, its full target polynomial ring is not
algebraic over its full source polynomial ring for the rename-induced action.
The option-variable equivalence sends the omitted variable to a univariate
indeterminate while leaving the entire source as the coefficient ring. The
coefficient transport is the injective identity, not an augmentation.

The coefficient ring `ZMod 4` has a nonzero square-zero element and is neither
reduced nor a domain. In contrast, zero coefficients make algebraicity false
even for identity renaming: a nonzero annihilating polynomial cannot exist
over a subsingleton source. Both a missing-variable example over `ZMod 1` and
a lifted arbitrary zero coefficient ring exhibit this boundary.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Equiv`: `optionEquivLeft`.
* Mathlib, `Mathlib.RingTheory.Algebraic.Basic`:
  `Polynomial.transcendental_X`, injective coefficient transport, and
  `Algebra.nontrivial_of_isAlgebraic`.
-/

universe r u v w

noncomputable section

namespace MvPolynomialRenameAlgebraicNegative

/-- The inclusion of the sole source variable does not identify variables. -/
private theorem somePUnit_injective :
    Function.Injective (some : PUnit → Option PUnit) := by
  intro i j h
  exact Option.some.inj h

/-- The extra target variable `none` has no preimage. -/
private theorem somePUnit_not_surjective :
    ¬ Function.Surjective (some : PUnit → Option PUnit) := by
  intro h
  obtain ⟨i, hi⟩ := h none
  cases hi

/-- The integer polynomial renaming is injective on the full source ring. -/
private theorem int_some_rename_injective :
    Function.Injective
      (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)) :=
  MvPolynomial.rename_injective _ somePUnit_injective

/-- The option-variable equivalence retains every integer source coefficient. -/
private theorem int_optionEquivLeft_comp_rename :
    (MvPolynomial.optionEquivLeft ℤ PUnit).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)).toRingHom =
      (Polynomial.C : MvPolynomial PUnit ℤ →+* Polynomial (MvPolynomial PUnit ℤ)) := by
  apply MvPolynomial.ringHom_ext
  · intro n
    simp
  · intro i
    simp

/-- The full integer polynomial renaming still misses a target polynomial. -/
private theorem int_some_rename_not_surjective :
    ¬ Function.Surjective
      (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)) := by
  intro h
  obtain ⟨p, hp⟩ := h (MvPolynomial.X none)
  have hpoly : (Polynomial.C p : Polynomial (MvPolynomial PUnit ℤ)) = Polynomial.X := by
    calc
      Polynomial.C p = (MvPolynomial.optionEquivLeft ℤ PUnit)
          (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit) p) :=
        (RingHom.congr_fun int_optionEquivLeft_comp_rename p).symm
      _ = Polynomial.X := by simp [hp]
  simpa using congrArg (fun q : Polynomial (MvPolynomial PUnit ℤ) => q.coeff 1) hpoly

/-- The omitted variable obstructs algebraicity over the full integer source. -/
private theorem int_some_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial PUnit ℤ) (MvPolynomial (Option PUnit) ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial PUnit ℤ) (MvPolynomial (Option PUnit) ℤ) :=
    (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)).toRingHom.toAlgebra
  intro h
  have hcomp :
      (algebraMap (MvPolynomial PUnit ℤ) (Polynomial (MvPolynomial PUnit ℤ))).comp
          (RingHom.id (MvPolynomial PUnit ℤ)) =
        (MvPolynomial.optionEquivLeft ℤ PUnit).toRingEquiv.toRingHom.comp
          (algebraMap (MvPolynomial PUnit ℤ) (MvPolynomial (Option PUnit) ℤ)) := by
    change (Polynomial.C : MvPolynomial PUnit ℤ →+* Polynomial (MvPolynomial PUnit ℤ)).comp
        (RingHom.id (MvPolynomial PUnit ℤ)) = _
    simp only [RingHom.algebraMap_toAlgebra, int_optionEquivLeft_comp_rename,
      RingHom.comp_id]
  have hx := h.isAlgebraic (MvPolynomial.X (none : Option PUnit))
  have hX := hx.ringHom_of_comp_eq (RingHom.id (MvPolynomial PUnit ℤ))
    (MvPolynomial.optionEquivLeft ℤ PUnit).toRingEquiv.toRingHom
    Function.injective_id hcomp
  exact (Polynomial.transcendental_X (MvPolynomial PUnit ℤ)) (by simpa using hX)

/-- A concrete nonzero coefficient in the ring of order four. -/
private theorem zmodFour_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  decide

/-- The same coefficient has square zero. -/
private theorem zmodFour_two_sq_eq_zero : (2 : ZMod 4) ^ 2 = 0 := by
  decide

/-- The ring of order four has a genuinely nonzero nilpotent. -/
private theorem zmodFour_has_nonzero_square_zero :
    ∃ a : ZMod 4, a ≠ 0 ∧ a ^ 2 = 0 :=
  ⟨2, zmodFour_two_ne_zero, zmodFour_two_sq_eq_zero⟩

/-- In particular, this coefficient ring is nontrivial. -/
private theorem zmodFour_nontrivial : Nontrivial (ZMod 4) :=
  ⟨⟨2, 0, zmodFour_two_ne_zero⟩⟩

/-- The square-zero element witnesses failure of reducedness. -/
private theorem zmodFour_not_isReduced : ¬ IsReduced (ZMod 4) := by
  intro h
  letI : IsReduced (ZMod 4) := h
  exact zmodFour_two_ne_zero (IsReduced.eq_zero (2 : ZMod 4)
    ⟨2, zmodFour_two_sq_eq_zero⟩)

/-- The same element also rules out a domain structure. -/
private theorem zmodFour_not_isDomain : ¬ IsDomain (ZMod 4) := by
  intro h
  letI : IsDomain (ZMod 4) := h
  have hmul : (2 : ZMod 4) * 2 = 0 := by
    simpa only [pow_two] using zmodFour_two_sq_eq_zero
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact zmodFour_two_ne_zero hzero
  · exact zmodFour_two_ne_zero hzero

/-- Nilpotents do not destroy injectivity of this variable inclusion. -/
private theorem zmodFour_some_rename_injective :
    Function.Injective
      (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)) :=
  MvPolynomial.rename_injective _ somePUnit_injective

/-- The option equivalence retains the whole source over the nonreduced ring. -/
private theorem zmodFour_optionEquivLeft_comp_rename :
    (MvPolynomial.optionEquivLeft (ZMod 4) PUnit).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)).toRingHom =
      (Polynomial.C : MvPolynomial PUnit (ZMod 4) →+*
        Polynomial (MvPolynomial PUnit (ZMod 4))) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp

/-- Nontrivial nonreduced coefficients still leave a missing target polynomial. -/
private theorem zmodFour_some_rename_not_surjective :
    ¬ Function.Surjective
      (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)) := by
  letI : Nontrivial (ZMod 4) := zmodFour_nontrivial
  intro h
  obtain ⟨p, hp⟩ := h (MvPolynomial.X none)
  have hpoly : (Polynomial.C p : Polynomial (MvPolynomial PUnit (ZMod 4))) =
      Polynomial.X := by
    calc
      Polynomial.C p = (MvPolynomial.optionEquivLeft (ZMod 4) PUnit)
          (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit) p) :=
        (RingHom.congr_fun zmodFour_optionEquivLeft_comp_rename p).symm
      _ = Polynomial.X := by simp [hp]
  simpa using congrArg
    (fun q : Polynomial (MvPolynomial PUnit (ZMod 4)) => q.coeff 1) hpoly

/-- Nonreduced coefficients do not make the full rename-induced algebra algebraic. -/
private theorem zmodFour_some_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial PUnit (ZMod 4))
      (MvPolynomial (Option PUnit) (ZMod 4)) inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial PUnit (ZMod 4)) (MvPolynomial (Option PUnit) (ZMod 4)) :=
    (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)).toRingHom.toAlgebra
  intro h
  have hcomp :
      (algebraMap (MvPolynomial PUnit (ZMod 4))
          (Polynomial (MvPolynomial PUnit (ZMod 4)))).comp
          (RingHom.id (MvPolynomial PUnit (ZMod 4))) =
        (MvPolynomial.optionEquivLeft (ZMod 4) PUnit).toRingEquiv.toRingHom.comp
          (algebraMap (MvPolynomial PUnit (ZMod 4))
            (MvPolynomial (Option PUnit) (ZMod 4))) := by
    change (Polynomial.C : MvPolynomial PUnit (ZMod 4) →+*
        Polynomial (MvPolynomial PUnit (ZMod 4))).comp
        (RingHom.id (MvPolynomial PUnit (ZMod 4))) = _
    simp only [RingHom.algebraMap_toAlgebra, zmodFour_optionEquivLeft_comp_rename,
      RingHom.comp_id]
  have hx := h.isAlgebraic (MvPolynomial.X (none : Option PUnit))
  have hX := hx.ringHom_of_comp_eq (RingHom.id (MvPolynomial PUnit (ZMod 4)))
    (MvPolynomial.optionEquivLeft (ZMod 4) PUnit).toRingEquiv.toRingHom
    Function.injective_id hcomp
  exact (Polynomial.transcendental_X (MvPolynomial PUnit (ZMod 4))) (by simpa using hX)

/-- The identity variable map is bijective, including with zero coefficients. -/
private theorem nat_id_bijective : Function.Bijective (id : ℕ → ℕ) :=
  ⟨Function.injective_id, Function.surjective_id⟩

/-- Identity renaming over the zero ring is surjective on full polynomial rings. -/
private theorem zmodOne_id_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)) :=
  MvPolynomial.rename_surjective _ nat_id_bijective.2

/-- Surjective identity renaming is nevertheless not algebraic over a zero source. -/
private theorem zmodOne_id_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) :=
    (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)).toRingHom.toAlgebra
  letI : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial ℕ (ZMod 1))
  intro h
  letI : Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) := h
  letI : Nontrivial (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.nontrivial_of_isAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
  exact zero_ne_one (Subsingleton.elim (0 : MvPolynomial ℕ (ZMod 1)) 1)

/-- The empty-variable map is injective. -/
private theorem empty_nat_injective : Function.Injective (Empty.elim : Empty → ℕ) := by
  intro i
  exact Empty.elim i

/-- The same map omits the natural-number variable zero. -/
private theorem empty_nat_not_surjective :
    ¬ Function.Surjective (Empty.elim : Empty → ℕ) := by
  intro h
  obtain ⟨i, _⟩ := h 0
  exact Empty.elim i

/-- Zero coefficients collapse the target even though the variable map is not surjective. -/
private theorem zmodOne_empty_nat_rename_surjective :
    Function.Surjective
      (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)) := by
  letI : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial ℕ (ZMod 1))
  exact Function.surjective_to_subsingleton _

/-- Even the zero target element needs a nonzero witness over the full zero source. -/
private theorem zmodOne_empty_nat_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) :=
    (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra
  letI : Subsingleton (MvPolynomial Empty (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial Empty (ZMod 1))
  intro h
  letI : Algebra.IsAlgebraic (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) := h
  letI : Nontrivial (MvPolynomial Empty (ZMod 1)) :=
    Algebra.nontrivial_of_isAlgebraic
      (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
  exact zero_ne_one (Subsingleton.elim (0 : MvPolynomial Empty (ZMod 1)) 1)

/-- Copying natural-number variables between independent universes. -/
private def liftedCopy : ULift.{v} ℕ → ULift.{w} ℕ := fun n => ⟨n.down⟩

/-- The lifted copy neither identifies nor omits variables. -/
private theorem liftedCopy_bijective :
    Function.Bijective (liftedCopy : ULift.{v} ℕ → ULift.{w} ℕ) := by
  constructor
  · intro i j h
    cases i
    cases j
    cases h
    rfl
  · intro n
    exact ⟨⟨n.down⟩, rfl⟩

/-- Lifting any zero coefficient ring preserves the negative algebraicity boundary,
even for a bijection of variable types in independent universes. -/
private theorem lifted_zero_not_isAlgebraic {R : Type u} [CommRing R] [Subsingleton R] :
    ¬ @Algebra.IsAlgebraic
      (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R)) inferInstance inferInstance
      (MvPolynomial.rename (R := ULift.{r} R)
        (liftedCopy : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R)) :=
    (MvPolynomial.rename (R := ULift.{r} R)
      (liftedCopy : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra
  letI : Subsingleton (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R)) :=
    Algebra.subsingleton (ULift.{r} R) (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
  intro h
  letI : Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R)) := h
  letI : Nontrivial (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R)) :=
    Algebra.nontrivial_of_isAlgebraic
      (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R))
  exact zero_ne_one
    (Subsingleton.elim (0 : MvPolynomial (ULift.{v} ℕ) (ULift.{r} R)) 1)

end MvPolynomialRenameAlgebraicNegative
