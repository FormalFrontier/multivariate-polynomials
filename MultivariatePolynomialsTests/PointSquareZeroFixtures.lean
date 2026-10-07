/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.PointSquareZeroPresentation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Boundary examples for polynomial point quotients

The empty, singleton, zero-ring and infinite families test the scope of the
presentation. Colliding and non-unit-separated integer points still admit the
forward map but fail the proposed separation hypothesis. No result from the
separated equivalence is imported.
-/

@[expose] public section

open scoped Polynomial TrivSqZeroExt

namespace PointSquareZeroFixtures

private def emptyPoints : Empty → ℤ := Empty.elim

private theorem empty_ideal : MvPolynomial.pointSquareZeroIdeal emptyPoints = ⊥ := by
  simp [MvPolynomial.pointSquareZeroIdeal]

private def singletonPoints : PUnit → ℤ := fun _ => 0

private theorem singleton_nontrivial :
    (Ideal.Quotient.mk (MvPolynomial.pointSquareZeroIdeal singletonPoints)
      (MvPolynomial.X (some PUnit.unit)) ≠ 0) ∧
    (Ideal.Quotient.mk (MvPolynomial.pointSquareZeroIdeal singletonPoints)
      (MvPolynomial.X (some PUnit.unit))) ^ 2 = 0 := by
  constructor
  · intro hy
    have hnonzero :
        (Ideal.Quotient.mk (RingHom.ker
          (Polynomial.evalRingHom (singletonPoints PUnit.unit))) (1 : ℤ[X])) ≠ 0 := by
      intro hz
      have hmem : (1 : ℤ[X]) ∈ RingHom.ker
          (Polynomial.evalRingHom (singletonPoints PUnit.unit)) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hz
      have heval : (1 : ℤ) = 0 := by simpa [RingHom.mem_ker] using hmem
      exact one_ne_zero heval
    have hzero : MvPolynomial.pointSquareZeroDelta singletonPoints PUnit.unit = 0 := by
      apply (TrivSqZeroExt.inr_injective (R := ℤ[X]))
      rw [← MvPolynomial.pointSquareZeroForward_mk_some]
      rw [hy, map_zero]
      rfl
    apply hnonzero
    have hcomponent := congrArg
      (fun d : MvPolynomial.pointSquareZeroModule singletonPoints => d PUnit.unit) hzero
    simpa only [MvPolynomial.pointSquareZeroDelta, DirectSum.lof_apply,
      DFinsupp.zero_apply] using hcomponent
  · exact MvPolynomial.pointSquareZero_sq singletonPoints PUnit.unit

private def zeroRingPoints : Bool → ZMod 1 := fun _ => 0

private theorem zeroRing_separated :
    ∀ i j : Bool, i ≠ j → IsUnit (zeroRingPoints i - zeroRingPoints j) := by
  intro i j _
  have h : zeroRingPoints i - zeroRingPoints j = (1 : ZMod 1) := Subsingleton.elim _ _
  rw [h]
  exact isUnit_one

private def infiniteSeparatedPoints : ℕ → ℚ := fun n => n

private theorem infinite_separated :
    ∀ i j : ℕ, i ≠ j → IsUnit (infiniteSeparatedPoints i - infiniteSeparatedPoints j) := by
  intro i j hij
  apply isUnit_iff_ne_zero.mpr
  apply sub_ne_zero.mpr
  change (i : ℚ) ≠ (j : ℚ)
  exact_mod_cast hij

private theorem infinite_range : (Set.range infiniteSeparatedPoints).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j h
  change (i : ℚ) = (j : ℚ) at h
  exact_mod_cast h

private def repeatedPoints : Bool → ℤ := fun _ => 0

private theorem repeated_not_separated :
    ¬ ∀ i j : Bool, i ≠ j → IsUnit (repeatedPoints i - repeatedPoints j) := by
  intro h
  have hbad := h true false (by decide)
  norm_num [repeatedPoints] at hbad

private def nonunitDifferencePoints : Bool → ℤ := fun b => if b then 2 else 0

private theorem nonunit_not_separated :
    ¬ ∀ i j : Bool, i ≠ j → IsUnit (nonunitDifferencePoints i - nonunitDifferencePoints j) := by
  intro h
  have hbad := h true false (by decide)
  norm_num [nonunitDifferencePoints, Int.isUnit_iff_natAbs_eq] at hbad

private theorem repeated_forward_exists :
    ∃ f : MvPolynomial.pointSquareZeroQuotient repeatedPoints →ₐ[ℤ[X]]
        TrivSqZeroExt ℤ[X] (MvPolynomial.pointSquareZeroModule repeatedPoints),
      f (Ideal.Quotient.mk (MvPolynomial.pointSquareZeroIdeal repeatedPoints)
        (MvPolynomial.X (some true))) =
          TrivSqZeroExt.inr (MvPolynomial.pointSquareZeroDelta repeatedPoints true) :=
  ⟨MvPolynomial.pointSquareZeroForward repeatedPoints, by simp⟩

private theorem nonunit_forward_exists :
    ∃ f : MvPolynomial.pointSquareZeroQuotient nonunitDifferencePoints →ₐ[ℤ[X]]
        TrivSqZeroExt ℤ[X] (MvPolynomial.pointSquareZeroModule nonunitDifferencePoints),
      f (Ideal.Quotient.mk (MvPolynomial.pointSquareZeroIdeal nonunitDifferencePoints)
        (MvPolynomial.X (some false))) =
          TrivSqZeroExt.inr (MvPolynomial.pointSquareZeroDelta nonunitDifferencePoints false) :=
  ⟨MvPolynomial.pointSquareZeroForward nonunitDifferencePoints, by simp⟩

end PointSquareZeroFixtures
