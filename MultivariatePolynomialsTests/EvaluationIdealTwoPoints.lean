/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.EvaluationIdeal
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum

/-!
# Two-point evaluation over commutative rings

Applications of the evaluation-kernel image, sum and comaximality lemmas.
The integer and residue-ring examples distinguish unequal points, unit
coordinate differences, and differences that jointly generate the unit ideal.
The empty-variable and one-element-ring examples include degenerate cases.
-/

open MvPolynomial

universe u v w

private theorem mem_ker_eval_sup_iff
    {R : Type u} {σ : Type v} [CommRing R] (a b : σ → R) (p : MvPolynomial σ R) :
    p ∈ RingHom.ker (eval a) ⊔ RingHom.ker (eval b) ↔
      eval a p ∈ Ideal.span (Set.range (fun i : σ => a i - b i)) := by
  rw [ker_eval_sup_ker_eval_eq_comap a b, Ideal.mem_comap]

section IntegerUnitDifference

local notation "a" => (fun _ : PUnit.{1} => (0 : ℤ))
local notation "b" => (fun _ : PUnit.{1} => (1 : ℤ))

private theorem integer_unit_difference_comaximal :
    RingHom.ker (eval a) ⊔ RingHom.ker (eval b) = ⊤ := by
  apply (ker_eval_sup_ker_eval_eq_top_iff a b).mpr
  rw [Set.range_const, Ideal.span_singleton_eq_top, Int.isUnit_iff]
  decide

end IntegerUnitDifference

section IntegerNonunitDifference

local notation "a" => (fun _ : PUnit.{1} => (0 : ℤ))
local notation "b" => (fun _ : PUnit.{1} => (2 : ℤ))

private theorem integer_nonunit_difference_image :
    Ideal.map (eval a) (RingHom.ker (eval b)) = Ideal.span {(-2 : ℤ)} := by
  simpa only [Set.range_const, zero_sub] using map_ker_eval_eq_span_sub a b

private theorem integer_nonunit_difference_not_comaximal :
    RingHom.ker (eval a) ⊔ RingHom.ker (eval b) ≠ ⊤ := by
  intro h
  have htop := (ker_eval_sup_ker_eval_eq_top_iff a b).mp h
  rw [Set.range_const] at htop
  have hunit := (Ideal.span_singleton_eq_top (α := ℤ)).mp htop
  norm_num [Int.isUnit_iff] at hunit

end IntegerNonunitDifference

section EmptyVariables

local notation "a" => (Empty.elim : Empty → ℤ)
local notation "b" => (fun i : Empty => (Empty.elim i : ℤ))

private theorem empty_variables_kernel_image :
    Ideal.map (eval a) (RingHom.ker (eval b)) = ⊥ := by
  rw [map_ker_eval_eq_span_sub a b]
  rw [show Set.range (fun i : Empty => a i - b i) = ∅ from
    Set.range_eq_empty_iff.mpr ⟨Empty.elim⟩]
  exact Ideal.span_empty

end EmptyVariables

section TrivialCoefficientRing

local notation "a" => (fun _ : PUnit.{1} => (0 : (PUnit : Type)))
local notation "b" => (fun _ : PUnit.{1} => (1 : (PUnit : Type)))

private theorem punit_ideal_bot_eq_top : (⊥ : Ideal PUnit.{1}) = ⊤ := by
  ext r
  simp [Subsingleton.elim r (0 : PUnit.{1})]

private theorem punit_evaluation_kernels_comaximal :
    RingHom.ker (eval a) ⊔ RingHom.ker (eval b) = ⊤ := by
  apply (ker_eval_sup_ker_eval_eq_top_iff a b).mpr
  apply (Ideal.eq_top_iff_one _).mpr
  have h : (1 : PUnit.{1}) = 0 := Subsingleton.elim _ _
  rw [h]
  exact Ideal.zero_mem _

end TrivialCoefficientRing

section ResidueRingNilpotentDifference

local notation "a" => (fun _ : PUnit.{1} => (0 : ZMod 4))
local notation "b" => (fun _ : PUnit.{1} => (2 : ZMod 4))

private theorem zmod_four_difference_nonzero_square_zero :
    a PUnit.unit - b PUnit.unit ≠ 0 ∧ (a PUnit.unit - b PUnit.unit) ^ 2 = 0 := by
  constructor <;> decide

private theorem zmod_four_evaluation_kernels_not_comaximal :
    RingHom.ker (eval a) ⊔ RingHom.ker (eval b) ≠ ⊤ := by
  have h : ¬ IsUnit (2 : ZMod 4) := by
    exact fun h => (by decide : ¬ Nat.Coprime 2 4)
      ((ZMod.isUnit_iff_coprime 2 4).mp h)
  intro hsum
  have htop := (ker_eval_sup_ker_eval_eq_top_iff a b).mp hsum
  rw [Set.range_const] at htop
  have hunit : IsUnit ((0 : ZMod 4) - 2) :=
    (Ideal.span_singleton_eq_top (α := ZMod 4)).mp htop
  exact h (by simpa only [zero_sub, IsUnit.neg_iff] using hunit)

end ResidueRingNilpotentDifference

section JointIntegerSeparation

local notation "a" => (fun _ : Bool => (0 : ℤ))
local notation "b" => (fun i : Bool => match i with | false => (2 : ℤ) | true => 3)

private theorem integer_coordinate_differences_not_units (i : Bool) :
    ¬ IsUnit (a i - b i) := by
  cases i <;> norm_num [Int.isUnit_iff]

private theorem integer_joint_differences_comaximal :
    RingHom.ker (eval a) ⊔ RingHom.ker (eval b) = ⊤ := by
  apply (ker_eval_sup_ker_eval_eq_top_iff a b).mpr
  have hrange :
      Set.range (fun i : Bool => a i - b i) =
        ({(-2 : ℤ)} ∪ {(-3 : ℤ)}) := by
    apply Set.ext
    intro z
    simp only [Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      cases i
      · exact Or.inl (by decide)
      · exact Or.inr (by decide)
    · rintro (rfl | rfl)
      · exact ⟨false, by decide⟩
      · exact ⟨true, by decide⟩
  rw [hrange, Ideal.span_union]
  exact (Ideal.sup_eq_top_iff_isCoprime (-2 : ℤ) (-3)).mpr ⟨1, -1, by decide⟩

end JointIntegerSeparation

private theorem raised_variables_kernel_image :
    Ideal.map (eval (fun _ : ULift.{w + 1} Unit => (0 : ℤ)))
        (RingHom.ker (eval (fun _ : ULift.{w + 1} Unit => (1 : ℤ)))) =
      Ideal.span (Set.range (fun _ : ULift.{w + 1} Unit =>
        (0 : ℤ) - 1)) :=
  map_ker_eval_eq_span_sub
    (fun _ : ULift.{w + 1} Unit => (0 : ℤ))
    (fun _ : ULift.{w + 1} Unit => (1 : ℤ))

private theorem raised_coefficients_kernel_sum :
    RingHom.ker (eval (fun _ : Unit => (0 : ULift.{w + 1} ℤ))) ⊔
        RingHom.ker (eval (fun _ : Unit => (2 : ULift.{w + 1} ℤ))) =
      Ideal.comap (eval (fun _ : Unit => (0 : ULift.{w + 1} ℤ)))
        (Ideal.span (Set.range (fun _ : Unit => (0 : ULift.{w + 1} ℤ) - 2))) :=
  ker_eval_sup_ker_eval_eq_comap
    (fun _ : Unit => (0 : ULift.{w + 1} ℤ))
    (fun _ : Unit => (2 : ULift.{w + 1} ℤ))
