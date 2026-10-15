/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.EvaluationIdeal
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Images of evaluation at two tuples

Integer parity and joint generation illustrate the image criterion for a common
polynomial. Empty variables give the diagonal, and a subsingleton coefficient
ring admits its unique pair of values.
-/

open MvPolynomial

universe uR uσ

private theorem coordinate_value_pair
    {R : Type uR} {σ : Type uσ} [CommRing R] (a b : σ → R) (i : σ) :
    (a i, b i) ∈ Set.range ((eval a).prod (eval b)) := by
  apply (mem_range_eval_prod_iff a b (a i) (b i)).mpr
  exact Ideal.subset_span (Set.mem_range_self i)

section IntegerParity

local notation "a" => (fun _ : PUnit.{1} => (0 : ℤ))
local notation "b" => (fun _ : PUnit.{1} => (2 : ℤ))

private theorem integer_pair_iff_two_dvd (r s : ℤ) :
    (r, s) ∈ Set.range ((eval a).prod (eval b)) ↔ (2 : ℤ) ∣ r - s := by
  simpa only [Set.range_const, zero_sub, Ideal.mem_span_singleton, neg_dvd] using
    mem_range_eval_prod_iff a b r s

private theorem integer_zero_two_pair :
    (0, 2) ∈ Set.range ((eval a).prod (eval b)) := by
  refine ⟨X PUnit.unit, ?_⟩
  simp only [RingHom.prod_apply, eval_X]

private theorem integer_zero_one_not_pair :
    (0, 1) ∉ Set.range ((eval a).prod (eval b)) := by
  rw [integer_pair_iff_two_dvd]
  norm_num

private theorem integer_pair_of_difference (r s k : ℤ) (h : s - r = 2 * k) :
    (r, s) ∈ Set.range ((eval a).prod (eval b)) := by
  refine ⟨C r + C k * X PUnit.unit, ?_⟩
  simp only [RingHom.prod_apply]
  apply Prod.ext
  · simp
  · simp only [map_add, map_mul, eval_C, eval_X]
    calc
      r + k * 2 = r + (s - r) := by rw [h, mul_comm k 2]
      _ = s := by ring

end IntegerParity

section JointIntegerDifferences

local notation "a" => (fun _ : Bool => (0 : ℤ))
local notation "b" => (fun i : Bool => match i with | false => (2 : ℤ) | true => 3)

private theorem integer_coordinate_differences_nonunits (i : Bool) :
    ¬ IsUnit (a i - b i) := by
  cases i <;> norm_num [Int.isUnit_iff]

private theorem integer_joint_difference_ideal :
    Ideal.span (Set.range (fun i : Bool => a i - b i)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h2 : (-2 : ℤ) ∈ Ideal.span (Set.range (fun i : Bool => a i - b i)) := by
    apply Ideal.subset_span
    exact ⟨false, by norm_num⟩
  have h3 : (-3 : ℤ) ∈ Ideal.span (Set.range (fun i : Bool => a i - b i)) := by
    apply Ideal.subset_span
    exact ⟨true, by norm_num⟩
  have h := Ideal.sub_mem _ h2 h3
  have hsum : (-2 : ℤ) - (-3) = 1 := by norm_num
  rw [hsum] at h
  exact h

private theorem integer_joint_pair (r s : ℤ) :
    (r, s) ∈ Set.range ((eval a).prod (eval b)) ∧
      r - s ∈ Ideal.span (Set.range (fun i : Bool => a i - b i)) := by
  have hp : (r, s) ∈ Set.range ((eval a).prod (eval b)) := by
    refine ⟨C r + C (s - r) * (-X false + X true), ?_⟩
    simp only [RingHom.prod_apply]
    apply Prod.ext <;> simp <;> ring
  exact ⟨hp, (mem_range_eval_prod_iff a b r s).mp hp⟩

end JointIntegerDifferences

private theorem empty_pair_iff
    {R : Type uR} [CommRing R] (r s : R) :
    (r, s) ∈ Set.range
      ((eval (Empty.elim : Empty → R)).prod (eval (Empty.elim : Empty → R))) ↔
        r = s := by
  rw [mem_range_eval_prod_iff]
  rw [show Set.range (fun i : Empty => (Empty.elim i : R) - Empty.elim i) = ∅ from
    Set.range_eq_empty_iff.mpr ⟨Empty.elim⟩, Ideal.span_empty]
  simp only [Submodule.mem_bot, sub_eq_zero]

private theorem empty_diagonal_pair
    {R : Type uR} [CommRing R] (r : R) :
    (r, r) ∈ Set.range
      ((eval (Empty.elim : Empty → R)).prod (eval (Empty.elim : Empty → R))) := by
  refine ⟨C r, ?_⟩
  simp only [RingHom.prod_apply, eval_C]

private theorem subsingleton_pair
    {R : Type uR} {σ : Type uσ} [CommRing R] [Subsingleton R]
    (a b : σ → R) (r s : R) :
    (r, s) ∈ Set.range ((eval a).prod (eval b)) ∧
      r - s ∈ Ideal.span (Set.range (fun i : σ => a i - b i)) := by
  have hp : (r, s) ∈ Set.range ((eval a).prod (eval b)) :=
    ⟨0, Subsingleton.elim _ _⟩
  exact ⟨hp, (mem_range_eval_prod_iff a b r s).mp hp⟩
