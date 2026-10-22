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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two-point and finite-family evaluation over commutative rings

Applications of the evaluation-kernel image, sum and comaximality lemmas.
The integer and residue-ring examples distinguish unequal points, unit
coordinate differences, and differences that jointly generate the unit ideal.
The empty-variable and one-element-ring examples include degenerate cases.

## Finite simultaneous evaluation

The proposition below relates surjectivity of simultaneous polynomial evaluation
at finitely many indexed points to the unit-ideal condition for every pair of
distinct indices. The coefficient ring is any commutative ring, and the variable
type is arbitrary. In particular, different indices may designate the same point.

Three integer points in infinitely many variables admit an explicit linear
interpolant. A separate application obtains their simultaneous-evaluation
surjectivity from `MvPolynomial.surjective_eval_family_iff` and their pairwise
coordinate-difference ideals. The integer points `0, 2` and `0, 1, 2`
distinguish the all-pairs condition from unequal-point and adjacent-pair conditions.
Empty and singleton index types, a one-element coefficient ring, repeated points, and
empty variables supply boundary examples.

## Limitations

The private proposition records the statement; the general equivalence is
supplied by `MvPolynomial.surjective_eval_family_iff`. The `0, 2`, `0, 1, 2`
chain and empty-variable negative examples prove failure of the ideal condition
only; their nonsurjectivity is not independently proved here.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Eval`, for polynomial evaluation,
  constants and variables.
* `MultivariatePolynomials.EvaluationIdeal`, for coordinate-difference ideals.
* `MultivariatePolynomialsTests.EvaluationIdealTwoPoints`, for integer
  nonunit differences and jointly generating coordinate differences.
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

section FiniteSimultaneousEvaluation

noncomputable section

/-- Surjectivity of finite simultaneous evaluation and its pairwise ideal criterion. -/
private def finiteEvaluationSurjectivityGoal
    {R : Type u} {σ : Type v} {ι : Type w}
    [CommRing R] (a : ι → σ → R) : Prop :=
  Function.Surjective
    (fun p : MvPolynomial σ R => fun i : ι => MvPolynomial.eval (a i) p) ↔
    Pairwise (fun i j : ι =>
      Ideal.span (Set.range (fun s : σ => a i s - a j s)) = ⊤)

private def integerSimplexPoints (i : Fin 3) (n : ℕ) : ℤ :=
  if i = 1 ∧ n = 0 then 1 else if i = 2 ∧ n = 1 then 1 else 0

private def integerSimplexInterpolant (y : Fin 3 → ℤ) : MvPolynomial ℕ ℤ :=
  C (y 0) + C (y 1 - y 0) * X 0 + C (y 2 - y 0) * X 1

private theorem integerSimplexInterpolant_eval (y : Fin 3 → ℤ) (i : Fin 3) :
    eval (integerSimplexPoints i) (integerSimplexInterpolant y) = y i := by
  fin_cases i <;> simp [integerSimplexInterpolant, integerSimplexPoints]

private theorem integerSimplex_evaluation_surjective :
    Function.Surjective
      (fun p : MvPolynomial ℕ ℤ => fun i : Fin 3 => eval (integerSimplexPoints i) p) := by
  intro y
  refine ⟨integerSimplexInterpolant y, ?_⟩
  funext i
  exact integerSimplexInterpolant_eval y i

private theorem integerSimplex_pairwise_span_eq_top :
    Pairwise (fun i j : Fin 3 =>
      Ideal.span (Set.range (fun n : ℕ =>
        integerSimplexPoints i n - integerSimplexPoints j n)) = ⊤) := by
  intro i j hij
  have hw : ∃ n : ℕ,
      integerSimplexPoints i n - integerSimplexPoints j n = 1 ∨
      integerSimplexPoints i n - integerSimplexPoints j n = -1 := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ⟨0, Or.inr (by norm_num [integerSimplexPoints])⟩
    · exact ⟨1, Or.inr (by norm_num [integerSimplexPoints])⟩
    · exact ⟨0, Or.inl (by norm_num [integerSimplexPoints])⟩
    · exact (hij rfl).elim
    · exact ⟨0, Or.inl (by norm_num [integerSimplexPoints])⟩
    · exact ⟨1, Or.inl (by norm_num [integerSimplexPoints])⟩
    · exact ⟨0, Or.inr (by norm_num [integerSimplexPoints])⟩
    · exact (hij rfl).elim
  obtain ⟨n, hn⟩ := hw
  apply (Ideal.eq_top_iff_one _).mpr
  have hgen : integerSimplexPoints i n - integerSimplexPoints j n ∈
      Ideal.span (Set.range (fun n : ℕ =>
        integerSimplexPoints i n - integerSimplexPoints j n)) :=
    Ideal.subset_span (Set.mem_range_self n)
  rcases hn with hn | hn
  · simpa only [hn] using hgen
  · simpa only [hn, neg_neg] using Submodule.neg_mem _ hgen

private theorem integerSimplex_evaluation_surjective_of_pairwise :
    Function.Surjective
      (fun p : MvPolynomial ℕ ℤ => fun i : Fin 3 => eval (integerSimplexPoints i) p) :=
  (surjective_eval_family_iff integerSimplexPoints).mpr
    integerSimplex_pairwise_span_eq_top

private theorem integerSimplex_nonconstant_values :
    eval (integerSimplexPoints 0)
        (integerSimplexInterpolant (fun i => (i.val : ℤ))) = 0 ∧
      eval (integerSimplexPoints 1)
        (integerSimplexInterpolant (fun i => (i.val : ℤ))) = 1 ∧
      eval (integerSimplexPoints 2)
        (integerSimplexInterpolant (fun i => (i.val : ℤ))) = 2 := by
  norm_num [integerSimplexInterpolant_eval]

private theorem integer_neg_two_span_ne_top : Ideal.span {(-2 : ℤ)} ≠ ⊤ :=
  Ideal.span_singleton_ne_top (by norm_num [Int.isUnit_iff])

private def integerParityPoints (i : Fin 2) (_ : PUnit.{1}) : ℤ :=
  if i = 0 then 0 else 2

private theorem integerParity_not_pairwise_span_eq_top :
    ¬ Pairwise (fun i j : Fin 2 =>
      Ideal.span (Set.range (fun s : PUnit.{1} =>
        integerParityPoints i s - integerParityPoints j s)) = ⊤) := by
  intro h
  apply integer_neg_two_span_ne_top
  simpa [integerParityPoints, Set.range_const] using
    h (by decide : (0 : Fin 2) ≠ 1)

private def integerChainPoints (i : Fin 3) (_ : PUnit.{1}) : ℤ := (i.val : ℤ)

private theorem integerChain_adjacent_spans_eq_top :
    Ideal.span (Set.range (fun s : PUnit.{1} =>
      integerChainPoints 0 s - integerChainPoints 1 s)) = ⊤ ∧
      Ideal.span (Set.range (fun s : PUnit.{1} =>
        integerChainPoints 1 s - integerChainPoints 2 s)) = ⊤ := by
  constructor <;>
    norm_num [integerChainPoints, Set.range_const, Ideal.span_singleton_eq_top,
      Int.isUnit_iff]

private theorem integerChain_not_pairwise_span_eq_top :
    ¬ Pairwise (fun i j : Fin 3 =>
      Ideal.span (Set.range (fun s : PUnit.{1} =>
        integerChainPoints i s - integerChainPoints j s)) = ⊤) := by
  intro h
  apply integer_neg_two_span_ne_top
  simpa [integerChainPoints, Set.range_const] using
    h (by decide : (0 : Fin 3) ≠ 2)

private theorem empty_index_evaluation
    {R : Type u} {σ : Type v} [CommRing R] (a : Empty → σ → R) :
    Function.Surjective
      (fun p : MvPolynomial σ R => fun i : Empty => eval (a i) p) ∧
      Pairwise (fun i j : Empty =>
        Ideal.span (Set.range (fun s : σ => a i s - a j s)) = ⊤) := by
  constructor
  · intro y
    refine ⟨0, ?_⟩
    funext i
    exact Empty.elim i
  · intro i
    exact Empty.elim i

private theorem singleton_index_evaluation
    {R : Type u} {σ : Type v} [CommRing R] (a : PUnit.{1} → σ → R) :
    Function.Surjective
      (fun p : MvPolynomial σ R => fun i : PUnit.{1} => eval (a i) p) ∧
      Pairwise (fun i j : PUnit.{1} =>
        Ideal.span (Set.range (fun s : σ => a i s - a j s)) = ⊤) := by
  constructor
  · intro y
    refine ⟨C (y PUnit.unit), ?_⟩
    funext i
    cases i
    exact eval_C _
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

private theorem zero_ring_evaluation
    {σ : Type v} {ι : Type w} (a : ι → σ → PUnit.{1}) :
    Function.Surjective
      (fun p : MvPolynomial σ PUnit.{1} => fun i : ι => eval (a i) p) ∧
      Pairwise (fun i j : ι =>
        Ideal.span (Set.range (fun s : σ => a i s - a j s)) = ⊤) := by
  constructor
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro i j _
    apply (Ideal.eq_top_iff_one _).mpr
    rw [Subsingleton.elim (1 : PUnit.{1}) 0]
    exact Ideal.zero_mem _

private def integerRepeatedPoints (_ : Fin 2) (_ : ℕ) : ℤ := 0

private theorem integerRepeated_evaluation_obstruction :
    ¬ Function.Surjective
      (fun p : MvPolynomial ℕ ℤ => fun i : Fin 2 => eval (integerRepeatedPoints i) p) ∧
      ¬ Pairwise (fun i j : Fin 2 =>
        Ideal.span (Set.range (fun n : ℕ =>
          integerRepeatedPoints i n - integerRepeatedPoints j n)) = ⊤) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h (fun i : Fin 2 => if i = 0 then 0 else 1)
    have h0 : eval (fun _ : ℕ => (0 : ℤ)) p = 0 := by
      have hp0 := congrFun hp (0 : Fin 2)
      change eval (fun _ : ℕ => (0 : ℤ)) p =
        (if (0 : Fin 2) = 0 then 0 else 1) at hp0
      simpa only [ite_true] using hp0
    have h1 : eval (fun _ : ℕ => (0 : ℤ)) p = 1 := by
      have hp1 := congrFun hp (1 : Fin 2)
      change eval (fun _ : ℕ => (0 : ℤ)) p =
        (if (1 : Fin 2) = 0 then 0 else 1) at hp1
      simpa only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] using hp1
    exact zero_ne_one (h0.symm.trans h1)
  · intro h
    have ht := h (by decide : (0 : Fin 2) ≠ 1)
    have hb : (⊥ : Ideal ℤ) = ⊤ := by
      simp [integerRepeatedPoints, Set.range_const] at ht
    exact bot_ne_top hb

private theorem empty_variables_not_pairwise_span_eq_top (a : Fin 2 → Empty → ℤ) :
    ¬ Pairwise (fun i j : Fin 2 =>
      Ideal.span (Set.range (fun s : Empty => a i s - a j s)) = ⊤) := by
  intro h
  have ht := h (by decide : (0 : Fin 2) ≠ 1)
  have hrange : Set.range (fun s : Empty => a 0 s - a 1 s) = ∅ :=
    Set.range_eq_empty_iff.mpr ⟨Empty.elim⟩
  change Ideal.span (Set.range (fun s : Empty => a 0 s - a 1 s)) = ⊤ at ht
  rw [hrange, Ideal.span_empty] at ht
  exact bot_ne_top ht

end

end FiniteSimultaneousEvaluation

/-- The stock quotient maps modulo two and three are jointly surjective. -/
private theorem integer_pair_quotient_surjective :
    Function.Surjective (RingHom.pi fun b : Bool =>
      Ideal.Quotient.mk (Ideal.span ({cond b (3 : ℤ) 2} : Set ℤ))) := by
  apply (Ideal.pi_quotient_mk_surjective_iff _).mpr
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact (Ideal.sup_eq_top_iff_isCoprime (2 : ℤ) 3).mpr ⟨-1, 1, by decide⟩
  · exact (Ideal.sup_eq_top_iff_isCoprime (3 : ℤ) 2).mpr ⟨1, -1, by decide⟩
  · exact (hij rfl).elim

/-- Repeating the zero ideal at distinct indices obstructs joint surjectivity. -/
private theorem repeated_zero_ideal_quotient_not_surjective :
    ¬ Function.Surjective (RingHom.pi fun _ : Bool => Ideal.Quotient.mk (⊥ : Ideal ℤ)) := by
  intro h
  have ht : (⊥ : Ideal ℤ) ⊔ ⊥ = ⊤ :=
    Ideal.pairwise_sup_eq_top_of_surjective_pi_quotient_mk
      (fun _ : Bool => (⊥ : Ideal ℤ)) h (by decide : false ≠ true)
  exact bot_ne_top (by simpa only [sup_idem] using ht)
