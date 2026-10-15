/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.LagrangeComparison
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Degree-controlled finite evaluation

The coordinate differences of each pair of selected points are required to
span the unit ideal. The evaluation-ideal interface identifies this condition
with comaximality of the corresponding evaluation kernels.

A three-point integer example uses two jointly generating, nonunit coordinate
differences and infinitely many ambient variables and labels. Its prescribed
values are attained by a quadratic polynomial. Empty and singleton selections
are realized by zero and constant polynomials, respectively.

The evaluation and total-degree operations are Mathlib's canonical ones.
The single-variable comparison proposition uses Mathlib's `uniqueAlgEquiv` and
`Lagrange.interpolate`. Its rational example has nodes `0, 1` and polynomial `X`;
the empty case uses zero.
-/

open MvPolynomial

universe uR uσ uι

/-- Finite evaluation with the cardinality-minus-one total-degree bound. -/
private def HasDegreeControlledEvaluation
    {R : Type uR} {σ : Type uσ} {ι : Type uι} [CommRing R]
    (s : Finset ι) (a : ι → σ → R) (v : ι → R) : Prop :=
  Set.Pairwise (↑s : Set ι) (fun i j =>
    Ideal.span (Set.range (fun x : σ => a i x - a j x)) = ⊤) →
  ∃ p : MvPolynomial σ R,
    (∀ i ∈ s, eval (a i) p = v i) ∧ p.totalDegree ≤ s.card - 1

/-- Coordinates outside the first two, and unselected labels, are zero. -/
private def integerPoints : ℕ → ℕ → ℤ
  | 1, 0 => 2
  | 1, 1 => 3
  | 2, 0 => 3
  | 2, 1 => 2
  | _, _ => 0

private def integerTargets : ℕ → ℤ
  | 2 => 1
  | _ => 0

private noncomputable def integerPolynomial : MvPolynomial ℕ ℤ :=
  (X 0 - X 1) * (X 0 - C 2)

/-- Signed differences of the first two generators give the Bezout certificates. -/
private theorem integerPoints_pairwise :
    Set.Pairwise (↑({0, 1, 2} : Finset ℕ) : Set ℕ) (fun i j =>
      Ideal.span (Set.range (fun x : ℕ => integerPoints i x - integerPoints j x)) = ⊤) := by
  intro i hi j hj hij
  have h0 : integerPoints i 0 - integerPoints j 0 ∈
      Ideal.span (Set.range (fun x : ℕ => integerPoints i x - integerPoints j x)) :=
    Ideal.subset_span (Set.mem_range_self 0)
  have h1 : integerPoints i 1 - integerPoints j 1 ∈
      Ideal.span (Set.range (fun x : ℕ => integerPoints i x - integerPoints j x)) :=
    Ideal.subset_span (Set.mem_range_self 1)
  have h01 := (Ideal.span _).sub_mem h0 h1
  have h10 := (Ideal.span _).sub_mem h1 h0
  apply (Ideal.eq_top_iff_one _).2
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals first
    | exact (hij rfl).elim
    | simpa [integerPoints] using h01
    | simpa [integerPoints] using h10
    | simpa [integerPoints] using h0

/-- The explicit quadratic realizes the selected integer values with degree at most two. -/
private theorem integer_degreeControlledEvaluation :
    HasDegreeControlledEvaluation ({0, 1, 2} : Finset ℕ) integerPoints integerTargets := by
  intro _h
  refine ⟨integerPolynomial, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      norm_num [integerPolynomial, integerPoints, integerTargets]
  · have hleft : (X 0 - X 1 : MvPolynomial ℕ ℤ).totalDegree ≤ 1 := by
      rw [sub_eq_add_neg]
      apply (totalDegree_add _ _).trans
      apply max_le
      · simp
      · exact (totalDegree_neg (X 1 : MvPolynomial ℕ ℤ)).le.trans
          (totalDegree_X (R := ℤ) 1).le
    have hright : (X 0 - C 2 : MvPolynomial ℕ ℤ).totalDegree ≤ 1 := by
      have h := totalDegree_add (X 0 : MvPolynomial ℕ ℤ) (C (-2))
      rw [totalDegree_X, totalDegree_C] at h
      simpa [sub_eq_add_neg] using h
    calc
      integerPolynomial.totalDegree ≤
          (X 0 - X 1 : MvPolynomial ℕ ℤ).totalDegree +
            (X 0 - C 2 : MvPolynomial ℕ ℤ).totalDegree := totalDegree_mul _ _
      _ ≤ 1 + 1 := Nat.add_le_add hleft hright
      _ = ({0, 1, 2} : Finset ℕ).card - 1 := by norm_num

/-- Both the actual premise and its degree-controlled evaluation conclusion hold. -/
example : ∃ p : MvPolynomial ℕ ℤ,
    (∀ i ∈ ({0, 1, 2} : Finset ℕ), eval (integerPoints i) p = integerTargets i) ∧
      p.totalDegree ≤ ({0, 1, 2} : Finset ℕ).card - 1 :=
  MvPolynomial.exists_eval_eq_totalDegree_le_of_pairwise_span_eq_top
    ({0, 1, 2} : Finset ℕ) integerPoints integerTargets integerPoints_pairwise

private theorem empty_degreeControlledEvaluation
    {R : Type uR} {σ : Type uσ} {ι : Type uι} [CommRing R]
    (a : ι → σ → R) (v : ι → R) :
    HasDegreeControlledEvaluation (∅ : Finset ι) a v := by
  intro _h
  exact ⟨0, by simp, by simp⟩

private theorem singleton_degreeControlledEvaluation
    {R : Type uR} {σ : Type uσ} {ι : Type uι} [CommRing R]
    (a : ι → σ → R) (v : ι → R) (i : ι) :
    HasDegreeControlledEvaluation ({i} : Finset ι) a v := by
  intro _h
  refine ⟨C (v i), ?_, ?_⟩
  · intro j hj
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    simp
  · simp

/-- A strict total-degree bound and prescribed values determine Mathlib's
interpolant under the canonical single-variable equivalence. -/
private def HasLagrangeAgreement
    {F : Type uR} {σ : Type uσ} {ι : Type uι} [Field F] [Unique σ]
    (s : Finset ι) (a v : ι → F) (p : MvPolynomial σ F) : Prop :=
  Set.InjOn a (↑s : Set ι) →
  p.totalDegree < s.card →
  (∀ i ∈ s, eval (fun _ : σ => a i) p = v i) →
  uniqueAlgEquiv F σ p =
    @Lagrange.interpolate F _ ι (Classical.decEq ι) s a v

/-- Identity data at two rational nodes are realized by the variable polynomial.
A witness from commutative-ring interpolation has the same univariate interpolant. -/
private theorem rational_lagrangeAgreement :
    Set.InjOn (fun i : ℚ => i) (↑({0, 1} : Finset ℚ) : Set ℚ) ∧
    (X () : MvPolynomial Unit ℚ).totalDegree = 1 ∧
    (X () : MvPolynomial Unit ℚ).totalDegree < ({0, 1} : Finset ℚ).card ∧
    (∀ i ∈ ({0, 1} : Finset ℚ),
      eval (fun _ : Unit => i) (X () : MvPolynomial Unit ℚ) = i) ∧
    HasLagrangeAgreement ({0, 1} : Finset ℚ) (fun i => i) (fun i => i)
      (X () : MvPolynomial Unit ℚ) ∧
    ∃ p : MvPolynomial Unit ℚ,
      (∀ i ∈ ({0, 1} : Finset ℚ), eval (fun _ : Unit => i) p = i) ∧
      p.totalDegree ≤ ({0, 1} : Finset ℚ).card - 1 ∧
      uniqueAlgEquiv ℚ Unit p =
        @Lagrange.interpolate ℚ _ ℚ (Classical.decEq ℚ)
          ({0, 1} : Finset ℚ) (fun i => i) (fun i => i) := by
  classical
  refine ⟨(fun _ _ _ _ h => h), totalDegree_X (), ?_, ?_, ?_, ?_⟩
  · norm_num
  · intro i hi
    simp
  · exact uniqueAlgEquiv_eq_interpolate_of_eval_eq
      ({0, 1} : Finset ℚ) (fun i => i) (fun i => i)
      (X () : MvPolynomial Unit ℚ)
  · have hspan : Set.Pairwise (↑({0, 1} : Finset ℚ) : Set ℚ) (fun i j =>
        Ideal.span (Set.range (fun _ : Unit => i - j)) = ⊤) := by
      intro i _hi j _hj hij
      refine Ideal.eq_top_of_isUnit_mem _ (x := i - j)
        (Ideal.subset_span ⟨(), rfl⟩) ?_
      exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hij)
    obtain ⟨p, hp, hdeg⟩ := exists_eval_eq_totalDegree_le_of_pairwise_span_eq_top
      ({0, 1} : Finset ℚ) (fun i (_ : Unit) => i) (fun i => i) hspan
    refine ⟨p, hp, hdeg, ?_⟩
    exact uniqueAlgEquiv_eq_interpolate_of_eval_eq_of_totalDegree_le
      ({0, 1} : Finset ℚ) (fun i => i) (fun i => i) p (by simp)
      (fun _ _ _ _ h => h) hdeg hp

/-- For an empty selection, zero agrees with Mathlib's zero interpolant. -/
private theorem empty_lagrangeAgreement
    {F : Type uR} {σ : Type uσ} {ι : Type uι} [Field F] [Unique σ]
    (a v : ι → F) :
    uniqueAlgEquiv F σ (0 : MvPolynomial σ F) =
      @Lagrange.interpolate F _ ι (Classical.decEq ι) ∅ a v := by
  classical
  rw [map_zero, Lagrange.interpolate_empty]
