/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.EvaluationIdeal
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Degree-controlled finite interpolation

Over a commutative ring, finitely many polynomial points admit arbitrary prescribed
values with total degree at most the number of points minus one, provided the
coordinate differences of each pair span the unit ideal. Neither the variable type
nor the ambient label type is required to be finite.

The proof constructs affine polynomials separating pairs of points. When a point
is added, a product of these polynomials corrects its value without changing the
values at the preceding points. The empty selection is represented by zero.

## References

The finite coefficient extraction uses Mathlib's
`Finsupp.mem_span_range_iff_exists_finsupp`, and the degree estimates use Mathlib's
multivariate total-degree API. The coordinate-difference hypothesis is the
comaximality criterion `MvPolynomial.ker_eval_sup_ker_eval_eq_top_iff`.
-/

@[expose] public section

namespace MvPolynomial

universe uR uσ uι

variable {R : Type uR} {σ : Type uσ} [CommRing R]

/-- A unit ideal of coordinate differences gives an affine polynomial with values
one and zero at the two points. -/
private theorem exists_affine_separator (a b : σ → R)
    (h : Ideal.span (Set.range (fun x : σ => a x - b x)) = ⊤) :
    ∃ p : MvPolynomial σ R,
      eval a p = 1 ∧ eval b p = 0 ∧ p.totalDegree ≤ 1 := by
  classical
  have h1 : (1 : R) ∈ Submodule.span R (Set.range (fun x : σ => a x - b x)) :=
    (Ideal.eq_top_iff_one _).mp h
  obtain ⟨c, hc₀⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  have hc : (∑ x ∈ c.support, c x * (a x - b x)) = 1 := by
    simpa only [Finsupp.sum, smul_eq_mul] using hc₀
  have hX (x : σ) : (X x : MvPolynomial σ R).totalDegree ≤ 1 := by
    simpa [MvPolynomial.X] using
      (totalDegree_monomial_le (Finsupp.single x 1) (1 : R))
  refine ⟨∑ x ∈ c.support, C (c x) * (X x - C (b x)), ?_, ?_, ?_⟩
  · simpa only [map_sum, map_mul, map_sub, eval_C, eval_X] using hc
  · simp only [map_sum, map_mul, map_sub, eval_C, eval_X, sub_self, mul_zero,
      Finset.sum_const_zero]
  · apply totalDegree_finsetSum_le
    intro x _hx
    calc
      (C (c x) * (X x - C (b x))).totalDegree ≤
          (C (c x) : MvPolynomial σ R).totalDegree + (X x - C (b x)).totalDegree :=
        totalDegree_mul _ _
      _ = (X x - C (b x) : MvPolynomial σ R).totalDegree := by
        rw [totalDegree_C, zero_add]
      _ ≤ (X x : MvPolynomial σ R).totalDegree := totalDegree_sub_C_le _ _
      _ ≤ 1 := hX x

/-- Prescribed values on a finite selection of polynomial points over a
commutative ring are attained with total degree at most `s.card - 1` when the
coordinate differences of each distinct pair span the unit ideal.

The variable and ambient label types may be infinite. For an empty selection the
bound is zero. This is an existence statement, with no uniqueness assertion. -/
theorem exists_eval_eq_totalDegree_le_of_pairwise_span_eq_top
    {ι : Type uι} (s : Finset ι) (a : ι → σ → R) (v : ι → R)
    (h : Set.Pairwise (↑s : Set ι) (fun i j =>
      Ideal.span (Set.range (fun x : σ => a i x - a j x)) = ⊤)) :
    ∃ p : MvPolynomial σ R,
      (∀ i ∈ s, eval (a i) p = v i) ∧ p.totalDegree ≤ s.card - 1 := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _h
      exact ⟨0, by simp, by simp⟩
  | @insert i s hi ih =>
      intro h
      have hs : Set.Pairwise (↑s : Set ι) (fun j k =>
          Ideal.span (Set.range (fun x : σ => a j x - a k x)) = ⊤) := by
        intro j hj k hk hjk
        exact h (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
      obtain ⟨p, hp, hdeg⟩ := ih hs
      have hsep : ∀ j : ι, ∃ q : MvPolynomial σ R,
          j ∈ s → eval (a i) q = 1 ∧ eval (a j) q = 0 ∧ q.totalDegree ≤ 1 := by
        intro j
        by_cases hj : j ∈ s
        · have hij : i ≠ j := by
            intro hij
            subst j
            exact hi hj
          obtain ⟨q, hq⟩ := exists_affine_separator (a i) (a j)
            (h (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj) hij)
          exact ⟨q, fun _ => hq⟩
        · exact ⟨0, fun hj' => (hj hj').elim⟩
      let q : ι → MvPolynomial σ R := fun j => Classical.choose (hsep j)
      have hq (j : ι) (hj : j ∈ s) :
          eval (a i) (q j) = 1 ∧ eval (a j) (q j) = 0 ∧ (q j).totalDegree ≤ 1 :=
        Classical.choose_spec (hsep j) hj
      let B : MvPolynomial σ R := ∏ j ∈ s, q j
      have hBnew : eval (a i) B = 1 := by
        dsimp only [B]
        rw [map_prod]
        exact Finset.prod_eq_one (fun j hj => (hq j hj).1)
      have hBold (j : ι) (hj : j ∈ s) : eval (a j) B = 0 := by
        dsimp only [B]
        rw [map_prod]
        exact Finset.prod_eq_zero hj (hq j hj).2.1
      have hBdeg : B.totalDegree ≤ s.card := by
        calc
          B.totalDegree ≤ ∑ j ∈ s, (q j).totalDegree := totalDegree_finsetProd _ _
          _ ≤ ∑ j ∈ s, 1 := Finset.sum_le_sum (fun j hj => (hq j hj).2.2)
          _ = s.card := by simp
      refine ⟨p + C (v i - eval (a i) p) * B, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [map_add, map_mul, eval_C, hBnew, mul_one, add_comm, sub_add_cancel]
        · rw [map_add, map_mul, eval_C, hBold j hj, mul_zero, add_zero, hp j hj]
      · rw [Finset.card_insert_of_notMem hi, Nat.add_sub_cancel]
        apply (totalDegree_add _ _).trans
        apply max_le
        · exact hdeg.trans (Nat.sub_le _ _)
        · calc
            (C (v i - eval (a i) p) * B).totalDegree ≤
                (C (v i - eval (a i) p) : MvPolynomial σ R).totalDegree +
                  B.totalDegree := totalDegree_mul _ _
            _ = B.totalDegree := by rw [totalDegree_C, zero_add]
            _ ≤ s.card := hBdeg

end MvPolynomial
