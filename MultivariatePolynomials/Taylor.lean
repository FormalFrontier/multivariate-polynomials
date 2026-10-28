/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.Ring

/-!
# Finite-support first-order polynomial evaluation

For a coefficient homomorphism into a commutative ring, the difference of two
polynomial values is a finite linear combination of the coordinate differences.
The coefficients vanish outside the polynomial's variables and are congruent to
its evaluated partial derivatives at any point congruent to both arguments.

The one-point specialization gives a remainder in the square of the ideal of
coordinate differences, and hence an exact differential formula for square-zero
ideals. All sums use the variables of the original polynomial, even if the
coefficient homomorphism kills some coefficients.

For a univariate polynomial `q`, use the standard one-variable equivalence with
variable type `PUnit`, the identity coefficient map, constant points `x` and
`x + y`, and the principal ideal `(y)`. The finite differential is `q'(x) * y`
(and is zero for empty variable support), while `(y) ^ 2 = (y ^ 2)`. Thus the
ideal-square remainder specializes to the quadratic remainder of
`Polynomial.exists_mul_sq_add_linear_part_eq_eval_add`; when `y ^ 2 = 0`, the
square-zero formula is `Polynomial.eval_add_of_sq_eq_zero`. Univariate clients
can use these stock results directly.

## References

The coefficient induction generalizes the formalization in
`AdicModules.MvPolynomial.Jacobian` by Formal Frontier Agents: constants, addition,
and multiplication by a variable use the same coefficient construction. A
finitely supported witness and replacement of points outside the polynomial's
variables remove the finite-index restriction. For ordinary univariate
polynomials, see also `Polynomial.exists_mul_sq_add_linear_part_eq_eval_add` and
`Polynomial.eval_add_of_sq_eq_zero` in Mathlib.
-/

@[expose] public section

namespace MvPolynomial

open scoped BigOperators

universe uC uR uσ

variable {C : Type uC} {R : Type uR} {σ : Type uσ}
variable [CommSemiring C] [CommRing R]

/-- The coefficient induction with global congruence hypotheses. The witness is
finitely supported, but need not yet be supported on the variables of `p`. -/
private theorem exists_eval₂_sub_eq_linearCombination
    (I : Ideal R) (φ : C →+* R) (a b c : σ → R)
    (hb : ∀ i, b i - a i ∈ I) (hc : ∀ i, c i - a i ∈ I)
    (p : MvPolynomial σ C) :
    ∃ d : σ →₀ R,
      eval₂ φ b p - eval₂ φ c p =
        Finsupp.linearCombination R (fun j => b j - c j) d ∧
      ∀ j, d j - eval₂ φ a (pderiv j p) ∈ I := by
  classical
  have hca (q : MvPolynomial σ C) : eval₂ φ c q - eval₂ φ a q ∈ I := by
    apply Ideal.Quotient.eq.mp
    simpa only [eval₂_comp_left, Function.comp_def] using
      congrArg (fun x : σ → R ⧸ I => eval₂ ((Ideal.Quotient.mk I).comp φ) x q)
        (funext fun i => Ideal.Quotient.eq.mpr (hc i))
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · intro j
      simp
  | add p q hp hq =>
    obtain ⟨d, hd, hdj⟩ := hp
    obtain ⟨e, he, hej⟩ := hq
    refine ⟨d + e, ?_, ?_⟩
    · calc
        eval₂ φ b (p + q) - eval₂ φ c (p + q) =
            (eval₂ φ b p - eval₂ φ c p) + (eval₂ φ b q - eval₂ φ c q) := by
          simp only [eval₂_add]
          ring
        _ = Finsupp.linearCombination R (fun j => b j - c j) (d + e) := by
          rw [map_add, ← hd, ← he]
    · intro j
      convert I.add_mem (hdj j) (hej j) using 1
      simp only [Finsupp.add_apply, map_add, eval₂_add]
      ring
  | mul_X p i hp =>
    obtain ⟨d, hd, hdj⟩ := hp
    refine ⟨b i • d + Finsupp.single i (eval₂ φ c p), ?_, ?_⟩
    · calc
        eval₂ φ b (p * X i) - eval₂ φ c (p * X i) =
            b i * (eval₂ φ b p - eval₂ φ c p) + eval₂ φ c p * (b i - c i) := by
          simp only [eval₂_mul, eval₂_X]
          ring
        _ = b i * Finsupp.linearCombination R (fun j => b j - c j) d +
            eval₂ φ c p * (b i - c i) := by rw [hd]
        _ = Finsupp.linearCombination R (fun j => b j - c j)
            (b i • d + Finsupp.single i (eval₂ φ c p)) := by
          simp [smul_eq_mul]
    · intro j
      by_cases hji : j = i
      · subst j
        convert I.add_mem
          (I.add_mem (I.mul_mem_right (d i) (hb i)) (I.mul_mem_left (a i) (hdj i)))
          (hca p) using 1
        simp [smul_eq_mul]
        ring
      · convert I.add_mem (I.mul_mem_right (d j) (hb i))
          (I.mul_mem_left (a i) (hdj j)) using 1
        simp [hji, Ne.symm hji, smul_eq_mul]
        ring

/-- Two-point polynomial evaluation as a sum over the original polynomial's
variables. The coefficients are exactly zero off that finite set and are
congruent to the evaluated partial derivatives at every coordinate.

The coefficient induction generalizes the two-point decomposition in
`AdicModules.MvPolynomial.Jacobian` by Formal Frontier Agents. -/
theorem exists_eval₂_sub_eq_sum
    (I : Ideal R) (φ : C →+* R) (a b c : σ → R) (p : MvPolynomial σ C)
    (hb : ∀ i ∈ p.vars, b i - a i ∈ I)
    (hc : ∀ i ∈ p.vars, c i - a i ∈ I) :
    ∃ d : σ → R,
      (∀ j, j ∉ p.vars → d j = 0) ∧
      eval₂ φ b p - eval₂ φ c p = p.vars.sum (fun j => d j * (b j - c j)) ∧
      ∀ j, d j - eval₂ φ a (pderiv j p) ∈ I := by
  classical
  let b' : σ → R := fun j => if j ∈ p.vars then b j else a j
  let c' : σ → R := fun j => if j ∈ p.vars then c j else a j
  have hb' (j) : b' j - a j ∈ I := by
    by_cases hj : j ∈ p.vars
    · simpa [b', hj] using hb j hj
    · simp [b', hj]
  have hc' (j) : c' j - a j ∈ I := by
    by_cases hj : j ∈ p.vars
    · simpa [c', hj] using hc j hj
    · simp [c', hj]
  have heb : eval₂ φ b' p = eval₂ φ b p :=
    eval₂Hom_congr' rfl (fun j hj _ => by simp [b', hj]) rfl
  have hec : eval₂ φ c' p = eval₂ φ c p :=
    eval₂Hom_congr' rfl (fun j hj _ => by simp [c', hj]) rfl
  obtain ⟨d, hd, hdj⟩ := exists_eval₂_sub_eq_linearCombination I φ a b' c' hb' hc' p
  have hsum : Finsupp.linearCombination R (fun j => b' j - c' j) d =
      p.vars.sum (fun j => d j * (b j - c j)) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      d.support.sum (fun j => d j • (b' j - c' j)) =
          (d.support ∪ p.vars).sum (fun j => d j • (b' j - c' j)) := by
        apply Finset.sum_subset Finset.subset_union_left
        intro j _ hj
        simp [Finsupp.notMem_support_iff.mp hj]
      _ = p.vars.sum (fun j => d j • (b' j - c' j)) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro j _ hj
        simp [b', c', hj]
      _ = p.vars.sum (fun j => d j * (b j - c j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [b', c', hj, smul_eq_mul]
  refine ⟨fun j => if j ∈ p.vars then d j else 0, ?_, ?_, ?_⟩
  · intro j hj
    simp [hj]
  · rw [← heb, ← hec, hd, hsum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [hj]
  · intro j
    by_cases hj : j ∈ p.vars
    · simpa [hj] using hdj j
    · simp [hj, pderiv_eq_zero_of_notMem_vars hj]

/-- The two-point error after subtracting the differential at `a` belongs to
`I * J` if both points differ from `a` by elements of `I`, and from each other
by elements of `J`, on the variables of the polynomial. -/
theorem eval₂_sub_eval₂_sub_sum_pderiv_mem_mul
    (I J : Ideal R) (φ : C →+* R) (a b c : σ → R) (p : MvPolynomial σ C)
    (hb : ∀ i ∈ p.vars, b i - a i ∈ I)
    (hc : ∀ i ∈ p.vars, c i - a i ∈ I)
    (hbc : ∀ i ∈ p.vars, b i - c i ∈ J) :
    eval₂ φ b p - eval₂ φ c p -
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - c j)) ∈ I * J := by
  classical
  obtain ⟨d, _, hd, hdI⟩ := exists_eval₂_sub_eq_sum I φ a b c p hb hc
  rw [hd, ← Finset.sum_sub_distrib]
  apply (I * J).sum_mem
  intro j hj
  rw [← sub_mul]
  exact Ideal.mul_mem_mul (hdI j) (hbc j hj)

/-- When `I * J = ⊥`, the two-point evaluation difference is exactly the
finite differential at `a`, under the same support-local ideal hypotheses. -/
theorem eval₂_eq_eval₂_add_sum_pderiv_of_mul_eq_bot
    (I J : Ideal R) (hIJ : I * J = ⊥) (φ : C →+* R) (a b c : σ → R)
    (p : MvPolynomial σ C)
    (hb : ∀ i ∈ p.vars, b i - a i ∈ I)
    (hc : ∀ i ∈ p.vars, c i - a i ∈ I)
    (hbc : ∀ i ∈ p.vars, b i - c i ∈ J) :
    eval₂ φ b p = eval₂ φ c p +
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - c j)) := by
  have h := eval₂_sub_eval₂_sub_sum_pderiv_mem_mul I J φ a b c p hb hc hbc
  rw [hIJ, Ideal.mem_bot] at h
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp h)).trans (add_comm _ _)

/-- The error after subtracting the finite evaluated differential belongs to
`I ^ 2` when the coordinates differ by elements of `I` on `p.vars`. -/
theorem eval₂_sub_eval₂_sub_sum_pderiv_mem_sq
    (I : Ideal R) (φ : C →+* R) (a b : σ → R) (p : MvPolynomial σ C)
    (hb : ∀ i ∈ p.vars, b i - a i ∈ I) :
    eval₂ φ b p - eval₂ φ a p -
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j)) ∈ I ^ 2 := by
  classical
  obtain ⟨d, _, hd, hdj⟩ := exists_eval₂_sub_eq_sum I φ a b a p hb (by simp)
  have heq : eval₂ φ b p - eval₂ φ a p -
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j)) =
      p.vars.sum (fun j => (d j - eval₂ φ a (pderiv j p)) * (b j - a j)) := by
    rw [hd, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply (I ^ 2).sum_mem
  intro j hj
  simpa only [pow_two] using Ideal.mul_mem_mul (hdj j) (hb j hj)

/-- Evaluation on a square-zero ideal coset is exactly its finite first-order
expansion, with the differential evaluated at the base point. -/
theorem eval₂_eq_eval₂_add_sum_pderiv_of_sq_eq_bot
    (I : Ideal R) (hI : I ^ 2 = ⊥) (φ : C →+* R) (a b : σ → R)
    (p : MvPolynomial σ C) (hb : ∀ i ∈ p.vars, b i - a i ∈ I) :
    eval₂ φ b p = eval₂ φ a p +
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j)) := by
  have h := eval₂_sub_eval₂_sub_sum_pderiv_mem_sq I φ a b p hb
  rw [hI, Ideal.mem_bot] at h
  calc
    eval₂ φ b p =
        (eval₂ φ b p - eval₂ φ a p -
          p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j))) +
        (eval₂ φ a p +
          p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j))) := by ring
    _ = _ := by rw [h, zero_add]

end MvPolynomial
