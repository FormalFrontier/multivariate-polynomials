/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import MultivariatePolynomials.ResultantFactorization

import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Fixed-nominal resultants modulo an ideal

Coefficientwise congruence modulo an ideal is preserved by the resultant with fixed
nominal Sylvester sizes. No degree assumptions are needed for this congruence.

When every element of `1 + I` is regular, coefficient perturbations in `(r)I`
transport a regular seed resultant to the crossed resultant of two factorizations.
The resulting ordered uniqueness theorem requires bounds and matching nominal top
coefficients only for the factors, not for the seeds.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Coefficientwise congruence modulo an ideal preserves fixed-nominal resultants.
The nominal sizes are arbitrary and do not impose degree bounds on the polynomials. -/
theorem resultant_sub_mem_ideal (J : Ideal R) (f f' g g' : R[X]) (m n : ℕ)
    (hf : ∀ k, f.coeff k - f'.coeff k ∈ J)
    (hg : ∀ k, g.coeff k - g'.coeff k ∈ J) :
    resultant f g m n - resultant f' g' m n ∈ J := by
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hfmap : f.map q = f'.map q := by
    apply Polynomial.ext
    intro k
    simp only [Polynomial.coeff_map]
    exact Ideal.Quotient.eq.mpr (hf k)
  have hgmap : g.map q = g'.map q := by
    apply Polynomial.ext
    intro k
    simp only [Polynomial.coeff_map]
    exact Ideal.Quotient.eq.mpr (hg k)
  have hres : q (resultant f g m n) = q (resultant f' g' m n) := by
    rw [← resultant_map_map f g m n q, ← resultant_map_map f' g' m n q, hfmap, hgmap]
  exact Ideal.Quotient.eq.mp hres

/-- Perturbing all coefficients by `(r)I`, where `r` is the seed resultant, preserves
regularity of the fixed-nominal resultant when every `1 + u` with `u ∈ I` is regular.
No degree or top-coefficient bounds are required for the seed or perturbed polynomials. -/
theorem isRegular_resultant_of_coeff_sub_mem_span_mul (I : Ideal R)
    (f g a b : R[X]) (m n : ℕ)
    (hI : ∀ u ∈ I, IsRegular (1 + u))
    (hr : IsRegular (resultant a b m n))
    (hf : ∀ k, f.coeff k - a.coeff k ∈ Ideal.span {resultant a b m n} * I)
    (hg : ∀ k, g.coeff k - b.coeff k ∈ Ideal.span {resultant a b m n} * I) :
    IsRegular (resultant f g m n) := by
  have hmem := resultant_sub_mem_ideal
    (Ideal.span {resultant a b m n} * I) f a g b m n hf hg
  obtain ⟨u, hu, hu_eq⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have heq : resultant f g m n = resultant a b m n * (1 + u) := by
    linear_combination -hu_eq
  rw [heq]
  exact hr.mul (hI u hu)

/-- A regular seed resultant and coefficient perturbations in `(r)I` give ordered
factorization uniqueness when every `1 + u` with `u ∈ I` is regular.
The four factors satisfy the degree bounds and pairwise matching nominal top
coefficients; the seed polynomials have no degree or top-coefficient bounds. -/
theorem eq_and_eq_of_mul_eq_mul_of_coeff_sub_mem_span_mul
    (I : Ideal R) (m n : ℕ) (A B G H G' H' : R[X])
    (hI : ∀ u ∈ I, IsRegular (1 + u))
    (hr : IsRegular (resultant A B m n))
    (hGA : ∀ k, G'.coeff k - A.coeff k ∈ Ideal.span {resultant A B m n} * I)
    (hHB : ∀ k, H.coeff k - B.coeff k ∈ Ideal.span {resultant A B m n} * I)
    (hG : G.natDegree ≤ m) (hG' : G'.natDegree ≤ m)
    (hH : H.natDegree ≤ n) (hH' : H'.natDegree ≤ n)
    (hGtop : G.coeff m = G'.coeff m) (hHtop : H.coeff n = H'.coeff n)
    (hprod : G * H = G' * H') :
    G = G' ∧ H = H' := by
  have hres := isRegular_resultant_of_coeff_sub_mem_span_mul I G' H A B m n hI hr hGA hHB
  exact eq_and_eq_of_mul_eq_mul_of_isRegular_resultant
    m n G H G' H' hG hG' hH hH' hGtop hHtop hprod hres

end Polynomial
