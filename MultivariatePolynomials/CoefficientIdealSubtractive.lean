/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdeal
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Tactic.Ring

/-!
# Subtractivity from a prime polynomial extension

If the extension of a coefficient ideal to a polynomial semiring with at least
one variable is prime, then membership of `a` and `a + b` forces membership of
`b`. The argument factors a cubic polynomial whose coefficients belong to the
ideal and examines one coefficient of whichever factor lies in the prime ideal.

The nonempty variable hypothesis is essential. In the natural numbers, the
ideal consisting of zero and all numbers at least two is prime: its complement
is the multiplicatively closed singleton containing one. This ideal contains
two and three but not one. With no variables, the constant map is an
isomorphism, so the extension of this ideal is still prime.

## References

* `MultivariatePolynomials.CoefficientIdeal` for
  `MvPolynomial.mem_map_C_iff_coeff_mem`.
* Mathlib's `AddMonoidAlgebra.coeff_add` and the coefficient lemmas in
  `Mathlib.Algebra.MvPolynomial.Basic`.
* `Mathlib.RingTheory.Ideal.Prime` for `Ideal.IsPrime.mem_or_mem` and
  `Ideal.IsPrime.one_notMem`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A prime extension to polynomials in a nonempty variable type forces
subtraction of ideal membership: if `a` and `a + b` lie in the coefficient
ideal, then so does `b`. -/
theorem mem_of_add_mem_of_isPrime_map_C {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R)
    (h : (I.map (C : R →+* MvPolynomial σ R)).IsPrime)
    {a b : R} (ha : a ∈ I) (hab : a + b ∈ I) : b ∈ I := by
  classical
  obtain ⟨j⟩ := ‹Nonempty σ›
  let J : Ideal (MvPolynomial σ R) := I.map (C : R →+* MvPolynomial σ R)
  have haC : C a ∈ J := Ideal.mem_map_of_mem C ha
  have habC : C (a + b) ∈ J := Ideal.mem_map_of_mem C hab
  have hfactor :
      (C a + C b * X j + C a * X j ^ 2 : MvPolynomial σ R) * (1 + X j) =
        C a + C (a + b) * X j + C (a + b) * X j ^ 2 + C a * X j ^ 3 := by
    simp only [map_add]
    ring
  have hprod :
      (C a + C b * X j + C a * X j ^ 2 : MvPolynomial σ R) * (1 + X j) ∈ J := by
    rw [hfactor]
    exact J.add_mem
      (J.add_mem (J.add_mem haC (J.mul_mem_right (X j) habC))
        (J.mul_mem_right (X j ^ 2) habC))
      (J.mul_mem_right (X j ^ 3) haC)
  rcases h.mem_or_mem hprod with hF | hG
  · have h01 : (0 : σ →₀ ℕ) ≠ Finsupp.single j 1 := by
      intro heq
      simpa using congrArg (fun d : σ →₀ ℕ => d j) heq
    have h21 : (Finsupp.single j 2 : σ →₀ ℕ) ≠ Finsupp.single j 1 := by
      intro heq
      simpa using congrArg (fun d : σ →₀ ℕ => d j) heq
    have hcoeff :
        (C a + C b * X j + C a * X j ^ 2 : MvPolynomial σ R).coeff
          (Finsupp.single j 1) = b := by
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C, if_neg h01,
        coeff_C_mul, coeff_X_same, coeff_X_pow, if_neg h21, mul_one, mul_zero,
        zero_add, add_zero]
    simpa only [hcoeff] using (mem_map_C_iff_coeff_mem.mp hF) (Finsupp.single j 1)
  · have hcoeff : (1 + X j : MvPolynomial σ R).coeff 0 = 1 := by
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_one,
        if_pos rfl, coeff_zero_X, add_zero]
      rfl
    have h1 : (1 : R) ∈ I := by
      simpa only [hcoeff] using (mem_map_C_iff_coeff_mem.mp hG) 0
    have h1J : (1 : MvPolynomial σ R) ∈ J := by
      simpa only [map_one] using
        (Ideal.mem_map_of_mem (C : R →+* MvPolynomial σ R) h1)
    exact (h.one_notMem h1J).elim

end MvPolynomial
