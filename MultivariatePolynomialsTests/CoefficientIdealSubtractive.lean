/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdealSubtractive
public import Mathlib.Algebra.Ring.Nat

/-!
# Subtractivity of the zero ideal over the natural numbers

The zero ideal extends to the prime zero ideal of the polynomial semiring in
one variable over the natural numbers. Thus the coefficient-ideal theorem
applies to this commutative semiring without additive inverses.
-/

@[expose] public section

namespace MvPolynomial

private theorem nat_bot_map_C_isPrime :
    ((⊥ : Ideal ℕ).map (C : ℕ →+* MvPolynomial Unit ℕ)).IsPrime := by
  rw [Ideal.map_bot]
  exact Ideal.isPrime_bot

example {a b : ℕ} (ha : a ∈ (⊥ : Ideal ℕ)) (hab : a + b ∈ (⊥ : Ideal ℕ)) :
    b ∈ (⊥ : Ideal ℕ) := by
  exact mem_of_add_mem_of_isPrime_map_C (σ := Unit) (⊥ : Ideal ℕ)
    nat_bot_map_C_isPrime ha hab

end MvPolynomial
