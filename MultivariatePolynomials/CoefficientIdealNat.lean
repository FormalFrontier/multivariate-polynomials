/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdealSubtractive
public import Mathlib.RingTheory.Ideal.NatInt

/-!
# Coefficient extension of the natural-number maximal ideal

The maximal ideal of `ℕ` is radical, but its coefficient extension to a
multivariate polynomial semiring with a nonempty variable type is not radical.
This gives a counterexample to preserving radicality without subtractivity.

The proof uses the general necessity theorem for radical coefficient extensions
and Mathlib's description of the natural-number maximal ideal, due to Junyan Xu.
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- The coefficient extension of the maximal ideal of `ℕ` is not radical when
there is at least one variable. -/
theorem not_isRadical_map_C_nat_maximalIdeal (σ : Type u) [Nonempty σ] :
    ¬ ((IsLocalRing.maximalIdeal ℕ).map
      (C : ℕ →+* MvPolynomial σ ℕ)).IsRadical := by
  intro h
  have h1 : (1 : ℕ) ∈ IsLocalRing.maximalIdeal ℕ :=
    mem_of_add_mem_of_isRadical_map_C (σ := σ) (IsLocalRing.maximalIdeal ℕ) h
      (a := 2) (b := 1) (by simp) (by simp)
  exact Nat.mem_maximalIdeal_iff.mp h1 rfl

end MvPolynomial
