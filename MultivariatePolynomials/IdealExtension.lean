/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Radicals of extended coefficient ideals

Extension of a coefficient ideal along the constant embedding into a multivariate
polynomial ring commutes with taking radicals. A polynomial belongs to this
radical exactly when every coefficient belongs to the radical of the original
ideal. The coefficient ring is commutative, and the variable type is arbitrary.

## References

* Mathlib's `MvPolynomial.ker_map` and `Ideal.mk_ker` identify the kernel of
  coefficient reduction modulo an ideal.
* Andrew Yang's `MvPolynomial.isNilpotent_iff` in Mathlib characterizes
  nilpotence by coefficients.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommRing R]

/-- Extending a coefficient ideal to a multivariate polynomial ring commutes
with taking its radical. -/
theorem radical_map_C (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).radical =
      I.radical.map (C : R →+* MvPolynomial σ R) := by
  ext p
  rw [mem_map_C_iff]
  have hker : RingHom.ker
      (map (Ideal.Quotient.mk I) : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ I)) =
      I.map (C : R →+* MvPolynomial σ R) := by
    rw [ker_map, Ideal.mk_ker]
  calc
    p ∈ (I.map (C : R →+* MvPolynomial σ R)).radical ↔
        IsNilpotent (map (Ideal.Quotient.mk I) p) := by
      rw [← hker, Ideal.mem_radical_iff]
      simp only [RingHom.mem_ker, map_pow, IsNilpotent]
    _ ↔ ∀ d : σ →₀ ℕ, p.coeff d ∈ I.radical := by
      rw [MvPolynomial.isNilpotent_iff]
      simp only [coeff_map, IsNilpotent, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_radical_iff]

/-- Membership in the radical of an extended coefficient ideal is equivalent
to coefficientwise membership in the radical of the original ideal. -/
theorem mem_radical_map_C_iff {I : Ideal R} {p : MvPolynomial σ R} :
    p ∈ (I.map (C : R →+* MvPolynomial σ R)).radical ↔
      ∀ d : σ →₀ ℕ, p.coeff d ∈ I.radical := by
  rw [radical_map_C, mem_map_C_iff]

end MvPolynomial
