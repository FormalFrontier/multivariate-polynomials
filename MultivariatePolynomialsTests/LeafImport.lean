/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IdealOfVars
import MultivariatePolynomials.ConstantUnits
import MultivariatePolynomials.IntegrallyClosed
import MultivariatePolynomials.IdealExtension
import Mathlib.Tactic.NormNum

/-!
# Direct-leaf clients

Test-only declarations exercise variable ideals, integrally closed polynomial
rings, constant units over the natural numbers, and radicals of extended
coefficient ideals through direct leaf imports.
The unequal-universe client checks that the coefficient and variable types need
not lie in the same universe. The concrete variable-ideal client is public; the
remaining clients are private by the module default. Over the integers,
`C 2 * X` lies in the radical of the extension of `(4)` but not in the
extension itself; the top ideal provides a boundary case.

## References

* `MultivariatePolynomials.IdealOfVars`: the variable-ideal theorem and its
  cited mathematical motivation and Mathlib dependencies.
* `MultivariatePolynomials.IntegrallyClosed`: integral closedness of multivariate
  polynomial rings.
* `MultivariatePolynomials.IdealExtension`: radicals of extended coefficient
  ideals.
-/

universe u v

example (σ : Type v) (n : ℕ) :
    IsUnit (algebraMap ℕ (MvPolynomial σ ℕ) n) ↔ IsUnit n := by
  simp only [isUnit_map_iff]

theorem leafGeneric (k : Type u) (σ : Type v)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

public theorem MultivariatePolynomialsTests.rationalInfiniteVariables :
    ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ

theorem leafUnequalUniverses (k : Type) (σ : Type 1)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

private theorem isIntegrallyClosed_rational_infinite :
    IsIntegrallyClosed (MvPolynomial ℕ ℚ) :=
  MvPolynomial.isIntegrallyClosed (R := ℚ) (ι := ℕ)

private theorem isIntegrallyClosed_rational_empty :
    IsIntegrallyClosed (MvPolynomial Empty ℚ) :=
  MvPolynomial.isIntegrallyClosed (R := ℚ) (ι := Empty)

section

open MvPolynomial

example :
    (C 2 * X () : MvPolynomial Unit ℤ) ∈
        ((Ideal.span ({4} : Set ℤ)).map C).radical ∧
      (C 2 * X () : MvPolynomial Unit ℤ) ∉
        (Ideal.span ({4} : Set ℤ)).map C := by
  have htwo : (2 : ℤ) ∈ (Ideal.span ({4} : Set ℤ)).radical := by
    apply Ideal.mem_radical_iff.mpr
    refine ⟨2, ?_⟩
    norm_num [Ideal.mem_span_singleton]
  constructor
  · rw [radical_map_C]
    apply mem_map_C_iff.mpr
    intro d
    rw [coeff_C_mul, coeff_X]
    by_cases hd : Finsupp.single () 1 = d
    · simpa [hd] using htwo
    · simp [hd]
  · intro hp
    have hcoeff := mem_map_C_iff.mp hp (Finsupp.single () 1)
    rw [coeff_C_mul, coeff_X] at hcoeff
    norm_num [Ideal.mem_span_singleton] at hcoeff

example (p : MvPolynomial Unit ℤ) :
    p ∈ ((⊤ : Ideal ℤ).map (C : ℤ →+* MvPolynomial Unit ℤ)).radical := by
  apply mem_radical_map_C_iff.mpr
  intro d
  exact Ideal.mem_radical_iff.mpr ⟨1, by simp⟩

end
