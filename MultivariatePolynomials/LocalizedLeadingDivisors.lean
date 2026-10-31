/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.MonomialOrder
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Leading divisors after coefficient localization

A family covering the leading exponents of an ideal still covers the leading exponents
of its extension after an injective localization of the coefficient semiring. Each member
of the extended ideal has a numerator in the original ideal. Its denominator is a unit,
so multiplication by that denominator does not change its leading exponent.

The coefficient localization property of multivariate polynomials follows from their
canonical algebraic pushout property. The coefficient algebra is Mathlib's canonical
`MvPolynomial.algebraMvPolynomial`. No finite generation assumption on the ideal or
the family is required.

## References

* Mathlib, `Mathlib.RingTheory.Localization.BaseChange`: localization and algebraic pushouts.
* Mathlib, `Mathlib.RingTheory.Localization.Ideal`: denominator clearing in extended ideals.
* Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`: polynomial algebraic base change.
-/

@[expose] public section

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v w x

namespace MvPolynomial

variable {σ : Type u} {R : Type w} {S : Type x}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Localizing coefficients localizes the submonoid of constant polynomials. -/
theorem isLocalization_coefficients (M : Submonoid R) [IsLocalization M S] :
    IsLocalization (M.map (C (σ := σ))) (MvPolynomial σ S) := by
  exact (Algebra.isLocalization_iff_isPushout
    (T := MvPolynomial σ R) (B := MvPolynomial σ S) M S).mpr inferInstance

end MvPolynomial

namespace MonomialOrder

variable {σ : Type u} {ι : Type v} {R : Type w} {S : Type x}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Leading-divisor coverage of an ideal is preserved by an injective localization
of the coefficient semiring. -/
theorem exists_degree_map_le_of_mem_ideal_map
    (m : MonomialOrder σ) (M : Submonoid R) [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S))
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hlead : ∀ q ∈ I, q ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree q)
    (p : MvPolynomial σ S)
    (hp : p ∈ I.map (MvPolynomial.map (algebraMap R S))) (hp0 : p ≠ 0) :
    ∃ i, m.degree (MvPolynomial.map (algebraMap R S) (g i)) ≤ m.degree p := by
  let _ : IsLocalization (M.map (MvPolynomial.C (σ := σ))) (MvPolynomial σ S) :=
    MvPolynomial.isLocalization_coefficients (S := S) M
  have hp' : p ∈ I.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) := by
    simpa only [MvPolynomial.algebraMap_def] using hp
  obtain ⟨⟨q, t⟩, hqt⟩ :=
    (IsLocalization.mem_map_algebraMap_iff
      (M.map (MvPolynomial.C (σ := σ))) (MvPolynomial σ S)).mp hp'
  have hden := IsLocalization.map_units (MvPolynomial σ S) t
  have hq0 : (q : MvPolynomial σ R) ≠ 0 := by
    intro hq
    apply hp0
    apply hden.mul_left_eq_zero.mp
    simpa only [hq, map_zero] using hqt
  obtain ⟨s, hs, hst⟩ := Submonoid.mem_map.mp t.property
  have hclear :
      p * MvPolynomial.C (algebraMap R S s) =
        MvPolynomial.map (algebraMap R S) (q : MvPolynomial σ R) := by
    simpa only [MvPolynomial.algebraMap_def, ← hst, MvPolynomial.map_C] using hqt
  have hsunit : IsUnit (algebraMap R S s) :=
    IsLocalization.map_units S (⟨s, hs⟩ : M)
  have hdegree :
      m.degree (MvPolynomial.map (algebraMap R S) (q : MvPolynomial σ R)) =
        m.degree p := by
    rw [← hclear, mul_comm, ← MvPolynomial.smul_eq_C_mul]
    exact m.degree_smul_of_mem_nonZeroDivisors hsunit.mem_nonZeroDivisors
  obtain ⟨i, hi⟩ := hlead (q : MvPolynomial σ R) q.property hq0
  refine ⟨i, ?_⟩
  calc
    m.degree (MvPolynomial.map (algebraMap R S) (g i)) = m.degree (g i) :=
      degree_map_of_injective m (algebraMap R S) hinj (g i)
    _ ≤ m.degree (q : MvPolynomial σ R) := hi
    _ = m.degree (MvPolynomial.map (algebraMap R S) (q : MvPolynomial σ R)) :=
      (degree_map_of_injective m (algebraMap R S) hinj (q : MvPolynomial σ R)).symm
    _ = m.degree p := hdegree

end MonomialOrder
