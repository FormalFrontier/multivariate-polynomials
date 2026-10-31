/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.WellFoundedSet

/-!
# Leading exponents and finite divisor families

An injective homomorphism of coefficient semirings preserves the leading exponent and maps the
leading coefficient to the leading coefficient of the mapped polynomial. For finitely many
variables, every set of polynomials has a finite subfamily of nonzero elements whose leading
exponents divide those of all its nonzero elements.

## Main results

* `MonomialOrder.degree_map_of_injective`: injective coefficient maps preserve leading exponents.
* `MonomialOrder.leadingCoeff_map_of_injective`: leading coefficients commute with injective maps.
* `MonomialOrder.exists_finset_leading_divisors`: a finite leading-divisor subfamily for any set.

## References

* Mathlib's `MvPolynomial.support_map_of_injective` and `MvPolynomial.coeff_map`.
* Dickson's lemma, in the form formalized by Mathlib's `Finsupp.wellQuasiOrderedLE`, together with
  Mathlib's partially well-ordered set and minimal-antichain APIs.
-/

@[expose] public section

namespace MonomialOrder

universe u v w

variable {σ : Type u} {R : Type v} {S : Type w}

/-- An injective coefficient homomorphism preserves the leading exponent. -/
theorem degree_map_of_injective [CommSemiring R] [CommSemiring S]
    (m : MonomialOrder σ) (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial σ R) :
    m.degree (MvPolynomial.map f p) = m.degree p := by
  simp only [degree, MvPolynomial.support_map_of_injective p hf]

/-- Leading coefficients commute with an injective coefficient homomorphism. -/
theorem leadingCoeff_map_of_injective [CommSemiring R] [CommSemiring S]
    (m : MonomialOrder σ) (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial σ R) :
    m.leadingCoeff (MvPolynomial.map f p) = f (m.leadingCoeff p) := by
  simp only [leadingCoeff, degree_map_of_injective m f hf p, MvPolynomial.coeff_map]

/-- For finitely many variables, every set of polynomials has a finite subfamily of nonzero
members whose leading exponents divide those of all its nonzero members. -/
theorem exists_finset_leading_divisors [Finite σ] [CommSemiring R]
    (m : MonomialOrder σ) (s : Set (MvPolynomial σ R)) :
    ∃ t : Finset (MvPolynomial σ R),
      (∀ q ∈ t, q ∈ s ∧ q ≠ 0) ∧
      ∀ p ∈ s, p ≠ 0 → ∃ q ∈ t, m.degree q ≤ m.degree p := by
  classical
  let D : Set (σ →₀ ℕ) := m.degree '' {p : MvPolynomial σ R | p ∈ s ∧ p ≠ 0}
  have hD : D.IsPWO := Set.isPWO_of_wellQuasiOrderedLE D
  have hmin : {d : σ →₀ ℕ | Minimal (· ∈ D) d}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (· ∈ D))
  let g : (σ →₀ ℕ) → MvPolynomial σ R :=
    fun d => if hd : d ∈ D then Classical.choose hd else 0
  have hg (d : σ →₀ ℕ) (hd : d ∈ D) :
      g d ∈ s ∧ g d ≠ 0 ∧ m.degree (g d) = d := by
    have hq := Classical.choose_spec hd
    simp only [g, dite_eq_left hd]
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  refine ⟨hmin.toFinset.image g, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨d, hd, rfl⟩
    have hd' : Minimal (· ∈ D) d := hmin.mem_toFinset.mp hd
    exact ⟨(hg d hd'.prop).1, (hg d hd'.prop).2.1⟩
  · intro p hp hp0
    have hpD : m.degree p ∈ D := ⟨p, ⟨hp, hp0⟩, rfl⟩
    obtain ⟨d, hdp, hd⟩ := hD.exists_le_minimal hpD
    refine ⟨g d, Finset.mem_image.mpr ⟨d, hmin.mem_toFinset.mpr hd, rfl⟩, ?_⟩
    simpa only [(hg d hd.prop).2.2] using hdp

end MonomialOrder
