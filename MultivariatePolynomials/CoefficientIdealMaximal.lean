/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdeal
import Mathlib.RingTheory.Ideal.Maps

/-!
# Maximal coefficient ideals

For a commutative semiring, a coefficient extension is maximal exactly when the
coefficient ideal is maximal and the variable type is empty. With a variable
available, evaluation at zero gives a proper ideal strictly above every proper
coefficient extension.

The proofs use coefficientwise ideal membership from
`MultivariatePolynomials.CoefficientIdeal` and Mathlib's ideal-map and
constant-coefficient APIs.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- With a variable available, the extension of a proper coefficient ideal is
strictly contained in its constant-coefficient preimage. -/
theorem map_C_lt_comap_constantCoeff [Nonempty σ] (I : Ideal R) (hI : I ≠ ⊤) :
    I.map (C : R →+* MvPolynomial σ R) <
      I.comap (constantCoeff : MvPolynomial σ R →+* R) := by
  classical
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simpa only [Ideal.mem_comap, constantCoeff_C] using hr
  · intro h
    obtain ⟨i⟩ := ‹Nonempty σ›
    have hi : (X i : MvPolynomial σ R) ∈ I.comap constantCoeff := by
      simpa only [Ideal.mem_comap, constantCoeff_X] using I.zero_mem
    have h1 := (mem_map_C_iff_coeff_mem.mp (h hi)) (Finsupp.single i 1)
    exact (Ideal.ne_top_iff_one I).mp hI (by simpa only [coeff_X_same] using h1)

/-- A coefficient extension is never maximal when the variable type is nonempty. -/
theorem not_isMaximal_map_C [Nonempty σ] (I : Ideal R) :
    ¬ (I.map (C : R →+* MvPolynomial σ R)).IsMaximal := by
  intro h
  by_cases hI : I = ⊤
  · apply h.ne_top
    rw [hI, Ideal.map_top]
  · have hlt := map_C_lt_comap_constantCoeff (σ := σ) I hI
    exact hlt.ne (h.eq_of_le
      (Ideal.comap_ne_top (constantCoeff : MvPolynomial σ R →+* R) hI) hlt.le)

/-- A coefficient extension is maximal exactly when its coefficient ideal is
maximal and the variable type is empty. -/
theorem isMaximal_map_C_iff (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).IsMaximal ↔
      I.IsMaximal ∧ IsEmpty σ := by
  constructor
  · intro h
    have hσ : IsEmpty σ := ⟨fun i => by
      let : Nonempty σ := ⟨i⟩
      exact not_isMaximal_map_C I h⟩
    let : IsEmpty σ := hσ
    exact ⟨(Ideal.isMaximal_map_iff_of_bijective
      (C : R →+* MvPolynomial σ R) ⟨C_injective σ R, C_surjective σ⟩).mp h, hσ⟩
  · rintro ⟨hI, hσ⟩
    let : IsEmpty σ := hσ
    exact (Ideal.isMaximal_map_iff_of_bijective
      (C : R →+* MvPolynomial σ R) ⟨C_injective σ R, C_surjective σ⟩).mpr hI

end MvPolynomial
