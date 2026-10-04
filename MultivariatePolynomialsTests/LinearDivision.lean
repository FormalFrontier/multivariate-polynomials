/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.LinearDivision
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

open _root_.MvPolynomial

namespace Test.LinearDivision

private theorem generic_client {σ ι R : Type*} [CommRing R]
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (J : Ideal R)
    (p q : MvPolynomial σ R) (a : R)
    (hp : p ∈ coeffsIn σ (J : Submodule R R)) :
    p = Finsupp.linearCombination (MvPolynomial σ R) b
        (m.linearDivisionQuotient b hb p) + m.linearDivisionRemainder b hb p ∧
      (∀ α ∈ (m.linearDivisionRemainder b hb p).support,
        ∀ i, ¬ m.degree (b i) ≤ α) ∧
      m.linearDivisionQuotient b hb (p + q) =
        m.linearDivisionQuotient b hb p + m.linearDivisionQuotient b hb q ∧
      m.linearDivisionRemainder b hb (a • p) =
        a • m.linearDivisionRemainder b hb p ∧
      m.linearDivisionRemainder b hb p ∈ coeffsIn σ (J : Submodule R R) ∧
      (∀ i, (m.linearDivisionQuotient b hb p) i ∈
        coeffsIn σ (J : Submodule R R)) := by
  exact ⟨m.linearDivision_decomposition b hb p, m.linearDivision_remainder_support b hb p,
    (m.linearDivisionQuotient b hb).map_add p q,
    (m.linearDivisionRemainder b hb).map_smul a p,
    m.linearDivision_remainder_coeffsIn b hb J p hp,
    m.linearDivision_quotient_coeffsIn b hb J p hp⟩

private theorem finite_family (m : MonomialOrder (Fin 2))
    (b : Fin 2 → MvPolynomial (Fin 2) ℤ)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (p q : MvPolynomial (Fin 2) ℤ) :
    m.linearDivisionQuotient b hb (p + q) =
      m.linearDivisionQuotient b hb p + m.linearDivisionQuotient b hb q ∧
    (∀ α ∈ (m.linearDivisionRemainder b hb p).support,
      ∀ i, ¬ m.degree (b i) ≤ α) := by
  have h := generic_client m b hb (⊤ : Ideal ℤ) p q 2
    (show p ∈ coeffsIn (Fin 2) (⊤ : Submodule ℤ ℤ) by simp [mem_coeffsIn])
  exact ⟨h.2.2.1, h.2.1⟩

private theorem empty_family {σ R : Type*} [CommRing R]
    (m : MonomialOrder σ) (p : MvPolynomial σ R) :
    m.linearDivisionRemainder (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) p = p ∧
    m.linearDivisionQuotient (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) p = 0 := by
  have hred : ∀ α ∈ p.support, ∀ i : Fin 0,
      ¬ m.degree ((fun j : Fin 0 => j.elim0) i : MvPolynomial σ R) ≤ α := by
    intro _ _ i
    exact i.elim0
  exact ⟨m.linearDivision_remainder_of_reduced _ _ p hred,
    m.linearDivision_quotient_of_reduced _ _ p hred⟩

public theorem zero_input {σ ι R : Type*} [CommRing R]
    (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) :
    m.linearDivisionQuotient b hb 0 = 0 ∧
    m.linearDivisionRemainder b hb 0 = 0 ∧
    (0 : MvPolynomial σ R) =
      Finsupp.linearCombination (MvPolynomial σ R) b (m.linearDivisionQuotient b hb 0) +
        m.linearDivisionRemainder b hb 0 := by
  exact ⟨(m.linearDivisionQuotient b hb).map_zero,
    (m.linearDivisionRemainder b hb).map_zero,
    m.linearDivision_decomposition b hb 0⟩

private theorem zero_ring_client (m : MonomialOrder (Fin 2)) :
    m.linearDivisionRemainder (fun _ : Fin 1 => (1 : MvPolynomial (Fin 2) (ZMod 1)))
      (by intro _; simpa only [m.leadingCoeff_one] using (isUnit_one : IsUnit (1 : ZMod 1)))
      0 = 0 := by
  exact (m.linearDivisionRemainder _
    (by intro _; simpa only [m.leadingCoeff_one] using (isUnit_one : IsUnit (1 : ZMod 1)))).map_zero

private theorem mod_four_ideal_nontrivial :
    Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)) ≠ ⊥ ∧
      Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)) ≠ ⊤ := by
  constructor
  · intro h
    exact (by decide : (2 : ZMod 4) ≠ 0) (Ideal.span_singleton_eq_bot.mp h)
  · apply Ideal.span_singleton_ne_top
    change ¬ IsUnit ((2 : ℕ) : ZMod 4)
    rw [ZMod.isUnit_iff_coprime]
    decide

private theorem mod_four_ideal (m : MonomialOrder (Fin 1)) :
    let J : Ideal (ZMod 4) := Ideal.span ({2} : Set (ZMod 4))
    m.linearDivisionRemainder (fun _ : Fin 1 => (1 : MvPolynomial (Fin 1) (ZMod 4)))
      (by intro _; simpa only [m.leadingCoeff_one] using (isUnit_one : IsUnit (1 : ZMod 4)))
      (C 2) ∈ coeffsIn (Fin 1) (J : Submodule (ZMod 4) (ZMod 4)) ∧
    (∀ i : Fin 1,
      (m.linearDivisionQuotient (fun _ : Fin 1 =>
        (1 : MvPolynomial (Fin 1) (ZMod 4)))
        (by intro _; simpa only [m.leadingCoeff_one] using (isUnit_one : IsUnit (1 : ZMod 4)))
        (C 2)) i ∈
          coeffsIn (Fin 1) (J : Submodule (ZMod 4) (ZMod 4))) := by
  intro J
  have hb : ∀ i : Fin 1,
      IsUnit (m.leadingCoeff ((fun _ => (1 : MvPolynomial (Fin 1) (ZMod 4))) i)) := by
    intro i
    simpa only [m.leadingCoeff_one] using (isUnit_one : IsUnit (1 : ZMod 4))
  have hp : (C 2 : MvPolynomial (Fin 1) (ZMod 4)) ∈
      coeffsIn (Fin 1) (J : Submodule (ZMod 4) (ZMod 4)) := by
    apply C_mem_coeffsIn.mpr
    exact Ideal.subset_span (by simp : (2 : ZMod 4) ∈ ({2} : Set (ZMod 4)))
  exact ⟨m.linearDivision_remainder_coeffsIn _ hb J _ hp,
    m.linearDivision_quotient_coeffsIn _ hb J _ hp⟩

private theorem already_reduced (m : MonomialOrder (Fin 1)) :
    m.linearDivisionRemainder (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (by intro _; simpa only [m.leadingCoeff_X] using (isUnit_one : IsUnit (1 : ℤ))) 1 = 1 ∧
    m.linearDivisionQuotient (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (by intro _; simpa only [m.leadingCoeff_X] using (isUnit_one : IsUnit (1 : ℤ))) 1 = 0 := by
  have hb : ∀ i : Fin 1,
      IsUnit (m.leadingCoeff ((fun _ => (X 0 : MvPolynomial (Fin 1) ℤ)) i)) := by
    intro i
    simpa only [m.leadingCoeff_X] using (isUnit_one : IsUnit (1 : ℤ))
  have hred : ∀ α ∈ (1 : MvPolynomial (Fin 1) ℤ).support,
      ∀ i : Fin 1, ¬ m.degree ((fun _ => (X 0 : MvPolynomial (Fin 1) ℤ)) i) ≤ α := by
    intro α hα i
    have hα0 : α = 0 := by simpa [support_one] using hα
    subst α
    simp [m.degree_X]
  exact ⟨m.linearDivision_remainder_of_reduced _ hb 1 hred,
    m.linearDivision_quotient_of_reduced _ hb 1 hred⟩

end Test.LinearDivision
