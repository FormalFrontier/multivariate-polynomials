/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.CoefficientIdeal
import Mathlib.Data.ZMod.Basic

/-!
# A proper coefficient ideal over the natural numbers

The nonzero polynomial `2 * X` belongs to the extension of the ideal `(2)`
over `ℕ`, whereas `X` does not. The same two polynomials distinguish membership
in the kernel of coefficient reduction modulo two. This uses the stock
natural-number semiring, its principal ideal and its canonical map to `ZMod 2`.

The intersection of the extensions of `(2)` and `(3)` contains `6 * X` but
not `2 * X`. Empty indexed intersections with no variables and set intersections
over the zero coefficient ring check the degenerate cases.
-/

open MvPolynomial

private theorem twiceVariable_coefficientIdeal_facts :
    (C 2 * X () : MvPolynomial Unit ℕ) ≠ 0 ∧
      (C 2 * X () : MvPolynomial Unit ℕ) ∈
        Ideal.map C (Ideal.span ({2} : Set ℕ)) ∧
      (X () : MvPolynomial Unit ℕ) ∉ Ideal.map C (Ideal.span ({2} : Set ℕ)) ∧
      (C 2 * X () : MvPolynomial Unit ℕ) ∈
        RingHom.ker (map (Nat.castRingHom (ZMod 2))) ∧
      (X () : MvPolynomial Unit ℕ) ∉
        RingHom.ker (map (Nat.castRingHom (ZMod 2))) := by
  have h2 : (2 : ℕ) ∈ Ideal.span ({2} : Set ℕ) := Ideal.subset_span (by simp)
  have h1 : (1 : ℕ) ∉ Ideal.span ({2} : Set ℕ) := by
    simp [Ideal.mem_span_singleton]
  have hX : (X () : MvPolynomial Unit ℕ) ∉
      Ideal.map C (Ideal.span ({2} : Set ℕ)) := by
    intro hx
    have hc := (mem_map_C_iff_coeff_mem.mp hx) (Finsupp.single () 1)
    exact h1 (by simpa using hc)
  have hker2 : (2 : ℕ) ∈ RingHom.ker (Nat.castRingHom (ZMod 2)) := by
    rw [RingHom.mem_ker]
    exact ZMod.natCast_self 2
  have hker1 : (1 : ℕ) ∉ RingHom.ker (Nat.castRingHom (ZMod 2)) := by
    simp [RingHom.mem_ker]
  have hker :
      RingHom.ker (map (Nat.castRingHom (ZMod 2)) :
        MvPolynomial Unit ℕ →+* MvPolynomial Unit (ZMod 2)) =
      Ideal.map (C : ℕ →+* MvPolynomial Unit ℕ)
        (RingHom.ker (Nat.castRingHom (ZMod 2))) :=
    ker_map_eq_map_C (σ := Unit) (Nat.castRingHom (ZMod 2))
  refine ⟨?_, ?_, hX, ?_, ?_⟩
  · intro hzero
    have hc := congrArg (fun p : MvPolynomial Unit ℕ => p.coeff (Finsupp.single () 1)) hzero
    rw [coeff_C_mul, coeff_X_same, mul_one] at hc
    simpa using hc
  · exact (Ideal.map (C : ℕ →+* MvPolynomial Unit ℕ)
      (Ideal.span ({2} : Set ℕ))).mul_mem_right (X ()) (Ideal.mem_map_of_mem C h2)
  · rw [hker]
    exact (Ideal.map (C : ℕ →+* MvPolynomial Unit ℕ)
      (RingHom.ker (Nat.castRingHom (ZMod 2)))).mul_mem_right (X ())
        (Ideal.mem_map_of_mem C hker2)
  · rw [hker]
    intro hx
    have hc := (mem_map_C_iff_coeff_mem.mp hx) (Finsupp.single () 1)
    exact hker1 (by simpa using hc)

private theorem intersectionOfTwoCoefficientIdeals :
    let I : Bool → Ideal ℕ := fun b => Ideal.span ({if b then 2 else 3} : Set ℕ)
    (C 6 * X () : MvPolynomial Unit ℕ) ∈ Ideal.map C (⨅ b, I b) ∧
      (C 2 * X () : MvPolynomial Unit ℕ) ∉ Ideal.map C (⨅ b, I b) := by
  dsimp only
  simp only [map_C_iInf, Ideal.mem_iInf]
  constructor
  · intro b
    have h6 : (6 : ℕ) ∈ Ideal.span ({if b then 2 else 3} : Set ℕ) := by
      rw [Ideal.mem_span_singleton]
      cases b
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    exact (Ideal.map (C : ℕ →+* MvPolynomial Unit ℕ) _).mul_mem_right
      (X ()) (Ideal.mem_map_of_mem C h6)
  · intro h
    have h2 : (2 : ℕ) ∈ Ideal.span ({3} : Set ℕ) := by
      have hc := (mem_map_C_iff_coeff_mem.mp (h false)) (Finsupp.single () 1)
      rw [coeff_C_mul, coeff_X_same, mul_one] at hc
      simpa using hc
    simpa [Ideal.mem_span_singleton] using h2

private theorem emptyIndexedIntersection_noVariables :
    Ideal.map (C : ℕ →+* MvPolynomial Empty ℕ)
      (⨅ _ : Empty, (⊥ : Ideal ℕ)) = ⊤ := by
  rw [map_C_iInf]
  simp

private theorem setIntersection_zeroCoefficients :
    Ideal.map (C : ZMod 1 →+* MvPolynomial Unit (ZMod 1))
      (sInf ({⊥, ⊤} : Set (Ideal (ZMod 1)))) = ⊤ := by
  rw [map_C_sInf]
  exact Subsingleton.elim _ _
