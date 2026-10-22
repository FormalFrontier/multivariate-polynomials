/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Regularity
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.Basic

/-!
# Scalar annihilators of coefficient families

The faithful family over `ZMod 6` need not contain a non-zero-divisor. The
polynomial over `ZMod 4` instead has an explicit nonzero coefficient-ring
annihilator. Constant, empty-variable and zero-polynomial examples record
boundary behavior. The coefficient-family facts are proved independently of
the scalar criterion. The marked model consumer applies it after those facts;
a separate unique-variable example checks agreement with the unary criterion.
-/

@[expose] public section

universe u v

namespace MultivariatePolynomialsTests.ScalarAnnihilatorCriterion

open MvPolynomial

private noncomputable def mixedPolynomial : MvPolynomial (Fin 1) (ZMod 6) :=
  C 2 + C 3 * X 0

private theorem mixed_coeff_zero : mixedPolynomial.coeff 0 = 2 := by
  simp [mixedPolynomial]

private theorem mixed_coeff_variable :
    mixedPolynomial.coeff (Finsupp.single (0 : Fin 1) 1) = 3 := by
  have h : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single (0 : Fin 1) 1 := by
    intro h
    have hzero := congrArg (fun d : Fin 1 →₀ ℕ => d 0) h
    simp at hzero
  simp [mixedPolynomial, MvPolynomial.coeff_C, h]

private theorem mixed_coefficient_family :
    ∀ r : ZMod 6,
      (∀ d : Fin 1 →₀ ℕ, r * mixedPolynomial.coeff d = 0) → r = 0 := by
  intro r hr
  have htwo : r * 2 = 0 := by simpa only [mixed_coeff_zero] using hr 0
  have hthree : r * 3 = 0 := by
    simpa only [mixed_coeff_variable] using hr (Finsupp.single (0 : Fin 1) 1)
  have hunit : (3 : ZMod 6) + 2 * 2 = 1 := by decide
  calc
    r = r * (3 + 2 * 2) := by rw [hunit, mul_one]
    _ = r * 3 + (r * 2) * 2 := by simp only [mul_add, mul_assoc]
    _ = 0 := by rw [hthree, htwo]; simp

private theorem mixed_coefficients_not_nonZeroDivisors :
    mixedPolynomial.coeff 0 ∉ nonZeroDivisors (ZMod 6) ∧
      mixedPolynomial.coeff (Finsupp.single (0 : Fin 1) 1) ∉ nonZeroDivisors (ZMod 6) := by
  rw [mixed_coeff_zero, mixed_coeff_variable]
  constructor
  · intro h
    exact (by decide : (3 : ZMod 6) ≠ 0)
      ((mem_nonZeroDivisors_iff_right.mp h) 3 (by decide))
  · intro h
    exact (by decide : (2 : ZMod 6) ≠ 0)
      ((mem_nonZeroDivisors_iff_right.mp h) 2 (by decide))

-- This consumer uses the independently established coefficient family.
example : mixedPolynomial ∈ nonZeroDivisors (MvPolynomial (Fin 1) (ZMod 6)) :=
  (MvPolynomial.mem_nonZeroDivisors_iff mixedPolynomial).2 mixed_coefficient_family

private noncomputable def torsionPolynomial : MvPolynomial (Fin 1) (ZMod 4) :=
  C 2 * X 0

private theorem torsion_coeff_variable :
    torsionPolynomial.coeff (Finsupp.single (0 : Fin 1) 1) = 2 := by
  simp [torsionPolynomial]

private theorem torsion_coefficient_annihilator :
    (2 : ZMod 4) ≠ 0 ∧
      ∀ d : Fin 1 →₀ ℕ, (2 : ZMod 4) * torsionPolynomial.coeff d = 0 := by
  refine ⟨by decide, ?_⟩
  intro d
  change (2 : ZMod 4) * (C 2 * X 0 : MvPolynomial (Fin 1) (ZMod 4)).coeff d = 0
  rw [MvPolynomial.coeff_C_mul, ← mul_assoc,
    show (2 : ZMod 4) * 2 = 0 from by decide, zero_mul]

example {R : Type u} {sigma : Type v} [CommSemiring R] :
    ∀ r : R, (∀ d : sigma →₀ ℕ,
      r * (C 1 : MvPolynomial sigma R).coeff d = 0) → r = 0 := by
  intro r hr
  simpa using hr 0

-- With no variables, the coefficient family consists of its constant term.
example {R : Type u} [CommSemiring R] (p : MvPolynomial Empty R) :
    (∀ r : R, (∀ d : Empty →₀ ℕ, r * p.coeff d = 0) → r = 0) ↔
      p.coeff 0 ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_right]
  constructor
  · intro h r hr
    apply h r
    intro d
    have hd : d = 0 := by
      ext i
      exact Empty.elim i
    simpa only [hd] using hr
  · intro h r hr
    exact h r (hr 0)

example {R : Type u} {sigma : Type v} [CommSemiring R] :
    (∀ r : R, (∀ d : sigma →₀ ℕ,
      r * (0 : MvPolynomial sigma R).coeff d = 0) → r = 0) ↔ Subsingleton R := by
  constructor
  · intro h
    have hzero : ∀ r : R, r = 0 := fun r => h r (by simp)
    exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  · intro h
    let := h
    intro r _
    exact Subsingleton.elim _ _

example {sigma : Type v} (p : MvPolynomial sigma (ZMod 1)) :
    ∀ r : ZMod 1, (∀ d : sigma →₀ ℕ, r * p.coeff d = 0) → r = 0 := by
  intro r _
  exact Subsingleton.elim _ _

/-- For a unique variable, the coefficient-family condition agrees with the unary
scalar-annihilator criterion under the canonical algebra equivalence. -/
private theorem unique_variable_scalar_annihilator_iff
    {R : Type u} {sigma : Type v} [CommSemiring R] [Unique sigma]
    (p : MvPolynomial sigma R) :
    (∀ r : R, (∀ d : sigma →₀ ℕ, r * p.coeff d = 0) → r = 0) ↔
      ∀ r : R, r • MvPolynomial.uniqueAlgEquiv R sigma p = 0 → r = 0 := by
  let e := MvPolynomial.uniqueAlgEquiv R sigma
  have htransport :
      p ∈ nonZeroDivisors (MvPolynomial sigma R) ↔
        e p ∈ nonZeroDivisors (Polynomial R) := by
    rw [← MulEquivClass.map_nonZeroDivisors e]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      exact (e.injective hqp) ▸ hq
  exact (MvPolynomial.mem_nonZeroDivisors_iff p).symm.trans
    (htransport.trans Polynomial.mem_nonZeroDivisors_iff)

end MultivariatePolynomialsTests.ScalarAnnihilatorCriterion
