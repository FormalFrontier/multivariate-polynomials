/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Regularity
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.Basic

/-!
# Coefficient-family boundary cases and the unary criterion

The coefficient-family condition is checked for the constant polynomial
`C 1`, an empty variable type, zero polynomials, and the zero coefficient
semiring. For a unique variable, its comparison with the unary criterion
uses the canonical algebra equivalence and the coefficient-ring scalar
action on the resulting unary polynomial.
-/

@[expose] public section

universe u v

namespace MultivariatePolynomialsTests.ScalarAnnihilatorCriterion

open MvPolynomial

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
