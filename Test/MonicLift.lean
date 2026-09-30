/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.MonicLift
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs

set_option warningAsError true

namespace Test.MonicLift

open MvPolynomial

private theorem client_generic {σ R S : Type*} [CommRing R] [CommRing S]
    (m : MonomialOrder σ) (φ : R →+* S) (hφ : Function.Surjective φ)
    (p : MvPolynomial σ S) (hp : m.Monic p) :
    ∃ q : MvPolynomial σ R, map φ q = p ∧ m.Monic q ∧ m.degree q = m.degree p :=
  m.exists_monic_lift φ hφ p hp

private theorem client_noninjective_quotient (m : MonomialOrder ℕ) :
    ∃ q : MvPolynomial ℕ ℤ,
      map (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)})) q =
        X 0 + C (1 : ℤ ⧸ Ideal.span {(2 : ℤ)}) ∧
      m.Monic q ∧
      m.degree q = m.degree (X 0 + C (1 : ℤ ⧸ Ideal.span {(2 : ℤ)})) :=
  m.exists_monic_lift _ Ideal.Quotient.mk_surjective _ (m.monic_X_add_C 0 1)

private theorem client_empty_variables {R S : Type*} [CommRing R] [CommRing S]
    (m : MonomialOrder Empty) (φ : R →+* S) (hφ : Function.Surjective φ) :
    ∃ q : MvPolynomial Empty R, map φ q = 1 ∧ m.Monic q ∧ m.degree q = 0 := by
  simpa using m.exists_monic_lift φ hφ (1 : MvPolynomial Empty S) m.monic_one

private theorem client_zero_target (m : MonomialOrder Empty) :
    ∃ q : MvPolynomial Empty ℤ,
      map (Int.castRingHom (ZMod 1)) q = 0 ∧ m.Monic q ∧
        m.degree q = m.degree (0 : MvPolynomial Empty (ZMod 1)) := by
  apply m.exists_monic_lift (Int.castRingHom (ZMod 1))
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact MonomialOrder.Monic.of_subsingleton

private theorem client_zero_source (m : MonomialOrder ℕ) :
    ∃ q : MvPolynomial ℕ (ZMod 1),
      map (RingHom.id (ZMod 1)) q = 0 ∧ m.Monic q ∧
        m.degree q = m.degree (0 : MvPolynomial ℕ (ZMod 1)) := by
  exact m.exists_monic_lift (RingHom.id (ZMod 1)) (fun y => ⟨y, rfl⟩)
    0 MonomialOrder.Monic.of_subsingleton

end Test.MonicLift
