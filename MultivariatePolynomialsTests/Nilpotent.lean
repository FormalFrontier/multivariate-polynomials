/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Nilpotent
import MultivariatePolynomials.PrimeSpectrum
import Mathlib.Data.ZMod.Basic

/-!
# Nilpotent polynomial and spectrum examples over semirings

Over `ZMod 4 × ℕ`, the polynomial with coefficient `(2, 0)` on each of two
variables is nonzero and has square zero. The coefficient semiring is not a
ring: its multiplicative identity has no additive inverse. The spectrum
criterion also applies to polynomials in infinitely many variables over `ℕ`.

Reducedness is available for polynomial semirings over `ℕ`, and reflects to
the coefficient semiring. The empty-variable equivalence and the empty spectrum
over a trivial base provide boundary examples.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Equiv`, for `isEmptyRingEquiv`.
* `MultivariatePolynomials.Nilpotent` and `MultivariatePolynomials.PrimeSpectrum`.
-/

@[expose] public section

universe u v

open MvPolynomial

local notation "ε" => ((2 : ZMod 4), (0 : ℕ))
local notation "p" =>
  (C ε * X (0 : Fin 2) + C ε * X (1 : Fin 2) :
    MvPolynomial (Fin 2) (ZMod 4 × ℕ))

example : ¬ ∃ a : ZMod 4 × ℕ, a + 1 = 0 := by
  rintro ⟨a, ha⟩
  have hs : a.2 + 1 = 0 := congrArg Prod.snd ha
  exact Nat.succ_ne_zero a.2 hs

example : p ≠ 0 ∧ p ^ 2 = 0 ∧
    ∀ d : Fin 2 →₀ ℕ, IsNilpotent ((p).coeff d) := by
  have hε : ε ^ 2 = 0 := by decide
  have hC : (C ε : MvPolynomial (Fin 2) (ZMod 4 × ℕ)) ^ 2 = 0 := by
    rw [← map_pow, hε, map_zero]
  have hsq : p ^ 2 = 0 := by
    calc
      p ^ 2 = (C ε * (X (0 : Fin 2) + X (1 : Fin 2))) ^ 2 := by rw [mul_add]
      _ = (C ε) ^ 2 * (X (0 : Fin 2) + X (1 : Fin 2)) ^ 2 := mul_pow _ _ 2
      _ = 0 := by rw [hC, zero_mul]
  refine ⟨?_, hsq, (isNilpotent_iff_coeff p).mp ⟨2, hsq⟩⟩
  have hmon : Finsupp.single (1 : Fin 2) (1 : ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro h
    have he := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    simpa using he
  intro hp
  have hc := congrArg
    (fun q : MvPolynomial (Fin 2) (ZMod 4 × ℕ) => q.coeff (Finsupp.single (0 : Fin 2) 1)) hp
  have hnonzero : ε ≠ 0 := by decide
  apply hnonzero
  simpa [coeff_X, hmon] using hc

example : IsReduced ℕ ∧ ¬ ∃ n : ℕ, n + 1 = 0 := by
  exact ⟨inferInstance, by simp⟩

example : IsReduced (MvPolynomial Bool ℕ) := inferInstance

example (q : MvPolynomial Bool ℕ) (hq : IsNilpotent q) : q = 0 := hq.eq_zero

example : IsReduced (MvPolynomial PEmpty (ZMod 1)) := inferInstance

example (σ : Type v) : ¬ IsReduced (MvPolynomial σ (ZMod 4)) := by
  intro h
  letI : IsReduced (ZMod 4) := (MvPolynomial.isReduced_iff (σ := σ)).mp h
  have hnil : IsNilpotent (2 : ZMod 4) := ⟨2, by decide⟩
  have hne : (2 : ZMod 4) ≠ 0 := by decide
  exact hne hnil.eq_zero

example : IrreducibleSpace (PrimeSpectrum (MvPolynomial ℕ ℕ)) :=
  (PrimeSpectrum.irreducibleSpace_mvPolynomial_iff ℕ ℕ).mpr inferInstance

example (R : Type u) [CommSemiring R] (q : MvPolynomial PEmpty R) :
    IsNilpotent q ↔ IsNilpotent ((isEmptyRingEquiv R PEmpty) q) :=
  (IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective).symm

example (σ : Type v) :
    (¬ IrreducibleSpace (PrimeSpectrum (ZMod 1))) ∧
      ¬ IrreducibleSpace (PrimeSpectrum (MvPolynomial σ (ZMod 1))) := by
  constructor <;> intro h <;> obtain ⟨x⟩ := h.toNonempty <;> exact isEmptyElim x
