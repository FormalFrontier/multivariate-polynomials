/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A quadratic with natural coefficients and infinitely many variables

For `X 0 ^ 2` over `ℕ`, evaluated in `ℤ`, the two-point coefficients at the
constant points zero and two have value two at coordinate zero and vanish at
every other coordinate. The differential at zero vanishes, whereas the
remainder is the nonzero integer four in the square of the ideal `(2)`.
-/

@[expose] public section

open MvPolynomial

example :
    let φ : ℕ →+* ℤ := Nat.castRingHom ℤ
    let p : MvPolynomial ℕ ℕ := X 0 ^ 2
    let I : Ideal ℤ := Ideal.span ({2} : Set ℤ)
    let a : ℕ → ℤ := fun _ => 0
    let b : ℕ → ℤ := fun _ => 2
    let remainder := eval₂ φ b p - eval₂ φ a p -
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j))
    (∃ d : ℕ → ℤ,
      d 0 = 2 ∧ (∀ j, j ≠ 0 → d j = 0) ∧
      eval₂ φ b p - eval₂ φ a p = p.vars.sum (fun j => d j * (b j - a j)) ∧
      ∀ j, d j - eval₂ φ a (pderiv j p) ∈ I) ∧
      remainder = 4 ∧ remainder ≠ 0 ∧ remainder ∈ I ^ 2 := by
  classical
  let φ : ℕ →+* ℤ := Nat.castRingHom ℤ
  let p : MvPolynomial ℕ ℕ := X 0 ^ 2
  let I : Ideal ℤ := Ideal.span ({2} : Set ℤ)
  let a : ℕ → ℤ := fun _ => 0
  let b : ℕ → ℤ := fun _ => 2
  have hvars : p.vars = {0} := by
    simp [p, X_pow_eq_monomial]
  have htwo : (2 : ℤ) ∈ I := Ideal.subset_span (by simp)
  have hb (j : ℕ) (_ : j ∈ p.vars) : b j - a j ∈ I := by
    simpa [a, b] using htwo
  obtain ⟨d, hs, hd, hdj⟩ :=
    exists_eval₂_sub_eq_sum I φ a b a p hb (by simp)
  have hd0 : d 0 = 2 := by
    have h := hd
    rw [hvars] at h
    norm_num [p, a, b, φ] at h
    linarith
  have hoff (j : ℕ) (hj : j ≠ 0) : d j = 0 :=
    hs j (by simpa only [hvars, Finset.mem_singleton] using hj)
  have hvalue : eval₂ φ b p - eval₂ φ a p -
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j)) = 4 := by
    rw [hvars]
    norm_num [p, a, b, φ, pderiv_pow]
  have hnonzero : eval₂ φ b p - eval₂ φ a p -
      p.vars.sum (fun j => eval₂ φ a (pderiv j p) * (b j - a j)) ≠ 0 := by
    rw [hvalue]
    norm_num
  exact ⟨⟨d, hd0, hoff, hd, hdj⟩, hvalue, hnonzero,
    eval₂_sub_eval₂_sub_sum_pderiv_mem_sq I φ a b p hb⟩
