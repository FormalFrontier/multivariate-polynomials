/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Formal Frontier Agents. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-!
# Raw subtractivity of radicals

If an ideal contains the second summand whenever it contains the first summand and their
sum, then its radical has the same property. The result holds over any commutative semiring.
-/

@[expose] public section

universe u

namespace Ideal

/-- In an ideal satisfying raw membership subtraction, membership of `a * (b + c)`
and `a * b ^ n` implies membership of `a * c ^ n`, retaining the common factor `a`. -/
theorem mul_pow_mem_of_mul_add_mem_of_mul_pow_mem {R : Type u} [CommSemiring R]
    (I : Ideal R) (hsub : ∀ x y : R, x ∈ I → x + y ∈ I → y ∈ I)
    (a b c : R) (n : ℕ) (hadd : a * (b + c) ∈ I) (hpow : a * b ^ n ∈ I) :
    a * c ^ n ∈ I := by
  induction n generalizing a with
  | zero => simpa only [pow_zero] using hpow
  | succ n ih =>
    have hb : (a * c) * b ^ n ∈ I := by
      apply hsub (a * b ^ (n + 1)) ((a * c) * b ^ n) hpow
      have heq : a * b ^ (n + 1) + (a * c) * b ^ n =
          b ^ n * (a * (b + c)) := by
        rw [pow_succ]
        ring
      rw [heq]
      exact I.mul_mem_left (b ^ n) hadd
    have hac : (a * c) * (b + c) ∈ I := by
      have heq : (a * c) * (b + c) = c * (a * (b + c)) := by ring
      rw [heq]
      exact I.mul_mem_left c hadd
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      ih (a * c) hac hb

/-- Radical closure preserves the raw membership-subtraction condition on an ideal. -/
theorem subtractive_radical {R : Type u} [CommSemiring R] (I : Ideal R)
    (hsub : ∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) :
    ∀ a b : R, a ∈ I.radical → a + b ∈ I.radical → b ∈ I.radical := by
  have factor (a b : R) : ∀ m : ℕ, ∃ c : R, (a + b) ^ m = b ^ m + a * c := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨b ^ m + c * (a + b), ?_⟩
      calc
        (a + b) ^ (m + 1) = (b ^ m + a * c) * (a + b) := by rw [pow_succ, hc]
        _ = b ^ (m + 1) + a * (b ^ m + c * (a + b)) := by
          simp only [pow_succ]
          ring
  intro a b ha hab
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hab
  obtain ⟨c, hc⟩ := factor a b m
  have hsum : b ^ m + a * c ∈ I := by
    rw [← hc]
    exact hm
  have hy : (a * c) ^ n ∈ I := by
    rw [mul_pow, mul_comm]
    exact I.mul_mem_left (c ^ n) hn
  have hx : (b ^ m) ^ n ∈ I := by
    simpa only [one_mul] using
      mul_pow_mem_of_mul_add_mem_of_mul_pow_mem I hsub 1 (a * c) (b ^ m) n
        (by simpa only [one_mul, add_comm] using hsum)
        (by simpa only [one_mul] using hy)
  exact Ideal.mem_radical_iff.mpr ⟨m * n, by rw [pow_mul]; exact hx⟩


end Ideal
