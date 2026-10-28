/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdealSubtractive
public import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Field.ZMod

/-!
# Subtractivity of the zero ideal over the natural numbers

The zero ideal extends to the prime zero ideal of the polynomial semiring in
one variable over the natural numbers. The same prime-ideal witness supplies
radicality, so both coefficient-ideal theorems apply to this commutative semiring
without additive inverses. The kernel of reduction modulo two gives a proper,
nonzero radical subtractive ideal of `ℕ`; its polynomial extension is radical
by the sufficiency theorem.
-/

@[expose] public section

namespace MvPolynomial

private theorem nat_bot_map_C_isPrime :
    ((⊥ : Ideal ℕ).map (C : ℕ →+* MvPolynomial Unit ℕ)).IsPrime := by
  rw [Ideal.map_bot]
  exact Ideal.isPrime_bot

example {a b : ℕ} (ha : a ∈ (⊥ : Ideal ℕ)) (hab : a + b ∈ (⊥ : Ideal ℕ)) :
    b ∈ (⊥ : Ideal ℕ) := by
  exact mem_of_add_mem_of_isPrime_map_C (σ := Unit) (⊥ : Ideal ℕ)
    nat_bot_map_C_isPrime ha hab

example {a b : ℕ} (ha : a ∈ (⊥ : Ideal ℕ)) (hab : a + b ∈ (⊥ : Ideal ℕ)) :
    b ∈ (⊥ : Ideal ℕ) := by
  exact mem_of_add_mem_of_isRadical_map_C (σ := Unit) (⊥ : Ideal ℕ)
    nat_bot_map_C_isPrime.isRadical ha hab

-- A proper nonzero coefficient ideal over a semiring without additive inverses.
private theorem nat_mod_two_radical_extension :
    let I := RingHom.ker (Nat.castRingHom (ZMod 2))
    (I.map (C : ℕ →+* MvPolynomial Unit ℕ)).IsRadical ∧
      (2 : ℕ) ∈ I ∧ (1 : ℕ) ∉ I := by
  dsimp only
  refine ⟨isRadical_map_C_of_subtractive _ ?_ ?_, ?_, ?_⟩
  · exact (Ideal.isRadical_bot (R := ZMod 2)).comap (f := Nat.castRingHom (ZMod 2))
  · intro a b ha hab
    apply RingHom.mem_ker.mpr
    have ha' := RingHom.mem_ker.mp ha
    have hab' := RingHom.mem_ker.mp hab
    rwa [map_add, ha', zero_add] at hab'
  · exact RingHom.mem_ker.mpr (ZMod.natCast_self 2)
  · norm_num [RingHom.mem_ker]

end MvPolynomial
