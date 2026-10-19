/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials
import Mathlib.Data.ZMod.Basic

/-!
# Aggregate-import clients

Test theorems check the generic semiring/infinite-variable interface and its
specialization to polynomials over `ℚ` indexed by `ℕ`. The concrete client is
public in the test namespace; neither is additional production API.

Membership examples use the nonzero ideal `(2)` in `ℤ`, with one selected
and one unselected Boolean variable. Four specializations check empty and
full selected sets, an empty variable type, and the zero coefficient ring.

## References

* `MultivariatePolynomials.IdealOfVars`: the theorem motivated by Vakil's
  Exercise 6.7.E and its Mathlib ideal infrastructure.
-/

private theorem aggregateGeneric (k : Type*) (σ : Type*)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

public theorem MultivariatePolynomialsTests.idealOfVarsRatNotFG :
    ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ

open MvPolynomial

-- A selected variable may have an odd coefficient; the unselected one may not.
example :
    (X false + C 2 * X true : MvPolynomial Bool ℤ) ∈
      Ideal.map C (Ideal.span ({2} : Set ℤ)) ⊔
        Ideal.span (X '' ({false} : Set Bool)) := by
  apply mem_map_C_sup_span_X_image_iff.mpr
  intro d hd
  have hne : Finsupp.single false 1 ≠ d := by
    intro h
    have hzero := hd false (by simp)
    rw [← h] at hzero
    simpa using hzero
  have htwice : (C 2 * X true : MvPolynomial Bool ℤ) ∈
      Ideal.map C (Ideal.span ({2} : Set ℤ)) := by
    exact (Ideal.map C (Ideal.span ({2} : Set ℤ))).mul_mem_right (X true)
      (Ideal.mem_map_of_mem C (Ideal.subset_span (Set.mem_singleton 2)))
  simpa [coeff_X, hne] using mem_map_C_iff_coeff_mem.mp htwice d

example :
    (X true : MvPolynomial Bool ℤ) ∉
      Ideal.map C (Ideal.span ({2} : Set ℤ)) ⊔
        Ideal.span (X '' ({false} : Set Bool)) := by
  intro hp
  have hcoeff := mem_map_C_sup_span_X_image_iff.mp hp (Finsupp.single true 1)
    (by
      intro i hi
      have hi' : i = false := Set.mem_singleton_iff.mp hi
      subst i
      simp)
  have hone : (1 : ℤ) ∈ Ideal.span ({2} : Set ℤ) := by simpa using hcoeff
  exact (by decide : ¬ (2 : ℤ) ∣ 1) (Ideal.mem_span_singleton.mp hone)

universe u v

example {R : Type u} {σ : Type v} [CommSemiring R]
    (I : Ideal R) (p : MvPolynomial σ R) :
    p ∈ Ideal.map C I ↔ ∀ d, p.coeff d ∈ I := by
  simpa using
    (mem_map_C_sup_span_X_image_iff (I := I) (S := (∅ : Set σ)) (p := p))

example {R : Type u} {σ : Type v} [CommSemiring R]
    (I : Ideal R) (p : MvPolynomial σ R) :
    p ∈ Ideal.map C I ⊔ Ideal.span (X '' (Set.univ : Set σ)) ↔ p.coeff 0 ∈ I := by
  rw [mem_map_C_sup_span_X_image_iff]
  constructor
  · intro hp
    exact hp 0 (by simp)
  · intro hp d hd
    have hdzero : d = 0 := Finsupp.ext fun i => hd i (Set.mem_univ i)
    simpa only [hdzero] using hp

example {R : Type u} [CommSemiring R]
    (I : Ideal R) (S : Set Empty) (p : MvPolynomial Empty R) :
    p ∈ Ideal.map C I ⊔ Ideal.span (X '' S) ↔ p.coeff 0 ∈ I := by
  rw [mem_map_C_sup_span_X_image_iff]
  constructor
  · intro hp
    exact hp 0 (by simp)
  · intro hp d _
    simpa only [Subsingleton.elim d 0] using hp

example {σ : Type v} (I : Ideal (ZMod 1)) (S : Set σ) (p : MvPolynomial σ (ZMod 1)) :
    p ∈ Ideal.map C I ⊔ Ideal.span (X '' S) := by
  apply mem_map_C_sup_span_X_image_iff.mpr
  intro d _
  simpa only [Subsingleton.elim (p.coeff d) 0] using I.zero_mem
