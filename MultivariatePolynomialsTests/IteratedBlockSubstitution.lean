/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.IteratedBlockSubstitution
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

/-!
# Private clients of finite disjoint-block iteration

-/

namespace IteratedBlockSubstitutionClient

open MvPolynomial

private theorem arity {ι : Type*} [Fintype ι] (r : ℕ) :
    Fintype.card (Fin r → ι) = Fintype.card ι ^ r := by
  simp

private theorem arityOfPower {ι : Type*} [Fintype ι] (d m r : ℕ)
    (hcard : Fintype.card ι = d ^ m) :
    Fintype.card (Fin r → ι) = d ^ (m * r) := by
  rw [arity, hcard, pow_mul]

private theorem homogeneousOnlyZero {ι R : Type*} [CommSemiring R]
    [Nontrivial R] [Nonempty ι] (p : MvPolynomial ι R) (d r : ℕ)
    (hp : p.IsHomogeneous d)
    (hz : ∀ y : ι → R, eval y p = 0 → y = 0) :
    (∀ x : (Fin r → ι) → R, eval x (iteratedBlockSubst p r) = 0 → x = 0) ∧
      (iteratedBlockSubst p r).totalDegree = d ^ r :=
  ⟨eval_iteratedBlockSubst_eq_zero_imp p hz r,
    iteratedBlockSubst_totalDegree p d hp hz r⟩

private theorem homogeneousIff {ι R : Type*} [CommSemiring R]
    (p : MvPolynomial ι R) (d r : ℕ) (hp : p.IsHomogeneous d)
    (hz : ∀ y : ι → R, eval y p = 0 ↔ y = 0)
    (x : (Fin r → ι) → R) :
    (iteratedBlockSubst p r).IsHomogeneous (d ^ r) ∧
      (eval x (iteratedBlockSubst p r) = 0 ↔ x = 0) :=
  ⟨isHomogeneous_iteratedBlockSubst p d hp r,
    eval_iteratedBlockSubst_eq_zero_iff p hz r x⟩

private theorem attainedDegreesAndArity {ι R : Type*} [CommSemiring R]
    [Nontrivial R] [Nonempty ι] [Fintype ι]
    (p : MvPolynomial ι R) (d m bound : ℕ) (hp : p.IsHomogeneous d)
    (hz : ∀ y : ι → R, eval y p = 0 → y = 0)
    (hd : 1 < d) (hcard : Fintype.card ι = d ^ m) :
    ∃ r : ℕ, bound < (iteratedBlockSubst p r).totalDegree ∧
      Fintype.card (Fin r → ι) = (iteratedBlockSubst p r).totalDegree ^ m := by
  obtain ⟨r, hr⟩ := exists_iteratedBlockSubst_totalDegree_gt p d hp hz hd bound
  refine ⟨r, hr, ?_⟩
  calc
    Fintype.card (Fin r → ι) = d ^ (m * r) := arityOfPower d m r hcard
    _ = (d ^ r) ^ m := by rw [mul_comm m r, pow_mul]
    _ = (iteratedBlockSubst p r).totalDegree ^ m := by
      rw [iteratedBlockSubst_totalDegree p d hp hz r]

private theorem zeroIterations {ι R : Type*} [CommSemiring R]
    (p : MvPolynomial ι R) (x : (Fin 0 → ι) → R) :
    eval x (iteratedBlockSubst p 0) = x Fin.elim0 :=
  eval_iteratedBlockSubst_zero p x

private theorem singletonZeroIff {R : Type*} [CommSemiring R]
    (z : Fin 1 → R) :
    eval z (X (0 : Fin 1) : MvPolynomial (Fin 1) R) = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hi, eval_X, Pi.zero_apply] using hz
  · intro hz
    subst z
    simp

private theorem finiteField (r : ℕ) (x : (Fin r → Fin 1) → ZMod 2) :
    eval x (iteratedBlockSubst (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 2)) r) = 0 ↔
      x = 0 :=
  eval_iteratedBlockSubst_eq_zero_iff _ singletonZeroIff r x

private theorem emptyVariables {R : Type*} [CommSemiring R]
    (r : ℕ) (x : (Fin r → PEmpty) → R) :
    eval x (iteratedBlockSubst (0 : MvPolynomial PEmpty R) r) = 0 ↔ x = 0 := by
  apply eval_iteratedBlockSubst_eq_zero_iff
  intro y
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by simp⟩

private theorem zeroRing (p : MvPolynomial (Fin 2) PUnit)
    (r : ℕ) (x : (Fin r → Fin 2) → PUnit) :
    eval x (iteratedBlockSubst p r) = 0 ↔ x = 0 := by
  apply eval_iteratedBlockSubst_eq_zero_iff
  intro y
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

private theorem constantForward (r : ℕ) (x : (Fin r → Fin 1) → ZMod 2) :
    eval x (iteratedBlockSubst (C 1 : MvPolynomial (Fin 1) (ZMod 2)) r) = 0 →
      x = 0 := by
  apply eval_iteratedBlockSubst_eq_zero_imp
  intro y hy
  exact (one_ne_zero (by simpa only [eval_C] using hy)).elim

private theorem constantNotIff :
    ¬ ∀ x : (Fin 1 → Fin 1) → ZMod 2,
      eval x (iteratedBlockSubst (C 1 : MvPolynomial (Fin 1) (ZMod 2)) 1) = 0 ↔
        x = 0 := by
  intro h
  have hzero := (h 0).mpr rfl
  have hone : (1 : ZMod 2) = 0 := by
    simpa only [eval_iteratedBlockSubst_succ, eval_C] using hzero
  exact one_ne_zero hone

end IteratedBlockSubstitutionClient
