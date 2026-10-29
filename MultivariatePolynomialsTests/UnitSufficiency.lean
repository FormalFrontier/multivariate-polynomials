/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.UnitSufficiency
import Mathlib.Data.ZMod.Basic

/-!
# Semiring polynomial units

The nonring control has coefficient semiring `ℕ × ZMod 4` and a nonzero
square-zero coefficient. Its nonconstant term has an additive inverse although
`1` in the coefficient semiring does not. The remaining checks cover the empty
variable type, the zero semiring, and compatibility with the ring criterion.
-/

open MvPolynomial

universe u v

/-- The semiring criterion agrees with Mathlib's ring criterion after adding the
automatic additive-invertibility conditions. -/
private theorem ring_specialization {R : Type u} {σ : Type v} [CommRing R]
    (p : MvPolynomial σ R) :
    (IsUnit (p.coeff 0) ∧ ∀ d ≠ 0,
      IsNilpotent (p.coeff d) ∧ IsAddUnit (p.coeff d)) ↔ IsUnit p := by
  constructor
  · rintro ⟨hc, hn⟩
    exact isUnit_of_coeff_isNilpotent_isAddUnit p hc hn
  · intro hp
    obtain ⟨hc, hn⟩ := MvPolynomial.isUnit_iff.mp hp
    exact ⟨hc, fun d hd =>
      ⟨hn d hd, ⟨⟨p.coeff d, -(p.coeff d), by simp, by simp⟩, rfl⟩⟩⟩

/-- A genuinely nonconstant polynomial meeting the criterion over a nonring. -/
private theorem nonring_control :
    ∃ p : MvPolynomial Unit (ℕ × ZMod 4),
      IsUnit p ∧ p ≠ C (p.coeff 0) ∧ IsUnit (p.coeff 0) ∧
        ∀ d ≠ 0, IsNilpotent (p.coeff d) ∧ IsAddUnit (p.coeff d) := by
  classical
  let e : ℕ × ZMod 4 := (0, 2)
  have he : e ≠ 0 := by decide
  have hen : IsNilpotent e := ⟨2, by decide⟩
  have hea : IsAddUnit e := ⟨⟨e, e, by decide, by decide⟩, rfl⟩
  let m : Unit →₀ ℕ := Finsupp.single () 1
  have hm : m ≠ 0 := by
    intro h
    have h' := congrArg (fun d : Unit →₀ ℕ => d ()) h
    simp [m] at h'
  let p : MvPolynomial Unit (ℕ × ZMod 4) := 1 + monomial m e
  have hc : IsUnit (p.coeff 0) := by
    simp [p, hm]
  have hpm : p.coeff m = e := by
    simp [p, coeff_one, Ne.symm hm]
  have hn : ∀ d ≠ 0, IsNilpotent (p.coeff d) ∧ IsAddUnit (p.coeff d) := by
    intro d hd
    by_cases hdm : d = m
    · subst d
      rw [hpm]
      exact ⟨hen, hea⟩
    · have hz : p.coeff d = 0 := by
        simp [p, coeff_one, Ne.symm hd, Ne.symm hdm]
      rw [hz]
      exact ⟨⟨1, by simp⟩, by simp⟩
  refine ⟨p, isUnit_of_coeff_isNilpotent_isAddUnit p hc hn, ?_, hc, hn⟩
  intro hp
  have hcoeff := congrArg (fun f : MvPolynomial Unit (ℕ × ZMod 4) => f.coeff m) hp
  rw [hpm, coeff_C_of_ne_zero hm] at hcoeff
  exact he hcoeff

/-- The coefficient semiring of the control is not additively a group. -/
private theorem one_not_isAddUnit_product : ¬ IsAddUnit (1 : ℕ × ZMod 4) := by
  rintro ⟨u, hu⟩
  have h : u.val.1 + u.neg.1 = 0 :=
    congrArg (fun x : ℕ × ZMod 4 => x.1) u.val_neg
  have hu1 : u.val.1 = 1 := congrArg (fun x : ℕ × ZMod 4 => x.1) hu
  rw [hu1] at h
  omega

/-- Empty variable types are included without a global decidable-equality premise. -/
private theorem empty_variables {R : Type u} [CommSemiring R]
    (p : MvPolynomial Empty R) (hc : IsUnit (p.coeff 0)) : IsUnit p := by
  apply isUnit_of_coeff_isNilpotent_isAddUnit p hc
  intro d hd
  exact (hd (Subsingleton.elim d 0)).elim

/-- The zero coefficient semiring is included. -/
private theorem zero_semiring {σ : Type v} (p : MvPolynomial σ (ZMod 1)) : IsUnit p := by
  apply isUnit_of_coeff_isNilpotent_isAddUnit p
  · have h : p.coeff 0 = 1 := Subsingleton.elim _ _
    rw [h]
    exact isUnit_one
  · intro d _
    have h : p.coeff d = 0 := Subsingleton.elim _ _
    rw [h]
    exact ⟨⟨1, by simp⟩, by simp⟩
