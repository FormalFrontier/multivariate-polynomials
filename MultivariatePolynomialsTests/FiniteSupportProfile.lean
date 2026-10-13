/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Basic

/-!
# Degree and support-cardinality profiles of exponent vectors

These examples use the profile `d ↦ (d.degree, d.support.card)` and aggregate
coefficient arrays with `Finsupp.mapDomain`. The two basis exponent vectors on
`Fin 2` have the same profile. Their distinct natural coefficient arrays therefore
have the same nonzero image, ruling out recovery by any total function, without
assuming an additive, linear or multiplicative decoder.

Doubling one basis vector also distinguishes the profile of a sum from the sum
of the profiles. With empty or singleton variable types the profile instead
retains the exponent vector; in the singleton case its degree coordinate already
suffices. With coefficients in `ZMod 1`, every coefficient array is zero and the
constant-zero function recovers every array, for any variable type.

The calculations use Mathlib's `Finsupp.degree_single`, `Finsupp.support_single`,
`Finsupp.mapDomain_single` and `Finsupp.unique_single`. No additional aggregation
operation or algebraic structure on the profile map is introduced.
-/

namespace FiniteSupportProfile

/-! ## Two variables and natural coefficients -/

private theorem fin_two_basis_ne :
    (Finsupp.single (0 : Fin 2) (1 : ℕ)) ≠ Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hindex : (0 : Fin 2) = 1 :=
    Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) h
  exact (by decide : (0 : Fin 2) ≠ 1) hindex

private theorem fin_two_zero_profile :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (0 : Fin 2) 1) = (1, 1) := by
  simp

private theorem fin_two_one_profile :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (1 : Fin 2) 1) = (1, 1) := by
  simp

private theorem fin_two_profile_not_injective :
    ¬ Function.Injective (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) := by
  intro h
  exact fin_two_basis_ne
    (h (fin_two_zero_profile.trans fin_two_one_profile.symm))

private theorem fin_two_nat_arrays_ne :
    (Finsupp.single (Finsupp.single (0 : Fin 2) (1 : ℕ)) (1 : ℕ) :
      (Fin 2 →₀ ℕ) →₀ ℕ) ≠
        Finsupp.single (Finsupp.single (1 : Fin 2) 1) 1 := by
  intro h
  exact fin_two_basis_ne
    (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) h)

private theorem fin_two_nat_zero_array_profile :
    Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (Finsupp.single (0 : Fin 2) (1 : ℕ)) (1 : ℕ)) =
        Finsupp.single (1, 1) 1 := by
  rw [Finsupp.mapDomain_single]
  exact congrArg (fun label : ℕ × ℕ => Finsupp.single label (1 : ℕ)) fin_two_zero_profile

private theorem fin_two_nat_one_array_profile :
    Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (Finsupp.single (1 : Fin 2) (1 : ℕ)) (1 : ℕ)) =
        Finsupp.single (1, 1) 1 := by
  rw [Finsupp.mapDomain_single]
  exact congrArg (fun label : ℕ × ℕ => Finsupp.single label (1 : ℕ)) fin_two_one_profile

private theorem fin_two_nat_profile_image_ne_zero :
    (Finsupp.single (1, 1) (1 : ℕ) : (ℕ × ℕ) →₀ ℕ) ≠ 0 := by
  exact Finsupp.single_ne_zero.mpr (by decide : (1 : ℕ) ≠ 0)

private theorem fin_two_nat_profile_not_injective :
    ¬ Function.Injective
      (Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) :
        ((Fin 2 →₀ ℕ) →₀ ℕ) → ((ℕ × ℕ) →₀ ℕ)) := by
  intro h
  exact fin_two_nat_arrays_ne
    (h (fin_two_nat_zero_array_profile.trans fin_two_nat_one_array_profile.symm))

/-- A decoder here is an arbitrary total function on profile coefficient arrays.
The source of `mapDomain` is inhabited by its zero coefficient array. -/
private theorem fin_two_nat_profile_no_decoder :
    ¬ Function.HasLeftInverse
      (Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) :
        ((Fin 2 →₀ ℕ) →₀ ℕ) → ((ℕ × ℕ) →₀ ℕ)) := by
  exact Function.injective_iff_hasLeftInverse.not.mp fin_two_nat_profile_not_injective

/-! ## The support statistic is not additive -/

private theorem fin_two_doubled_basis_profile :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1) = (2, 1) := by
  have hsum : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1 :
      Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 2 :=
    (Finsupp.single_add (0 : Fin 2) (1 : ℕ) 1).symm
  simp only [hsum, Finsupp.degree_single,
    Finsupp.support_single (0 : Fin 2) (by decide : (2 : ℕ) ≠ 0),
    Finset.card_singleton]

private theorem fin_two_profile_not_additive :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1) ≠
      (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
          (Finsupp.single (0 : Fin 2) 1) +
        (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
          (Finsupp.single (0 : Fin 2) 1) := by
  intro h
  simp only [fin_two_doubled_basis_profile, fin_two_zero_profile] at h
  have hcard : (1 : ℕ) = 2 := congrArg Prod.snd h
  exact (by decide : (1 : ℕ) ≠ 2) hcard

/-! ## Empty and singleton variable types -/

private theorem empty_profile_value {σ : Type*} [IsEmpty σ] (d : σ →₀ ℕ) :
    (fun d : σ →₀ ℕ => (d.degree, d.support.card)) d = (0, 0) := by
  have hzero : d = 0 := Subsingleton.elim _ _
  simp [hzero]

private theorem empty_profile_injective {σ : Type*} [IsEmpty σ] :
    Function.Injective (fun d : σ →₀ ℕ => (d.degree, d.support.card)) := by
  exact Function.injective_of_subsingleton _

private theorem unique_exponent_from_degree {σ : Type*} [Unique σ] (d : σ →₀ ℕ) :
    Finsupp.single (default : σ) d.degree = d := by
  have hdegree : d.degree = d default := by
    simpa only [Finsupp.degree_single] using
      congrArg (fun e : σ →₀ ℕ => e.degree) (Finsupp.unique_single d)
  rw [hdegree]
  exact (Finsupp.unique_single d).symm

private theorem unique_profile_injective {σ : Type*} [Unique σ] :
    Function.Injective (fun d : σ →₀ ℕ => (d.degree, d.support.card)) := by
  intro d e h
  have hdegree : d.degree = e.degree := congrArg Prod.fst h
  calc
    d = Finsupp.single (default : σ) d.degree := (unique_exponent_from_degree d).symm
    _ = Finsupp.single (default : σ) e.degree :=
      congrArg (Finsupp.single (default : σ)) hdegree
    _ = e := unique_exponent_from_degree e

/-! ## Trivial coefficients on arbitrary variable types -/

private theorem zmod_one_profile_arrays_zero {σ : Type*}
    (coefficients : (σ →₀ ℕ) →₀ ZMod 1) :
    coefficients = 0 ∧
      Finsupp.mapDomain (fun d : σ →₀ ℕ => (d.degree, d.support.card)) coefficients = 0 := by
  constructor <;> exact Subsingleton.elim _ _

private theorem zmod_one_zero_decoder_recovers {σ : Type*} :
    Function.LeftInverse
      (fun _ : (ℕ × ℕ) →₀ ZMod 1 => (0 : (σ →₀ ℕ) →₀ ZMod 1))
      (Finsupp.mapDomain (fun d : σ →₀ ℕ => (d.degree, d.support.card))) := by
  intro coefficients
  exact Subsingleton.elim _ _

end FiniteSupportProfile
