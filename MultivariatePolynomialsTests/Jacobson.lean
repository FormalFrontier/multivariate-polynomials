/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
import MultivariatePolynomials.Jacobson
import MultivariatePolynomials.CoefficientIdeal
import Mathlib.Tactic.NormNum

/-!
# Nilpotent constants and polynomial Jacobson radicals

In `MvPolynomial Unit (ZMod 4)`, `C 2` is nonzero and square-zero. Its second
power witnesses radical membership, and `Ideal.radical_le_jacobson` gives
Jacobson membership. Both ideals therefore contain a nonzero element. Over
the zero coefficient ring both ideals are zero.
-/

@[expose] public section

example :
    Ideal.jacobson (⊥ : Ideal (MvPolynomial Unit (ZMod 1))) =
      (⊥ : Ideal (MvPolynomial Unit (ZMod 1))).radical :=
  Subsingleton.elim _ _

example :
    ∃ p : MvPolynomial Unit (ZMod 4), p ≠ 0 ∧ p ^ 2 = 0 ∧
      p ∈ (⊥ : Ideal (MvPolynomial Unit (ZMod 4))).radical ∧
      p ∈ Ideal.jacobson (⊥ : Ideal (MvPolynomial Unit (ZMod 4))) :=
  let p : MvPolynomial Unit (ZMod 4) := MvPolynomial.C 2
  have hne : p ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (show (2 : ZMod 4) ≠ 0 from by decide)
  have hsquare : p ^ 2 = 0 := by
    simpa only [p, map_pow, map_zero] using
      congrArg (MvPolynomial.C : ZMod 4 →+* MvPolynomial Unit (ZMod 4))
        (show (2 : ZMod 4) ^ 2 = 0 from by decide)
  have hradical : p ∈ (⊥ : Ideal (MvPolynomial Unit (ZMod 4))).radical :=
    Ideal.mem_radical_iff.mpr
      ⟨2, by simpa only [Ideal.mem_bot] using hsquare⟩
  ⟨p, hne, hsquare, hradical, Ideal.radical_le_jacobson hradical⟩

example :
    Ideal.jacobson (⊥ : Ideal (MvPolynomial Unit (ZMod 4))) =
      (⊥ : Ideal (MvPolynomial Unit (ZMod 4))).radical :=
  Ideal.jacobson_bot_mvPolynomial

/-!
For the proper integer ideal `(4)`, the polynomial `C 2 * X ()` is nonzero and
belongs to the Jacobson radical of the extended ideal, but not to the extended
ideal itself. Its square lies in the extension, so this membership uses only
the inclusion of the radical in the Jacobson radical. The coefficient of the
variable excludes membership in the extension; the constant coefficient also
shows that the Jacobson radical remains proper.
-/

open MvPolynomial

/-- A nonconstant witness separates the extension of `(4)` from its proper
Jacobson radical over the integers. -/
theorem fourIdeal_twiceVariable_jacobson_facts :
    (C 2 * X () : MvPolynomial Unit ℤ) ≠ 0 ∧
      (C 2 * X () : MvPolynomial Unit ℤ) ∈
        Ideal.jacobson ((Ideal.span ({4} : Set ℤ)).map C) ∧
      (C 2 * X () : MvPolynomial Unit ℤ) ∉
        (Ideal.span ({4} : Set ℤ)).map C ∧
      (1 : MvPolynomial Unit ℤ) ∉
        Ideal.jacobson ((Ideal.span ({4} : Set ℤ)).map C) := by
  classical
  have hne : (C 2 * X () : MvPolynomial Unit ℤ) ≠ 0 := by
    intro h
    have hc := congrArg
      (fun q : MvPolynomial Unit ℤ => q.coeff (Finsupp.single () 1)) h
    rw [coeff_C_mul, coeff_X_same, mul_one] at hc
    norm_num at hc
  have h4 : (4 : ℤ) ∈ Ideal.span ({4} : Set ℤ) :=
    Ideal.subset_span (by simp)
  have hsquare : (C 2 * X () : MvPolynomial Unit ℤ) ^ 2 =
      C 4 * (X () : MvPolynomial Unit ℤ) ^ 2 := by
    rw [mul_pow, ← map_pow, show (2 : ℤ) ^ 2 = 4 by norm_num]
  have hsquare_mem : (C 2 * X () : MvPolynomial Unit ℤ) ^ 2 ∈
      (Ideal.span ({4} : Set ℤ)).map C := by
    rw [hsquare]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h4)
  have hradical : (C 2 * X () : MvPolynomial Unit ℤ) ∈
      ((Ideal.span ({4} : Set ℤ)).map C).radical :=
    Ideal.mem_radical_iff.mpr ⟨2, hsquare_mem⟩
  have hout : (C 2 * X () : MvPolynomial Unit ℤ) ∉
      (Ideal.span ({4} : Set ℤ)).map C := by
    intro h
    have hc := (mem_map_C_iff_coeff_mem.mp h) (Finsupp.single () 1)
    have hdiv : (4 : ℤ) ∣ 2 :=
      Ideal.mem_span_singleton.mp (by
        simpa only [coeff_C_mul, coeff_X_same, mul_one] using hc)
    norm_num at hdiv
  have hone : (1 : MvPolynomial Unit ℤ) ∉
      Ideal.jacobson ((Ideal.span ({4} : Set ℤ)).map C) := by
    intro h
    have htop : Ideal.jacobson
        ((Ideal.span ({4} : Set ℤ)).map (C : ℤ →+* MvPolynomial Unit ℤ)) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr h
    have hmaptop := Ideal.jacobson_eq_top_iff.mp htop
    have hmem : (1 : MvPolynomial Unit ℤ) ∈
        (Ideal.span ({4} : Set ℤ)).map C := by
      rw [hmaptop]
      trivial
    have hc := (mem_map_C_iff_coeff_mem.mp hmem) 0
    have hdiv : (4 : ℤ) ∣ 1 :=
      Ideal.mem_span_singleton.mp (by simpa using hc)
    norm_num at hdiv
  exact ⟨hne, Ideal.radical_le_jacobson hradical, hout, hone⟩

/-- The extension formula also proves membership of the nonconstant integer
polynomial directly from the coefficient radical. -/
example :
    (C 2 * X () : MvPolynomial Unit ℤ) ∈
      Ideal.jacobson ((Ideal.span ({4} : Set ℤ)).map C) := by
  have htwo : (2 : ℤ) ∈ (Ideal.span ({4} : Set ℤ)).radical :=
    Ideal.mem_radical_iff.mpr ⟨2, by
      change (2 : ℤ) ^ 2 ∈ Ideal.span ({4} : Set ℤ)
      rw [show (2 : ℤ) ^ 2 = 4 by norm_num]
      exact Ideal.subset_span (by simp)⟩
  rw [Ideal.jacobson_map_mvPolynomial_C]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ htwo)

universe u v

example {R : Type u} [CommRing R] {σ : Type v} :
    Ideal.jacobson ((⊤ : Ideal R).map (C : R →+* MvPolynomial σ R)) =
      (⊤ : Ideal R).radical.map (C : R →+* MvPolynomial σ R) := by
  rw [Ideal.map_top, Ideal.jacobson_top, Ideal.radical_top, Ideal.map_top]

