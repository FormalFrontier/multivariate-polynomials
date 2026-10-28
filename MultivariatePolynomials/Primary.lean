/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdeal
public import MultivariatePolynomials.CoefficientIdealSubtractive
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Fintype.Option
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Primary coefficient ideals

Extension along the constant-polynomial homomorphism preserves primary ideals
of a commutative semiring when the coefficient ideal satisfies
`a ∈ I → a + b ∈ I → b ∈ I`. If there is a variable, this condition is also
necessary. The coefficient and variable universes are independent.

The semiring argument by Formal Frontier contributors uses finite coefficient
filters, power peeling with one retained factor, and indexed product and power
coefficients for a monomial order. It does not require cancellation or
non-zero-divisor hypotheses. In a commutative ring membership subtraction is
automatic, giving the primary-extension equivalence for every variable type,
including the empty type. All statements quantify over every ideal, including
the top ideal.

Over rings, the persistence result also admits an approach through McCoy's
theorem, polynomial nilpotence and finite-variable presentations; the relevant
Mathlib interfaces remain re-exported by this module.

## References

* Mathlib's `Mathlib.RingTheory.MvPolynomial.MonomialOrder` supplies the
  fixed-index product and power coefficient identities and degree bounds.
* `MultivariatePolynomials.CoefficientIdealSubtractive` supplies coefficientwise
  ideal membership, subtractivity and radical commutation.

* Mathlib's `Mathlib.Algebra.Polynomial.AlgebraMap`, by Chris Hughes,
  Johannes Hölzl, Kim Morrison and Jens Wagemaker, supplies the univariate
  McCoy theorem `Polynomial.notMem_nonZeroDivisors_iff`.
* `Mathlib.RingTheory.Polynomial.Nilpotent`, by Emilie Uthaiwat and Oliver
  Nash (copyright 2023 Oliver Nash), supplies `Polynomial.isNilpotent_iff`.
* `Mathlib.Algebra.MvPolynomial.Nilpotent`, by Andrew Yang (copyright 2025
  Andrew Yang), provides a finite-variable induction approach to nilpotence.
  These Mathlib sources are released under the Apache 2.0 license.
* `Mathlib.Algebra.MvPolynomial.Rename` supplies the joint finite-variable
  presentation `exists_finset_rename₂`; `Mathlib.Algebra.MvPolynomial.Equiv`
  supplies the empty-variable and option-variable equivalences.
* `Mathlib.RingTheory.Ideal.IsPrimary`, by Kenny Lau and Yakov Pechersky,
  supplies the stock primary criterion and contraction theorem. The
  quotient kernel and coefficient kernel APIs identify the extended ideal.
-/

@[expose] public section

universe u v

namespace MvPolynomial

section Semiring

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- Extension of a subtractive primary ideal to multivariate polynomials is primary,
including when the variable type is empty. -/
theorem isPrimary_map_C_of_subtractive (I : Ideal R) (hI : I.IsPrimary)
    (hsub : ∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrimary := by
  classical
  let J : Ideal (MvPolynomial σ R) := I.map C
  have hsubJ := (subtractive_map_C_iff (σ := σ) I).2 hsub
  have hrad : J.radical = I.radical.map C := radical_map_C_of_subtractive I hsub
  -- The two finite coefficient filters give a decomposition for either ideal.
  have split (K : Ideal R) (p : MvPolynomial σ R) :
      ∃ p₁ p₂ : MvPolynomial σ R, p₁ + p₂ = p ∧ p₁ ∈ K.map C ∧
        ∀ d, p₂.coeff d ≠ 0 → p₂.coeff d ∉ K := by
    let p₁ : MvPolynomial σ R := ⟨Finsupp.filter (fun d => p.coeff d ∈ K) p.coeff⟩
    let p₂ : MvPolynomial σ R := ⟨Finsupp.filter (fun d => ¬ p.coeff d ∈ K) p.coeff⟩
    refine ⟨p₁, p₂, ?_, ?_, ?_⟩
    · apply MvPolynomial.ext
      intro d
      simpa only [p₁, p₂, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
        congrArg (fun q : (σ →₀ ℕ) →₀ R => q d)
          (Finsupp.filter_add_filter_not p.coeff (fun d => p.coeff d ∈ K))
    · apply mem_map_C_iff_coeff_mem.mpr
      intro d
      simp only [p₁, Finsupp.filter_apply]
      split_ifs with h
      · exact h
      · exact K.zero_mem
    · intro d hd
      simp only [p₂, Finsupp.filter_apply] at hd ⊢
      by_cases h : p.coeff d ∈ K <;> simp_all
  change J.IsPrimary
  refine Ideal.isPrimary_iff.mpr ⟨?_, ?_⟩
  · intro htop
    apply hI.ne_top
    have hc := congrArg (Ideal.comap (C : R →+* MvPolynomial σ R)) htop
    simpa only [J, comap_map_C, Ideal.comap_top] using hc
  · intro f g hfg
    by_cases hf : f ∈ J
    · exact Or.inl hf
    right
    by_contra hg
    obtain ⟨fin, F, hfs, hfin, hFout⟩ := split I f
    have hF : F ∉ J := by
      intro h
      apply hf
      rw [← hfs]
      exact J.add_mem hfin h
    have hF0 : F ≠ 0 := by
      intro h
      apply hF
      rw [h]
      exact J.zero_mem
    have hfinmul : fin * g ∈ J := by
      simpa only [mul_comm] using J.mul_mem_left g hfin
    have hsum : fin * g + F * g ∈ J := by
      rw [← add_mul, hfs]
      exact hfg
    have hFg : F * g ∈ J := hsubJ _ _ hfinmul hsum
    obtain ⟨u, v, hgs, huI, hvout⟩ := split I.radical g
    have hu : u ∈ J.radical := by
      rw [hrad]
      exact huI
    have hv : v ≠ 0 := by
      intro h
      apply hg
      rw [← hgs, h, add_zero]
      exact hu
    obtain ⟨n, hun⟩ := Ideal.mem_radical_iff.mp hu
    have hFuv : F * (u + v) ∈ J := by
      rw [hgs]
      exact hFg
    have hFvn : F * v ^ n ∈ J :=
      J.mul_pow_mem_of_mul_add_mem_of_mul_pow_mem hsubJ F u v n hFuv
        (J.mul_mem_left F hun)
    obtain ⟨ord, hwf⟩ := exists_wellFoundedGT σ
    let : LinearOrder σ := ord
    let : WellFoundedGT σ := hwf
    let m : MonomialOrder.{v, v} σ := MonomialOrder.lex
    have ha : m.leadingCoeff F ∉ I :=
      hFout _ (m.leadingCoeff_ne_zero_iff.mpr hF0)
    have hb : m.leadingCoeff v ∉ I.radical :=
      hvout _ (m.leadingCoeff_ne_zero_iff.mpr hv)
    have hab : m.leadingCoeff F * m.leadingCoeff v ^ n ∈ I := by
      have hc := (mem_map_C_iff_coeff_mem.mp hFvn) (m.degree F + n • m.degree v)
      rw [m.coeff_mul_of_add_of_degree_le (f := F) (g := v ^ n) le_rfl
        (m.degree_pow_le (f := v) n), m.coeff_pow_nsmul_degree v n] at hc
      exact hc
    rcases (Ideal.isPrimary_iff.mp hI).2 hab with ha' | hb'
    · exact ha ha'
    · apply hb
      obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hb'
      exact Ideal.mem_radical_iff.mpr ⟨n * k, by simpa only [pow_mul] using hk⟩

/-- With a nonempty variable type, primaryness of a coefficient extension is
equivalent to primaryness and subtractivity of the coefficient ideal. -/
theorem isPrimary_map_C_iff_subtractive [Nonempty σ] (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrimary ↔
      I.IsPrimary ∧ (∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [comap_map_C] using h.comap (C : R →+* MvPolynomial σ R)
    · intro a b ha hab
      exact mem_of_add_mem_of_isPrimary_map_C I h ha hab
  · rintro ⟨hI, hsub⟩
    exact isPrimary_map_C_of_subtractive I hI hsub

end Semiring

section Ring

variable {R : Type u} {σ : Type v} [CommRing R]

/-- A coefficient ideal is primary if and only if its extension to multivariate
polynomials is primary. -/
theorem isPrimary_map_C_iff (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrimary ↔ I.IsPrimary := by
  constructor
  · intro h
    simpa only [comap_map_C] using h.comap (C : R →+* MvPolynomial σ R)
  · intro hI
    apply isPrimary_map_C_of_subtractive I hI
    intro a b ha hab
    simpa using I.sub_mem hab ha

end Ring

end MvPolynomial
