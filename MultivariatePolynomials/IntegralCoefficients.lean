/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Nilpotent
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Integral multivariate polynomials and their coefficients

A multivariate polynomial over a commutative ring is integral over its coefficient
ring exactly when every nonconstant coefficient is nilpotent. The scalar action
is the canonical coefficient algebra, and the variable type is arbitrary.
For reduced coefficient rings, `MvPolynomial.isIntegral_iff_eq_C_coeff_zero`
identifies the integral polynomials with their constant coefficients.

The polynomial `C (2 : ZMod 4) * X ()` is square-zero, integral over `ZMod 4`,
and nonconstant. Thus nilpotent coefficients cannot be replaced by zero
coefficients in this criterion. Constants with an empty variable type supply a
boundary case.

For sufficiency, subtract the constant coefficient and use coefficientwise
nilpotence. For necessity, map into fraction fields of prime quotients. An
integral polynomial over a field is either zero or a unit, so its nonconstant
coefficients vanish; membership in every prime ideal gives coefficient nilpotence.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic`, for the canonical coefficient
  algebra and coefficient formulas.
* `MultivariatePolynomials.Nilpotent`, for coefficientwise nilpotence of
  multivariate polynomials, extending `Mathlib.Algebra.MvPolynomial.Nilpotent`.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Nilpotent`, for the coefficient criterion
  for polynomial units.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`, for integrality
  of constants, zero, and elements with an integral positive power.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, for closure of
  integral elements under addition.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`, for units
  among nonzero integral elements over a field.
* Mathlib, `Mathlib.RingTheory.Nilpotent.Lemmas`, for the prime-ideal criterion
  for nilpotence.
* Mathlib, `Mathlib.RingTheory.Localization.FractionRing`, for fraction fields.
* Mathlib, `Mathlib.Data.ZMod.Basic`, for residue-class coefficient rings.
-/

@[expose] public section

universe u v

namespace MvPolynomial

private theorem isIntegral_of_coeff_isNilpotent {R : Type u} [CommRing R] {σ : Type v}
    (p : MvPolynomial σ R)
    (h : ∀ d : σ →₀ ℕ, d ≠ 0 → IsNilpotent (p.coeff d)) : IsIntegral R p := by
  classical
  have hnil : IsNilpotent (p - C (p.coeff 0)) := by
    rw [isNilpotent_iff_coeff]
    intro d
    by_cases hd : d = 0
    · subst d
      rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_zero_C, sub_self]
      exact IsNilpotent.zero
    · rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_C_of_ne_zero hd, sub_zero]
      exact h d hd
  obtain ⟨n, hn⟩ := hnil
  have htail : IsIntegral R (p - C (p.coeff 0)) := by
    apply IsIntegral.of_pow (n := n + 1) (Nat.succ_pos n)
    rw [pow_succ, hn, zero_mul]
    exact isIntegral_zero
  have hconst : IsIntegral R (C (p.coeff 0) : MvPolynomial σ R) :=
    isIntegral_algebraMap
  simpa only [sub_add_cancel] using htail.add hconst

private theorem coeff_eq_zero_of_isIntegral {K : Type u} [Field K] {τ : Type v}
    (q : MvPolynomial τ K) (hq : IsIntegral K q) (d : τ →₀ ℕ) (hd : d ≠ 0) :
    q.coeff d = 0 := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · exact ((MvPolynomial.isUnit_iff.mp (hq.isUnit hq0)).2 d hd).eq_zero

private theorem coeff_isNilpotent_of_isIntegral {R : Type u} [CommRing R] {σ : Type v}
    (p : MvPolynomial σ R) (hp : IsIntegral R p) (d : σ →₀ ℕ) (hd : d ≠ 0) :
    IsNilpotent (p.coeff d) := by
  apply nilpotent_iff_mem_prime.mpr
  intro I hI
  let : I.IsPrime := hI
  let K := FractionRing (R ⧸ I)
  let f : R →+* K :=
    (algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I)
  have hmap : IsIntegral K (map f p) := by
    apply IsIntegral.map_of_comp_eq f (map f) ?_ hp
    ext r
    simp only [RingHom.comp_apply, algebraMap_eq, map_C]
  have hcoeff : f (p.coeff d) = 0 := by
    simpa only [coeff_map] using
      coeff_eq_zero_of_isIntegral (map f p) hmap d hd
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (R ⧸ I) K
  simpa only [f, RingHom.comp_apply, map_zero] using hcoeff

/-- A multivariate polynomial is integral over its coefficient ring if and only
if all coefficients of nonconstant monomials are nilpotent. -/
theorem isIntegral_iff_coeff_isNilpotent {R : Type u} [CommRing R] {σ : Type v}
    (p : MvPolynomial σ R) :
    IsIntegral R p ↔ ∀ d : σ →₀ ℕ, d ≠ 0 → IsNilpotent (p.coeff d) := by
  constructor
  · exact coeff_isNilpotent_of_isIntegral p
  · exact isIntegral_of_coeff_isNilpotent p

/-- Over a reduced coefficient ring, a multivariate polynomial is integral if and
only if it equals the constant polynomial given by its constant coefficient. -/
theorem isIntegral_iff_eq_C_coeff_zero {R : Type u} [CommRing R] [IsReduced R]
    {σ : Type v} (p : MvPolynomial σ R) :
    IsIntegral R p ↔ p = C (p.coeff 0) := by
  classical
  rw [isIntegral_iff_coeff_isNilpotent]
  constructor
  · intro hp
    ext d
    by_cases hd : d = 0
    · subst d
      simp only [coeff_zero_C]
    · rw [coeff_C_of_ne_zero hd]
      exact (hp d hd).eq_zero
  · intro hp d hd
    rw [hp, coeff_C_of_ne_zero hd]
    exact IsNilpotent.zero

/-- A nonconstant square-zero polynomial over the residue ring modulo four. -/
private theorem zmod_four_square_zero_integral_nonconstant :
    (C (2 : ZMod 4) * X () : MvPolynomial Unit (ZMod 4)) ^ 2 = 0 ∧
      IsIntegral (ZMod 4) (C (2 : ZMod 4) * X () : MvPolynomial Unit (ZMod 4)) ∧
      ∀ r : ZMod 4, (C (2 : ZMod 4) * X () : MvPolynomial Unit (ZMod 4)) ≠ C r := by
  have htwo_sq : (2 : ZMod 4) ^ 2 = 0 := by decide
  have hsq : (C (2 : ZMod 4) * X () : MvPolynomial Unit (ZMod 4)) ^ 2 = 0 := by
    rw [mul_pow, ← map_pow, htwo_sq, map_zero, zero_mul]
  refine ⟨hsq, ?_, ?_⟩
  · apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hsq]
    exact isIntegral_zero
  · intro r h
    have hd : (Finsupp.single () 1 : Unit →₀ ℕ) ≠ 0 := by simp
    have hc := congrArg (fun q : MvPolynomial Unit (ZMod 4) =>
      q.coeff (Finsupp.single () 1)) h
    have htwo_ne : (2 : ZMod 4) ≠ 0 := by decide
    apply htwo_ne
    simpa only [coeff_C_mul, coeff_X_same, mul_one, coeff_C_of_ne_zero hd] using hc

/-- Constant polynomials remain integral when there are no variables. -/
private theorem empty_variables_constant_isIntegral (r : ℤ) :
    IsIntegral ℤ (C r : MvPolynomial Empty ℤ) := by
  exact isIntegral_algebraMap

/-- The square-zero polynomial `2X` over `ZMod 4` is integral. -/
private theorem zmod_four_nonconstant_isIntegral :
    IsIntegral (ZMod 4) (C (2 : ZMod 4) * X () : MvPolynomial Unit (ZMod 4)) := by
  have hnil : IsNilpotent (C (2 : ZMod 4) * X () : MvPolynomial Unit (ZMod 4)) :=
    ⟨2, zmod_four_square_zero_integral_nonconstant.1⟩
  exact (isIntegral_iff_coeff_isNilpotent _).mpr fun d _ ↦
    (isNilpotent_iff_coeff _).mp hnil d

end MvPolynomial
