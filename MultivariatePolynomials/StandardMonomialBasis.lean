/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.LinearDivision
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic

set_option warningAsError true

/-!
# Standard monomials in a polynomial quotient

Let `g` be a family in an ideal `I`, with unit leading coefficients. If the leading
exponent of every nonzero element of `I` is divisible by a leading exponent of `g`,
then the monomials outside those leading cones form a basis of the quotient by `I`.
Divisibility here is the componentwise order on exponent vectors, not the chosen
monomial order.

The quotient map restricts to a linear equivalence on `MvPolynomial.restrictSupport`.
The basis is the image of `MvPolynomial.basisRestrictSupport` under this equivalence,
and its coordinates are the coefficients of the fixed linear division remainder.

## References

* Mathlib, `Mathlib.RingTheory.MvPolynomial.Groebner`: Antoine Chambert-Loir's
  division theorem, used by the fixed linear division operators.
* Mathlib, `Mathlib.RingTheory.MvPolynomial.Basic`: the canonical restricted-support
  submodule and its monomial basis.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {σ : Type u} {R : Type w} [CommSemiring R]

/-- Restricted-support monomial coordinates are polynomial coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (D : Set (σ →₀ ℕ))
    (p : restrictSupport R D) (d : D) :
    (basisRestrictSupport R D).repr p d = (p : MvPolynomial σ R).coeff d.1 :=
  rfl

/-- A restricted-support basis vector is its monomial with coefficient one. -/
@[simp]
theorem basisRestrictSupport_apply (D : Set (σ →₀ ℕ)) (d : D) :
    (basisRestrictSupport R D d : MvPolynomial σ R) = monomial d.1 (1 : R) := by
  classical
  apply (AddMonoidAlgebra.coeffLinearEquiv R).injective
  change ((Finsupp.supportedEquivFinsupp (R := R) D).symm
    (Finsupp.single d (1 : R)) : (σ →₀ ℕ) →₀ R) = Finsupp.single d.1 (1 : R)
  exact Finsupp.supportedEquivFinsupp_symm_single D d 1

end MvPolynomial

namespace MonomialOrder

open MvPolynomial

variable {σ : Type u} {ι : Type v} {R : Type w}

section CommSemiring

variable [CommSemiring R]

/-- Leading-divisor coverage forces a standard-supported polynomial in `I` to vanish. -/
theorem eq_zero_of_mem_ideal_of_restrictSupport (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p)
    (p : MvPolynomial σ R) (hpI : p ∈ I)
    (hp : p ∈ restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}) :
    p = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := hlead p hpI hne
  rw [mem_restrictSupport_iff] at hp
  exact hp (m.degree_mem_support hne) i hi

end CommSemiring

variable [CommRing R]

/-- The fixed division remainder belongs to the submodule supported on the standard
exponents. -/
theorem linearDivision_remainder_mem_restrictSupport (m : MonomialOrder σ)
    (g : ι → MvPolynomial σ R) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (p : MvPolynomial σ R) :
    linearDivisionRemainder m g hunit p ∈
      restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d} := by
  rw [mem_restrictSupport_iff]
  exact linearDivision_remainder_support m g hunit p

/-- Division by polynomials in `I` does not change the class in the quotient by `I`. -/
theorem quotient_linearDivisionRemainder (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (p : MvPolynomial σ R) :
    Ideal.Quotient.mk I (linearDivisionRemainder m g hunit p) =
      Ideal.Quotient.mk I p := by
  classical
  have hmem : Finsupp.linearCombination (MvPolynomial σ R) g
      (linearDivisionQuotient m g hunit p) ∈ I := by
    rw [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem I (fun i _ => I.smul_mem _ (hgI i))
  have h := congrArg (Ideal.Quotient.mk I) (linearDivision_decomposition m g hunit p)
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_add] at h
  exact h.symm

/-- The quotient map is bijective on the submodule supported outside all leading cones. -/
theorem standardMonomialQuotient_bijective (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p) :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).toLinearMap.comp
        (restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}).subtype) := by
  constructor
  · intro p q hpq
    have hmem : (p : MvPolynomial σ R) - (q : MvPolynomial σ R) ∈ I :=
      Ideal.Quotient.eq.mp hpq
    have hzero : (p : MvPolynomial σ R) - (q : MvPolynomial σ R) = 0 :=
      eq_zero_of_mem_ideal_of_restrictSupport m I g hlead _ hmem
        ((restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}).sub_mem
          p.property q.property)
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨⟨linearDivisionRemainder m g hunit p,
      linearDivision_remainder_mem_restrictSupport m g hunit p⟩, ?_⟩
    exact quotient_linearDivisionRemainder m I g hgI hunit p

/-- Restricting the quotient map to standard-supported polynomials gives a linear
equivalence with the quotient. -/
noncomputable def standardMonomialEquiv (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p) :
    restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d} ≃ₗ[R]
      (MvPolynomial σ R ⧸ I) :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp
      (restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}).subtype)
    (standardMonomialQuotient_bijective m I g hgI hunit hlead)

/-- The restricted-support equivalence sends a polynomial to its quotient class. -/
@[simp]
theorem standardMonomialEquiv_apply (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p)
    (p : restrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}) :
    standardMonomialEquiv m I g hgI hunit hlead p = Ideal.Quotient.mk I p :=
  rfl

/-- The inverse of the restricted quotient map selects the fixed division remainder. -/
@[simp]
theorem standardMonomialEquiv_symm_mk (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p)
    (p : MvPolynomial σ R) :
    (standardMonomialEquiv m I g hgI hunit hlead).symm (Ideal.Quotient.mk I p) =
      ⟨linearDivisionRemainder m g hunit p,
        linearDivision_remainder_mem_restrictSupport m g hunit p⟩ := by
  apply (standardMonomialEquiv m I g hgI hunit hlead).injective
  simpa only [LinearEquiv.apply_symm_apply, standardMonomialEquiv_apply] using
    (quotient_linearDivisionRemainder m I g hgI hunit p).symm

/-- The quotient basis consisting of monomials not divisible by a leading monomial
of the given family. -/
noncomputable def standardMonomialBasis
    {σ : Type u} {ι : Type v} {R : Type w} [CommRing R]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I)
    (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p) :
    Module.Basis {d : σ →₀ ℕ // ∀ i, ¬ m.degree (g i) ≤ d} R (MvPolynomial σ R ⧸ I) :=
  (basisRestrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}).map
    (standardMonomialEquiv m I g hgI hunit hlead)

/-- A standard-monomial basis vector is the class of its monomial with coefficient one. -/
@[simp]
theorem standardMonomialBasis_apply (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p)
    (d : {d : σ →₀ ℕ // ∀ i, ¬ m.degree (g i) ≤ d}) :
    standardMonomialBasis m I g hgI hunit hlead d =
      Ideal.Quotient.mk I (monomial d.1 (1 : R)) := by
  rw [standardMonomialBasis, Module.Basis.map_apply, standardMonomialEquiv_apply]
  exact congrArg (Ideal.Quotient.mk I)
    (basisRestrictSupport_apply (R := R) _ d)

/-- The coordinates of a quotient class are the coefficients of its fixed division
remainder at the standard exponents. -/
@[simp]
theorem standardMonomialBasis_repr_mk (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (g : ι → MvPolynomial σ R)
    (hgI : ∀ i, g i ∈ I) (hunit : ∀ i, IsUnit (m.leadingCoeff (g i)))
    (hlead : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (g i) ≤ m.degree p)
    (p : MvPolynomial σ R)
    (d : {d : σ →₀ ℕ // ∀ i, ¬ m.degree (g i) ≤ d}) :
    (standardMonomialBasis m I g hgI hunit hlead).repr (Ideal.Quotient.mk I p) d =
      (linearDivisionRemainder m g hunit p).coeff d.1 := by
  change (basisRestrictSupport R {d : σ →₀ ℕ | ∀ i, ¬ m.degree (g i) ≤ d}).repr
    ((standardMonomialEquiv m I g hgI hunit hlead).symm (Ideal.Quotient.mk I p)) d = _
  rw [standardMonomialEquiv_symm_mk, basisRestrictSupport_repr_apply]

end MonomialOrder
