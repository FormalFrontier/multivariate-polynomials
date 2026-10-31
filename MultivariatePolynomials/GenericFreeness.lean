/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.LocalizedLeadingDivisors
public import MultivariatePolynomials.StandardMonomialBasis
public import MultivariatePolynomials.TensorQuotient
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Generic freeness for finite-type algebras

A finite-type commutative algebra over an integral domain becomes a free module after base change
to a suitable principal localization. The resulting free module need not have finite rank.

The proof selects finitely many leading monomials from the kernel of a polynomial presentation
using Mathlib's `Finsupp.wellQuasiOrderedLE` (Dickson's lemma). Denominator clearing uses
`MvPolynomial.isLocalization_coefficients` and `IsLocalization.mem_map_algebraMap_iff`.
After inverting the
product of the selected leading coefficients, `MonomialOrder.standardMonomialBasis`, built from
Mathlib's support-restricted polynomial basis, gives a basis of the localized quotient.

The quotient base-change equivalence uses Mathlib's `MvPolynomial.algebraTensorAlgEquiv` and
`Algebra.TensorProduct.tensorQuotientEquiv`. All algebra structures and the left tensor scalar
action are canonical.

## References

* The Stacks Project, Algebra, “Generic freeness” (Grothendieck's generic freeness lemma).
* Mathlib's formalizations of Dickson's lemma (`Finsupp.wellQuasiOrderedLE`), localization and
  algebraic pushouts (`Algebra.isLocalization_iff_isPushout`), the related polynomial-localization
  theorem (`MvPolynomial.isLocalization`), ideal denominator clearing
  (`IsLocalization.mem_map_algebraMap_iff`), and tensor quotient base change
  (`MvPolynomial.algebraTensorAlgEquiv` and `Algebra.TensorProduct.tensorQuotientEquiv`).
* `MonomialOrder.standardMonomialBasis` and Mathlib's support-restricted polynomial bases.
-/

@[expose] public section

universe u v w

open scoped BigOperators TensorProduct

namespace MonomialOrder

private theorem exists_free_localizationAway_quotient
    {A : Type u} {σ : Type w} [CommRing A] [IsDomain A] [Finite σ]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ A)) :
    ∃ a : A, a ≠ 0 ∧ Module.Free (Localization.Away a)
      (MvPolynomial σ (Localization.Away a) ⧸
        I.map (MvPolynomial.map (algebraMap A (Localization.Away a)))) := by
  classical
  obtain ⟨t, ht, ht_le⟩ := m.exists_finset_leading_divisors (I : Set (MvPolynomial σ A))
  let a : A := ∏ q ∈ t, m.leadingCoeff q
  have ha : a ≠ 0 := by
    apply (Finset.prod_ne_zero_iff).2
    intro q hq
    exact (m.leadingCoeff_ne_zero_iff).2 (ht q hq).2
  have hinj : Function.Injective (algebraMap A (Localization.Away a)) :=
    IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hunit (q : t) : IsUnit (m.leadingCoeff
      (MvPolynomial.map (algebraMap A (Localization.Away a)) q.val)) := by
    rw [m.leadingCoeff_map_of_injective _ hinj]
    exact IsLocalization.Away.isUnit_of_dvd (S := Localization.Away a) a
      (Finset.dvd_prod_of_mem (fun p => m.leadingCoeff p) q.property)
  have hlead : ∀ p ∈ I, p ≠ 0 → ∃ q : t, m.degree q.val ≤ m.degree p := by
    intro p hp hp0
    obtain ⟨q, hqt, hqp⟩ := ht_le p hp hp0
    exact ⟨⟨q, hqt⟩, hqp⟩
  refine ⟨a, ha, Module.Free.of_basis (m.standardMonomialBasis
    (I.map (MvPolynomial.map (algebraMap A (Localization.Away a))))
    (fun q : t => MvPolynomial.map (algebraMap A (Localization.Away a)) q.val)
    ?_ hunit ?_)⟩
  · intro q
    exact Ideal.mem_map_of_mem _ (ht q.val q.property).1
  · intro p hp hp0
    exact m.exists_degree_map_le_of_mem_ideal_map (Submonoid.powers a) hinj I
      (fun q : t => q.val) hlead p hp hp0

end MonomialOrder

namespace Algebra.FiniteType

/-- Grothendieck's generic freeness lemma for finite-type commutative algebras over an integral
domain: some principal localization makes the base-changed algebra a free module.

See The Stacks Project, Algebra, “Generic freeness”. Neither a Noetherian hypothesis on the domain
nor finite presentation of the algebra is required, and the free module can have infinite rank. -/
theorem exists_free_localizationAway
    {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] :
    ∃ a : A, a ≠ 0 ∧
      Module.Free (Localization.Away a) (Localization.Away a ⊗[A] B) := by
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let I : Ideal (MvPolynomial (Fin n) A) := RingHom.ker f
  obtain ⟨a, ha, hfree⟩ := MonomialOrder.exists_free_localizationAway_quotient
    (MonomialOrder.lex (σ := Fin n)) I
  refine ⟨a, ha, ?_⟩
  let _ : Module.Free (Localization.Away a)
      (MvPolynomial (Fin n) (Localization.Away a) ⧸
        I.map (MvPolynomial.map (algebraMap A (Localization.Away a)))) := hfree
  let e := (MvPolynomial.tensorQuotientAlgEquiv (S := Localization.Away a) I).symm.trans
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : Localization.Away a ≃ₐ[Localization.Away a] Localization.Away a)
      (Ideal.quotientKerAlgEquivOfSurjective hf))
  exact Module.Free.of_equiv e.toLinearEquiv

end Algebra.FiniteType
