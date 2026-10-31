/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Scalar extension of polynomial quotients

For an algebra `S` over a commutative ring `R`, scalar extension of a quotient of
`MvPolynomial σ R` is the quotient of `MvPolynomial σ S` by the extended ideal.
The equivalence uses the left `S`-algebra structure on the tensor product and
requires neither flatness nor a finiteness assumption on the ideal or variables.

## References

The construction composes Mathlib's `MvPolynomial.algebraTensorAlgEquiv`,
`Algebra.TensorProduct.tensorQuotientEquiv`, and `Ideal.quotientEquivAlg`.
-/

@[expose] public section

open TensorProduct

namespace MvPolynomial

universe u v w

variable {σ : Type u} {R : Type v} {S : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension commutes with quotienting a multivariate polynomial ring by
an arbitrary ideal, using the left scalar action on the tensor product. -/
noncomputable def tensorQuotientAlgEquiv (I : Ideal (MvPolynomial σ R)) :
    S ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[S]
      MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial σ R) S I).trans
    (Ideal.quotientEquivAlg _ _ (algebraTensorAlgEquiv R S) (by
      rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight
        (R := R) (A := S) (B := MvPolynomial σ R)) I, Ideal.map_map]
      apply congrArg (fun f : MvPolynomial σ R →+* MvPolynomial σ S => I.map f)
      apply RingHom.ext
      intro p
      change MvPolynomial.map (algebraMap R S) p =
        algebraTensorAlgEquiv R S ((1 : S) ⊗ₜ[R] p)
      rw [algebraTensorAlgEquiv_tmul, one_smul]))

/-- On a pure tensor of a quotient representative, scalar extension maps the
coefficients and multiplies by the left tensor factor. -/
@[simp] theorem tensorQuotientAlgEquiv_tmul_mk
    (I : Ideal (MvPolynomial σ R)) (s : S) (p : MvPolynomial σ R) :
    tensorQuotientAlgEquiv (S := S) I (s ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk _ (s • MvPolynomial.map (algebraMap R S) p) := by
  simp only [tensorQuotientAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, algebraTensorAlgEquiv_tmul]

/-- The inverse scalar-extension equivalence sends a mapped polynomial class to
one tensored with its original class. -/
@[simp] theorem tensorQuotientAlgEquiv_symm_mk_map
    (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    (tensorQuotientAlgEquiv (S := S) I).symm
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p)) =
      (1 : S) ⊗ₜ[R] Ideal.Quotient.mk I p := by
  apply (tensorQuotientAlgEquiv (S := S) I).injective
  simp only [AlgEquiv.apply_symm_apply, tensorQuotientAlgEquiv_tmul_mk, one_smul]

end MvPolynomial
