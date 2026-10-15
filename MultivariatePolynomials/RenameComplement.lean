/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Set

@[expose] public section

/-!
# Splitting off complementary variables

For a set of variables `S`, `splitComplAlgEquiv` treats the variables in `S`
as coefficients and the variables in its complement as polynomial variables.
The construction works over any commutative semiring, with independent
coefficient and variable universes. Its compatibility with inclusion of `S`
identifies the original renaming action with the ordinary coefficient action.
-/

universe u w

namespace MvPolynomial

/-- Separate the complementary variables from the variables in `S`, treating
polynomials in `S` as coefficients. -/
noncomputable def splitComplAlgEquiv {R : Type u} {τ : Type w}
    [CommSemiring R] (S : Set τ) :
    MvPolynomial τ R ≃ₐ[R] MvPolynomial (Sᶜ : Set τ) (MvPolynomial S R) := by
  classical
  exact (renameEquiv R ((Equiv.Set.sumCompl S).symm.trans
    (Equiv.sumComm S (Sᶜ : Set τ)))).trans (sumAlgEquiv R (Sᶜ : Set τ) S)

/-- Splitting complementary variables turns retained-variable inclusion into
coefficient inclusion. -/
theorem splitComplAlgEquiv_comp_rename_subtypeVal
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ) :
    (splitComplAlgEquiv (R := R) S).toAlgHom.comp
        (rename (Subtype.val : S → τ)) =
      IsScalarTower.toAlgHom R (MvPolynomial S R)
        (MvPolynomial (Sᶜ : Set τ) (MvPolynomial S R)) := by
  classical
  have hrename :
      (renameEquiv R ((Equiv.Set.sumCompl S).symm.trans
        (Equiv.sumComm S (Sᶜ : Set τ)))).toAlgHom.comp
          (rename (Subtype.val : S → τ)) =
        rename (Sum.inr : S → (Sᶜ : Set τ) ⊕ S) := by
    apply algHom_ext
    intro i
    simp [renameEquiv_apply]
  change (sumAlgEquiv R (Sᶜ : Set τ) S).toAlgHom.comp
    ((renameEquiv R ((Equiv.Set.sumCompl S).symm.trans
      (Equiv.sumComm S (Sᶜ : Set τ)))).toAlgHom.comp
        (rename (Subtype.val : S → τ))) = _
  rw [hrename]
  exact sumAlgEquiv_comp_rename_inr R (Sᶜ : Set τ) S

/-- Retained-variable renaming becomes coefficient inclusion. -/
@[simp]
theorem splitComplAlgEquiv_rename_subtypeVal
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ)
    (p : MvPolynomial S R) :
    splitComplAlgEquiv (R := R) S (rename (Subtype.val : S → τ) p) = C p := by
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    IsScalarTower.coe_toAlgHom', algebraMap_eq] using
    DFunLike.congr_fun (splitComplAlgEquiv_comp_rename_subtypeVal (R := R) S) p

/-- A coefficient remains a coefficient at both polynomial levels. -/
@[simp]
theorem splitComplAlgEquiv_C
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ) (r : R) :
    splitComplAlgEquiv (R := R) S (C r) = C (C r) := by
  classical
  simp [splitComplAlgEquiv, renameEquiv_apply]

/-- A retained variable becomes a coefficient variable. -/
@[simp]
theorem splitComplAlgEquiv_X_mem
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ) (i : S) :
    splitComplAlgEquiv (R := R) S (X (i : τ)) = C (X i) := by
  simpa only [rename_X] using
    splitComplAlgEquiv_rename_subtypeVal (R := R) S (X i)

/-- A complementary variable remains an outer polynomial variable. -/
@[simp]
theorem splitComplAlgEquiv_X_compl
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ) (i : (Sᶜ : Set τ)) :
    splitComplAlgEquiv (R := R) S (X (i : τ)) = X i := by
  classical
  simp [splitComplAlgEquiv, renameEquiv_apply,
    Equiv.Set.sumCompl_symm_apply_of_notMem i.property]

/-- In the inverse direction, coefficient inclusion is retained-variable renaming. -/
@[simp]
theorem splitComplAlgEquiv_symm_C
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ)
    (p : MvPolynomial S R) :
    (splitComplAlgEquiv (R := R) S).symm (C p) = rename (Subtype.val : S → τ) p := by
  apply (splitComplAlgEquiv (R := R) S).injective
  rw [AlgEquiv.apply_symm_apply, splitComplAlgEquiv_rename_subtypeVal]

/-- In the inverse direction, an outer variable recovers the original variable. -/
@[simp]
theorem splitComplAlgEquiv_symm_X
    {R : Type u} {τ : Type w} [CommSemiring R] (S : Set τ) (i : (Sᶜ : Set τ)) :
    (splitComplAlgEquiv (R := R) S).symm (X i) = X (i : τ) := by
  apply (splitComplAlgEquiv (R := R) S).injective
  rw [AlgEquiv.apply_symm_apply, splitComplAlgEquiv_X_compl]

end MvPolynomial
