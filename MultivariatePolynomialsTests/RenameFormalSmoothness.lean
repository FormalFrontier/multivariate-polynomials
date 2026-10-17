/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFormalSmoothness
import MultivariatePolynomials.RenameFlatness
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Smooth.Flat

/-!
# Models for formal smoothness of variable renaming

Over `ℤ`, including one variable into two is a polynomial extension of the full
source ring, whereas collapsing two variables is not formally smooth over that
source. The latter target is nevertheless formally smooth over `ℤ`, independently
of the variable map. Over `ZMod 1`, the same noninjective variable map induces a
bijective, formally smooth polynomial-ring homomorphism.

The polynomial-extension proof uses Mathlib's sum-variable equivalence with its
source-action equation. The integer collision uses finite presentation over its
Noetherian source, smoothness implying flatness, and the full-source flatness
criterion. These independent model proofs do not use either formal-smoothness
characterization. Applying the two criteria to the inclusion model also gives
injectivity of the polynomial map and of the variable map.

## References

* Mathlib's `MvPolynomial.sumAlgEquiv`, polynomial formal smoothness,
  `RingHom.FinitePresentation.of_finiteType`, and `RingHom.Smooth.flat`.
* `MultivariatePolynomials.RenameFlatness`: the full-source flatness criterion.
-/

namespace MultivariatePolynomialsTests.RenameFormalSmoothness

open MvPolynomial

noncomputable section

section IntegerInclusion

private def oneVariableInclusion : Fin 1 → Fin 2 := Fin.natAdd 1

private def integerVariableInclusion :
    MvPolynomial (Fin 1) ℤ →+* MvPolynomial (Fin 2) ℤ :=
  (rename (R := ℤ) oneVariableInclusion).toRingHom

private theorem integerVariableInclusion_variable_action (i : Fin 1) :
    @algebraMap (MvPolynomial (Fin 1) ℤ) (MvPolynomial (Fin 2) ℤ) _ _
      integerVariableInclusion.toAlgebra (X i) = X (oneVariableInclusion i) := by
  change integerVariableInclusion (X i) = _
  simp [integerVariableInclusion]

private def integerVariableInclusionCoordinates :
    MvPolynomial (Fin 2) ℤ ≃ₐ[ℤ]
      MvPolynomial (Fin 1) (MvPolynomial (Fin 1) ℤ) :=
  (renameEquiv ℤ (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm).trans
    (sumAlgEquiv ℤ (Fin 1) (Fin 1))

private theorem integerVariableInclusionCoordinates_source_action
    (p : MvPolynomial (Fin 1) ℤ) :
    integerVariableInclusionCoordinates (integerVariableInclusion p) = C p := by
  have h : integerVariableInclusionCoordinates.toAlgHom.comp
      (rename (R := ℤ) oneVariableInclusion) =
      IsScalarTower.toAlgHom ℤ (MvPolynomial (Fin 1) ℤ)
        (MvPolynomial (Fin 1) (MvPolynomial (Fin 1) ℤ)) := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      integerVariableInclusionCoordinates, AlgEquiv.trans_apply, renameEquiv_apply,
      rename_X, oneVariableInclusion, finSumFinEquiv_symm_apply_natAdd,
      sumAlgEquiv_X_inr, IsScalarTower.coe_toAlgHom', algebraMap_eq]
  simpa only [integerVariableInclusion, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom', algebraMap_eq] using
      DFunLike.congr_fun h p

private theorem integerVariableInclusion_formallySmooth :
    integerVariableInclusion.FormallySmooth := by
  let e := integerVariableInclusionCoordinates
  have hcomp : e.symm.toRingEquiv.toRingHom.comp
      (C : MvPolynomial (Fin 1) ℤ →+*
        MvPolynomial (Fin 1) (MvPolynomial (Fin 1) ℤ)) =
      integerVariableInclusion := by
    apply RingHom.ext
    intro p
    apply e.injective
    change e (e.symm (C p)) = e (integerVariableInclusion p)
    rw [AlgEquiv.apply_symm_apply]
    exact (integerVariableInclusionCoordinates_source_action p).symm
  have hC : (C : MvPolynomial (Fin 1) ℤ →+*
      MvPolynomial (Fin 1) (MvPolynomial (Fin 1) ℤ)).FormallySmooth := by
    change (algebraMap (MvPolynomial (Fin 1) ℤ)
      (MvPolynomial (Fin 1) (MvPolynomial (Fin 1) ℤ))).FormallySmooth
    exact RingHom.formallySmooth_algebraMap.mpr inferInstance
  rw [← hcomp]
  exact hC.comp (RingHom.FormallySmooth.of_bijective e.symm.bijective)

private theorem integerVariableInclusion_injective :
    Function.Injective integerVariableInclusion :=
  (rename_formallySmooth_iff_injective (R := ℤ) oneVariableInclusion).mp
    integerVariableInclusion_formallySmooth

private theorem oneVariableInclusion_injective :
    Function.Injective oneVariableInclusion :=
  ((rename_formallySmooth_iff (R := ℤ) oneVariableInclusion).mp
    integerVariableInclusion_formallySmooth).resolve_right (not_subsingleton ℤ)

end IntegerInclusion

section IntegerCollision

private def variableCollision : Fin 2 → Unit := fun _ => ()

private theorem variableCollision_not_injective :
    ¬ Function.Injective variableCollision := by
  intro h
  have h01 : (0 : Fin 2) = 1 := h (show variableCollision 0 = variableCollision 1 from rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

private def integerVariableCollision :
    MvPolynomial (Fin 2) ℤ →+* MvPolynomial Unit ℤ :=
  (rename (R := ℤ) variableCollision).toRingHom

private theorem integerVariableCollision_variable_action (i : Fin 2) :
    @algebraMap (MvPolynomial (Fin 2) ℤ) (MvPolynomial Unit ℤ) _ _
      integerVariableCollision.toAlgebra (X i) = X () := by
  change integerVariableCollision (X i) = _
  simp [integerVariableCollision, variableCollision]

private theorem integerCollisionTarget_coefficient_formallySmooth :
    Algebra.FormallySmooth ℤ (MvPolynomial Unit ℤ) := inferInstance

private theorem integerVariableCollision_surjective :
    Function.Surjective integerVariableCollision := by
  apply rename_surjective variableCollision
  intro u
  exact ⟨0, Subsingleton.elim _ _⟩

private theorem integerVariableCollision_source_noetherian :
    IsNoetherianRing (MvPolynomial (Fin 2) ℤ) := inferInstance

private theorem integerVariableCollision_finitePresentation :
    integerVariableCollision.FinitePresentation := by
  let : IsNoetherianRing (MvPolynomial (Fin 2) ℤ) :=
    integerVariableCollision_source_noetherian
  exact RingHom.FinitePresentation.of_finiteType.mp
    (RingHom.FiniteType.of_surjective integerVariableCollision
      integerVariableCollision_surjective)

private theorem integerVariableCollision_not_formallySmooth :
    ¬ integerVariableCollision.FormallySmooth := by
  intro h
  have hsmooth : integerVariableCollision.Smooth :=
    RingHom.smooth_def.mpr ⟨h, integerVariableCollision_finitePresentation⟩
  have hflat := hsmooth.flat
  rcases (rename_flat_iff (R := ℤ) variableCollision).mp hflat with hinj | hzero
  · exact variableCollision_not_injective hinj
  · exact (not_subsingleton ℤ) hzero

end IntegerCollision

section ZeroRingCollision

private def zeroRingVariableCollision :
    MvPolynomial (Fin 2) (ZMod 1) →+* MvPolynomial Unit (ZMod 1) :=
  (rename (R := ZMod 1) variableCollision).toRingHom

private theorem zeroRingVariableCollision_variable_action (i : Fin 2) :
    @algebraMap (MvPolynomial (Fin 2) (ZMod 1)) (MvPolynomial Unit (ZMod 1)) _ _
      zeroRingVariableCollision.toAlgebra (X i) = X () := by
  change zeroRingVariableCollision (X i) = _
  simp [zeroRingVariableCollision, variableCollision]

private theorem zeroRingVariableCollision_index_not_injective :
    ¬ Function.Injective variableCollision := variableCollision_not_injective

private theorem zeroRingVariableCollision_bijective :
    Function.Bijective zeroRingVariableCollision := by
  let : Subsingleton (MvPolynomial (Fin 2) (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial (Fin 2) (ZMod 1))
  let : Subsingleton (MvPolynomial Unit (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial Unit (ZMod 1))
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem zeroRingVariableCollision_formallySmooth :
    zeroRingVariableCollision.FormallySmooth :=
  RingHom.FormallySmooth.of_bijective zeroRingVariableCollision_bijective

end ZeroRingCollision

end

end MultivariatePolynomialsTests.RenameFormalSmoothness
