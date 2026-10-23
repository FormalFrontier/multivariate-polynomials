/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFlatness
import MultivariatePolynomials.RenameFiniteType
import MultivariatePolynomials.RenameSmooth
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Sum
import Mathlib.RingTheory.Smooth.Flat

/-!
# Models of smooth and nonsmooth variable renaming

These examples concern the canonical ring map, hence the full source-polynomial
action, rather than just the coefficient-ring action. The five model proofs
remain independent of the smoothness criterion. A final contract uses the
smoothness/flat finite-type comparison on the adjoining model.

The integer examples adjoin one variable, swap two variables, collide two
variables, and adjoin infinitely many variables. The collision has finite
complement but fails flatness. The empty-source map into natural-number variables
is injective but fails finite type. Over `ZMod 1`, the same infinite-complement
map is smooth by bijectivity of maps between subsingleton polynomial rings.

In the adjoining model the displayed equivalence is only an integer-algebra
equivalence. The full ring-map identity, using the public sum-equivalence action
equation, joins its composite with coefficient inclusion to renaming.
No new algebra structure over the source polynomial ring is introduced.
-/

namespace MultivariatePolynomialsTests.RenameSmooth

open MvPolynomial

-- Adjoining one variable over the integers.
private theorem integer_adjoining_variable_smooth :
    (rename (R := ℤ) (PEmpty.elim : PEmpty → Unit)).toRingHom.Smooth := by
  let E := (sumAlgEquiv ℤ Unit PEmpty).symm.trans
    (renameEquiv ℤ (Equiv.sumEmpty Unit PEmpty))
  have hC : (C : MvPolynomial PEmpty ℤ →+*
      MvPolynomial Unit (MvPolynomial PEmpty ℤ)).Smooth := by
    change (algebraMap (MvPolynomial PEmpty ℤ)
      (MvPolynomial Unit (MvPolynomial PEmpty ℤ))).Smooth
    exact RingHom.smooth_algebraMap.mpr
      (show Algebra.Smooth (MvPolynomial PEmpty ℤ)
        (MvPolynomial Unit (MvPolynomial PEmpty ℤ)) from ⟨inferInstance, inferInstance⟩)
  have hjoin : E.toRingEquiv.toRingHom.comp
      (C : MvPolynomial PEmpty ℤ →+* MvPolynomial Unit (MvPolynomial PEmpty ℤ)) =
        (rename (R := ℤ) (PEmpty.elim : PEmpty → Unit)).toRingHom := by
    apply RingHom.ext
    intro p
    have hinr : sumAlgEquiv ℤ Unit PEmpty
        (rename (Sum.inr : PEmpty → Unit ⊕ PEmpty) p) = C p := by
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        IsScalarTower.coe_toAlgHom', algebraMap_eq] using
        DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr ℤ Unit PEmpty) p
    have hempty : (Equiv.sumEmpty Unit PEmpty : Unit ⊕ PEmpty → Unit) ∘
        (Sum.inr : PEmpty → Unit ⊕ PEmpty) = (PEmpty.elim : PEmpty → Unit) := by
      funext i
      exact PEmpty.elim i
    change rename (Equiv.sumEmpty Unit PEmpty)
      ((sumAlgEquiv ℤ Unit PEmpty).symm (C p)) =
        rename (PEmpty.elim : PEmpty → Unit) p
    rw [← hinr, AlgEquiv.symm_apply_apply, rename_rename, hempty]
  rw [← hjoin]
  exact hC.comp (RingHom.Smooth.of_bijective E.bijective)

-- A nonidentity permutation, independently using a bijective renaming.
private theorem integer_variable_swap_smooth :
    (rename (R := ℤ) (Equiv.swap true false)).toRingHom.Smooth := by
  exact RingHom.Smooth.of_bijective (renameEquiv ℤ (Equiv.swap true false)).bijective

-- A collision is not flat, although no target variable is missed.
private theorem integer_collision_not_smooth :
    ¬ (rename (R := ℤ) (fun _ : Fin 2 => (() : Unit))).toRingHom.Smooth := by
  intro h
  rcases (rename_flat_iff (R := ℤ) (fun _ : Fin 2 => (() : Unit))).mp h.flat with hinj | hzero
  · have h01 : (0 : Fin 2) = 1 := hinj rfl
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  · exact (zero_ne_one : (0 : ℤ) ≠ 1) (hzero.elim 0 1)

-- Infinitely many adjoined variables violate finite type, not injectivity.
private theorem integer_infinite_adjoining_not_smooth :
    ¬ (rename (R := ℤ) (PEmpty.elim : PEmpty → ℕ)).toRingHom.Smooth := by
  intro h
  have hft := RingHom.FiniteType.of_finitePresentation h.finitePresentation
  rcases (finiteType_rename_iff (R := ℤ) (PEmpty.elim : PEmpty → ℕ)).mp hft with
    hzero | hfinite
  · exact (zero_ne_one : (0 : ℤ) ≠ 1) (hzero.elim 0 1)
  · have hnat : (Set.univ : Set ℕ).Finite := hfinite.subset (by
      rintro n _ ⟨i, _⟩
      exact PEmpty.elim i)
    exact Set.infinite_univ hnat

-- The same genuinely infinite complement is harmless over the zero ring.
private theorem zero_ring_infinite_adjoining_smooth :
    (rename (R := ZMod 1) (PEmpty.elim : PEmpty → ℕ)).toRingHom.Smooth := by
  exact RingHom.Smooth.of_bijective
    (Function.bijective_of_subsingleton'
      ((rename (R := ZMod 1) (PEmpty.elim : PEmpty → ℕ)).toRingHom))

-- The comparison recovers flatness and finite type from the independent smooth model.
private theorem integer_adjoining_variable_flat_and_finiteType :
    (rename (R := ℤ) (PEmpty.elim : PEmpty → Unit)).toRingHom.Flat ∧
      (rename (R := ℤ) (PEmpty.elim : PEmpty → Unit)).toRingHom.FiniteType := by
  constructor
  · exact ((rename_smooth_iff_flat_and_finiteType (R := ℤ)
      (PEmpty.elim : PEmpty → Unit)).mp integer_adjoining_variable_smooth).1
  · exact ((rename_smooth_iff_flat_and_finiteType (R := ℤ)
      (PEmpty.elim : PEmpty → Unit)).mp integer_adjoining_variable_smooth).2

end MultivariatePolynomialsTests.RenameSmooth
