/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameFlatness
public import MultivariatePolynomials.RenameFiniteType
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Flat

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-!
# Smoothness of variable renaming

Variable renaming is smooth over the full source polynomial ring exactly when
the variable map is injective and misses only finitely many target variables,
or the coefficient ring is subsingleton. Injectivity excludes collisions, while
the finite complement measures the variables adjoined to the source. The zero
ring is a separate case: its polynomial rings are subsingleton even with
infinitely many missed variables.

Here `RingHom.Smooth` uses the algebra structure induced by the renaming
homomorphism. Thus a source polynomial acts by multiplication by its renamed
image; this is not smoothness merely over the coefficient ring. Coefficients and
both variable types have independent universes, with empty and infinite variable
types allowed. For these variable-renaming homomorphisms, smoothness is also
equivalent to flatness together with finite type.

Smoothness consists of formal smoothness and finite presentation. It implies
flatness, so the injectivity and finite-complement obstructions follow from the
flatness and finite-type criteria.
Conversely, an injective variable map identifies the source with polynomials on
its range. Splitting off the finite complement then factors renaming through a
smooth polynomial coefficient inclusion, using equalities of the full ring maps.

## Applications

The private applications give five direct settings: adjoining one variable over
`ℤ`, swapping Boolean variables, a collision, infinitely many new variables, and
the same infinite extension over `ZMod 1`. The collision fails flatness; the
infinite extension over `ℤ` fails finite type despite injectivity. The zero-ring
case is smooth even with infinite complement. A final comparison application
extracts flatness and finite type from the independent one-variable model.
Its base `MvPolynomial PEmpty ℤ` is isomorphic to `ℤ`; the proof still records
the full ring-map identity joining coefficient inclusion to renaming.

## References

* Mathlib, `Mathlib.RingTheory.RingHom.Smooth`: smoothness for the algebra structure
  induced by a ring homomorphism.
* `MultivariatePolynomials.RenameFlatness`: the flatness obstruction to collisions.
* `MultivariatePolynomials.RenameFiniteType`: finite generation and missed variables.
-/

namespace MvPolynomial

universe u v w

/-- Renaming is smooth relative to the full source polynomial ring exactly when
the variable map is injective with finite complement, or the coefficients are
subsingleton. -/
theorem rename_smooth_iff {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}
    (f : σ → τ) :
    (MvPolynomial.rename (R := R) f).toRingHom.Smooth ↔
      (Function.Injective f ∧ Set.Finite ((Set.range f)ᶜ)) ∨ Subsingleton R := by
  classical
  constructor
  · intro h
    rcases (rename_flat_iff (R := R) f).mp h.flat with hf | hR
    · have hft := RingHom.FiniteType.of_finitePresentation h.finitePresentation
      rcases (finiteType_rename_iff (R := R) f).mp hft with hR | hfinite
      · exact Or.inr hR
      · exact Or.inl ⟨hf, hfinite⟩
    · exact Or.inr hR
  · rintro (⟨hf, hfinite⟩ | hR)
    · let : Fintype ((Set.range f)ᶜ : Set τ) := hfinite.fintype
      let e₁ := renameEquiv R (Equiv.ofInjective f hf)
      let e₂ := splitComplAlgEquiv (R := R) (Set.range f)
      have hrename :
          (rename (R := R) (Subtype.val : Set.range f → τ)).comp e₁.toAlgHom =
            rename (R := R) f := by
        apply algHom_ext
        intro i
        simp [e₁, renameEquiv_apply]
      have hcomp : e₂.symm.toRingEquiv.toRingHom.comp
          ((C : MvPolynomial (Set.range f) R →+*
            MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)).comp
            e₁.toRingEquiv.toRingHom) = (rename (R := R) f).toRingHom := by
        apply RingHom.ext
        intro p
        apply e₂.injective
        change e₂ (e₂.symm (C (e₁ p))) = e₂ (rename f p)
        have hr : rename f p = rename (Subtype.val : Set.range f → τ) (e₁ p) :=
          (DFunLike.congr_fun hrename p).symm
        rw [AlgEquiv.apply_symm_apply, hr]
        exact (splitComplAlgEquiv_rename_subtypeVal (R := R) (Set.range f) (e₁ p)).symm
      have hC : (C : MvPolynomial (Set.range f) R →+*
          MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)).Smooth := by
        change (algebraMap (MvPolynomial (Set.range f) R)
          (MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R))).Smooth
        exact RingHom.smooth_algebraMap.mpr
          (show Algebra.Smooth (MvPolynomial (Set.range f) R)
            (MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)) from
              ⟨inferInstance, inferInstance⟩)
      have h₁ : e₁.toRingEquiv.toRingHom.Smooth :=
        RingHom.Smooth.of_bijective e₁.bijective
      rw [← hcomp]
      exact (h₁.comp hC).comp (RingHom.Smooth.of_bijective e₂.symm.bijective)
    · let : Subsingleton R := hR
      exact RingHom.Smooth.of_bijective
        (Function.bijective_of_subsingleton' ((rename (R := R) f).toRingHom))

/-- For variable-renaming homomorphisms, smoothness over the full source polynomial
ring is equivalent to flatness together with finite type. -/
theorem rename_smooth_iff_flat_and_finiteType {R : Type u} [CommRing R]
    {σ : Type v} {τ : Type w} (f : σ → τ) :
    (rename (R := R) f).toRingHom.Smooth ↔
      (rename (R := R) f).toRingHom.Flat ∧ (rename (R := R) f).toRingHom.FiniteType := by
  rw [rename_smooth_iff, rename_flat_iff, RingHom.FiniteType, finiteType_rename_iff]
  constructor
  · rintro (⟨hf, hfinite⟩ | hR)
    · exact ⟨Or.inl hf, Or.inr hfinite⟩
    · exact ⟨Or.inr hR, Or.inl hR⟩
  · rintro ⟨hflat, hft⟩
    rcases hflat with hf | hR
    · rcases hft with hR | hfinite
      · exact Or.inr hR
      · exact Or.inl ⟨hf, hfinite⟩
    · exact Or.inr hR

end MvPolynomial

end

/-!
## Concrete renamings

These private applications use the full source-polynomial action induced by
renaming. The first five proofs are independent of the smoothness criterion;
the last applies the comparison to the one-variable extension.
-/

namespace MvPolynomial

section Applications

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


end Applications

end MvPolynomial
