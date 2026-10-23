/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameFlatness
public import MultivariatePolynomials.RenameFiniteType
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Flat

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

Smoothness implies flatness and finite presentation, hence the injectivity and
finite-complement obstructions follow from the flatness and finite-type criteria.
Conversely, an injective variable map identifies the source with polynomials on
its range. Splitting off the finite complement then factors renaming through a
smooth polynomial coefficient inclusion, using equalities of the full ring maps.

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
