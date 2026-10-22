/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.FinitePresentation

@[expose] public section

/-!
# Finite presentation from a surjective scalar map

Evaluation in an empty family of variables is the composite of the existing
`MvPolynomial.isEmptyAlgEquiv` with the scalar map. This identifies its
surjectivity and ideal kernel with those of the scalar map.

`Algebra.FinitePresentation.of_surjective_algebraMap` constructs a presentation
with no variables when the scalar map is surjective and its ideal kernel is
finitely generated. The target may be an arbitrary semiring. Here finite
presentation means Mathlib's finite-variable surjection with finitely generated
ideal kernel, not finite presentation of a semiring congruence.

For commutative rings, `RingHom.finitePresentation_algebraMap` identifies the
conclusion with finite presentation of the scalar ring homomorphism.

## References

The construction uses Mathlib's `Algebra.FinitePresentation`, empty-variable
polynomial equivalence, and finite-generation transport for ideals.
-/

universe u v w

namespace MvPolynomial

variable {R : Type u} {A : Type v} {ι : Type w}
  [CommSemiring R] [CommSemiring A] [Algebra R A] [IsEmpty ι]

/-- Evaluation in no variables is the scalar map after the empty-variable equivalence. -/
theorem aeval_eq_comp_isEmptyAlgEquiv (x : ι → A) :
    aeval x = (Algebra.ofId R A).comp (isEmptyAlgEquiv R ι).toAlgHom := by
  apply algHom_ext
  intro i
  exact IsEmpty.elim' ‹IsEmpty ι› i

/-- Evaluation in no variables is surjective exactly when the scalar map is surjective. -/
@[simp]
theorem aeval_surjective_iff_of_isEmpty (x : ι → A) :
    Function.Surjective (aeval (R := R) x) ↔ Function.Surjective (algebraMap R A) := by
  rw [aeval_eq_comp_isEmptyAlgEquiv]
  constructor
  · intro h a
    obtain ⟨p, hp⟩ := h a
    exact ⟨isEmptyAlgEquiv R ι p, hp⟩
  · intro h a
    obtain ⟨r, hr⟩ := h a
    refine ⟨(isEmptyAlgEquiv R ι).symm r, ?_⟩
    change algebraMap R A ((isEmptyAlgEquiv R ι) ((isEmptyAlgEquiv R ι).symm r)) = a
    rw [AlgEquiv.apply_symm_apply]
    exact hr

/-- The kernel of evaluation in no variables is the scalar kernel transported to polynomials. -/
theorem ker_aeval_of_isEmpty (x : ι → A) :
    RingHom.ker (aeval x).toRingHom =
      (RingHom.ker (algebraMap R A)).map
        (isEmptyAlgEquiv R ι).symm.toRingEquiv.toRingHom := by
  rw [aeval_eq_comp_isEmptyAlgEquiv]
  change RingHom.ker ((algebraMap R A).comp
    (isEmptyAlgEquiv R ι).toRingEquiv.toRingHom) = _
  rw [← RingHom.comap_ker]
  exact (Ideal.map_symm (I := RingHom.ker (algebraMap R A))
    (isEmptyAlgEquiv R ι).toRingEquiv).symm

/-- The ideal kernel of evaluation in no variables is finitely generated exactly when the
scalar kernel is finitely generated. -/
@[simp]
theorem ker_aeval_fg_iff_of_isEmpty (x : ι → A) :
    (RingHom.ker (aeval (R := R) x).toRingHom).FG ↔ (RingHom.ker (algebraMap R A)).FG := by
  rw [ker_aeval_of_isEmpty]
  constructor
  · intro h
    have hmap := h.map (isEmptyAlgEquiv R ι).toRingEquiv.toRingHom
    have hround := Ideal.map_of_equiv (I := RingHom.ker (algebraMap R A))
      (isEmptyAlgEquiv R ι).toRingEquiv.symm
    exact hround ▸ hmap
  · intro h
    exact h.map _

end MvPolynomial

namespace Algebra.FinitePresentation

/-- A surjective scalar map with finitely generated ideal kernel gives a finite presentation
with no variables. -/
theorem of_surjective_algebraMap
    {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (hsurj : Function.Surjective (algebraMap R A))
    (hker : (RingHom.ker (algebraMap R A)).FG) : Algebra.FinitePresentation R A := by
  let e := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
  refine ⟨0, (Algebra.ofId R A).comp e.toAlgHom, ?_, ?_⟩
  · exact hsurj.comp e.surjective
  · change (RingHom.ker ((algebraMap R A).comp e.toRingEquiv.toRingHom)).FG
    rw [← RingHom.comap_ker]
    exact (Ideal.map_symm (I := RingHom.ker (algebraMap R A)) e.toRingEquiv) ▸
      (hker.map e.symm.toRingEquiv.toRingHom)

end Algebra.FinitePresentation
