/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

/-!
# Integrality of variable renaming

A coefficient-preserving variable renaming between polynomial rings over a
commutative ring is integral exactly when every target variable is hit or the
coefficient ring is subsingleton. The coefficient type and the two variable
types may have independent universes, and the variable map need not be injective.

Integrality is the existing ring-homomorphism predicate for the map from the
full source polynomial ring to the full target polynomial ring. It is not
integrality over the coefficient ring, nor a statement about fraction rings
or a map whose codomain has been restricted to its image.

For a specified target variable, integrality over the full source through the
renaming action is equivalent to that variable being hit or the coefficient
ring being subsingleton.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: coefficient-preserving variable renaming.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: integrality of
  ring homomorphisms and of elements with respect to a ring homomorphism.
-/

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]

/-- A target variable is integral over the full source polynomial ring through
renaming exactly when its index is hit or the coefficient ring is subsingleton.
The algebra structure is induced by the specified renaming, including when the
source and target variable types coincide. -/
@[simp]
theorem isIntegral_X_rename_iff (f : σ → τ) (j : τ) :
    @IsIntegral (MvPolynomial σ R) (MvPolynomial τ R) inferInstance inferInstance
      (rename (R := R) f).toRingHom.toAlgebra (X j) ↔
        j ∈ Set.range f ∨ Subsingleton R := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · have : Nontrivial R := hR
      left
      by_contra hj
      have hj' (s : σ) : f s ≠ j := fun hs => hj ⟨s, hs⟩
      let ψ : MvPolynomial τ R →+* Polynomial R :=
        eval₂Hom Polynomial.C (fun k => if k = j then Polynomial.X else 0)
      let ε : MvPolynomial σ R →+* R :=
        eval₂Hom (RingHom.id R) (fun _ => 0)
      -- Every renamed source variable vanishes under this evaluation.
      have hcomp : ψ.comp (rename (R := R) f).toRingHom = Polynomial.C.comp ε := by
        apply ringHom_ext
        · intro r
          simp [ψ, ε]
        · intro s
          simp [ψ, ε, hj' s]
      change RingHom.IsIntegralElem (rename (R := R) f).toRingHom (X j) at h
      have hx := h.map ψ
      rw [hcomp] at hx
      have hX : IsIntegral R (Polynomial.X : Polynomial R) := by
        simpa [IsIntegral, ψ] using hx.of_comp
      exact (Polynomial.transcendental_X R) hX.isAlgebraic
  · rintro (⟨i, rfl⟩ | hR)
    · have hi := isIntegral_algebraMap (R := MvPolynomial σ R)
        (A := MvPolynomial τ R) (x := X i)
      change IsIntegral (MvPolynomial σ R) (rename f (X i)) at hi
      simpa only [rename_X] using hi
    · have : Subsingleton R := hR
      have : Subsingleton (MvPolynomial τ R) := Algebra.subsingleton R _
      have hj : (X j : MvPolynomial τ R) = 0 := Subsingleton.elim _ _
      rw [hj]
      exact isIntegral_zero

/-- A coefficient-preserving variable renaming is integral over the full source
polynomial ring exactly when the variable map is surjective or the coefficient
ring is subsingleton. -/
theorem isIntegral_rename_iff (f : σ → τ) :
    RingHom.IsIntegral ((rename (R := R) f).toRingHom) ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · have : Nontrivial R := hR
      left
      intro j
      rcases (isIntegral_X_rename_iff (R := R) f j).mp (h (X j)) with hj | hsub
      · exact hj
      · exact (zero_ne_one (hsub.elim 0 1)).elim
  · rintro (hf | hR)
    · exact RingHom.isIntegral_of_surjective _ (rename_surjective f hf)
    · have : Subsingleton R := hR
      have : Subsingleton (MvPolynomial τ R) := Algebra.subsingleton R _
      exact RingHom.isIntegral_of_surjective _ (Function.surjective_to_subsingleton _)

end MvPolynomial
