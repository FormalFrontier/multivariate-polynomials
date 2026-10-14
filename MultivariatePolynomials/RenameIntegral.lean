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

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: coefficient-preserving variable renaming.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: integrality of
  ring homomorphisms and of elements with respect to a ring homomorphism.
-/

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]

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
      by_contra hf
      simp only [Function.Surjective, not_forall, not_exists] at hf
      obtain ⟨t, ht⟩ := hf
      let ψ : MvPolynomial τ R →+* Polynomial R :=
        eval₂Hom Polynomial.C (fun j => if j = t then Polynomial.X else 0)
      let ε : MvPolynomial σ R →+* R :=
        eval₂Hom (RingHom.id R) (fun _ => 0)
      -- Every renamed source variable vanishes under this evaluation.
      have hcomp : ψ.comp (rename (R := R) f).toRingHom = Polynomial.C.comp ε := by
        apply ringHom_ext
        · intro r
          simp [ψ, ε]
        · intro s
          simp [ψ, ε, ht s]
      have hx := (h (X t)).map ψ
      rw [hcomp] at hx
      have hX : IsIntegral R (Polynomial.X : Polynomial R) := by
        simpa [IsIntegral, ψ] using hx.of_comp
      exact (Polynomial.transcendental_X R) hX.isAlgebraic
  · rintro (hf | hR)
    · exact RingHom.isIntegral_of_surjective _ (rename_surjective f hf)
    · have : Subsingleton R := hR
      have : Subsingleton (MvPolynomial τ R) := Algebra.subsingleton R _
      exact RingHom.isIntegral_of_surjective _ (Function.surjective_to_subsingleton _)

end MvPolynomial
