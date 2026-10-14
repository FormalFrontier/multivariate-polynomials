/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import MultivariatePolynomials.Rename

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Algebraic.MvPolynomial

@[expose] public section

/-!
# Algebraicity of variable renaming

A coefficient-preserving variable renaming between full polynomial rings over
an arbitrary commutative ring is algebraic exactly when the coefficients are
nontrivial and the variable map is surjective or noninjective. The coefficient,
source-variable and target-variable types have independent universes.

Here algebraicity is Mathlib's predicate requiring a nonzero annihilating
polynomial, not necessarily monic or of positive degree. A collision of source
variables supplies a nonzero constant annihilator through the kernel, even if
some target variables are missed. For zero coefficients, no nonzero polynomial
exists, so even identity renaming is not algebraic. This differs from integrality.

## References

* Mathlib, `Mathlib.RingTheory.Algebraic.Basic`: algebraicity under injective
  coefficient maps, and algebraicity of a noninjective algebra map.
* Mathlib, `Mathlib.RingTheory.Algebraic.MvPolynomial`: transcendence of a variable
  over the subalgebra supported on a set not containing it.
-/

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]

/-- The full target polynomial ring is algebraic over the full source through
renaming exactly when the coefficients are nontrivial and the variable map is
surjective or noninjective. The algebra structure is the one induced by the
specified renaming map, including when the variable types coincide. -/
theorem isAlgebraic_rename_iff (f : σ → τ) :
    @Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R)
      inferInstance inferInstance
      (rename (R := R) f).toRingHom.toAlgebra ↔
        Nontrivial R ∧ (Function.Surjective f ∨ ¬ Function.Injective f) := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  constructor
  · intro h
    have : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R) := h
    have : Nontrivial (MvPolynomial σ R) :=
      Algebra.nontrivial_of_isAlgebraic (MvPolynomial σ R) (MvPolynomial τ R)
    have hR : Nontrivial R := (C : R →+* MvPolynomial σ R).domain_nontrivial
    refine ⟨hR, ?_⟩
    by_cases hf : Function.Injective f
    · left
      by_contra hs
      simp only [Function.Surjective, not_forall, not_exists] at hs
      obtain ⟨t, ht⟩ := hs
      let g : MvPolynomial σ R →ₐ[R] supported R (Set.range f) :=
        (rename (R := R) f).codRestrict (supported R (Set.range f)) (fun p => by
          rw [mem_supported]
          intro j hj
          obtain ⟨i, _, rfl⟩ := mem_vars_rename f p hj
          exact ⟨i, rfl⟩)
      have hg : Function.Injective g := by
        intro p q hpq
        apply rename_injective f hf
        exact congrArg Subtype.val hpq
      have hcomp :
          (algebraMap (supported R (Set.range f)) (MvPolynomial τ R)).comp g.toRingHom =
            (RingHom.id (MvPolynomial τ R)).comp
              (algebraMap (MvPolynomial σ R) (MvPolynomial τ R)) := by
        ext p <;> rfl
      have hx := (Algebra.IsAlgebraic.isAlgebraic (R := MvPolynomial σ R)
        (X t : MvPolynomial τ R)).ringHom_of_comp_eq
          g.toRingHom (RingHom.id (MvPolynomial τ R)) hg hcomp
      exact (transcendental_supported_X R (show t ∉ Set.range f from by
        rintro ⟨i, hi⟩
        exact ht i hi)) hx
    · exact Or.inr hf
  · rintro ⟨hR, hf | hf⟩
    · have : Nontrivial R := hR
      have hi : RingHom.IsIntegral (rename (R := R) f).toRingHom :=
        RingHom.isIntegral_of_surjective _ (rename_surjective f hf)
      refine ⟨fun p => ?_⟩
      have hp : IsIntegral (MvPolynomial σ R) p := hi p
      exact hp.isAlgebraic
    · have : Nontrivial R := hR
      apply Algebra.isAlgebraic_of_not_injective
      intro hi
      rcases (injective_rename_iff f).1 hi with hfi | hsub
      · exact hf hfi
      · exact zero_ne_one (hsub.elim 0 1)

end MvPolynomial
