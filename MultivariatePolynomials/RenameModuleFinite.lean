/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

/-!
# Module finiteness of variable renaming

A map `f : σ → τ` makes the full target polynomial semiring a module over the
full source polynomial semiring by `p • q = MvPolynomial.rename f p * q`.
This module is finitely generated exactly when `f` is surjective or the
coefficient semiring is subsingleton.

The coefficient semiring and both variable types may lie in independent
universes. No injectivity or finiteness assumption on the variable types is
needed. This is not finiteness over the coefficient semiring: the scalars are
the full source polynomial semiring, and the module structure is supplied
explicitly by the renaming homomorphism.

For nontrivial coefficients, even one missed target variable prevents module
finiteness. This is stronger than finite type, which permits finitely many
missed target variables.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: polynomial variable renaming.
* Mathlib, `Mathlib.RingTheory.Finiteness.Defs`: finite generation of modules
  over semirings.
* Mathlib, `Mathlib.Algebra.Algebra.Defs`: the algebra and module structures
  induced by a ring homomorphism.
-/

universe u v w

/-- The full target polynomial semiring is a finite module over the full source
polynomial semiring via renaming exactly when the variable map is surjective or
the coefficient semiring is subsingleton. The module structure is induced by
the renaming homomorphism, so `p • q = MvPolynomial.rename f p * q`. -/
theorem MvPolynomial.moduleFinite_rename_iff
    {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (f : σ → τ) :
    @Module.Finite (MvPolynomial σ R) (MvPolynomial τ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R)
        inferInstance inferInstance
        (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra) ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra
  change Module.Finite (MvPolynomial σ R) (MvPolynomial τ R) ↔ _
  constructor
  · intro h
    by_cases hR : Subsingleton R
    · exact Or.inr hR
    · left
      let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      by_contra hf
      simp only [Function.Surjective, not_forall, not_exists] at hf
      obtain ⟨j, hj⟩ := hf
      let g : τ → Polynomial R := fun t => if t = j then Polynomial.X else 0
      let e : MvPolynomial τ R →ₐ[R] Polynomial R := MvPolynomial.aeval g
      have he : Function.Surjective e := by
        intro p
        refine ⟨Polynomial.aeval (MvPolynomial.X j) p, ?_⟩
        have hsec : e.comp (Polynomial.aeval (MvPolynomial.X j)) =
            AlgHom.id R (Polynomial R) := by
          apply Polynomial.algHom_ext
          simp [e, g]
        exact DFunLike.congr_fun hsec p
      have hcomp (a : MvPolynomial σ R) :
          e (MvPolynomial.rename f a) = Polynomial.C (MvPolynomial.constantCoeff a) := by
        change MvPolynomial.eval₂Hom (algebraMap R (Polynomial R)) g
          (MvPolynomial.rename f a) = _
        rw [MvPolynomial.eval₂Hom_rename]
        have hg : g ∘ f = fun _ => 0 := by
          funext i
          exact ite_eq_right (hj i)
        rw [hg, MvPolynomial.eval₂Hom_zero'_apply]
        rfl
      let l : MvPolynomial τ R →ₛₗ[MvPolynomial.constantCoeff] Polynomial R :=
        { e.toAddMonoidHom with
          map_smul' := fun a b => by
            change e (MvPolynomial.rename f a * b) =
              MvPolynomial.constantCoeff a • e b
            rw [map_mul, hcomp]
            exact (Algebra.smul_def _ _).symm }
      let : Module.Finite (MvPolynomial σ R) (MvPolynomial τ R) := h
      exact Polynomial.not_finite (R := R) (Module.Finite.of_surjective l he)
  · rintro (hf | hR)
    · exact Module.Finite.of_surjective
        (Algebra.linearMap (MvPolynomial σ R) (MvPolynomial τ R))
        (MvPolynomial.rename_surjective f hf)
    · let := hR
      infer_instance
