/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameFiniteType
public import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.Algebra.MvPolynomial.Variables

@[expose] public section

/-!
# Essentially finite type of variable renaming

A polynomial renaming is essentially of finite type precisely when the coefficient ring is
subsingleton or only finitely many target variables lie outside the range of the variable map.
The algebra structure is over the full source polynomial ring: a source polynomial acts by
multiplication by its renamed image, not merely by coefficient scalars.

For nontrivial coefficients, the necessity follows because maps from an essentially finite
type algebra are determined by finitely many elements. Those polynomials involve only finitely
many variables. A missed variable outside that finite union can be sent to zero by an
endomorphism fixing both the renamed source and every essential generator, contradicting
uniqueness. Sufficiency follows from finite type.

## References

* `MultivariatePolynomials.RenameFiniteType`: the finite-type renaming criterion over the
  full source polynomial semiring.
* Mathlib, `Mathlib.RingTheory.EssentialFiniteness` and
  `Mathlib.RingTheory.RingHom.EssFiniteType`: essential generators and uniqueness of ring maps.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Variables`: finite variable sets and evaluation.
-/

universe u v w

namespace MvPolynomial

/-- Renaming is essentially of finite type over the full source polynomial ring exactly when
its coefficient ring is subsingleton or only finitely many target variables are missed. -/
theorem essFiniteType_rename_iff {R : Type u} {σ : Type v} {τ : Type w}
    [CommRing R] (f : σ → τ) :
    RingHom.EssFiniteType ((rename (R := R) f).toRingHom) ↔
      Subsingleton R ∨ Set.Finite ((Set.range f)ᶜ) := by
  classical
  constructor
  · intro hf
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inl hR
    let : Nontrivial R := hR
    let S : Finset τ := hf.finset.biUnion vars
    refine Or.inr (S.finite_toSet.subset ?_)
    intro j hj
    by_contra hjS
    let δ : τ → MvPolynomial τ R := fun k => if k = j then 0 else X k
    let e : MvPolynomial τ R →ₐ[R] MvPolynomial τ R := aeval δ
    have hδ : δ ∘ f = (X : τ → MvPolynomial τ R) ∘ f := by
      funext i
      have hfi : f i ≠ j := fun h => hj ⟨i, h⟩
      simp [δ, hfi]
    have hcomp : e.comp (rename f) = rename f := by
      change (aeval δ).comp (rename f) = rename f
      rw [aeval_comp_rename, hδ, ← rename_eq_aeval]
    have hgen (p : MvPolynomial τ R) (hp : p ∈ hf.finset) : e p = p := by
      have hpvars : (p.vars : Set τ) ⊆ ({j} : Set τ)ᶜ := by
        intro k hk
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hkj
        subst k
        exact hjS (Finset.mem_biUnion.mpr ⟨p, hp, hk⟩)
      simpa [e, δ, Set.mem_compl_iff, Set.mem_singleton_iff, ite_not] using
        (aeval_ite_mem_eq_self p hpvars)
    have he : e.toRingHom = RingHom.id (MvPolynomial τ R) := by
      apply hf.ext
      · change (e.comp (rename f)).toRingHom = (rename f).toRingHom
        exact congrArg AlgHom.toRingHom hcomp
      · intro p hp
        exact hgen p hp
    have hX : (0 : MvPolynomial τ R) = X j := by
      simpa [e, δ] using RingHom.congr_fun he (X j)
    exact (X_ne_zero j) hX.symm
  · intro h
    apply RingHom.FiniteType.essFiniteType
    exact (finiteType_rename_iff (R := R) f).mpr h

private theorem essFiniteType_rename_succ_int :
    RingHom.EssFiniteType ((rename (R := ℤ) Nat.succ).toRingHom) := by
  exact (essFiniteType_rename_iff (R := ℤ) Nat.succ).mpr
    ((finiteType_rename_iff (R := ℤ) Nat.succ).mp
      (finiteType_rename_succ (R := ℤ)))

end MvPolynomial
