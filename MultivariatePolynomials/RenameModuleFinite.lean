/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Polynomial.Basic

import MultivariatePolynomials.RenameFiniteType
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

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
/-!
## Applications

These applications use `moduleFinite_rename_iff`, always with full source-polynomial
scalars and the displayed renaming action. They contrast coverage with injectivity,
finite type with module finiteness, and empty targets with missed variables.
-/

namespace MvPolynomial

/-- Infinitely many variables cause no obstruction for the identity, even over
`ℕ`, where one has no additive inverse. Its full-source action is multiplication. -/
private theorem nat_identity_application (p q : MvPolynomial ℕ ℕ) :
    Infinite ℕ ∧ (¬ ∃ n : ℕ, 1 + n = 0) ∧
    @SMul.smul (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      (rename (R := ℕ) (id : ℕ → ℕ)).toRingHom.toAlgebra.toSMul p q = p * q ∧
    @Module.Finite (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
        inferInstance inferInstance
        (rename (R := ℕ) (id : ℕ → ℕ)).toRingHom.toAlgebra) := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    exact Nat.succ_ne_zero n (by simpa only [Nat.add_comm] using hn)
  · change rename (id : ℕ → ℕ) p * q = p * q
    rw [rename_id_apply]
  · exact (moduleFinite_rename_iff (R := ℕ) (id : ℕ → ℕ)).mpr
      (Or.inl fun n => ⟨n, rfl⟩)

/-- Projection merges variables but covers every target variable. This works over
any commutative semiring, in particular `ℕ`; neither variable type is finite. -/
private theorem projection_application {R : Type u} [CommSemiring R]
    (p : MvPolynomial (ℕ × Bool) R) (q : MvPolynomial ℕ R) :
    (Infinite (ℕ × Bool) ∧ Infinite ℕ) ∧
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) ∧
    ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) ∧
    @SMul.smul (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R)
      (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra.toSMul p q =
        rename Prod.fst p * q ∧
    @Module.Finite (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R)
        inferInstance inferInstance
        (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra) := by
  have hf : Function.Surjective (Prod.fst : ℕ × Bool → ℕ) :=
    fun n => ⟨(n, false), rfl⟩
  refine ⟨⟨inferInstance, inferInstance⟩, hf, ?_, rfl,
    (moduleFinite_rename_iff (R := R) _).mpr (Or.inl hf)⟩
  intro h
  have hfalse : false = true := congrArg Prod.snd
    (h (show Prod.fst (0, false) = Prod.fst (0, true) from rfl))
  cases hfalse

/-- With zero coefficients even an empty source and infinitely many missed
variables give a finite module. The variable map itself is not surjective. -/
private theorem zero_coefficients_application :
    ¬ Function.Surjective (Empty.elim : Empty → ℕ) ∧
    @Module.Finite (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
        inferInstance inferInstance
        (rename (R := (ZMod 1)) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra) := by
  refine ⟨?_, (moduleFinite_rename_iff (R := ZMod 1) _).mpr (Or.inr inferInstance)⟩
  intro h
  obtain ⟨i, _⟩ := h 0
  exact Empty.elim i

/-- An empty target is harmless, for arbitrary coefficients, including `ℕ`. -/
private theorem empty_target_application {R : Type u} [CommSemiring R] :
    @Module.Finite (MvPolynomial Empty R) (MvPolynomial Empty R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial Empty R) (MvPolynomial Empty R)
        inferInstance inferInstance
        (rename (R := R) (Empty.elim : Empty → Empty)).toRingHom.toAlgebra) := by
  exact (moduleFinite_rename_iff (R := R) _).mpr (Or.inl fun i => Empty.elim i)

private def liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ :=
  fun i => ⟨i.down.1⟩

/-- The noninjective projection remains a finite-module example with independent
coefficient, source-variable and target-variable universes. -/
private theorem lifted_projection_application :
    (Infinite (ULift.{v} (ℕ × Bool)) ∧ Infinite (ULift.{w} ℕ)) ∧
    (0 : ULift.{u} ℕ) ≠ 1 ∧
    Function.Surjective (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ) ∧
    ¬ Function.Injective (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ) ∧
    @Module.Finite (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ))
        (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
        inferInstance inferInstance
        (rename (R := (ULift.{u} ℕ))
          (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ)).toRingHom.toAlgebra) := by
  have hf : Function.Surjective
      (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ) := by
    rintro ⟨n⟩
    exact ⟨⟨(n, false)⟩, rfl⟩
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, hf, ?_,
    (moduleFinite_rename_iff (R := ULift.{u} ℕ) _).mpr (Or.inl hf)⟩
  · intro h
    exact zero_ne_one (congrArg ULift.down h : (0 : ℕ) = 1)
  · intro h
    have heq : (⟨(0, false)⟩ : ULift.{v} (ℕ × Bool)) = ⟨(0, true)⟩ :=
      h (show liftedProjection (⟨(0, false)⟩ : ULift.{v} (ℕ × Bool)) =
        (liftedProjection (⟨(0, true)⟩ : ULift.{v} (ℕ × Bool)) : ULift.{w} ℕ) from rfl)
    have hfalse : false = true :=
      congrArg (fun i : ULift.{v} (ℕ × Bool) => i.down.2) heq
    cases hfalse

/-- Successor misses zero. The exact boundary is coefficient collapse, not
injectivity: the source and target polynomial types are nevertheless identical. -/
private theorem moduleFinite_succ_iff {R : Type u} [CommSemiring R] :
    @Module.Finite (MvPolynomial ℕ R) (MvPolynomial ℕ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ R) (MvPolynomial ℕ R)
        inferInstance inferInstance
        (rename (R := R) Nat.succ).toRingHom.toAlgebra) ↔ Subsingleton R := by
  constructor
  · intro h
    rcases (moduleFinite_rename_iff (R := R) Nat.succ).mp h with hf | hR
    · obtain ⟨n, hn⟩ := hf 0
      exact (Nat.succ_ne_zero n hn).elim
    · exact hR
  · intro hR
    exact (moduleFinite_rename_iff (R := R) Nat.succ).mpr (Or.inr hR)

private theorem not_moduleFinite_succ {R : Type u} [CommSemiring R] [Nontrivial R] :
    ¬ @Module.Finite (MvPolynomial ℕ R) (MvPolynomial ℕ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ R) (MvPolynomial ℕ R)
        inferInstance inferInstance
        (rename (R := R) Nat.succ).toRingHom.toAlgebra) := by
  intro h
  have hR := (moduleFinite_succ_iff (R := R)).mp h
  exact zero_ne_one (hR.elim 0 1)

/-- Over `ℕ`, successor renaming separates finite type from module finiteness.
Both assertions use the successor-induced structure, not the regular self-action. -/
private theorem nat_successor_application :
    @Algebra.FiniteType (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance (rename (R := ℕ) Nat.succ).toRingHom.toAlgebra ∧
    ¬ @Module.Finite (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
        inferInstance inferInstance
        (rename (R := ℕ) Nat.succ).toRingHom.toAlgebra) :=
  ⟨finiteType_rename_succ, not_moduleFinite_succ⟩

/-- A nonzero square-zero coefficient does not remove the missed-variable
obstruction: no reducedness assumption is needed. -/
private theorem nonreduced_successor_application :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
    ¬ @Module.Finite (MvPolynomial ℕ (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
        inferInstance inferInstance
        (rename (R := (ZMod 4)) Nat.succ).toRingHom.toAlgebra) := by
  refine ⟨by decide, by decide, ?_⟩
  let : Nontrivial (ZMod 4) := ⟨⟨2, 0, by decide⟩⟩
  exact not_moduleFinite_succ

/-- Nor is additive cancellation needed: extended naturals have absorbing top.
This is a semiring example, not an application of a ring-only finite-map lemma. -/
private theorem noncancellative_successor_application :
    (⊤ : ℕ∞) + 0 = ⊤ + 1 ∧ (0 : ℕ∞) ≠ 1 ∧
    ¬ @Module.Finite (MvPolynomial ℕ ℕ∞) (MvPolynomial ℕ ℕ∞)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ ℕ∞) (MvPolynomial ℕ ℕ∞)
        inferInstance inferInstance
        (rename (R := ℕ∞) Nat.succ).toRingHom.toAlgebra) :=
  ⟨rfl, zero_ne_one, not_moduleFinite_succ⟩

/-- In contrast with the empty target, a single missed variable over `ℕ` already
prevents module finiteness. -/
private theorem empty_source_application :
    ¬ @Module.Finite (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ)
        inferInstance inferInstance
        (rename (R := ℕ) (Empty.elim : Empty → Unit)).toRingHom.toAlgebra) := by
  intro h
  rcases (moduleFinite_rename_iff (R := ℕ) (Empty.elim : Empty → Unit)).mp h with hf | hR
  · obtain ⟨i, _⟩ := hf ()
    exact Empty.elim i
  · exact zero_ne_one (hR.elim 0 1)

/-- The missed-zero obstruction also survives independent lifts of all three
universes; the coefficient semiring is still the lifted natural numbers. -/
private theorem lifted_successor_application :
    ¬ @Module.Finite (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
        (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
        inferInstance inferInstance
        (rename (R := (ULift.{u} ℕ))
          (fun n : ULift.{v} ℕ => (⟨n.down.succ⟩ : ULift.{w} ℕ))).toRingHom.toAlgebra) := by
  intro h
  rcases (moduleFinite_rename_iff (R := ULift.{u} ℕ)
    (fun n : ULift.{v} ℕ => (⟨n.down.succ⟩ : ULift.{w} ℕ))).mp h with hf | hR
  · obtain ⟨n, hn⟩ := hf ⟨0⟩
    exact Nat.succ_ne_zero n.down (congrArg ULift.down hn)
  · exact zero_ne_one (congrArg ULift.down (hR.elim 0 1) : (0 : ℕ) = 1)

end MvPolynomial
