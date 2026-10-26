/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

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

/-!
## Applications

All integrality statements here are over the full source polynomial ring through
renaming. These applications identify integral renamings by target-variable
coverage or coefficient collapse. The successor examples use
`isIntegral_X_rename_iff` directly, keeping the renaming-induced algebra explicit
even when the source and target polynomial types coincide.
-/

namespace MvPolynomial

/-- Identity renaming over the integers is integral despite infinitely many
variables; the coefficients are nontrivial. -/
private theorem integer_identity_application :
    Infinite ℕ ∧ (0 : ℤ) ≠ 1 ∧ RingHom.IsIntegral ((rename (R := ℤ) (id : ℕ → ℕ)).toRingHom) := by
  exact ⟨inferInstance, zero_ne_one,
    (isIntegral_rename_iff (R := ℤ) _).mpr (Or.inl fun n => ⟨n, rfl⟩)⟩

/-- Projection is integral over every commutative coefficient ring, including
`ℤ`. Infinite variable sets and collisions are compatible with integrality. -/
private theorem projection_application {R : Type u} [CommRing R] :
    (Infinite (ℕ × Bool) ∧ Infinite ℕ) ∧
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) ∧
    ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) ∧
    RingHom.IsIntegral ((rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom) := by
  have hf : Function.Surjective (Prod.fst : ℕ × Bool → ℕ) :=
    fun n => ⟨(n, false), rfl⟩
  refine ⟨⟨inferInstance, inferInstance⟩, hf, ?_,
    (isIntegral_rename_iff (R := R) _).mpr (Or.inl hf)⟩
  intro h
  have hpair : ((0 : ℕ), false) = (0, true) := h rfl
  cases congrArg Prod.snd hpair

/-- Zero coefficients collapse the target: an empty source gives a surjective
polynomial homomorphism even though its variable map misses every natural number. -/
private theorem zero_coefficients_application :
    ¬ Function.Surjective (Empty.elim : Empty → ℕ) ∧
    Subsingleton (MvPolynomial ℕ (ZMod 1)) ∧
    Function.Surjective ((rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom) ∧
    RingHom.IsIntegral ((rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom) := by
  have htarget : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) _
  refine ⟨?_, htarget, ?_,
    (isIntegral_rename_iff (R := ZMod 1) _).mpr (Or.inr inferInstance)⟩
  · intro h
    obtain ⟨i, _⟩ := h 0
    exact Empty.elim i
  · let := htarget
    exact Function.surjective_to_subsingleton _

/-- With an empty target, arbitrary coefficient rings work without nontriviality;
this includes the empty-to-empty integer example. -/
private theorem empty_target_application {R : Type u} [CommRing R] :
    RingHom.IsIntegral ((rename (R := R) (Empty.elim : Empty → Empty)).toRingHom) := by
  exact (isIntegral_rename_iff (R := R) _).mpr (Or.inl fun i => Empty.elim i)

/-- Identity transport between separately lifted variable universes, with a third
independent lift for the integer coefficients. This is not a projection map. -/
private theorem lifted_identity_application :
    (0 : ULift.{u} ℤ) ≠ 1 ∧
    Function.Surjective (fun n : ULift.{v} ℕ => (ULift.up n.down : ULift.{w} ℕ)) ∧
    RingHom.IsIntegral ((rename (R := ULift.{u} ℤ)
      (fun n : ULift.{v} ℕ => (ULift.up n.down : ULift.{w} ℕ))).toRingHom) := by
  have hf : Function.Surjective
      (fun n : ULift.{v} ℕ => (ULift.up n.down : ULift.{w} ℕ)) := by
    intro n
    exact ⟨ULift.up n.down, rfl⟩
  refine ⟨?_, hf, (isIntegral_rename_iff (R := ULift.{u} ℤ) _).mpr (Or.inl hf)⟩
  intro h
  exact zero_ne_one (congrArg ULift.down h : (0 : ℤ) = 1)

/-- Successor renaming is integral exactly at the zero-ring boundary. -/
private theorem isIntegral_succ_iff {R : Type u} [CommRing R] :
    RingHom.IsIntegral ((rename (R := R) Nat.succ).toRingHom) ↔ Subsingleton R := by
  constructor
  · intro h
    rcases (isIntegral_rename_iff (R := R) Nat.succ).mp h with hf | hR
    · obtain ⟨n, hn⟩ := hf 0
      exact (Nat.succ_ne_zero n hn).elim
    · exact hR
  · intro hR
    exact (isIntegral_rename_iff (R := R) Nat.succ).mpr (Or.inr hR)

private theorem not_isIntegral_succ {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ RingHom.IsIntegral ((rename (R := R) Nat.succ).toRingHom) := by
  intro h
  have hR := (isIntegral_succ_iff (R := R)).mp h
  exact zero_ne_one (hR.elim 0 1)

/-- The integer instance is an injective, nonsurjective renaming which is not
integral over the full source polynomial ring. -/
private theorem integer_successor_application :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ ∧
    ¬ RingHom.IsIntegral ((rename (R := ℤ) Nat.succ).toRingHom) := by
  refine ⟨Nat.succ_injective, ?_, not_isIntegral_succ⟩
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

/-- For the successor-induced algebra, `X 1` comes from the source, while `X 0`
is integral precisely when the coefficients collapse. Under the default identity
algebra both would instead be images of source elements. -/
private theorem successor_variables {R : Type u} [CommRing R] :
    @IsIntegral (MvPolynomial ℕ R) (MvPolynomial ℕ R) inferInstance inferInstance
      (rename (R := R) Nat.succ).toRingHom.toAlgebra (X 1) ∧
    (@IsIntegral (MvPolynomial ℕ R) (MvPolynomial ℕ R) inferInstance inferInstance
      (rename (R := R) Nat.succ).toRingHom.toAlgebra (X 0) ↔ Subsingleton R) := by
  constructor
  · exact (isIntegral_X_rename_iff (R := R) Nat.succ 1).mpr (Or.inl ⟨0, rfl⟩)
  · constructor
    · intro h
      rcases (isIntegral_X_rename_iff (R := R) Nat.succ 0).mp h with ⟨n, hn⟩ | hR
      · exact (Nat.succ_ne_zero n hn).elim
      · exact hR
    · intro hR
      exact (isIntegral_X_rename_iff (R := R) Nat.succ 0).mpr (Or.inr hR)

private theorem successor_zero_not_integral
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ @IsIntegral (MvPolynomial ℕ R) (MvPolynomial ℕ R) inferInstance inferInstance
      (rename (R := R) Nat.succ).toRingHom.toAlgebra (X 0) := by
  intro h
  have hR := (successor_variables (R := R)).2.mp h
  exact zero_ne_one (hR.elim 0 1)

/-- The same nonreduced coefficient ring has both outcomes: projection is
integral, successor is not, and the coefficient `2` is nonzero and square-zero. -/
private theorem nonreduced_applications :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
    RingHom.IsIntegral ((rename (R := ZMod 4) (Prod.fst : ℕ × Bool → ℕ)).toRingHom) ∧
    ¬ RingHom.IsIntegral ((rename (R := ZMod 4) Nat.succ).toRingHom) := by
  refine ⟨by decide, by decide,
    (isIntegral_rename_iff (R := ZMod 4) _).mpr (Or.inl fun n => ⟨(n, false), rfl⟩), ?_⟩
  let : Nontrivial (ZMod 4) := ⟨⟨2, 0, by decide⟩⟩
  exact not_isIntegral_succ

private def shiftedProjection : ℕ × Bool → ℕ := fun p => p.1 + 1

/-- The shifted projection is neither injective nor surjective and is nonintegral
over any nontrivial commutative ring, in particular `ℤ`. Comparing with projection
shows that missing a target, rather than merging sources, is the obstruction. -/
private theorem shifted_projection_application
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ Function.Injective shiftedProjection ∧
    ¬ Function.Surjective shiftedProjection ∧
    ¬ RingHom.IsIntegral ((rename (R := R) shiftedProjection).toRingHom) := by
  have hf : ¬ Function.Surjective shiftedProjection := by
    intro h
    obtain ⟨p, hp⟩ := h 0
    exact Nat.succ_ne_zero p.1 hp
  refine ⟨?_, hf, ?_⟩
  · intro h
    have hpair : ((0 : ℕ), false) = (0, true) := h rfl
    cases congrArg Prod.snd hpair
  · intro h
    rcases (isIntegral_rename_iff (R := R) shiftedProjection).mp h with hs | hR
    · exact hf hs
    · exact zero_ne_one (hR.elim 0 1)

/-- A single missed variable already obstructs integrality over an empty source
with integer coefficients, unlike the empty-target and zero-coefficient cases. -/
private theorem empty_source_application :
    ¬ Function.Surjective (Empty.elim : Empty → Unit) ∧
    ¬ RingHom.IsIntegral ((rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom) := by
  have hf : ¬ Function.Surjective (Empty.elim : Empty → Unit) := by
    intro h
    obtain ⟨i, _⟩ := h ()
    exact Empty.elim i
  refine ⟨hf, ?_⟩
  intro h
  rcases (isIntegral_rename_iff (R := ℤ) (Empty.elim : Empty → Unit)).mp h with hs | hR
  · exact hf hs
  · exact zero_ne_one (hR.elim 0 1)

private def liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨n.down.succ⟩

/-- The omitted lifted zero still obstructs integrality with three independent
universes and lifted integer coefficients. -/
private theorem lifted_successor_application :
    ¬ Function.Surjective (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ) ∧
    ¬ RingHom.IsIntegral ((rename (R := ULift.{u} ℤ)
      (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom) := by
  have hf : ¬ Function.Surjective
      (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ) := by
    intro h
    obtain ⟨n, hn⟩ := h ⟨0⟩
    exact Nat.succ_ne_zero n.down (congrArg ULift.down hn)
  refine ⟨hf, ?_⟩
  intro h
  rcases (isIntegral_rename_iff (R := ULift.{u} ℤ)
    (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).mp h with hs | hR
  · exact hf hs
  · exact zero_ne_one (congrArg ULift.down (hR.elim 0 1) : (0 : ℤ) = 1)

end MvPolynomial
