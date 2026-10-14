/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameAlgebraic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Bool.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Algebraicity of variable renaming

The algebra structure in each statement is induced by renaming from the full
source polynomial ring to the full target polynomial ring. Its scalar action
is multiplication by the renamed source polynomial.

Algebraicity uses a nonzero annihilating polynomial, not necessarily a monic
polynomial or one of positive degree. Consequently a collision of source
variables can make this algebra algebraic even when a target variable is
omitted. In contrast, zero coefficients give no nonzero annihilating polynomial,
even for an identity renaming.

The examples below apply `MvPolynomial.isAlgebraic_rename_iff` to integer coefficients, the
nonreduced ring `ZMod 4`, zero coefficients, empty variable types, and lifts in
three independently chosen universes.
-/

universe u v w

namespace MvPolynomial

/-- Identity renaming on infinitely many variables over the integers is algebraic. -/
private theorem int_identity_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  apply (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) (id : ℕ → ℕ)).2
  refine ⟨inferInstance, Or.inl ?_⟩
  intro n
  exact ⟨n, rfl⟩

/-- Forgetting a Boolean coordinate gives an algebraic renaming over the integers. -/
private theorem int_projection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  apply (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).2
  refine ⟨inferInstance, Or.inl ?_⟩
  intro n
  exact ⟨(n, false), rfl⟩

/-- A shifted projection identifies variables and omits the zero variable. -/
private def shiftedProjection : ℕ × Bool → ℕ := fun p => p.1 + 1

/-- The shifted projection is algebraic despite omitting a target variable. -/
private theorem int_shiftedProjection_isAlgebraic :
    ¬ Function.Surjective shiftedProjection ∧
      @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h 0
    exact Nat.succ_ne_zero p.1 hp
  · apply (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) shiftedProjection).2
    refine ⟨inferInstance, Or.inr ?_⟩
    intro h
    have hpair : ((0 : ℕ), false) = (0, true) := h rfl
    cases congrArg Prod.snd hpair

/-- An injective renaming missing zero is not algebraic over the integers. -/
private theorem int_successor_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom.toAlgebra := by
  intro h
  rcases ((MvPolynomial.isAlgebraic_rename_iff (R := ℤ) Nat.succ).1 h).2 with hs | hi
  · obtain ⟨n, hn⟩ := hs 0
    exact Nat.succ_ne_zero n hn
  · exact hi (fun _ _ hab => Nat.succ.inj hab)

/-- The coefficient ring of order four has a nonzero square-zero element. -/
private theorem zmod_four_has_nonzero_square_zero :
    ∃ a : ZMod 4, a ≠ 0 ∧ a ^ 2 = 0 := by
  refine ⟨2, ?_, ?_⟩ <;> decide

/-- Projection remains algebraic with nonreduced coefficients. -/
private theorem zmod_four_projection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) (ZMod 4))
      (MvPolynomial ℕ (ZMod 4)) inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4)
        (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  obtain ⟨a, ha, _⟩ := zmod_four_has_nonzero_square_zero
  apply (MvPolynomial.isAlgebraic_rename_iff (R := ZMod 4) (Prod.fst : ℕ × Bool → ℕ)).2
  refine ⟨⟨⟨a, 0, ha⟩⟩, Or.inl ?_⟩
  intro n
  exact ⟨(n, false), rfl⟩

/-- Nonreduced coefficients do not make successor renaming algebraic. -/
private theorem zmod_four_successor_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4) Nat.succ).toRingHom.toAlgebra := by
  intro h
  rcases ((MvPolynomial.isAlgebraic_rename_iff (R := ZMod 4) Nat.succ).1 h).2 with hs | hi
  · obtain ⟨n, hn⟩ := hs 0
    exact Nat.succ_ne_zero n hn
  · exact hi (fun _ _ hab => Nat.succ.inj hab)

/-- Even an identity renaming is not algebraic when the coefficients are zero. -/
private theorem zmod_one_identity_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  intro h
  haveI : Nontrivial (ZMod 1) :=
    ((MvPolynomial.isAlgebraic_rename_iff (R := ZMod 1) (id : ℕ → ℕ)).1 h).1
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

/-- An empty source variable set does not change the zero-coefficient obstruction. -/
private theorem zmod_one_empty_to_nat_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1)
        (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra := by
  intro h
  haveI : Nontrivial (ZMod 1) :=
    ((MvPolynomial.isAlgebraic_rename_iff (R := ZMod 1) (Empty.elim : Empty → ℕ)).1 h).1
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

/-- The unique map between two empty variable types is a bijection. -/
private theorem empty_map_bijective :
    Function.Bijective (Empty.elim : Empty → Empty) := by
  constructor
  · intro i
    exact Empty.elim i
  · intro i
    exact Empty.elim i

/-- Empty variable sets still give algebraicity through their unique bijection. -/
private theorem int_empty_bijection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial Empty ℤ) (MvPolynomial Empty ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (Empty.elim : Empty → Empty)).toRingHom.toAlgebra := by
  exact (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) (Empty.elim : Empty → Empty)).2
    ⟨inferInstance, Or.inl empty_map_bijective.2⟩

/-- The underlying natural number is preserved between independent lifts. -/
private def liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨n.down⟩

/-- Coefficients and both variable types may occupy independent universes. -/
private theorem lifted_identity_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ)) inferInstance inferInstance
      (MvPolynomial.rename (R := ULift.{u} ℤ)
        (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra := by
  apply (MvPolynomial.isAlgebraic_rename_iff (R := ULift.{u} ℤ)
    (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ)).2
  refine ⟨inferInstance, Or.inl ?_⟩
  intro n
  exact ⟨⟨n.down⟩, rfl⟩

/-- Successor between independent lifts still omits lifted zero. -/
private def liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨n.down.succ⟩

/-- The missing-variable obstruction also retains three independent universes. -/
private theorem lifted_successor_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ)) inferInstance inferInstance
      (MvPolynomial.rename (R := ULift.{u} ℤ)
        (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra := by
  intro h
  rcases ((MvPolynomial.isAlgebraic_rename_iff (R := ULift.{u} ℤ)
    (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).1 h).2 with hs | hi
  · obtain ⟨n, hn⟩ := hs ⟨0⟩
    have hn' : n.down.succ = 0 := congrArg ULift.down hn
    exact Nat.succ_ne_zero n.down hn'
  · apply hi
    intro a b hab
    cases a with
    | up a =>
      cases b with
      | up b =>
        have hab' : a.succ = b.succ := congrArg ULift.down hab
        exact congrArg (fun n : ℕ => (ULift.up n : ULift.{v} ℕ)) (Nat.succ.inj hab')

end MvPolynomial
