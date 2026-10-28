/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
import MultivariatePolynomials.FiniteSupport
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic

/-!
# Injectivity and surjectivity of polynomial variable renaming

For a map `f : σ → τ` and a commutative semiring `R`, variable renaming is the
homomorphism from the full polynomial semiring `MvPolynomial σ R` to the full
polynomial semiring `MvPolynomial τ R` that sends `X i` to `X (f i)`.

Its underlying function is injective exactly when `f` is injective or `R` is
subsingleton, and surjective exactly when `f` is surjective or `R` is subsingleton.
The coefficient and two variable types may lie in independent universes. Neither
variable type is required to be finite or inhabited, and the coefficients need
not form a ring or be nontrivial.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: variable renaming and its
  injectivity and surjectivity for injective and surjective variable maps.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]

/-- Polynomial variable renaming is injective exactly when the variable map is
injective or the coefficient semiring is subsingleton. -/
theorem injective_rename_iff (f : σ → τ) :
    Function.Injective (rename (R := R) f) ↔
      Function.Injective f ∨ Subsingleton R := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · left
      intro i j hij
      apply X_injective (R := R)
      apply h
      simpa only [rename_X] using congrArg (X (R := R)) hij
  · rintro (hf | hR)
    · exact rename_injective f hf
    · exact Function.injective_of_subsingleton _

/-- Polynomial variable renaming is surjective exactly when the variable map is
surjective or the coefficient semiring is subsingleton. -/
theorem surjective_rename_iff (f : σ → τ) :
    Function.Surjective (rename (R := R) f) ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · left
      intro t
      obtain ⟨p, hp⟩ := h (X t)
      have ht : t ∈ (rename f p).vars := by
        rw [hp, vars_X]
        exact Finset.mem_singleton_self t
      obtain ⟨s, _, hs⟩ := mem_vars_rename f p ht
      exact ⟨s, hs⟩
  · rintro (hf | hR)
    · exact rename_surjective f hf
    · have : Nonempty (MvPolynomial σ R) := ⟨0⟩
      exact Function.surjective_to_subsingleton _

end MvPolynomial

/-!
## Renaming over nontrivial coefficients

Over a nontrivial coefficient semiring, the subsingleton alternative is
impossible. Polynomial renaming therefore reflects injectivity and surjectivity
of the variable map, not merely preserving them. These applications require
neither finiteness nor inhabitedness of either variable type.

Formalization: Formal Frontier Agents, using Mathlib's
`not_subsingleton_iff_nontrivial`.
-/

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]

private theorem injective_rename_iff_of_nontrivial [Nontrivial R] (f : σ → τ) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) ↔
      Function.Injective f := by
  have hR : ¬ Subsingleton R := not_subsingleton_iff_nontrivial.mpr inferInstance
  simpa only [hR, or_false] using MvPolynomial.injective_rename_iff (R := R) f

private theorem surjective_rename_iff_of_nontrivial [Nontrivial R] (f : σ → τ) :
    Function.Surjective (rename f : MvPolynomial σ R → MvPolynomial τ R) ↔
      Function.Surjective f := by
  have hR : ¬ Subsingleton R := not_subsingleton_iff_nontrivial.mpr inferInstance
  simpa only [hR, or_false] using MvPolynomial.surjective_rename_iff (R := R) f

end MvPolynomial

/-!
## Collisions and missing indeterminates

The following applications distinguish identifying variables from omitting them.
They use Mathlib's renaming API directly: the obstructions concern entire
polynomial maps, not just coefficients. The same maps work over a semiring and
over a nonreduced ring; lifting the successor separates all three universes.

Formalization: Formal Frontier Agents, using Mathlib's `rename_X`,
`mem_vars_rename`, `rename_injective` and `rename_surjective`.
-/

/-!
# Noninjective and nonsurjective polynomial renamings

Projection from `ℕ × Bool` identifies two distinct indeterminates, even though every target
variable has a preimage. Successor misses the indeterminate indexed by zero. Their combination
both identifies indeterminates and misses one. These phenomena occur over both `ℕ` and the
nonreduced ring `ZMod 4`.

The map from `Empty` to `Unit` is injective, but its polynomial renaming misses the target
indeterminate. A lifted successor gives the same obstruction with independently lifted
coefficient, source-variable, and target-variable universes.
-/

noncomputable section

namespace MvPolynomial
namespace RenameNegative

private def pairProjection : ℕ × Bool → ℕ := fun i => i.1

private def pairSuccessor : ℕ × Bool → ℕ := fun i => Nat.succ i.1

private def emptyToUnit : Empty → Unit := Empty.elim

private theorem pairProjection_not_injective : ¬ Function.Injective pairProjection := by
  intro h
  have hp : (0, false) = ((0, true) : ℕ × Bool) := h rfl
  have hb : false = true := congrArg Prod.snd hp
  cases hb

private theorem pairProjection_surjective : Function.Surjective pairProjection := by
  intro n
  exact ⟨(n, false), rfl⟩

private theorem successor_injective : Function.Injective Nat.succ := Nat.succ_injective

private theorem successor_not_surjective : ¬ Function.Surjective Nat.succ := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

private theorem pairSuccessor_not_injective : ¬ Function.Injective pairSuccessor := by
  intro h
  have hp : (0, false) = ((0, true) : ℕ × Bool) := h rfl
  have hb : false = true := congrArg Prod.snd hp
  cases hb

private theorem pairSuccessor_not_surjective : ¬ Function.Surjective pairSuccessor := by
  intro h
  obtain ⟨i, hi⟩ := h 0
  exact Nat.succ_ne_zero i.1 hi

private theorem emptyToUnit_injective : Function.Injective emptyToUnit := by
  intro i
  exact Empty.elim i

private theorem emptyToUnit_not_surjective : ¬ Function.Surjective emptyToUnit := by
  intro h
  obtain ⟨i, _⟩ := h ()
  exact Empty.elim i

section FixedMaps

variable {R : Type*} [CommSemiring R]

private theorem projection_X_collision :
    rename pairProjection (X (0, false) : MvPolynomial (ℕ × Bool) R) =
      rename pairProjection (X (0, true) : MvPolynomial (ℕ × Bool) R) := by
  simp only [rename_X, pairProjection]

private theorem pairSuccessor_X_collision :
    rename pairSuccessor (X (0, false) : MvPolynomial (ℕ × Bool) R) =
      rename pairSuccessor (X (0, true) : MvPolynomial (ℕ × Bool) R) := by
  simp only [rename_X, pairSuccessor]

variable [Nontrivial R]

private theorem pair_X_ne :
    (X (0, false) : MvPolynomial (ℕ × Bool) R) ≠ X (0, true) := by
  intro h
  have hp : (0, false) = ((0, true) : ℕ × Bool) := X_injective h
  have hb : false = true := congrArg Prod.snd hp
  cases hb

private theorem projection_map_not_injective :
    ¬ Function.Injective
      (rename pairProjection : MvPolynomial (ℕ × Bool) R → MvPolynomial ℕ R) := by
  intro h
  exact pair_X_ne (R := R) (h (projection_X_collision (R := R)))

private theorem successor_misses_X_zero :
    ¬ ∃ p : MvPolynomial ℕ R, rename Nat.succ p = X 0 := by
  classical
  rintro ⟨p, hp⟩
  have hz : 0 ∈ (rename Nat.succ p).vars := by
    rw [hp, vars_X]
    exact Finset.mem_singleton_self 0
  obtain ⟨n, _, hn⟩ := mem_vars_rename Nat.succ p hz
  exact Nat.succ_ne_zero n hn

private theorem successor_map_not_surjective :
    ¬ Function.Surjective
      (rename Nat.succ : MvPolynomial ℕ R → MvPolynomial ℕ R) := by
  intro h
  exact successor_misses_X_zero (R := R) (h (X 0))

private theorem pairSuccessor_map_not_injective :
    ¬ Function.Injective
      (rename pairSuccessor : MvPolynomial (ℕ × Bool) R → MvPolynomial ℕ R) := by
  intro h
  exact pair_X_ne (R := R) (h (pairSuccessor_X_collision (R := R)))

private theorem pairSuccessor_misses_X_zero :
    ¬ ∃ p : MvPolynomial (ℕ × Bool) R, rename pairSuccessor p = X 0 := by
  classical
  rintro ⟨p, hp⟩
  have hz : 0 ∈ (rename pairSuccessor p).vars := by
    rw [hp, vars_X]
    exact Finset.mem_singleton_self 0
  obtain ⟨i, _, hi⟩ := mem_vars_rename pairSuccessor p hz
  exact Nat.succ_ne_zero i.1 hi

private theorem pairSuccessor_map_not_surjective :
    ¬ Function.Surjective
      (rename pairSuccessor : MvPolynomial (ℕ × Bool) R → MvPolynomial ℕ R) := by
  intro h
  exact pairSuccessor_misses_X_zero (R := R) (h (X 0))

private theorem emptyToUnit_misses_X :
    ¬ ∃ p : MvPolynomial Empty R, rename emptyToUnit p = X () := by
  classical
  rintro ⟨p, hp⟩
  have hu : () ∈ (rename emptyToUnit p).vars := by
    rw [hp, vars_X]
    exact Finset.mem_singleton_self ()
  obtain ⟨i, _, _⟩ := mem_vars_rename emptyToUnit p hu
  exact Empty.elim i

private theorem emptyToUnit_map_not_surjective :
    ¬ Function.Surjective
      (rename emptyToUnit : MvPolynomial Empty R → MvPolynomial Unit R) := by
  intro h
  exact emptyToUnit_misses_X (R := R) (h (X ()))

end FixedMaps

private theorem nat_projection_not_injective :
    ¬ Function.Injective
      ((rename (R := ℕ) pairProjection).toRingHom :
        MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) :=
  projection_map_not_injective (R := ℕ)

private theorem nat_projection_surjective :
    Function.Surjective
      (rename pairProjection : MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) :=
  rename_surjective pairProjection pairProjection_surjective

private theorem nat_successor_injective :
    Function.Injective (rename Nat.succ : MvPolynomial ℕ ℕ → MvPolynomial ℕ ℕ) :=
  rename_injective Nat.succ successor_injective

private theorem nat_successor_not_surjective :
    ¬ Function.Surjective
      ((rename (R := ℕ) Nat.succ).toRingHom : MvPolynomial ℕ ℕ → MvPolynomial ℕ ℕ) :=
  successor_map_not_surjective (R := ℕ)

private theorem nat_pairSuccessor_not_injective :
    ¬ Function.Injective
      (rename pairSuccessor : MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) :=
  pairSuccessor_map_not_injective (R := ℕ)

private theorem nat_pairSuccessor_not_surjective :
    ¬ Function.Surjective
      ((rename (R := ℕ) pairSuccessor).toRingHom :
        MvPolynomial (ℕ × Bool) ℕ → MvPolynomial ℕ ℕ) :=
  pairSuccessor_map_not_surjective (R := ℕ)

private theorem nat_emptyToUnit_not_surjective :
    ¬ Function.Surjective
      (rename emptyToUnit : MvPolynomial Empty ℕ → MvPolynomial Unit ℕ) :=
  emptyToUnit_map_not_surjective (R := ℕ)

private theorem zmod4_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  decide

private theorem zmod4_two_sq_zero : (2 : ZMod 4) ^ 2 = 0 := by
  decide

private theorem zmod4_projection_not_injective :
    ¬ Function.Injective
      (rename pairProjection : MvPolynomial (ℕ × Bool) (ZMod 4) → MvPolynomial ℕ (ZMod 4)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact projection_map_not_injective (R := ZMod 4)

private theorem zmod4_projection_surjective :
    Function.Surjective
      ((rename (R := ZMod 4) pairProjection).toRingHom :
        MvPolynomial (ℕ × Bool) (ZMod 4) → MvPolynomial ℕ (ZMod 4)) :=
  rename_surjective pairProjection pairProjection_surjective

private theorem zmod4_successor_injective :
    Function.Injective
      (rename Nat.succ : MvPolynomial ℕ (ZMod 4) → MvPolynomial ℕ (ZMod 4)) :=
  rename_injective Nat.succ successor_injective

private theorem zmod4_successor_not_surjective :
    ¬ Function.Surjective
      ((rename (R := ZMod 4) Nat.succ).toRingHom :
        MvPolynomial ℕ (ZMod 4) → MvPolynomial ℕ (ZMod 4)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact successor_map_not_surjective (R := ZMod 4)

private theorem zmod4_pairSuccessor_not_injective :
    ¬ Function.Injective
      (rename pairSuccessor : MvPolynomial (ℕ × Bool) (ZMod 4) → MvPolynomial ℕ (ZMod 4)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact pairSuccessor_map_not_injective (R := ZMod 4)

private theorem zmod4_pairSuccessor_not_surjective :
    ¬ Function.Surjective
      (rename pairSuccessor : MvPolynomial (ℕ × Bool) (ZMod 4) → MvPolynomial ℕ (ZMod 4)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  exact pairSuccessor_map_not_surjective (R := ZMod 4)

private def liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨Nat.succ n.down⟩

private theorem liftedSuccessor_injective : Function.Injective liftedSuccessor.{v, w} := by
  intro a b h
  cases a with
  | up a =>
    cases b with
    | up b =>
      have hab : a = b := Nat.succ_injective (congrArg ULift.down h)
      exact congrArg ULift.up hab

private theorem liftedSuccessor_not_surjective :
    ¬ Function.Surjective liftedSuccessor.{v, w} := by
  intro h
  obtain ⟨n, hn⟩ := h (ULift.up 0)
  exact Nat.succ_ne_zero n.down (congrArg ULift.down hn)

private theorem liftedSuccessor_misses_X_zero :
    ¬ ∃ p : MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ),
      rename liftedSuccessor.{v, w} p =
        (X (ULift.up 0) : MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) := by
  classical
  rintro ⟨p, hp⟩
  have hz : (ULift.up 0 : ULift.{w} ℕ) ∈ (rename liftedSuccessor.{v, w} p).vars := by
    rw [hp, vars_X]
    exact Finset.mem_singleton_self _
  obtain ⟨n, _, hn⟩ := mem_vars_rename liftedSuccessor.{v, w} p hz
  exact Nat.succ_ne_zero n.down (congrArg ULift.down hn)

private theorem liftedSuccessor_map_injective :
    Function.Injective
      (rename liftedSuccessor.{v, w} :
        MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ) →
          MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) :=
  rename_injective liftedSuccessor.{v, w} liftedSuccessor_injective

private theorem liftedSuccessor_map_not_surjective :
    ¬ Function.Surjective
      ((rename (R := ULift.{u} ℕ) liftedSuccessor.{v, w}).toRingHom :
        MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ) →
          MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) := by
  intro h
  exact liftedSuccessor_misses_X_zero (h (X (ULift.up 0)))

end RenameNegative
end MvPolynomial
