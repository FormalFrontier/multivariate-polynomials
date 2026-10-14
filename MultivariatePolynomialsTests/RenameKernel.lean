/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Examples of variable collisions and renaming kernels

Injective variable maps have bottom, finitely generated kernels, even for infinite
source types. Empty source types and maps to uninhabited targets give the same
boundary without choosing a target variable. The coefficient and the two variable
types in these examples are independently universe-polymorphic.

The predecessor map on natural numbers has exactly two collision participants,
zero and one, and a nonzero variable difference in its kernel over the integers.
Projection from `ℕ × Bool` has every source variable in a collision, so its collision
set is infinite. The finite-collision or subsingleton-coefficient alternative is
false for this projection over both `ℤ` and the nonreduced ring `ZMod 4`.
Over `ZMod 1`, the same projection instead has a top, finitely generated kernel.

These examples use polynomial renaming, kernel calculus, and finite generation from
Mathlib. The collision calculations describe the indexing functions; they do not
identify the predecessor kernel's generators or assert failure of finite generation
for the paired projection over nontrivial coefficients.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: injectivity of renaming and
  images of variables.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic`: injectivity of distinct variables
  over nontrivial coefficients.
* Mathlib, `Mathlib.RingTheory.Ideal.Maps` and `Mathlib.RingTheory.Finiteness.Basic`:
  bottom kernels of injections, top kernels with subsingleton targets, and finite
  generation of bottom and top ideals.
* Mathlib, `Mathlib.Data.ZMod.Basic`: modular coefficient rings.
-/

universe u v w

namespace MvPolynomial

/-- An embedding gives a bottom kernel and no collision participants, with no
restriction on the cardinalities or universes of the indexing types. -/
private theorem embedding_kernel_facts
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f) :
    RingHom.ker (rename (R := R) f).toRingHom = ⊥ ∧
      (RingHom.ker (rename (R := R) f).toRingHom).FG ∧
      {i : σ | ∃ j : σ, i ≠ j ∧ f i = f j} = ∅ := by
  have hker : RingHom.ker (rename (R := R) f).toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (rename_injective f hf)
  refine ⟨hker, ?_, ?_⟩
  · rw [hker]
    exact Submodule.fg_bot
  · ext i
    constructor
    · rintro ⟨j, hij, heq⟩
      exact False.elim (hij (hf heq))
    · intro hi
      cases hi

-- Infinite source and target types do not preclude a bottom kernel.
example :
    Infinite ℕ ∧ RingHom.ker (rename (R := ℤ) (id : ℕ → ℕ)).toRingHom = ⊥ ∧
      (RingHom.ker (rename (R := ℤ) (id : ℕ → ℕ)).toRingHom).FG := by
  have h := embedding_kernel_facts (R := ℤ) (id : ℕ → ℕ) Function.injective_id
  exact ⟨inferInstance, h.1, h.2.1⟩

-- A map out of any uninhabited source is an embedding.
example {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] [IsEmpty σ]
    (f : σ → τ) :
    RingHom.ker (rename (R := R) f).toRingHom = ⊥ ∧
      (RingHom.ker (rename (R := R) f).toRingHom).FG := by
  have hf : Function.Injective f := by
    intro i j _
    exact isEmptyElim i
  have h := embedding_kernel_facts (R := R) f hf
  exact ⟨h.1, h.2.1⟩

-- A function to an uninhabited target forces the source to be uninhabited.
example {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] [IsEmpty τ]
    (f : σ → τ) :
    RingHom.ker (rename (R := R) f).toRingHom = ⊥ ∧
      (RingHom.ker (rename (R := R) f).toRingHom).FG := by
  have hf : Function.Injective f := by
    intro i j _
    exact isEmptyElim (f i)
  have h := embedding_kernel_facts (R := R) f hf
  exact ⟨h.1, h.2.1⟩

-- The elimination map supplies data with both variable types empty at independent universes.
example {R : Type u} [CommRing R] :
    RingHom.ker
        (rename (R := R) (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1})).toRingHom = ⊥ ∧
      (RingHom.ker
        (rename (R := R) (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1})).toRingHom).FG := by
  have hf : Function.Injective (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1}) := by
    intro i j _
    exact i.elim
  have h := embedding_kernel_facts (R := R) PEmpty.elim hf
  exact ⟨h.1, h.2.1⟩

/-- The only nonsingleton fibre of predecessor is the fibre containing zero and one. -/
private theorem pred_collision_set :
    {i : ℕ | ∃ j : ℕ, i ≠ j ∧ Nat.pred i = Nat.pred j} = ({0, 1} : Set ℕ) := by
  ext i
  constructor
  · rintro ⟨j, hij, heq⟩
    cases i with
    | zero => simp
    | succ i =>
      cases i with
      | zero => simp
      | succ i =>
        cases j with
        | zero =>
          change Nat.succ i = 0 at heq
          exact False.elim (Nat.succ_ne_zero i heq)
        | succ j =>
          change Nat.succ i = j at heq
          exact False.elim (hij (congrArg Nat.succ heq))
  · intro hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · exact ⟨1, Nat.zero_ne_one, rfl⟩
    · exact ⟨0, Nat.one_ne_zero, rfl⟩

example :
    {i : ℕ | ∃ j : ℕ, i ≠ j ∧ Nat.pred i = Nat.pred j} = ({0, 1} : Set ℕ) ∧
      Set.Finite {i : ℕ | ∃ j : ℕ, i ≠ j ∧ Nat.pred i = Nat.pred j} := by
  refine ⟨pred_collision_set, ?_⟩
  rw [pred_collision_set]
  exact (Set.finite_singleton 1).insert 0

-- This witnesses a nonzero kernel, without claiming its full ideal presentation or FG.
example :
    (X 0 - X 1 : MvPolynomial ℕ ℤ) ≠ 0 ∧
      (X 0 - X 1 : MvPolynomial ℕ ℤ) ∈
        RingHom.ker (rename (R := ℤ) Nat.pred).toRingHom := by
  constructor
  · intro h
    exact Nat.zero_ne_one (X_injective (sub_eq_zero.mp h))
  · rw [RingHom.sub_mem_ker_iff]
    change rename (R := ℤ) Nat.pred (X 0) = rename (R := ℤ) Nat.pred (X 1)
    rw [rename_X, rename_X]
    rfl

/-- Projection onto the natural-number index has two-element fibres, with every
source variable participating in a collision. -/
private theorem paired_collision_set :
    {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j} = Set.univ := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rcases i with ⟨n, b⟩
  cases b
  · exact ⟨(n, true), by simp, rfl⟩
  · exact ⟨(n, false), by simp, rfl⟩

private theorem paired_collision_set_infinite :
    {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j}.Infinite := by
  rw [paired_collision_set]
  exact Set.infinite_univ

example :
    {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j} = Set.univ ∧
      {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j}.Infinite := by
  exact ⟨paired_collision_set, paired_collision_set_infinite⟩

-- This is a calculation of the coefficient/collision alternative, not a kernel non-FG proof.
example :
    ¬ (Subsingleton ℤ ∨
      Set.Finite {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j}) := by
  rintro (h | h)
  · exact zero_ne_one (@Subsingleton.elim ℤ h 0 1)
  · exact paired_collision_set_infinite h

-- A nonzero square-zero coefficient is compatible with the same infinite collision data.
example :
    Nontrivial (ZMod 4) ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      ¬ (Subsingleton (ZMod 4) ∨
        Set.Finite {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j}) := by
  refine ⟨ZMod.nontrivial_iff.mpr (by decide), by decide, by decide, ?_⟩
  rintro (h | h)
  · exact (by decide : (4 : ℕ) ≠ 1) (ZMod.subsingleton_iff.mp h)
  · exact paired_collision_set_infinite h

-- Subsingleton coefficients give a top FG kernel despite the infinite collision set.
example :
    Subsingleton (ZMod 1) ∧
      {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j}.Infinite ∧
      RingHom.ker (rename (R := ZMod 1) (Prod.fst : ℕ × Bool → ℕ)).toRingHom = ⊤ ∧
      (RingHom.ker (rename (R := ZMod 1) (Prod.fst : ℕ × Bool → ℕ)).toRingHom).FG := by
  have hker :
      RingHom.ker (rename (R := ZMod 1) (Prod.fst : ℕ × Bool → ℕ)).toRingHom = ⊤ :=
    RingHom.ker_eq_top_of_subsingleton _
  refine ⟨inferInstance, paired_collision_set_infinite, hker, ?_⟩
  rw [hker]
  exact Ideal.fg_top _

end MvPolynomial
