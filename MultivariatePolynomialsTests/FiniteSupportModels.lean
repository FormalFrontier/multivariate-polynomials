/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Examples of transport of finitely supported coefficient arrays

An embedding of index types preserves every source coefficient and distinguishes
coefficient arrays over any additive commutative monoid. The index types and the
coefficient type may lie in independent universes. Zero coefficients do not
distinguish indices, whereas a chosen nonzero coefficient does.

The empty index type gives only the zero array. A function to an empty target
forces the source to be empty as well; no nonempty-source assumption is imposed.
For the constant function from `Fin 2` to `Unit`, coefficients in `ZMod 1` still
give injective transport because all coefficient arrays are equal. Natural-number
coefficients instead give two distinct single-point arrays with the same image.
Extended natural numbers provide nontrivial coefficients whose top element
absorbs addition: adding a second nonzero entry can also leave the image unchanged.
A two-entry example with independently lifted index and coefficient types records
preserved values and a zero value outside the image of an embedding.

## References

* Mathlib, `Mathlib.Data.Finsupp.Basic`: domain transport, transport of single-point
  arrays, and coefficient recovery along an injective index function.
* Mathlib, `Mathlib.Data.Finsupp.Single` and `Mathlib.Data.Finsupp.Defs`:
  single-point arrays and subsingleton instances for empty indices or coefficients.
* Mathlib, `Mathlib.Data.ZMod.Defs`, `Mathlib.Data.ENat.Monoid`, and
  `Mathlib.Algebra.Group.ULift`: the coefficient structures used in the examples.
-/

universe u v w

noncomputable section

namespace Finsupp

/-- An embedding preserves each coefficient and reflects equality of arrays,
using only additive commutative monoid structure on the coefficients. -/
private theorem embedding_preserves_coefficients_and_equality
    {α : Type u} {β : Type v} {M : Type w} [AddCommMonoid M]
    (e : α ↪ β) (x y : α →₀ M) :
    (∀ a, mapDomain e x (e a) = x a) ∧
      (mapDomain e x = mapDomain e y ↔ x = y) := by
  exact ⟨fun a => mapDomain_apply_of_injective e.injective x a,
    (mapDomain_injective e.injective).eq_iff⟩

/-- Zero-valued single-point arrays coincide, but a chosen nonzero value
separates two distinct indices without any addition on the coefficients. -/
private theorem zero_and_nonzero_singles
    {α : Type u} {M : Type w} [Zero M]
    (a b : α) (hab : a ≠ b) (m : M) (hm : m ≠ 0) :
    (single a 0 : α →₀ M) = single b 0 ∧
      (single a m : α →₀ M) ≠ single b m := by
  exact ⟨by simp only [single_zero],
    fun h => hab (single_left_injective hm h)⟩

/-- The canonical function out of the empty type transports only the zero
array, and its action on arrays is injective even with nontrivial coefficients. -/
private theorem empty_source_transport
    {β : Type v} {M : Type w} [AddCommMonoid M] (x : Empty →₀ M) :
    x = 0 ∧ mapDomain (Empty.elim : Empty → β) x = 0 ∧
      Function.Injective (mapDomain (M := M) (Empty.elim : Empty → β)) := by
  have hx : x = 0 := Subsingleton.elim _ _
  refine ⟨hx, ?_, Function.injective_of_subsingleton _⟩
  rw [hx, mapDomain_zero]

/-- A function to the empty type forces every source array to be zero.
The function is allowed without imposing a contradictory nonempty-source hypothesis. -/
private theorem empty_target_transport
    {α : Type u} {M : Type w} [AddCommMonoid M]
    (f : α → Empty) (x : α →₀ M) :
    x = 0 ∧ mapDomain f x = 0 ∧ Function.Injective (mapDomain (M := M) f) := by
  have hx : x = 0 := by
    apply Finsupp.ext
    intro a
    exact (f a).elim
  have hf : Function.Injective f := by
    intro a b _
    exact (f a).elim
  exact ⟨hx, Subsingleton.elim _ _, mapDomain_injective hf⟩

/-- The constant function identifies zero and one, which are distinct indices. -/
private theorem constant_fin_two_not_injective :
    ¬ Function.Injective (fun _ : Fin 2 => (() : Unit)) := by
  intro h
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  exact h01 (h rfl)

/-- A collision of indices causes no loss of information for the trivial
modular coefficient ring: its coefficient arrays, including its single with
coefficient one, are all zero. -/
private theorem zmod_one_collapse_injective :
    (0 : ZMod 1) = 1 ∧ ¬ Function.Injective (fun _ : Fin 2 => (() : Unit)) ∧
      Function.Injective (mapDomain (M := ZMod 1) (fun _ : Fin 2 => (() : Unit))) ∧
      (single (0 : Fin 2) (1 : ZMod 1) : Fin 2 →₀ ZMod 1) = 0 := by
  exact ⟨Subsingleton.elim _ _, constant_fin_two_not_injective,
    Function.injective_of_subsingleton _, Subsingleton.elim _ _⟩

/-- Two distinct natural-number single-point arrays have the same image
under the constant index function, so its action on arrays is not injective. -/
private theorem nat_singles_collapse :
    (single (0 : Fin 2) (1 : ℕ) : Fin 2 →₀ ℕ) ≠ single 1 1 ∧
      mapDomain (fun _ : Fin 2 => (() : Unit)) (single (0 : Fin 2) (1 : ℕ)) =
        mapDomain (fun _ : Fin 2 => (() : Unit)) (single 1 1) ∧
      ¬ Function.Injective (mapDomain (M := ℕ) (fun _ : Fin 2 => (() : Unit))) := by
  have hne : (single (0 : Fin 2) (1 : ℕ) : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    exact h01 (single_left_injective (by decide : (1 : ℕ) ≠ 0) h)
  have heq : mapDomain (fun _ : Fin 2 => (() : Unit)) (single (0 : Fin 2) (1 : ℕ)) =
      mapDomain (fun _ : Fin 2 => (() : Unit)) (single 1 1) := by
    simp only [mapDomain_single]
  exact ⟨hne, heq, fun h => hne (h heq)⟩

/-- Extended natural numbers are nontrivial, but adding top on the left
identifies zero and one, so this addition is not cancellative. -/
private theorem enat_top_add_not_injective :
    (0 : ℕ∞) ≠ 1 ∧ (⊤ : ℕ∞) + 0 = ⊤ + 1 ∧
      ¬ Function.Injective (fun m : ℕ∞ => (⊤ : ℕ∞) + m) := by
  have heq : (⊤ : ℕ∞) + 0 = ⊤ + 1 := by simp only [top_add]
  exact ⟨zero_ne_one, heq, fun h => zero_ne_one (h heq)⟩

/-- A nonzero top-valued array and the array obtained by adding a one-valued
entry at the other index are distinct. Transport along the constant index
function identifies them because top absorbs the extra coefficient. -/
private theorem enat_absorbing_collision :
    (single (0 : Fin 2) (⊤ : ℕ∞) : Fin 2 →₀ ℕ∞) ≠ 0 ∧
      (single (0 : Fin 2) (⊤ : ℕ∞) : Fin 2 →₀ ℕ∞) ≠
        single 0 ⊤ + single 1 1 ∧
      mapDomain (fun _ : Fin 2 => (() : Unit)) (single (0 : Fin 2) (⊤ : ℕ∞)) =
        mapDomain (fun _ : Fin 2 => (() : Unit)) (single 0 ⊤ + single 1 1) ∧
      ¬ Function.Injective (mapDomain (M := ℕ∞) (fun _ : Fin 2 => (() : Unit))) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hne : (single (0 : Fin 2) (⊤ : ℕ∞) : Fin 2 →₀ ℕ∞) ≠
      single 0 ⊤ + single 1 1 := by
    intro h
    have hcoeff := congrArg (fun x : Fin 2 →₀ ℕ∞ => x 1) h
    have h01 : (0 : ℕ∞) = 1 := by
      simpa only [add_apply, single_eq_of_ne h10, single_eq_same, zero_add] using hcoeff
    exact zero_ne_one h01
  have heq : mapDomain (fun _ : Fin 2 => (() : Unit)) (single (0 : Fin 2) (⊤ : ℕ∞)) =
      mapDomain (fun _ : Fin 2 => (() : Unit)) (single 0 ⊤ + single 1 1) := by
    simp only [mapDomain_add, mapDomain_single, ← single_add, top_add]
  exact ⟨single_ne_zero.mpr ENat.top_ne_zero, hne, heq, fun h => hne (h heq)⟩

/-- With source indices, target indices, and coefficients lifted into three
independent universes, the inclusion into optional indices preserves two
specified coefficients and is zero at the unused target index. -/
private theorem ulift_inclusion_preserves_two_coefficients :
    let f : ULift.{u} (Fin 2) → ULift.{v} (Option (Fin 2)) := fun a => ⟨some a.down⟩
    let x : ULift.{u} (Fin 2) →₀ ULift.{w} ℕ :=
      single ⟨0⟩ ⟨3⟩ + single ⟨1⟩ ⟨5⟩
    mapDomain f x (f ⟨0⟩) = ⟨3⟩ ∧
      mapDomain f x (f ⟨1⟩) = ⟨5⟩ ∧ mapDomain f x ⟨none⟩ = 0 := by
  let f : ULift.{u} (Fin 2) → ULift.{v} (Option (Fin 2)) := fun a => ⟨some a.down⟩
  let x : ULift.{u} (Fin 2) →₀ ULift.{w} ℕ :=
    single ⟨0⟩ ⟨3⟩ + single ⟨1⟩ ⟨5⟩
  change mapDomain f x (f ⟨0⟩) = ⟨3⟩ ∧
    mapDomain f x (f ⟨1⟩) = ⟨5⟩ ∧ mapDomain f x ⟨none⟩ = 0
  have h01 : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)
  have hf : Function.Injective f := by
    intro a b h
    apply Equiv.ulift.injective
    exact Option.some.inj (congrArg ULift.down h)
  refine ⟨?_, ?_, ?_⟩
  · rw [mapDomain_apply_of_injective hf]
    simp only [x, add_apply, single_eq_same, single_eq_of_ne h01, add_zero]
  · rw [mapDomain_apply_of_injective hf]
    simp only [x, add_apply, single_eq_same, single_eq_of_ne h01.symm, zero_add]
  · apply mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    have hnone : some a.down = (none : Option (Fin 2)) := congrArg ULift.down ha
    exact Option.some_ne_none a.down hnone

end Finsupp
