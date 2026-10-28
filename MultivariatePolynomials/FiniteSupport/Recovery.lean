/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.FiniteSupport
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.ZMod.Basic

/-!
# Recovery from degree and support cardinality

`Finsupp.degree_support_injective_iff` says that the degree-support profile
recovers natural exponent vectors exactly for subsingleton variable types.
Distinct variables give degree-one, support-one vectors with the same profile.

Together with `Finsupp.mapDomain_injective_iff` and
`Function.injective_iff_hasLeftInverse`, this characterizes arbitrary total
functional recovery of profile-pushforward arrays over an independent
`M : Type w` with `[AddCommMonoid M]`: `Subsingleton σ ∨ Subsingleton M`.
Arrays are inhabited by zero; decoders need not be additive, linear or ring maps.
The profile is not additive, unlike `Finsupp.mapDomain` on coefficient arrays.

## References

Mathlib's `Finsupp` API (`Basic`, `Defs`, `Single`, `Weight`) supplies transport,
`degree_single`, `unique_single` and `uniqueEquiv`. The private calculations also
use Mathlib's `ZMod`, `ENat` and `ULift` structures.
-/

@[expose] public section

universe u v w

namespace Finsupp

/-- Total degree and support cardinality determine a natural exponent vector
exactly when the variable type has at most one element. No finiteness or
nonemptiness assumption on the variable type is needed. -/
theorem degree_support_injective_iff {σ : Type u} :
    Function.Injective (fun d : σ →₀ ℕ => (d.degree, d.support.card)) ↔
      Subsingleton σ := by
  classical
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    apply single_left_injective Nat.one_ne_zero
    apply h
    simp only [degree_single, support_single a Nat.one_ne_zero,
      support_single b Nat.one_ne_zero, Finset.card_singleton]
  · intro hσ
    let : Subsingleton σ := hσ
    intro d e h
    ext a
    have hdegree (f : σ →₀ ℕ) : f a = f.degree :=
      (degree_single a (f a)).symm.trans
        (congrArg (fun f : σ →₀ ℕ => f.degree) ((uniqueEquiv a).symm_apply_apply f))
    exact (hdegree d).trans ((congrArg Prod.fst h).trans (hdegree e).symm)

end Finsupp

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
    let f : ULift.{u} (Fin 2) → ULift.{v} (Option (Fin 2)) := fun a => ⟨Option.some a.down⟩
    let x : ULift.{u} (Fin 2) →₀ ULift.{w} ℕ :=
      single ⟨0⟩ ⟨3⟩ + single ⟨1⟩ ⟨5⟩
    mapDomain f x (f ⟨0⟩) = ⟨3⟩ ∧
      mapDomain f x (f ⟨1⟩) = ⟨5⟩ ∧ mapDomain f x ⟨none⟩ = 0 := by
  let f : ULift.{u} (Fin 2) → ULift.{v} (Option (Fin 2)) := fun a => ⟨Option.some a.down⟩
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
    have hnone : Option.some a.down = (none : Option (Fin 2)) := congrArg ULift.down ha
    exact Option.some_ne_none a.down hnone

end Finsupp
end

namespace Finsupp.DegreeSupport

/-! ## Two variables and natural coefficients -/

private theorem fin_two_basis_ne :
    (Finsupp.single (0 : Fin 2) (1 : ℕ)) ≠ Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hindex : (0 : Fin 2) = 1 :=
    Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) h
  exact (by decide : (0 : Fin 2) ≠ 1) hindex

private theorem fin_two_zero_profile :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (0 : Fin 2) 1) = (1, 1) := by
  simp

private theorem fin_two_one_profile :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (1 : Fin 2) 1) = (1, 1) := by
  simp

private theorem fin_two_profile_not_injective :
    ¬ Function.Injective (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) := by
  intro h
  exact fin_two_basis_ne
    (h (fin_two_zero_profile.trans fin_two_one_profile.symm))

private theorem fin_two_nat_arrays_ne :
    (Finsupp.single (Finsupp.single (0 : Fin 2) (1 : ℕ)) (1 : ℕ) :
      (Fin 2 →₀ ℕ) →₀ ℕ) ≠
        Finsupp.single (Finsupp.single (1 : Fin 2) 1) 1 := by
  intro h
  exact fin_two_basis_ne
    (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) h)

private theorem fin_two_nat_zero_array_profile :
    Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (Finsupp.single (0 : Fin 2) (1 : ℕ)) (1 : ℕ)) =
        Finsupp.single (1, 1) 1 := by
  rw [Finsupp.mapDomain_single]
  exact congrArg (fun label : ℕ × ℕ => Finsupp.single label (1 : ℕ)) fin_two_zero_profile

private theorem fin_two_nat_one_array_profile :
    Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (Finsupp.single (1 : Fin 2) (1 : ℕ)) (1 : ℕ)) =
        Finsupp.single (1, 1) 1 := by
  rw [Finsupp.mapDomain_single]
  exact congrArg (fun label : ℕ × ℕ => Finsupp.single label (1 : ℕ)) fin_two_one_profile

private theorem fin_two_nat_profile_image_ne_zero :
    (Finsupp.single (1, 1) (1 : ℕ) : (ℕ × ℕ) →₀ ℕ) ≠ 0 := by
  exact Finsupp.single_ne_zero.mpr (by decide : (1 : ℕ) ≠ 0)

private theorem fin_two_nat_profile_not_injective :
    ¬ Function.Injective
      (Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) :
        ((Fin 2 →₀ ℕ) →₀ ℕ) → ((ℕ × ℕ) →₀ ℕ)) := by
  intro h
  exact fin_two_nat_arrays_ne
    (h (fin_two_nat_zero_array_profile.trans fin_two_nat_one_array_profile.symm))

/-- A decoder here is an arbitrary total function on profile coefficient arrays.
The source of `mapDomain` is inhabited by its zero coefficient array. -/
private theorem fin_two_nat_profile_no_decoder :
    ¬ Function.HasLeftInverse
      (Finsupp.mapDomain (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) :
        ((Fin 2 →₀ ℕ) →₀ ℕ) → ((ℕ × ℕ) →₀ ℕ)) := by
  exact Function.injective_iff_hasLeftInverse.not.mp fin_two_nat_profile_not_injective

/-! ## The support statistic is not additive -/

private theorem fin_two_doubled_basis_profile :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1) = (2, 1) := by
  have hsum : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1 :
      Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 2 :=
    (Finsupp.single_add (0 : Fin 2) (1 : ℕ) 1).symm
  simp only [hsum, Finsupp.degree_single,
    Finsupp.support_single (0 : Fin 2) (by decide : (2 : ℕ) ≠ 0),
    Finset.card_singleton]

private theorem fin_two_profile_not_additive :
    (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1) ≠
      (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
          (Finsupp.single (0 : Fin 2) 1) +
        (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card))
          (Finsupp.single (0 : Fin 2) 1) := by
  intro h
  simp only [fin_two_doubled_basis_profile, fin_two_zero_profile] at h
  have hcard : (1 : ℕ) = 2 := congrArg Prod.snd h
  exact (by decide : (1 : ℕ) ≠ 2) hcard

/-! ## Empty and singleton variable types -/

private theorem empty_profile_value {σ : Type*} [IsEmpty σ] (d : σ →₀ ℕ) :
    (fun d : σ →₀ ℕ => (d.degree, d.support.card)) d = (0, 0) := by
  have hzero : d = 0 := Subsingleton.elim _ _
  simp [hzero]

private theorem empty_profile_injective {σ : Type*} [IsEmpty σ] :
    Function.Injective (fun d : σ →₀ ℕ => (d.degree, d.support.card)) := by
  exact Function.injective_of_subsingleton _

private theorem unique_exponent_from_degree {σ : Type*} [Unique σ] (d : σ →₀ ℕ) :
    Finsupp.single (default : σ) d.degree = d := by
  have hdegree : d.degree = d default := by
    simpa only [Finsupp.degree_single] using
      congrArg (fun e : σ →₀ ℕ => e.degree) (Finsupp.unique_single d)
  rw [hdegree]
  exact (Finsupp.unique_single d).symm

private theorem unique_profile_injective {σ : Type*} [Unique σ] :
    Function.Injective (fun d : σ →₀ ℕ => (d.degree, d.support.card)) := by
  exact Finsupp.degree_support_injective_iff.mpr inferInstance

/-! ## Trivial coefficients on arbitrary variable types -/

private theorem zmod_one_profile_arrays_zero {σ : Type*}
    (coefficients : (σ →₀ ℕ) →₀ ZMod 1) :
    coefficients = 0 ∧
      Finsupp.mapDomain (fun d : σ →₀ ℕ => (d.degree, d.support.card)) coefficients = 0 := by
  constructor <;> exact Subsingleton.elim _ _

private theorem zmod_one_zero_decoder_recovers {σ : Type*} :
    Function.LeftInverse
      (fun _ : (ℕ × ℕ) →₀ ZMod 1 => (0 : (σ →₀ ℕ) →₀ ZMod 1))
      (Finsupp.mapDomain (fun d : σ →₀ ℕ => (d.degree, d.support.card))) := by
  intro coefficients
  exact Subsingleton.elim _ _

end Finsupp.DegreeSupport
