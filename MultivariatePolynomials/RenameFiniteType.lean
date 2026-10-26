/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Finite type of variable renaming

A map of variable types induces an algebra structure on the target polynomial
semiring over the source polynomial semiring. A source polynomial acts by
multiplication by its renamed image. This algebra is of finite type exactly when
the coefficient semiring is subsingleton or only finitely many target variables
lie outside the image of the variable map.

The variable types and coefficient type may have independent universes, and the
variable map need not be injective or surjective. The finite set concerns missed
target variables, not source variables that are identified by renaming.

Finite type means finite generation as an algebra over the source polynomial
semiring. It does not mean finite presentation or finiteness as a module over
the coefficient semiring.

For natural-number variable indices, `finiteType_rename_add` treats every shift
`n ↦ n + k`, and `finiteType_rename_succ` treats the successor map. Renaming by
`n ↦ 2 * n` is finite type exactly for subsingleton coefficients, as expressed
by `finiteType_rename_even_iff`. For nontrivial coefficients,
`not_finiteType_rename_even` gives the negative conclusion. This map renames
indices; it sends `X n` to `X (2 * n)`, not to `(X n) ^ 2`.

Applications below compare a noninjective surjective projection, the singleton
generator for successor renaming, independently lifted empty variable types,
and infinite missed sets over zero and nonreduced coefficient rings.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: polynomial variable renaming.
* Mathlib, `Mathlib.RingTheory.FiniteType`: finite generation of semiring algebras.
* Mathlib, `Mathlib.RingTheory.Adjoin.Basic` and `Mathlib.RingTheory.Adjoin.FG`:
  algebra generation and change of base in a scalar tower.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Supported`: supported subalgebras and
  detection of variables over nontrivial coefficients.
* Mathlib, `Mathlib.Data.Set.Finite.Basic`: finite initial segments and infinite
  ranges of injective maps.
* Mathlib, `Mathlib.Data.Nat.Init`: separation of even and odd indices.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic`: polynomial induction.
* Mathlib, `Mathlib.Data.ZMod.Basic`: zero and nonreduced coefficient rings.
-/

universe u v w

namespace MvPolynomial

/-- Renaming variables gives a finite-type algebra over the source polynomial semiring
exactly when the coefficient semiring is subsingleton or finitely many target variables
are missed. The algebra structure is induced by the renaming homomorphism. -/
theorem finiteType_rename_iff {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (f : σ → τ) :
    @Algebra.FiniteType (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra ↔
      Subsingleton R ∨ Set.Finite ((Set.range f)ᶜ) := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) (MvPolynomial τ R) :=
    IsScalarTower.of_algHom (rename (R := R) f)
  -- Restriction of scalars retains all the renamed source variables.
  have hadjoin (s : Set (MvPolynomial τ R)) :
      (Algebra.adjoin (MvPolynomial σ R) s).restrictScalars R =
        Algebra.adjoin R
          (algebraMap (MvPolynomial σ R) (MvPolynomial τ R) ''
            Set.range (X : σ → MvPolynomial σ R) ∪ s) :=
    Algebra.adjoin_eq_adjoin_union R _ s adjoin_range_X
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inl hR
    let : Nontrivial R := hR
    obtain ⟨s, hs⟩ := h.out
    let t : Finset τ := s.biUnion vars
    have hbound :
        Algebra.adjoin R
          (algebraMap (MvPolynomial σ R) (MvPolynomial τ R) ''
            Set.range (X : σ → MvPolynomial σ R) ∪ (s : Set (MvPolynomial τ R))) ≤
          supported R (Set.range f ∪ (t : Set τ)) := by
      apply Algebra.adjoin_le
      rintro p (hp | hp)
      · rcases hp with ⟨q, ⟨i, rfl⟩, rfl⟩
        change rename f (X i) ∈ supported R _
        rw [rename_X, X_mem_supported]
        exact Or.inl ⟨i, rfl⟩
      · apply mem_supported.mpr
        intro j hj
        exact Or.inr (Finset.subset_biUnion_of_mem vars hp hj)
    rw [← hadjoin, hs, Subalgebra.restrictScalars_top] at hbound
    refine Or.inr (t.finite_toSet.subset ?_)
    intro j hj
    have hj' : j ∈ Set.range f ∪ (t : Set τ) :=
      X_mem_supported.mp (hbound (show X j ∈ (⊤ : Subalgebra R (MvPolynomial τ R))
        from trivial))
    exact hj'.resolve_left hj
  · rintro (hR | hf)
    · let : Subsingleton R := hR
      let : Subsingleton (MvPolynomial τ R) :=
        Algebra.subsingleton R (MvPolynomial τ R)
      refine ⟨⟨∅, ?_⟩⟩
      apply top_unique
      intro p _
      rw [Subsingleton.elim p 0]
      exact Subalgebra.zero_mem _
    · refine ⟨Subalgebra.fg_def.mpr
        ⟨X '' (Set.range f)ᶜ, hf.image X, ?_⟩⟩
      apply Subalgebra.restrictScalars_injective R
      rw [hadjoin, Subalgebra.restrictScalars_top]
      have hcover :
          algebraMap (MvPolynomial σ R) (MvPolynomial τ R) ''
              Set.range (X : σ → MvPolynomial σ R) ∪ X '' (Set.range f)ᶜ =
            Set.range (X : τ → MvPolynomial τ R) := by
        ext p
        constructor
        · rintro (hp | hp)
          · rcases hp with ⟨q, ⟨i, rfl⟩, rfl⟩
            exact ⟨f i, (rename_X f i).symm⟩
          · rcases hp with ⟨j, _, rfl⟩
            exact ⟨j, rfl⟩
        · rintro ⟨j, rfl⟩
          by_cases hj : j ∈ Set.range f
          · obtain ⟨i, rfl⟩ := hj
            exact Or.inl ⟨X i, ⟨i, rfl⟩, rename_X f i⟩
          · exact Or.inr ⟨j, hj, rfl⟩
      rw [hcover, adjoin_range_X]

/-- Shifting natural-number variable indices by any fixed amount gives a finite-type
algebra over the source polynomial semiring. The algebra structure is induced by
renaming `n` to `n + k`; only the first `k` target variables are missed. -/
theorem finiteType_rename_add {R : Type u} [CommSemiring R] (k : ℕ) :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (rename (R := R) (fun n : ℕ => n + k)).toRingHom.toAlgebra := by
  apply (finiteType_rename_iff (R := R) (fun n : ℕ => n + k)).mpr
  right
  refine (Set.finite_lt_nat k).subset ?_
  intro n hn
  exact lt_of_not_ge fun h => hn ⟨n - k, Nat.sub_add_cancel h⟩

/-- Successor renaming gives a finite-type algebra over the source polynomial semiring,
with the algebra structure induced by `X n ↦ X (n + 1)`. -/
theorem finiteType_rename_succ {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (rename (R := R) Nat.succ).toRingHom.toAlgebra :=
  finiteType_rename_add 1

/-- Renaming natural-number variable indices by `n ↦ 2 * n` gives a finite-type algebra
over the source polynomial semiring exactly when the coefficient semiring is
subsingleton. The algebra structure is induced by renaming, not coefficient scalars;
the infinitely many odd target indices are missed. -/
theorem finiteType_rename_even_iff {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (rename (R := R) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra ↔
      Subsingleton R := by
  have hodd_injective : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro m n h
    exact Nat.mul_left_cancel Nat.zero_lt_two (Nat.add_right_cancel h)
  have hodd_subset : Set.range (fun n : ℕ => 2 * n + 1) ⊆
      (Set.range (fun n : ℕ => 2 * n))ᶜ := by
    rintro _ ⟨n, rfl⟩ ⟨m, hm⟩
    exact Nat.two_mul_ne_two_mul_add_one hm
  have hmissed : ((Set.range (fun n : ℕ => 2 * n))ᶜ).Infinite :=
    (Set.infinite_range_of_injective hodd_injective).mono hodd_subset
  rw [finiteType_rename_iff]
  exact ⟨fun h => h.resolve_right hmissed, Or.inl⟩

/-- Over nontrivial coefficients, even-index renaming is not a finite-type algebra over
the source polynomial semiring. Nontriviality is necessary: for a subsingleton
coefficient semiring the same renaming is finite type. -/
theorem not_finiteType_rename_even {R : Type u} [CommSemiring R] [Nontrivial R] :
    ¬ @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (rename (R := R) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra := by
  rw [finiteType_rename_even_iff]
  exact not_subsingleton R

/-!
## Applications with infinite or empty variable types

The projection identifies variables without missing any. Successor renaming
misses exactly zero and needs the single relative generator `X 0`. These two
examples use the non-ring coefficient semiring `ℕ`. Even-index renaming
contrasts nontrivial coefficients with the zero semiring. Empty variable types
and nonreduced coefficients give further boundary cases of the criterion.
-/

-- A surjective variable map may identify infinitely many pairs of variables.
private theorem paired_projection :
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) ∧
      ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) ∧
      (Set.range (Prod.fst : ℕ × Bool → ℕ))ᶜ = ∅ ∧
      @Algebra.FiniteType (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) _ _
        (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  have hsurj : Function.Surjective (Prod.fst : ℕ × Bool → ℕ) := by
    intro n
    exact ⟨(n, false), rfl⟩
  refine ⟨hsurj, ?_, ?_, ?_⟩
  · intro h
    have hfalse : false = true := congrArg Prod.snd
      (h (show Prod.fst (0, false) = Prod.fst (0, true) from rfl))
    cases hfalse
  · rw [Set.range_eq_univ.mpr hsurj, Set.compl_univ]
  · let : Algebra (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) :=
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
    exact Algebra.FiniteType.of_surjective
      (Algebra.ofId (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ))
      (rename_surjective _ hsurj)

-- All positive-index variables are scalar images; only X 0 is adjoined.
private theorem successor_over_nat :
    (¬ ∃ n : ℕ, 1 + n = 0) ∧
      (Set.range Nat.succ)ᶜ = ({0} : Set ℕ) ∧
      @Algebra.FiniteType (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) _ _
        (rename (R := ℕ) Nat.succ).toRingHom.toAlgebra := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    exact Nat.succ_ne_zero n (by simpa only [Nat.add_comm] using hn)
  · ext n
    cases n <;> simp
  · let : Algebra (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) :=
      (rename (R := ℕ) Nat.succ).toRingHom.toAlgebra
    refine ⟨⟨{(X 0 : MvPolynomial ℕ ℕ)}, ?_⟩⟩
    rw [Finset.coe_singleton]
    let S : Subalgebra (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) :=
      Algebra.adjoin (MvPolynomial ℕ ℕ) ({X 0} : Set (MvPolynomial ℕ ℕ))
    change S = ⊤
    apply top_unique
    intro p _hp
    clear _hp
    induction p using MvPolynomial.induction_on with
    | C r =>
        have hr := S.algebraMap_mem (C r)
        change rename Nat.succ (C r) ∈ S at hr
        simpa only [rename_C] using hr
    | add p q hp hq => exact S.add_mem hp hq
    | mul_X p n hp =>
        apply S.mul_mem hp
        cases n with
        | zero => exact Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)
        | succ n =>
            have hn := S.algebraMap_mem (X n)
            change rename Nat.succ (X n) ∈ S at hn
            simpa only [rename_X] using hn

-- The coefficient semiring need not be a ring, nontrivial, or Noetherian.
private theorem finiteType_rename_add_two {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (rename (R := R) (fun n : ℕ => n + 2)).toRingHom.toAlgebra :=
  finiteType_rename_add 2

private theorem even_index_coefficient_contrast :
    (¬ @Algebra.FiniteType (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) _ _
      (rename (R := ℕ) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra) ∧
      @Algebra.FiniteType (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) _ _
        (rename (R := ZMod 1) (fun n : ℕ => 2 * n)).toRingHom.toAlgebra :=
  ⟨not_finiteType_rename_even,
    (finiteType_rename_even_iff (R := ZMod 1)).mpr inferInstance⟩

-- The source, target, and coefficient universes remain independent.
private theorem empty_rename_finiteType {R : Type u} [CommSemiring R] :
    @Algebra.FiniteType (MvPolynomial PEmpty.{v + 1} R)
      (MvPolynomial PEmpty.{w + 1} R) _ _
      (rename (R := R)
        (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1})).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial PEmpty.{v + 1} R) (MvPolynomial PEmpty.{w + 1} R) :=
    (rename (R := R)
      (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1})).toRingHom.toAlgebra
  exact Algebra.FiniteType.of_surjective
    (Algebra.ofId (MvPolynomial PEmpty.{v + 1} R) (MvPolynomial PEmpty.{w + 1} R))
    (rename_surjective _ (fun x => PEmpty.elim x))

-- Over the zero semiring, infinitely many missed variables need no generators.
private theorem empty_source_over_zero :
    Set.Infinite ((Set.range (PEmpty.elim : PEmpty.{v + 1} → ℕ))ᶜ) ∧
      @Algebra.FiniteType (MvPolynomial PEmpty.{v + 1} (ZMod 1))
        (MvPolynomial ℕ (ZMod 1)) _ _
        (rename (R := ZMod 1)
          (PEmpty.elim : PEmpty.{v + 1} → ℕ)).toRingHom.toAlgebra := by
  constructor
  · have hr : Set.range (PEmpty.elim : PEmpty.{v + 1} → ℕ) = ∅ := by
      ext n
      constructor
      · rintro ⟨i, _hi⟩
        exact PEmpty.elim i
      · intro hn
        exact hn.elim
    rw [hr, Set.compl_empty]
    exact Set.infinite_univ
  · let : Algebra (MvPolynomial PEmpty.{v + 1} (ZMod 1))
        (MvPolynomial ℕ (ZMod 1)) :=
      (rename (R := ZMod 1)
        (PEmpty.elim : PEmpty.{v + 1} → ℕ)).toRingHom.toAlgebra
    refine ⟨⟨∅, ?_⟩⟩
    rw [Finset.coe_empty]
    apply top_unique
    intro p _hp
    have hp : p = 0 := Subsingleton.elim _ _
    rw [hp]
    exact (Algebra.adjoin (MvPolynomial PEmpty.{v + 1} (ZMod 1))
      (∅ : Set (MvPolynomial ℕ (ZMod 1)))).zero_mem

-- A nonreduced coefficient ring still has the infinite-misses obstruction.
-- Here the obstruction is an application of finiteType_rename_iff.
private theorem singleton_source_over_zmod_four :
    ((2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0) ∧
      Set.Infinite ((Set.range (fun _ : Fin 1 => (0 : ℕ)))ᶜ) ∧
      ¬ @Algebra.FiniteType (MvPolynomial (Fin 1) (ZMod 4))
        (MvPolynomial ℕ (ZMod 4)) _ _
        (rename (R := ZMod 4)
          (fun _ : Fin 1 => (0 : ℕ))).toRingHom.toAlgebra := by
  have hmissed : Set.Infinite ((Set.range (fun _ : Fin 1 => (0 : ℕ)))ᶜ) := by
    intro h
    have hu : (Set.univ : Set ℕ).Finite := by
      simpa only [Set.union_compl_self] using
        (Set.finite_range (fun _ : Fin 1 => (0 : ℕ))).union h
    exact Set.infinite_univ hu
  refine ⟨?_, hmissed, ?_⟩
  · decide
  · let : Nontrivial (ZMod 4) := ZMod.nontrivial_iff.mpr (by decide)
    intro h
    rcases (finiteType_rename_iff (R := ZMod 4)
      (fun _ : Fin 1 => (0 : ℕ))).mp h with hR | hf
    · exact not_subsingleton (ZMod 4) hR
    · exact hmissed hf

end MvPolynomial
