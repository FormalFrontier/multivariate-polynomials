/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.FinitePresentation

/-!
# Finite presentation of paired-variable renaming over the naturals

Projection `ℕ × Bool → ℕ` gives a surjective, noninjective renaming over `ℕ`.
Every source index participates in a collision, including both endpoints of
each pair, and there are infinitely many such indices. Nevertheless its ideal
kernel is bottom: summing natural-number coefficients along monomial fibres
cannot turn a nonzero polynomial into zero.

With the target algebra structure induced by renaming, the existing
`Algebra.FinitePresentation` class has a zero-variable witness. Compose the
empty-variable polynomial equivalence over the source semiring with its
canonical scalar map to the target. This composite is onto and has bottom,
finitely generated ideal kernel. Thus finiteness of all collision participants
is not necessary for this class over commutative semirings.

## Limitations

These examples concern the ideal kernel in `Algebra.FinitePresentation`, not a
kernel congruence or categorical finite presentation of semirings. A bottom
ideal kernel does not imply injectivity here. All declarations are private.

## References

* Mathlib, `Mathlib.Data.Finsupp.Basic`: zero-reflection of `mapDomain` when
  the additive units of the coefficient monoid are subsingleton.
* Mathlib, `Mathlib.Algebra.Order.Group.Nat` and
  `Mathlib.Algebra.Order.Monoid.Canonical.Defs`: the canonical additive order
  on `ℕ` and uniqueness of its additive units.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename` and
  `Mathlib.Algebra.MvPolynomial.Equiv`: renaming and the empty-variable equivalence.
* Mathlib, `Mathlib.RingTheory.FinitePresentation`: the existing ideal-kernel
  definition of finite presentation.
-/

namespace MvPolynomial

/-- Paired-variable renaming is onto over the natural-number semiring. -/
private theorem rename_fst_nat_surjective :
    Function.Surjective (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)) :=
  rename_surjective _ (fun n => ⟨(n, false), rfl⟩)

/-- Natural-number coefficients cannot cancel in the monomial fibres of renaming. -/
private theorem rename_fst_nat_eq_zero_iff (p : MvPolynomial (ℕ × Bool) ℕ) :
    rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    have hc := congrArg AddMonoidAlgebra.coeff hp
    change Finsupp.mapDomain (Finsupp.mapDomain (Prod.fst : ℕ × Bool → ℕ))
      p.coeff = 0 at hc
    exact AddMonoidAlgebra.coeff_eq_zero.mp
      ((Finsupp.mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits
        (Finsupp.mapDomain (Prod.fst : ℕ × Bool → ℕ)) p.coeff).mp hc)
  · rintro rfl
    exact map_zero _

/-- The ideal kernel is bottom even though the paired renaming is not injective. -/
private theorem ker_rename_fst_nat_eq_bot :
    RingHom.ker (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom = ⊥ := by
  ext p
  rw [RingHom.mem_ker, Submodule.mem_bot]
  exact rename_fst_nat_eq_zero_iff p

/-- The two variables in the zeroth pair have equal images but are distinct. -/
private theorem rename_fst_nat_not_injective :
    ¬ Function.Injective (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)) := by
  intro h
  have hX :
      rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) (X (0, false)) =
        rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) (X (0, true)) := by
    rw [rename_X, rename_X]
  have hb : false = true := congrArg Prod.snd (X_injective (h hX))
  cases hb

/-- No target index is missed by the projection. -/
private theorem paired_missed_targets_eq_empty :
    (Set.range (Prod.fst : ℕ × Bool → ℕ))ᶜ = ∅ := by
  ext n
  change (¬ ∃ i : ℕ × Bool, Prod.fst i = n) ↔ False
  constructor
  · intro h
    exact h ⟨(n, false), rfl⟩
  · exact False.elim

/-- Every source index collides with the index having the opposite Boolean coordinate. -/
private theorem paired_collision_participants_eq_univ :
    {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j} = Set.univ := by
  ext i
  constructor
  · intro _
    exact Set.mem_univ i
  · intro _
    refine ⟨(i.1, !i.2), ?_, rfl⟩
    intro h
    exact (Bool.self_ne_not i.2) (congrArg Prod.snd h)

/-- The set of all collision participants, not just a single fibre, is infinite. -/
private theorem paired_collision_participants_infinite :
    {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ Prod.fst i = Prod.fst j}.Infinite := by
  rw [paired_collision_participants_eq_univ]
  exact Set.infinite_univ

/-- The canonical source-polynomial action admits a zero-variable finite presentation. -/
private theorem finitePresentation_rename_fst_nat :
    @Algebra.FinitePresentation (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) _ _
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  let A := MvPolynomial (ℕ × Bool) ℕ
  let B := MvPolynomial ℕ ℕ
  let : Algebra A B :=
    (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  let e : MvPolynomial (Fin 0) A ≃ₐ[A] A := isEmptyAlgEquiv A (Fin 0)
  let g : MvPolynomial (Fin 0) A →ₐ[A] B := (Algebra.ofId A B).comp e.toAlgHom
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨p, hp⟩ := rename_fst_nat_surjective q
    refine ⟨e.symm p, ?_⟩
    change rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) (e (e.symm p)) = q
    rw [e.apply_symm_apply]
    exact hp
  have hgker : RingHom.ker g.toRingHom = ⊥ := by
    ext p
    rw [RingHom.mem_ker, Submodule.mem_bot]
    change rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) (e p) = 0 ↔ p = 0
    rw [rename_fst_nat_eq_zero_iff]
    constructor
    · intro hp
      apply e.injective
      simpa only [map_zero] using hp
    · rintro rfl
      exact map_zero e
  refine ⟨0, g, hg, ?_⟩
  rw [hgker]
  exact Submodule.fg_bot

/-- The same canonical algebra is of finite type, using the surjective presentation. -/
private theorem finiteType_rename_fst_nat :
    @Algebra.FiniteType (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) _ _
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) :=
    (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  obtain ⟨n, g, hg, _⟩ := finitePresentation_rename_fst_nat.out
  exact Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨n, g, hg⟩

/-- Relative finite presentation over `ℕ` does not force finite collision participants. -/
private theorem paired_nat_finitePresentation_counterexample :
    @Algebra.FinitePresentation (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) _ _
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra ∧
      ¬ (Subsingleton ℕ ∨
        Set.Finite ((Set.range (Prod.fst : ℕ × Bool → ℕ))ᶜ) ∧
          Set.Finite {i : ℕ × Bool | ∃ j : ℕ × Bool,
            i ≠ j ∧ Prod.fst i = Prod.fst j}) := by
  refine ⟨finitePresentation_rename_fst_nat, ?_⟩
  rintro (h | ⟨_, h⟩)
  · exact Nat.zero_ne_one (@Subsingleton.elim ℕ h 0 1)
  · exact paired_collision_participants_infinite h

end MvPolynomial
