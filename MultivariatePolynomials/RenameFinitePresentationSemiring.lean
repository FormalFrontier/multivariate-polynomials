/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.FinitePresentation
public import MultivariatePolynomials.Rename
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite presentation of renaming over semirings with trivial additive units

If the additive units of the coefficient semiring are subsingleton, renaming
reflects zero for every variable map. Its ideal kernel is therefore bottom.
A surjective variable map then gives a finite presentation with no variables,
over the full source polynomial semiring acting by renaming.

No additive cancellation, order, or finiteness hypothesis is needed. In
particular, the hypothesis includes noncancellative zero-sum-free semirings.

The paired-variable example over natural-number coefficients is surjective
but not injective, and every source variable participates in a collision.
Its scalar base is the full source polynomial semiring, not the coefficient
semiring `ℕ`. The explicit empty-variable evaluation is onto with bottom ideal
kernel, and sends each constant source polynomial to its renamed image.

Here `Algebra.FinitePresentation` uses a finitely generated ideal kernel, not
a kernel congruence or categorical finite presentation of semirings. A bottom
ideal kernel does not imply injectivity. Thus the ring criterion involving
finitely many collision participants does not extend to these semirings.

## References

* Mathlib, `Mathlib.Data.Finsupp.Basic`: zero-reflection of `mapDomain` when
  the additive units of the coefficient monoid are subsingleton.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: variable renaming.
* `MultivariatePolynomials.FinitePresentation`: empty-variable evaluation and
  finite presentation from a surjective scalar map.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w}
  [CommSemiring R] [Subsingleton (AddUnits R)]

/-- Renaming reflects zero when the coefficient semiring has only the trivial additive unit. -/
@[simp]
theorem rename_eq_zero_iff_of_subsingletonAddUnits (f : σ → τ) (p : MvPolynomial σ R) :
    rename (R := R) f p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    have hc := congrArg AddMonoidAlgebra.coeff hp
    change Finsupp.mapDomain (Finsupp.mapDomain f) p.coeff = 0 at hc
    exact AddMonoidAlgebra.coeff_eq_zero.mp
      ((Finsupp.mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits
        (Finsupp.mapDomain f) p.coeff).mp hc)
  · rintro rfl
    exact map_zero _

/-- The ideal kernel of renaming is bottom when additive units are subsingleton. -/
theorem ker_rename_eq_bot_of_subsingletonAddUnits (f : σ → τ) :
    RingHom.ker (rename (R := R) f).toRingHom = ⊥ := by
  ext p
  rw [RingHom.mem_ker, Submodule.mem_bot]
  exact rename_eq_zero_iff_of_subsingletonAddUnits f p

/-- Surjective renaming is finitely presented over the full source polynomial semiring
when the coefficient semiring has only the trivial additive unit. -/
theorem finitePresentation_rename_of_surjective_of_subsingletonAddUnits
    (f : σ → τ) (hf : Function.Surjective f) :
    @Algebra.FinitePresentation (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (rename (R := R) f).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  apply Algebra.FinitePresentation.of_surjective_algebraMap
  · exact rename_surjective f hf
  · change (RingHom.ker (rename (R := R) f).toRingHom).FG
    rw [ker_rename_eq_bot_of_subsingletonAddUnits]
    exact Submodule.fg_bot

/-- Paired-variable renaming is onto over the natural-number semiring. -/
private theorem rename_fst_nat_surjective :
    Function.Surjective (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)) :=
  rename_surjective _ (fun n => ⟨(n, false), rfl⟩)

/-- Natural-number coefficients cannot cancel in the monomial fibres of renaming. -/
private theorem rename_fst_nat_eq_zero_iff (p : MvPolynomial (ℕ × Bool) ℕ) :
    rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) p = 0 ↔ p = 0 :=
  rename_eq_zero_iff_of_subsingletonAddUnits _ p

/-- The ideal kernel is bottom even though the paired renaming is not injective. -/
private theorem ker_rename_fst_nat_eq_bot :
    RingHom.ker (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom = ⊥ :=
  ker_rename_eq_bot_of_subsingletonAddUnits _

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

/-- Empty-variable evaluation presents the full source-polynomial action explicitly. -/
private theorem paired_nat_zero_variable_presentation :
    let A := MvPolynomial (ℕ × Bool) ℕ
    let B := MvPolynomial ℕ ℕ
    letI : Algebra A B :=
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
    ∃ g : MvPolynomial (Fin 0) A →ₐ[A] B,
      Function.Surjective g ∧ RingHom.ker g.toRingHom = ⊥ ∧
        ∀ p : A, g (C p) = rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ) p := by
  let A := MvPolynomial (ℕ × Bool) ℕ
  let B := MvPolynomial ℕ ℕ
  let : Algebra A B :=
    (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  let g : MvPolynomial (Fin 0) A →ₐ[A] B := aeval (Fin.elim0 : Fin 0 → B)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact (aeval_surjective_iff_of_isEmpty (Fin.elim0 : Fin 0 → B)).mpr
      rename_fst_nat_surjective
  · dsimp only [g]
    rw [ker_aeval_of_isEmpty]
    change (RingHom.ker
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom).map _ = ⊥
    rw [ker_rename_fst_nat_eq_bot, Ideal.map_bot]
  · intro p
    exact aeval_C _ p

/-- The full source-polynomial action is finitely presented. -/
private theorem finitePresentation_rename_fst_nat :
    @Algebra.FinitePresentation (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) _ _
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra :=
  finitePresentation_rename_of_surjective_of_subsingletonAddUnits _
    (fun n => ⟨(n, false), rfl⟩)

/-- The same full-source algebra is of finite type, using the empty-variable presentation. -/
private theorem finiteType_rename_fst_nat :
    @Algebra.FiniteType (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) _ _
      (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) :=
    (rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  obtain ⟨g, hg, _, _⟩ := paired_nat_zero_variable_presentation
  exact Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨0, g, hg⟩

/-- Finite presentation for the full-source action over natural-number coefficients
does not force finite collision participants. -/
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
