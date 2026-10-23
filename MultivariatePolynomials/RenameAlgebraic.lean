/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import MultivariatePolynomials.Rename

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Bool.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import MultivariatePolynomials.RenameIntegral

@[expose] public section

/-!
# Algebraicity of variable renaming

A coefficient-preserving variable renaming between full polynomial rings over
an arbitrary commutative ring is algebraic exactly when the coefficients are
nontrivial and the variable map is surjective or noninjective. The coefficient,
source-variable and target-variable types have independent universes.

Here algebraicity is Mathlib's predicate requiring a nonzero annihilating
polynomial, not necessarily monic or of positive degree. A collision of source
variables supplies a nonzero constant annihilator through the kernel, even if
some target variables are missed. For zero coefficients, no nonzero polynomial
exists, so even identity renaming is not algebraic. This differs from integrality.

## Examples

Private applications include identity, projection and shifted projection over
integers, as well as nonreduced coefficients in `ZMod 4`. Independent proofs by
surjectivity or a noninjective algebra map accompany applications of the criteria.
The missing variable of shifted projection is not integral, by the integrality
criterion whose proof uses augmentation and monicity.

For the finite inclusion into an option type, the option-variable equivalence
preserves the entire source as coefficients. Injective identity coefficient
transport then proves nonalgebraicity over the full source, even with nilpotents.
Zero coefficients, empty variable types, same-carrier successor renaming and
independent universe lifts give further boundary examples.

## References

* Mathlib, `Mathlib.RingTheory.Algebraic.Basic`: algebraicity under injective
  coefficient maps, and algebraicity of a noninjective algebra map.
* Mathlib, `Mathlib.RingTheory.Algebraic.MvPolynomial`: transcendence of a variable
  over the subalgebra supported on a set not containing it.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Equiv`: the option-variable equivalence.
* Mathlib, `Mathlib.RingTheory.Algebraic.Integral`: integral algebras are algebraic
  over a nontrivial base ring.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`:
  surjective ring homomorphisms are integral.
-/

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]

/-- A target variable is algebraic over the full source through renaming exactly
when the coefficients are nontrivial and the variable is retained or the variable
map is noninjective. The algebra structure is induced by the specified renaming. -/
@[simp]
theorem isAlgebraic_X_rename_iff (f : σ → τ) (j : τ) :
    @IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R)
      inferInstance inferInstance
      (rename (R := R) f).toRingHom.toAlgebra (X j) ↔
        Nontrivial R ∧ (j ∈ Set.range f ∨ ¬ Function.Injective f) := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  constructor
  · intro h
    have : Nontrivial (MvPolynomial σ R) := h.nontrivial
    have hR : Nontrivial R := (C : R →+* MvPolynomial σ R).domain_nontrivial
    refine ⟨hR, ?_⟩
    by_cases hf : Function.Injective f
    · left
      by_contra hj
      let g : MvPolynomial σ R →ₐ[R] supported R (Set.range f) :=
        (rename (R := R) f).codRestrict (supported R (Set.range f)) (fun p => by
          rw [mem_supported]
          intro j hj
          obtain ⟨i, _, rfl⟩ := mem_vars_rename f p hj
          exact ⟨i, rfl⟩)
      have hg : Function.Injective g := by
        intro p q hpq
        apply rename_injective f hf
        exact congrArg Subtype.val hpq
      have hcomp :
          (algebraMap (supported R (Set.range f)) (MvPolynomial τ R)).comp g.toRingHom =
            (RingHom.id (MvPolynomial τ R)).comp
              (algebraMap (MvPolynomial σ R) (MvPolynomial τ R)) := by
        ext p <;> rfl
      have hx := h.ringHom_of_comp_eq
        g.toRingHom (RingHom.id (MvPolynomial τ R)) hg hcomp
      exact (transcendental_supported_X R (show j ∉ Set.range f from hj)) hx
    · exact Or.inr hf
  · rintro ⟨hR, hj | hf⟩
    · have : Nontrivial R := hR
      obtain ⟨i, rfl⟩ := hj
      have hx : IsAlgebraic (MvPolynomial σ R)
          ((rename (R := R) f) (X i)) := isAlgebraic_algebraMap (X i)
      simpa only [rename_X] using hx
    · have : Nontrivial R := hR
      have : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R) := by
        apply Algebra.isAlgebraic_of_not_injective
        intro hi
        rcases (injective_rename_iff f).1 hi with hfi | hsub
        · exact hf hfi
        · exact zero_ne_one (hsub.elim 0 1)
      exact Algebra.IsAlgebraic.isAlgebraic (R := MvPolynomial σ R) (X j)

/-- The full target polynomial ring is algebraic over the full source through
renaming exactly when the coefficients are nontrivial and the variable map is
surjective or noninjective. The algebra structure is the one induced by the
specified renaming map, including when the variable types coincide. -/
theorem isAlgebraic_rename_iff (f : σ → τ) :
    @Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R)
      inferInstance inferInstance
      (rename (R := R) f).toRingHom.toAlgebra ↔
        Nontrivial R ∧ (Function.Surjective f ∨ ¬ Function.Injective f) := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  constructor
  · intro h
    have : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R) := h
    have : Nontrivial (MvPolynomial σ R) :=
      Algebra.nontrivial_of_isAlgebraic (MvPolynomial σ R) (MvPolynomial τ R)
    have hR : Nontrivial R := (C : R →+* MvPolynomial σ R).domain_nontrivial
    refine ⟨hR, ?_⟩
    by_cases hf : Function.Injective f
    · left
      intro j
      rcases ((isAlgebraic_X_rename_iff f j).1
        (Algebra.IsAlgebraic.isAlgebraic (R := MvPolynomial σ R)
          (X j : MvPolynomial τ R))).2 with hj | hi
      · exact hj
      · exact (hi hf).elim
    · exact Or.inr hf
  · rintro ⟨hR, hf | hf⟩
    · have : Nontrivial R := hR
      have hi : RingHom.IsIntegral (rename (R := R) f).toRingHom :=
        RingHom.isIntegral_of_surjective _ (rename_surjective f hf)
      refine ⟨fun p => ?_⟩
      have hp : IsIntegral (MvPolynomial σ R) p := hi p
      exact hp.isAlgebraic
    · have : Nontrivial R := hR
      apply Algebra.isAlgebraic_of_not_injective
      intro hi
      rcases (injective_rename_iff f).1 hi with hfi | hsub
      · exact hf hfi
      · exact zero_ne_one (hsub.elim 0 1)

end MvPolynomial

end

noncomputable section

universe r u v w

namespace MvPolynomial

/-- The identity variable map is bijective, including with zero coefficients. -/
private theorem nat_identity_bijective : Function.Bijective (id : ℕ → ℕ) :=
  ⟨Function.injective_id, Function.surjective_id⟩

/-- Projection hits every natural-number variable. -/
private theorem projection_surjective :
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) := by
  intro n
  exact ⟨(n, false), rfl⟩

/-- Projection identifies two distinct variables. -/
private theorem projection_not_injective :
    ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) := by
  intro h
  have hp : ((0 : ℕ), false) = (0, true) := h rfl
  cases congrArg Prod.snd hp

/-- A shifted projection identifies variables and omits the zero variable. -/
private def shiftedProjection : ℕ × Bool → ℕ := fun p => p.1 + 1

/-- Two distinct source variables have the same shifted image. -/
private theorem shiftedProjection_collision :
    ((0, false) : ℕ × Bool) ≠ (0, true) ∧
      shiftedProjection (0, false) = shiftedProjection (0, true) := by
  refine ⟨?_, rfl⟩
  intro h
  cases congrArg Prod.snd h

/-- In particular, shifted projection is not injective. -/
private theorem shiftedProjection_not_injective : ¬ Function.Injective shiftedProjection := by
  intro h
  exact shiftedProjection_collision.1 (h shiftedProjection_collision.2)

/-- The target variable indexed by zero is missing. -/
private theorem shiftedProjection_misses_zero (p : ℕ × Bool) : shiftedProjection p ≠ 0 := by
  simp [shiftedProjection]

/-- Shifted projection is not surjective. -/
private theorem shiftedProjection_not_surjective : ¬ Function.Surjective shiftedProjection := by
  intro h
  obtain ⟨p, hp⟩ := h 0
  exact shiftedProjection_misses_zero p hp

/-- The coefficient `2` is genuinely nonzero modulo four. -/
private theorem zmodFour_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  decide

/-- The same coefficient has square zero. -/
private theorem zmodFour_two_sq_zero : (2 : ZMod 4) ^ 2 = 0 := by
  decide

/-- Thus the coefficient ring has an actual nonzero nilpotent. -/
private theorem zmodFour_has_nonzero_square_zero :
    ∃ a : ZMod 4, a ≠ 0 ∧ a ^ 2 = 0 :=
  ⟨2, zmodFour_two_ne_zero, zmodFour_two_sq_zero⟩

/-- This witness also supplies coefficient nontriviality. -/
private theorem zmodFour_nontrivial : Nontrivial (ZMod 4) :=
  ⟨⟨2, 0, zmodFour_two_ne_zero⟩⟩

/-- The underlying natural number is preserved between independent lifts. -/
private def liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨n.down⟩

/-- The lifted copy neither identifies nor omits variables. -/
private theorem liftedIdentity_bijective :
    Function.Bijective (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ) := by
  constructor
  · intro i j h
    cases i
    cases j
    cases h
    rfl
  · intro n
    exact ⟨⟨n.down⟩, rfl⟩

end MvPolynomial

namespace MvPolynomialRenameAlgebraicPositive

open MvPolynomial

/-- Identity renaming is algebraic over the full integer polynomial ring. -/
private theorem int_nat_identity_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom.toAlgebra
  change Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
  have : Nontrivial (MvPolynomial ℕ ℤ) := inferInstance
  have : Algebra.IsIntegral (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) :=
    ⟨RingHom.isIntegral_of_surjective _
      (MvPolynomial.rename_surjective (R := ℤ) _ nat_identity_bijective.2)⟩
  exact Algebra.IsIntegral.isAlgebraic

/-- A surjective, noninjective renaming is algebraic over its full source. -/
private theorem int_projection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  change Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
  have : Nontrivial (MvPolynomial (ℕ × Bool) ℤ) := inferInstance
  have : Algebra.IsIntegral (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    ⟨RingHom.isIntegral_of_surjective _
      (MvPolynomial.rename_surjective (R := ℤ) _ projection_surjective)⟩
  exact Algebra.IsIntegral.isAlgebraic

/-- The canonical full-source algebra map identifies distinct indeterminates. -/
private theorem int_shiftedProjection_algebraMap_not_injective :
    ¬ Function.Injective
      (@algebraMap (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra) := by
  intro h
  have hx : (MvPolynomial.X (0, false) : MvPolynomial (ℕ × Bool) ℤ) =
      MvPolynomial.X (0, true) := by
    apply h
    change MvPolynomial.rename shiftedProjection (MvPolynomial.X (0, false)) =
      MvPolynomial.rename shiftedProjection (MvPolynomial.X (0, true))
    simp only [MvPolynomial.rename_X, shiftedProjection_collision.2]
  exact shiftedProjection_collision.1 (MvPolynomial.X_injective hx)

/-- The algebraic model uses the actual nonfaithful renaming action. -/
private theorem int_shiftedProjection_not_faithful :
    ¬ @FaithfulSMul (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      (@Algebra.toSMul (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra) := by
  let : Algebra (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra
  change ¬ FaithfulSMul (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
  intro h
  exact int_shiftedProjection_algebraMap_not_injective
    ((faithfulSMul_iff_algebraMap_injective _ _).mp h)

/-- The missing target variable still prevents integrality for this fixed map. -/
private theorem int_shiftedProjection_not_isIntegral :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom) := by
  intro h
  rcases (MvPolynomial.isIntegral_X_rename_iff (R := ℤ) shiftedProjection 0).mp
      (h (MvPolynomial.X 0)) with hzero | hsub
  · obtain ⟨p, hp⟩ := hzero
    exact shiftedProjection_misses_zero p hp
  · exact zero_ne_one (hsub.elim 0 1)

/-- Infinitely many variables coexist with algebraicity and failure of integrality. -/
private theorem int_shiftedProjection_infinite_algebraic_not_integral :
    Infinite (ℕ × Bool) ∧ Infinite ℕ ∧
      ¬ Function.Injective shiftedProjection ∧ ¬ Function.Surjective shiftedProjection ∧
      @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra ∧
      ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom) := by
  refine ⟨inferInstance, inferInstance, shiftedProjection_not_injective,
    shiftedProjection_not_surjective, ?_, int_shiftedProjection_not_isIntegral⟩
  let : Algebra (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra
  change Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
  exact Algebra.isAlgebraic_of_not_injective int_shiftedProjection_algebraMap_not_injective

/-- Distinct source indeterminates remain distinct with these nonreduced coefficients,
but their images under shifted renaming coincide. -/
private theorem zmodFour_shiftedProjection_algebraMap_not_injective :
    ¬ Function.Injective
      (@algebraMap (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
        inferInstance inferInstance
        (MvPolynomial.rename (R := ZMod 4) shiftedProjection).toRingHom.toAlgebra) := by
  have : Nontrivial (ZMod 4) := zmodFour_nontrivial
  intro h
  have hx : (MvPolynomial.X (0, false) : MvPolynomial (ℕ × Bool) (ZMod 4)) =
      MvPolynomial.X (0, true) := by
    apply h
    change MvPolynomial.rename shiftedProjection (MvPolynomial.X (0, false)) =
      MvPolynomial.rename shiftedProjection (MvPolynomial.X (0, true))
    simp only [MvPolynomial.rename_X, shiftedProjection_collision.2]
  exact shiftedProjection_collision.1 (MvPolynomial.X_injective hx)

/-- Shifted projection over the nonreduced coefficient ring is algebraic over
its full source polynomial ring, not merely over its coefficients. -/
private theorem zmodFour_shiftedProjection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4) shiftedProjection).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4)) :=
    (MvPolynomial.rename (R := ZMod 4) shiftedProjection).toRingHom.toAlgebra
  change Algebra.IsAlgebraic
    (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
  exact Algebra.isAlgebraic_of_not_injective
    zmodFour_shiftedProjection_algebraMap_not_injective

/-- The target variable omitted by shifted projection over the ring of order four
is not integral over the full source for the specified renaming action. -/
private theorem zmodFour_shiftedProjection_X_zero_not_isIntegral :
    ¬ @IsIntegral (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4) shiftedProjection).toRingHom.toAlgebra
      (MvPolynomial.X 0) := by
  intro h
  rcases (MvPolynomial.isIntegral_X_rename_iff (R := ZMod 4) shiftedProjection 0).mp h with
    hzero | hsub
  · obtain ⟨p, hp⟩ := hzero
    exact shiftedProjection_misses_zero p hp
  · have : Nontrivial (ZMod 4) := zmodFour_nontrivial
    exact zero_ne_one (hsub.elim 0 1)

end MvPolynomialRenameAlgebraicPositive

namespace MvPolynomialRenameAlgebraicNegative

open MvPolynomial

/-- The inclusion of the sole source variable does not identify variables. -/
private theorem somePUnit_injective :
    Function.Injective (some : PUnit → Option PUnit) := by
  intro i j h
  exact Option.some.inj h

/-- The extra target variable `none` has no preimage. -/
private theorem somePUnit_not_surjective :
    ¬ Function.Surjective (some : PUnit → Option PUnit) := by
  intro h
  obtain ⟨i, hi⟩ := h none
  cases hi

/-- The integer polynomial renaming is injective on the full source ring. -/
private theorem int_some_rename_injective :
    Function.Injective
      (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)) :=
  MvPolynomial.rename_injective _ somePUnit_injective

/-- The option-variable equivalence retains every integer source coefficient. -/
private theorem int_optionEquivLeft_comp_rename :
    (MvPolynomial.optionEquivLeft ℤ PUnit).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)).toRingHom =
      (Polynomial.C : MvPolynomial PUnit ℤ →+* Polynomial (MvPolynomial PUnit ℤ)) := by
  apply MvPolynomial.ringHom_ext
  · intro n
    simp
  · intro i
    simp

/-- The full integer polynomial renaming still misses a target polynomial. -/
private theorem int_some_rename_not_surjective :
    ¬ Function.Surjective
      (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)) := by
  intro h
  obtain ⟨p, hp⟩ := h (MvPolynomial.X none)
  have hpoly : (Polynomial.C p : Polynomial (MvPolynomial PUnit ℤ)) = Polynomial.X := by
    calc
      Polynomial.C p = (MvPolynomial.optionEquivLeft ℤ PUnit)
          (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit) p) :=
        (RingHom.congr_fun int_optionEquivLeft_comp_rename p).symm
      _ = Polynomial.X := by simp [hp]
  simpa using congrArg (fun q : Polynomial (MvPolynomial PUnit ℤ) => q.coeff 1) hpoly

/-- The omitted variable obstructs algebraicity over the full integer source. -/
private theorem int_some_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial PUnit ℤ) (MvPolynomial (Option PUnit) ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial PUnit ℤ) (MvPolynomial (Option PUnit) ℤ) :=
    (MvPolynomial.rename (R := ℤ) (some : PUnit → Option PUnit)).toRingHom.toAlgebra
  intro h
  have hcomp :
      (algebraMap (MvPolynomial PUnit ℤ) (Polynomial (MvPolynomial PUnit ℤ))).comp
          (RingHom.id (MvPolynomial PUnit ℤ)) =
        (MvPolynomial.optionEquivLeft ℤ PUnit).toRingEquiv.toRingHom.comp
          (algebraMap (MvPolynomial PUnit ℤ) (MvPolynomial (Option PUnit) ℤ)) := by
    change (Polynomial.C : MvPolynomial PUnit ℤ →+* Polynomial (MvPolynomial PUnit ℤ)).comp
        (RingHom.id (MvPolynomial PUnit ℤ)) = _
    simp only [RingHom.algebraMap_toAlgebra, int_optionEquivLeft_comp_rename,
      RingHom.comp_id]
  have hx := h.isAlgebraic (MvPolynomial.X (none : Option PUnit))
  have hX := hx.ringHom_of_comp_eq (RingHom.id (MvPolynomial PUnit ℤ))
    (MvPolynomial.optionEquivLeft ℤ PUnit).toRingEquiv.toRingHom
    Function.injective_id hcomp
  exact (Polynomial.transcendental_X (MvPolynomial PUnit ℤ)) (by simpa using hX)

/-- The square-zero element witnesses failure of reducedness. -/
private theorem zmodFour_not_isReduced : ¬ IsReduced (ZMod 4) := by
  intro h
  let : IsReduced (ZMod 4) := h
  exact zmodFour_two_ne_zero (IsReduced.eq_zero (2 : ZMod 4)
    ⟨2, zmodFour_two_sq_zero⟩)

/-- The same element also rules out a domain structure. -/
private theorem zmodFour_not_isDomain : ¬ IsDomain (ZMod 4) := by
  intro h
  let : IsDomain (ZMod 4) := h
  have hmul : (2 : ZMod 4) * 2 = 0 := by
    simpa only [pow_two] using zmodFour_two_sq_zero
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact zmodFour_two_ne_zero hzero
  · exact zmodFour_two_ne_zero hzero

/-- Nilpotents do not destroy injectivity of this variable inclusion. -/
private theorem zmodFour_some_rename_injective :
    Function.Injective
      (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)) :=
  MvPolynomial.rename_injective _ somePUnit_injective

/-- The option equivalence retains the whole source over the nonreduced ring. -/
private theorem zmodFour_optionEquivLeft_comp_rename :
    (MvPolynomial.optionEquivLeft (ZMod 4) PUnit).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)).toRingHom =
      (Polynomial.C : MvPolynomial PUnit (ZMod 4) →+*
        Polynomial (MvPolynomial PUnit (ZMod 4))) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp

/-- Nontrivial nonreduced coefficients still leave a missing target polynomial. -/
private theorem zmodFour_some_rename_not_surjective :
    ¬ Function.Surjective
      (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)) := by
  let : Nontrivial (ZMod 4) := zmodFour_nontrivial
  intro h
  obtain ⟨p, hp⟩ := h (MvPolynomial.X none)
  have hpoly : (Polynomial.C p : Polynomial (MvPolynomial PUnit (ZMod 4))) =
      Polynomial.X := by
    calc
      Polynomial.C p = (MvPolynomial.optionEquivLeft (ZMod 4) PUnit)
          (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit) p) :=
        (RingHom.congr_fun zmodFour_optionEquivLeft_comp_rename p).symm
      _ = Polynomial.X := by simp [hp]
  simpa using congrArg
    (fun q : Polynomial (MvPolynomial PUnit (ZMod 4)) => q.coeff 1) hpoly

/-- Nonreduced coefficients do not make the full rename-induced algebra algebraic. -/
private theorem zmodFour_some_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial PUnit (ZMod 4))
      (MvPolynomial (Option PUnit) (ZMod 4)) inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial PUnit (ZMod 4)) (MvPolynomial (Option PUnit) (ZMod 4)) :=
    (MvPolynomial.rename (R := ZMod 4) (some : PUnit → Option PUnit)).toRingHom.toAlgebra
  intro h
  have hcomp :
      (algebraMap (MvPolynomial PUnit (ZMod 4))
          (Polynomial (MvPolynomial PUnit (ZMod 4)))).comp
          (RingHom.id (MvPolynomial PUnit (ZMod 4))) =
        (MvPolynomial.optionEquivLeft (ZMod 4) PUnit).toRingEquiv.toRingHom.comp
          (algebraMap (MvPolynomial PUnit (ZMod 4))
            (MvPolynomial (Option PUnit) (ZMod 4))) := by
    change (Polynomial.C : MvPolynomial PUnit (ZMod 4) →+*
        Polynomial (MvPolynomial PUnit (ZMod 4))).comp
        (RingHom.id (MvPolynomial PUnit (ZMod 4))) = _
    simp only [RingHom.algebraMap_toAlgebra, zmodFour_optionEquivLeft_comp_rename,
      RingHom.comp_id]
  have hx := h.isAlgebraic (MvPolynomial.X (none : Option PUnit))
  have hX := hx.ringHom_of_comp_eq (RingHom.id (MvPolynomial PUnit (ZMod 4)))
    (MvPolynomial.optionEquivLeft (ZMod 4) PUnit).toRingEquiv.toRingHom
    Function.injective_id hcomp
  exact (Polynomial.transcendental_X (MvPolynomial PUnit (ZMod 4))) (by simpa using hX)

/-- Identity renaming over the zero ring is surjective on full polynomial rings. -/
private theorem zmodOne_id_rename_surjective :
    Function.Surjective (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)) :=
  MvPolynomial.rename_surjective _ nat_identity_bijective.2

/-- Surjective identity renaming is nevertheless not algebraic over a zero source. -/
private theorem zmodOne_id_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) :=
    (MvPolynomial.rename (R := ZMod 1) (id : ℕ → ℕ)).toRingHom.toAlgebra
  let : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial ℕ (ZMod 1))
  intro h
  let : Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) := h
  let : Nontrivial (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.nontrivial_of_isAlgebraic (MvPolynomial ℕ (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
  exact zero_ne_one (Subsingleton.elim (0 : MvPolynomial ℕ (ZMod 1)) 1)

/-- The empty-variable map is injective. -/
private theorem empty_nat_injective : Function.Injective (Empty.elim : Empty → ℕ) := by
  intro i
  exact Empty.elim i

/-- The same map omits the natural-number variable zero. -/
private theorem empty_nat_not_surjective :
    ¬ Function.Surjective (Empty.elim : Empty → ℕ) := by
  intro h
  obtain ⟨i, _⟩ := h 0
  exact Empty.elim i

/-- Zero coefficients collapse the target even though the variable map is not surjective. -/
private theorem zmodOne_empty_nat_rename_surjective :
    Function.Surjective
      (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)) := by
  let : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial ℕ (ZMod 1))
  exact Function.surjective_to_subsingleton _

/-- Even the zero target element needs a nonzero witness over the full zero source. -/
private theorem zmodOne_empty_nat_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) :=
    (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra
  let : Subsingleton (MvPolynomial Empty (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial Empty (ZMod 1))
  intro h
  let : Algebra.IsAlgebraic (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) := h
  let : Nontrivial (MvPolynomial Empty (ZMod 1)) :=
    Algebra.nontrivial_of_isAlgebraic
      (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
  exact zero_ne_one (Subsingleton.elim (0 : MvPolynomial Empty (ZMod 1)) 1)

/-- Lifting any zero coefficient ring preserves the negative algebraicity boundary,
even for a bijection of variable types in independent universes. -/
private theorem lifted_zero_not_isAlgebraic {R : Type u} [CommRing R] [Subsingleton R] :
    ¬ @Algebra.IsAlgebraic
      (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R)) inferInstance inferInstance
      (MvPolynomial.rename (R := ULift.{r} R)
        (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R)) :=
    (MvPolynomial.rename (R := ULift.{r} R)
      (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra
  let : Subsingleton (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R)) :=
    Algebra.subsingleton (ULift.{r} R) (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
  intro h
  let : Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R)) := h
  let : Nontrivial (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R)) :=
    Algebra.nontrivial_of_isAlgebraic
      (MvPolynomial (ULift.{v} ℕ) (ULift.{r} R))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{r} R))
  exact zero_ne_one
    (Subsingleton.elim (0 : MvPolynomial (ULift.{v} ℕ) (ULift.{r} R)) 1)

end MvPolynomialRenameAlgebraicNegative

namespace MvPolynomial

/-- Identity renaming on infinitely many variables over the integers is algebraic. -/
private theorem int_identity_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  exact (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) (id : ℕ → ℕ)).2
    ⟨inferInstance, Or.inl nat_identity_bijective.2⟩

/-- Forgetting a Boolean coordinate gives an algebraic renaming over the integers. -/
private theorem int_projection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  exact (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).2
    ⟨inferInstance, Or.inl projection_surjective⟩

/-- The shifted projection is algebraic despite omitting a target variable. -/
private theorem int_shiftedProjection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) shiftedProjection).toRingHom.toAlgebra := by
  exact (MvPolynomial.isAlgebraic_rename_iff (R := ℤ) shiftedProjection).2
    ⟨inferInstance, Or.inr shiftedProjection_not_injective⟩

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

/-- Projection remains algebraic with nonreduced coefficients. -/
private theorem zmod_four_projection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) (ZMod 4))
      (MvPolynomial ℕ (ZMod 4)) inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4)
        (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  obtain ⟨a, ha, _⟩ := zmodFour_has_nonzero_square_zero
  apply (MvPolynomial.isAlgebraic_rename_iff (R := ZMod 4) (Prod.fst : ℕ × Bool → ℕ)).2
  exact ⟨⟨⟨a, 0, ha⟩⟩, Or.inl projection_surjective⟩

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
  have : Nontrivial (ZMod 1) :=
    ((MvPolynomial.isAlgebraic_rename_iff (R := ZMod 1) (id : ℕ → ℕ)).1 h).1
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

/-- An empty source variable set does not change the zero-coefficient obstruction. -/
private theorem zmod_one_empty_to_nat_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 1)
        (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra := by
  intro h
  have : Nontrivial (ZMod 1) :=
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

/-- Coefficients and both variable types may occupy independent universes. -/
private theorem lifted_identity_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ)) inferInstance inferInstance
      (MvPolynomial.rename (R := ULift.{u} ℤ)
        (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra := by
  apply (MvPolynomial.isAlgebraic_rename_iff (R := ULift.{u} ℤ)
    (liftedIdentity : ULift.{v} ℕ → ULift.{w} ℕ)).2
  exact ⟨inferInstance, Or.inl liftedIdentity_bijective.2⟩

/-- Successor between independent lifts still omits lifted zero. -/
private def liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ :=
  fun n => ⟨n.down.succ⟩

/-- The missing-variable obstruction also retains three independent universes. -/
private theorem lifted_successor_not_isAlgebraic :
    ¬ @Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ)) inferInstance inferInstance
      (MvPolynomial.rename (R := ULift.{u} ℤ)
        (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra := by
  let : Algebra (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ)) :=
    (MvPolynomial.rename (R := ULift.{u} ℤ)
      (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ)).toRingHom.toAlgebra
  intro h
  have : Algebra.IsAlgebraic (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ)) := h
  have hx := Algebra.IsAlgebraic.isAlgebraic
    (R := MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℤ))
    (X (ULift.up 0 : ULift.{w} ℕ) :
      MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℤ))
  rcases ((MvPolynomial.isAlgebraic_X_rename_iff (R := ULift.{u} ℤ)
    (liftedSuccessor : ULift.{v} ℕ → ULift.{w} ℕ) (ULift.up 0)).1 hx).2 with hs | hi
  · obtain ⟨n, hn⟩ := hs
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

end
