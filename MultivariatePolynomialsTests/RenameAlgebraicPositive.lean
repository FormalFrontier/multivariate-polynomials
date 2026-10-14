/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Bool.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraic variable renaming: independent positive models

The algebras in these examples have the full source polynomial ring as their
base and the full target polynomial ring as their carrier. Their algebra
structure is explicitly induced by the coefficient-preserving renaming ring
homomorphism. These are not algebraicity assertions over the coefficient ring.

Over the integers, identity on natural-number variables and projection from
`ℕ × Bool` give algebraic algebras by surjectivity and integrality. Projection
is surjective but not injective. The shifted projection `(n, b) ↦ n + 1` has
both a collision and a missing target variable. Its induced algebra is
nonfaithful and algebraic, but the renaming homomorphism is not integral.
Thus a missing variable does not imply nonalgebraicity over the full source.

The same shifted projection is algebraic over the full source polynomial ring
with coefficients in `ZMod 4`. The coefficient `2` is nonzero and has square
zero, so this example has genuinely nonreduced coefficients. All four models
have infinitely many source and target variables.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: renaming and its surjectivity.
* Mathlib, `Mathlib.RingTheory.Algebraic.Basic`:
  `Algebra.isAlgebraic_of_not_injective`.
* Mathlib, `Mathlib.RingTheory.Algebraic.Integral`: integral implies algebraic
  over a nontrivial base ring.
* Mathlib, `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`:
  surjective ring homomorphisms are integral.
-/

namespace MvPolynomialRenameAlgebraicPositive

/-- Identity leaves every natural-number variable available. -/
private theorem nat_identity_surjective : Function.Surjective (id : ℕ → ℕ) := by
  intro n
  exact ⟨n, rfl⟩

/-- Identity renaming is algebraic over the full integer polynomial ring. -/
private theorem int_nat_identity_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) (id : ℕ → ℕ)).toRingHom.toAlgebra
  change Algebra.IsAlgebraic (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)
  haveI : Nontrivial (MvPolynomial ℕ ℤ) := inferInstance
  haveI : Algebra.IsIntegral (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) :=
    ⟨RingHom.isIntegral_of_surjective _
      (MvPolynomial.rename_surjective (R := ℤ) _ nat_identity_surjective)⟩
  exact Algebra.IsIntegral.isAlgebraic

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

/-- A surjective, noninjective renaming is algebraic over its full source. -/
private theorem int_projection_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  change Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
  haveI : Nontrivial (MvPolynomial (ℕ × Bool) ℤ) := inferInstance
  haveI : Algebra.IsIntegral (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    ⟨RingHom.isIntegral_of_surjective _
      (MvPolynomial.rename_surjective (R := ℤ) _ projection_surjective)⟩
  exact Algebra.IsIntegral.isAlgebraic

/-- The projection example really has both advertised variable-map properties. -/
private theorem int_projection_model :
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) ∧
      ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) ∧
      @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra :=
  ⟨projection_surjective, projection_not_injective, int_projection_isAlgebraic⟩

/-- A fixed renaming that forgets the Boolean coordinate and omits zero. -/
private def pairSucc : ℕ × Bool → ℕ := fun p => p.1 + 1

/-- Two distinct source variables have the same shifted image. -/
private theorem pairSucc_collision :
    ((0, false) : ℕ × Bool) ≠ (0, true) ∧
      pairSucc (0, false) = pairSucc (0, true) := by
  refine ⟨?_, rfl⟩
  intro h
  cases congrArg Prod.snd h

/-- In particular, shifted projection is not injective. -/
private theorem pairSucc_not_injective : ¬ Function.Injective pairSucc := by
  intro h
  exact pairSucc_collision.1 (h pairSucc_collision.2)

/-- The target variable indexed by zero is missing. -/
private theorem pairSucc_misses_zero (p : ℕ × Bool) : pairSucc p ≠ 0 := by
  simp [pairSucc]

/-- Shifted projection is not surjective. -/
private theorem pairSucc_not_surjective : ¬ Function.Surjective pairSucc := by
  intro h
  obtain ⟨p, hp⟩ := h 0
  exact pairSucc_misses_zero p hp

/-- The canonical full-source algebra map identifies distinct indeterminates. -/
private theorem int_pairSucc_algebraMap_not_injective :
    ¬ Function.Injective
      (@algebraMap (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom.toAlgebra) := by
  intro h
  have hx : (MvPolynomial.X (0, false) : MvPolynomial (ℕ × Bool) ℤ) =
      MvPolynomial.X (0, true) := by
    apply h
    change MvPolynomial.rename pairSucc (MvPolynomial.X (0, false)) =
      MvPolynomial.rename pairSucc (MvPolynomial.X (0, true))
    simp only [MvPolynomial.rename_X, pairSucc_collision.2]
  exact pairSucc_collision.1 (MvPolynomial.X_injective hx)

/-- The algebraic model uses the actual nonfaithful renaming action. -/
private theorem int_pairSucc_not_faithful :
    ¬ @FaithfulSMul (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      (@Algebra.toSMul (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom.toAlgebra) := by
  letI : Algebra (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom.toAlgebra
  change ¬ FaithfulSMul (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
  intro h
  exact int_pairSucc_algebraMap_not_injective
    ((faithfulSMul_iff_algebraMap_injective _ _).mp h)

/-- Noninjectivity of the full-source algebra map makes every target element algebraic. -/
private theorem int_pairSucc_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
      inferInstance inferInstance
      (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) :=
    (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom.toAlgebra
  change Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
  exact Algebra.isAlgebraic_of_not_injective int_pairSucc_algebraMap_not_injective

/-- The missing target variable still prevents integrality for this fixed map. -/
private theorem int_pairSucc_not_isIntegral :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) pairSucc).toRingHom) := by
  intro h
  let ψ : MvPolynomial ℕ ℤ →+* Polynomial ℤ :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun n => if n = 0 then Polynomial.X else 0)
  let ε : MvPolynomial (ℕ × Bool) ℤ →+* ℤ :=
    MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun _ => 0)
  have hcomp : ψ.comp (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom =
      Polynomial.C.comp ε := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, ε]
    · intro p
      simp [ψ, ε, pairSucc]
  have hx := (h (MvPolynomial.X 0)).map ψ
  rw [hcomp] at hx
  have hX : IsIntegral ℤ (Polynomial.X : Polynomial ℤ) := by
    simpa [IsIntegral, ψ] using hx.of_comp
  exact (Polynomial.transcendental_X ℤ) hX.isAlgebraic

/-- Infinitely many variables coexist with algebraicity and failure of integrality. -/
private theorem int_pairSucc_infinite_algebraic_not_integral :
    Infinite (ℕ × Bool) ∧ Infinite ℕ ∧
      ¬ Function.Injective pairSucc ∧ ¬ Function.Surjective pairSucc ∧
      @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℤ) pairSucc).toRingHom.toAlgebra ∧
      ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := ℤ) pairSucc).toRingHom) :=
  ⟨inferInstance, inferInstance, pairSucc_not_injective, pairSucc_not_surjective,
    int_pairSucc_isAlgebraic, int_pairSucc_not_isIntegral⟩

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

/-- Distinct source indeterminates remain distinct with these nonreduced coefficients,
but their images under shifted renaming coincide. -/
private theorem zmodFour_pairSucc_algebraMap_not_injective :
    ¬ Function.Injective
      (@algebraMap (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
        inferInstance inferInstance
        (MvPolynomial.rename (R := ZMod 4) pairSucc).toRingHom.toAlgebra) := by
  haveI : Nontrivial (ZMod 4) := zmodFour_nontrivial
  intro h
  have hx : (MvPolynomial.X (0, false) : MvPolynomial (ℕ × Bool) (ZMod 4)) =
      MvPolynomial.X (0, true) := by
    apply h
    change MvPolynomial.rename pairSucc (MvPolynomial.X (0, false)) =
      MvPolynomial.rename pairSucc (MvPolynomial.X (0, true))
    simp only [MvPolynomial.rename_X, pairSucc_collision.2]
  exact pairSucc_collision.1 (MvPolynomial.X_injective hx)

/-- Shifted projection over the nonreduced coefficient ring is algebraic over
its full source polynomial ring, not merely over its coefficients. -/
private theorem zmodFour_pairSucc_isAlgebraic :
    @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
      inferInstance inferInstance
      (MvPolynomial.rename (R := ZMod 4) pairSucc).toRingHom.toAlgebra := by
  letI : Algebra (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4)) :=
    (MvPolynomial.rename (R := ZMod 4) pairSucc).toRingHom.toAlgebra
  change Algebra.IsAlgebraic
    (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
  exact Algebra.isAlgebraic_of_not_injective
    zmodFour_pairSucc_algebraMap_not_injective

/-- A collision and a missing variable give a positive model even with a
nonzero square-zero coefficient. -/
private theorem zmodFour_pairSucc_model :
    (∃ a : ZMod 4, a ≠ 0 ∧ a ^ 2 = 0) ∧
      ¬ Function.Injective pairSucc ∧ ¬ Function.Surjective pairSucc ∧
      @Algebra.IsAlgebraic (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
        inferInstance inferInstance
        (MvPolynomial.rename (R := ZMod 4) pairSucc).toRingHom.toAlgebra :=
  ⟨zmodFour_has_nonzero_square_zero, pairSucc_not_injective,
    pairSucc_not_surjective, zmodFour_pairSucc_isAlgebraic⟩

end MvPolynomialRenameAlgebraicPositive
