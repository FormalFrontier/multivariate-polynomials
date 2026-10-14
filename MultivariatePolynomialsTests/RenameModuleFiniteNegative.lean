/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFiniteType
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Nonfinite modules from variable renaming

Successor renaming on countably many variables misses the variable indexed by zero.
Over the natural numbers it gives a finite-type algebra which is not finite as a
module over the source polynomial semiring. The module obstruction also applies to
coefficients in `ZMod 4` and the extended natural numbers, without cancellation or
reducedness assumptions. An empty source and a one-variable target give another
boundary case. Separate universe lifts of the coefficients and both variable types
retain the obstruction.

The module structures below are induced by renaming: a source polynomial acts by
multiplication by its renamed image. In particular, successor renaming does not use
the regular self-module structure, even though source and target have the same carrier.

## References

* Mathlib, `MvPolynomial.eval₂Hom_rename` and `MvPolynomial.eval₂Hom_zero'_apply`:
  evaluation of renamed polynomials and specialization at zero.
* Mathlib, `Polynomial.aeval` and `Polynomial.algHom_ext`: a section of evaluation
  onto a univariate polynomial semiring.
* Mathlib, `Module.Finite.of_surjective` and `Polynomial.not_finite`: the semilinear
  image obstruction to finite generation over the source polynomial semiring.
* `MvPolynomial.finiteType_rename_iff`: finite type of a variable-renaming algebra.
-/

public section

noncomputable section

universe u v w

namespace MvPolynomial

private theorem not_finite_rename_succ {R : Type u} [CommSemiring R] [Nontrivial R] :
    ¬ @Module.Finite (MvPolynomial ℕ R) (MvPolynomial ℕ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ R) (MvPolynomial ℕ R)
        inferInstance inferInstance
        (rename (R := R) Nat.succ).toRingHom.toAlgebra) := by
  classical
  intro h
  let : Module (MvPolynomial ℕ R) (MvPolynomial ℕ R) :=
    @Algebra.toModule (MvPolynomial ℕ R) (MvPolynomial ℕ R)
      inferInstance inferInstance (rename (R := R) Nat.succ).toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial ℕ R) (MvPolynomial ℕ R) := h
  let π : MvPolynomial ℕ R →ₐ[R] Polynomial R :=
    aeval fun n => if n = 0 then Polynomial.X else 0
  have hfactor (a : MvPolynomial ℕ R) :
      π (rename Nat.succ a) = Polynomial.C (constantCoeff a) := by
    change eval₂Hom (algebraMap R (Polynomial R))
      (fun n => if n = 0 then Polynomial.X else 0) (rename Nat.succ a) = _
    rw [eval₂Hom_rename]
    have hzero : (fun n : ℕ => if n = 0 then (Polynomial.X : Polynomial R) else 0) ∘
        Nat.succ = fun _ => 0 := by
      funext n
      simp
    rw [hzero, eval₂Hom_zero'_apply, Polynomial.algebraMap_eq]
  have hsection : π.comp (Polynomial.aeval (X (0 : ℕ))) =
      AlgHom.id R (Polynomial R) := by
    apply Polynomial.algHom_ext
    simp [π]
  let ψ : @LinearMap (MvPolynomial ℕ R) R inferInstance inferInstance
      (constantCoeff : MvPolynomial ℕ R →+* R)
      (MvPolynomial ℕ R) (Polynomial R) inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ R) (MvPolynomial ℕ R)
        inferInstance inferInstance (rename (R := R) Nat.succ).toRingHom.toAlgebra)
      inferInstance :=
    { toFun := π
      map_add' := π.map_add
      map_smul' := fun a b => by
        change π (rename Nat.succ a * b) = constantCoeff a • π b
        rw [map_mul, hfactor]
        simpa only [Polynomial.algebraMap_eq] using
          (Algebra.smul_def (constantCoeff a) (π b)).symm }
  have hsurj : Function.Surjective ψ := by
    intro p
    exact ⟨Polynomial.aeval (X (0 : ℕ)) p, AlgHom.congr_fun hsection p⟩
  exact Polynomial.not_finite (Module.Finite.of_surjective ψ hsurj)

/-- Successor misses zero, although both variable types are infinite. -/
private theorem not_surjective_succ : ¬ Function.Surjective Nat.succ := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

/-- Successor renaming over the natural numbers is finite type. -/
private theorem finiteType_succ_nat : @Algebra.FiniteType (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
    inferInstance inferInstance (rename (R := ℕ) Nat.succ).toRingHom.toAlgebra := by
  apply (finiteType_rename_iff (R := ℕ) Nat.succ).2
  right
  apply (Set.finite_singleton 0).subset
  intro n hn
  cases n with
  | zero => simp
  | succ n => exact False.elim (hn ⟨n, rfl⟩)

/-- Finite type does not imply module finiteness over the source polynomial semiring. -/
private theorem not_finite_rename_succ_nat : ¬ @Module.Finite (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
    inferInstance inferInstance
    (@Algebra.toModule (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance
      (rename (R := ℕ) Nat.succ).toRingHom.toAlgebra) :=
  not_finite_rename_succ

/-- The coefficient semiring has a nonzero square-zero element. -/
private theorem zmod_four_two_ne_zero_and_sq_eq_zero : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  decide

/-- Nilpotent coefficients do not remove the missed-variable obstruction. -/
private theorem zmod4_not_fg : ¬ @Module.Finite (MvPolynomial ℕ (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
    inferInstance inferInstance
    (@Algebra.toModule (MvPolynomial ℕ (ZMod 4)) (MvPolynomial ℕ (ZMod 4))
      inferInstance inferInstance
      (rename (R := ZMod 4) Nat.succ).toRingHom.toAlgebra) := by
  let : Fact (1 < 4) := ⟨by decide⟩
  exact not_finite_rename_succ

/-- Addition of extended natural numbers is not cancellative at infinity. -/
private theorem enat_top_add_eq_and_zero_ne_one : (⊤ : ℕ∞) + 0 = ⊤ + 1 ∧ (0 : ℕ∞) ≠ 1 := by
  exact ⟨rfl, zero_ne_one⟩

/-- The same obstruction holds over a noncancellative semiring. -/
private theorem not_finite_succ_enat : ¬ @Module.Finite (MvPolynomial ℕ ℕ∞) (MvPolynomial ℕ ℕ∞)
    inferInstance inferInstance
    (@Algebra.toModule (MvPolynomial ℕ ℕ∞) (MvPolynomial ℕ ℕ∞)
      inferInstance inferInstance
      (rename (R := ℕ∞) Nat.succ).toRingHom.toAlgebra) :=
  not_finite_rename_succ

/-- An empty source and a single target variable already give a nonfinite module. -/
private theorem not_finite_empty : ¬ @Module.Finite (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ)
    inferInstance inferInstance
    (@Algebra.toModule (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ)
      inferInstance inferInstance
      (rename (R := ℕ) (Empty.elim : Empty → Unit)).toRingHom.toAlgebra) := by
  classical
  intro h
  let : Module (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ) :=
    @Algebra.toModule (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ)
      inferInstance inferInstance
      (rename (R := ℕ) (Empty.elim : Empty → Unit)).toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ) := h
  let π : MvPolynomial Unit ℕ →ₐ[ℕ] Polynomial ℕ := aeval fun _ => Polynomial.X
  have hfactor (a : MvPolynomial Empty ℕ) :
      π (rename (Empty.elim : Empty → Unit) a) = Polynomial.C (constantCoeff a) := by
    change eval₂Hom (algebraMap ℕ (Polynomial ℕ)) (fun _ : Unit => Polynomial.X)
      (rename (Empty.elim : Empty → Unit) a) = _
    rw [eval₂Hom_rename]
    have hzero : (fun _ : Unit => (Polynomial.X : Polynomial ℕ)) ∘
        (Empty.elim : Empty → Unit) = fun _ => 0 := by
      funext i
      exact i.elim
    rw [hzero, eval₂Hom_zero'_apply, Polynomial.algebraMap_eq]
  have hsection : π.comp (Polynomial.aeval (X Unit.unit)) =
      AlgHom.id ℕ (Polynomial ℕ) := by
    apply Polynomial.algHom_ext
    simp [π]
  let ψ : @LinearMap (MvPolynomial Empty ℕ) ℕ inferInstance inferInstance
      (constantCoeff : MvPolynomial Empty ℕ →+* ℕ)
      (MvPolynomial Unit ℕ) (Polynomial ℕ) inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial Empty ℕ) (MvPolynomial Unit ℕ)
        inferInstance inferInstance
        (rename (R := ℕ) (Empty.elim : Empty → Unit)).toRingHom.toAlgebra)
      inferInstance :=
    { toFun := π
      map_add' := π.map_add
      map_smul' := fun a b => by
        change π (rename (Empty.elim : Empty → Unit) a * b) = constantCoeff a • π b
        rw [map_mul, hfactor]
        simpa only [Polynomial.algebraMap_eq] using
          (Algebra.smul_def (constantCoeff a) (π b)).symm }
  have hsurj : Function.Surjective ψ := by
    intro p
    exact ⟨Polynomial.aeval (X Unit.unit) p, AlgHom.congr_fun hsection p⟩
  exact Polynomial.not_finite (Module.Finite.of_surjective ψ hsurj)

/-- Coefficients, source variables, and target variables can be lifted independently. -/
private theorem not_finite_rename_succ_ulift : ¬ @Module.Finite
    (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
    (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
    inferInstance inferInstance
    (@Algebra.toModule
      (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
      inferInstance inferInstance
      (rename (R := ULift.{u} ℕ)
        (fun n : ULift.{v} ℕ => (⟨n.down.succ⟩ : ULift.{w} ℕ))).toRingHom.toAlgebra) := by
  classical
  intro h
  let f : ULift.{v} ℕ → ULift.{w} ℕ := fun n => ⟨n.down.succ⟩
  let : Module
      (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) :=
    @Algebra.toModule
      (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
      inferInstance inferInstance (rename (R := ULift.{u} ℕ) f).toRingHom.toAlgebra
  let : Module.Finite
      (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) := h
  let π : MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ) →ₐ[ULift.{u} ℕ]
      Polynomial (ULift.{u} ℕ) :=
    aeval fun n => if n.down = 0 then Polynomial.X else 0
  have hfactor (a : MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ)) :
      π (rename f a) = Polynomial.C (constantCoeff a) := by
    change eval₂Hom (algebraMap (ULift.{u} ℕ) (Polynomial (ULift.{u} ℕ)))
      (fun n : ULift.{w} ℕ => if n.down = 0 then Polynomial.X else 0) (rename f a) = _
    rw [eval₂Hom_rename]
    have hzero : (fun n : ULift.{w} ℕ =>
        if n.down = 0 then (Polynomial.X : Polynomial (ULift.{u} ℕ)) else 0) ∘ f =
          fun _ => 0 := by
      funext n
      simp [f]
    rw [hzero, eval₂Hom_zero'_apply, Polynomial.algebraMap_eq]
  have hsection : π.comp (Polynomial.aeval (X (⟨0⟩ : ULift.{w} ℕ))) =
      AlgHom.id (ULift.{u} ℕ) (Polynomial (ULift.{u} ℕ)) := by
    apply Polynomial.algHom_ext
    simp [π]
  let ψ : @LinearMap
      (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ)) (ULift.{u} ℕ)
      inferInstance inferInstance
      (constantCoeff : MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ) →+* ULift.{u} ℕ)
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) (Polynomial (ULift.{u} ℕ))
      inferInstance inferInstance
      (@Algebra.toModule
        (MvPolynomial (ULift.{v} ℕ) (ULift.{u} ℕ))
        (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
        inferInstance inferInstance (rename (R := ULift.{u} ℕ) f).toRingHom.toAlgebra)
      inferInstance :=
    { toFun := π
      map_add' := π.map_add
      map_smul' := fun a b => by
        change π (rename f a * b) = constantCoeff a • π b
        rw [map_mul, hfactor]
        simpa only [Polynomial.algebraMap_eq] using
          (Algebra.smul_def (constantCoeff a) (π b)).symm }
  have hsurj : Function.Surjective ψ := by
    intro p
    exact ⟨Polynomial.aeval (X (⟨0⟩ : ULift.{w} ℕ)) p, AlgHom.congr_fun hsection p⟩
  exact Polynomial.not_finite (Module.Finite.of_surjective ψ hsurj)

end MvPolynomial
