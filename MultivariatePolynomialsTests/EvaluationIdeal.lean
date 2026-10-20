/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.EvaluationIdeal
import MultivariatePolynomials.IdealOfVars
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Evaluation-ideal clients

These examples exercise the evaluation-ideal statements at a nonzero integer
point, in infinitely many or no variables, over rings with zero divisors or
only one element, and at a rational point. Evaluation at zero in one variable
has a finitely generated kernel over `ℤ`, but contracting it along the renaming
that sends every natural-number-indexed variable to that variable gives an
augmentation ideal that is not finitely generated.
The coefficient-ideal example evaluates `X + 1` at `3` over `ℤ`: its nonzero
value `4` lies in the proper nonzero ideal `(2)`.
The cotangent basis is used on an integer variable class with infinitely many
available variables and on a mixed linear and quadratic representative over
`ZMod 4`, where the coefficient `2` is nilpotent but survives as a coordinate.

## References

* `MultivariatePolynomials.EvaluationIdeal`: coordinate-ideal and singleton
  vanishing-ideal results, and contraction of evaluation kernels.
* `MultivariatePolynomials.IdealOfVars`: the infinite-variable obstruction
  motivated by Vakil's Exercise 6.7.E.
* Mathlib's `Mathlib.RingTheory.MvPolynomial.Ideal`: finite-variable finite
  generation and membership in powers of the variable ideal.
* Mathlib's `Mathlib.Algebra.MvPolynomial.Eval` and
  `Mathlib.Algebra.MvPolynomial.Rename`: evaluation at zero and preservation
  of the constant coefficient under renaming.
* Mathlib's `Mathlib.Data.Finsupp.Weight`: the zero-degree criterion for
  exponent vectors; `Mathlib.Data.ZMod.Basic` supplies finite-ring boundaries.
-/

private theorem integerNonconstant :
    (MvPolynomial.X (3 : ℕ) ^ 2 - MvPolynomial.C (25 : ℤ)) ∈
      Ideal.span (Set.range (fun i : ℕ =>
        (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (5 : ℤ))) := by
  apply (MvPolynomial.mem_ideal_span_X_sub_C_iff (fun _ : ℕ => (5 : ℤ)) _).2
  norm_num

public theorem MultivariatePolynomialsTests.integerNonmember :
    (MvPolynomial.X (3 : ℕ) - MvPolynomial.C (4 : ℤ)) ∉
      Ideal.span (Set.range (fun i : ℕ =>
        (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (5 : ℤ))) := by
  rw [MvPolynomial.mem_ideal_span_X_sub_C_iff]
  norm_num

/-- A nonzero value in a proper nonzero coefficient ideal gives membership
in the sum ideal without belonging to the evaluation kernel. -/
private theorem integerCoefficientFiber :
    let I : Ideal ℤ := Ideal.span {2}
    let x : Unit → ℤ := fun _ => 3
    let p : MvPolynomial Unit ℤ := MvPolynomial.X () + MvPolynomial.C 1
    I ≠ ⊥ ∧ I ≠ ⊤ ∧ MvPolynomial.eval x p = 4 ∧ (4 : ℤ) ∈ I ∧
      MvPolynomial.eval x p ≠ 0 ∧
      p ∈ Ideal.map (MvPolynomial.C : ℤ →+* MvPolynomial Unit ℤ) I ⊔
        Ideal.span (Set.range (fun i : Unit =>
          MvPolynomial.X i - MvPolynomial.C (x i))) := by
  dsimp only
  have htwo : (2 : ℤ) ∈ Ideal.span ({2} : Set ℤ) :=
    Ideal.mem_span_singleton_self 2
  have hfour : (4 : ℤ) ∈ Ideal.span ({2} : Set ℤ) := by
    norm_num [Ideal.mem_span_singleton]
  have heval : MvPolynomial.eval (fun _ : Unit => (3 : ℤ))
      (MvPolynomial.X () + MvPolynomial.C 1) = 4 := by
    norm_num
  refine ⟨?_, ?_, heval, hfour, ?_, ?_⟩
  · intro h
    have hz : (2 : ℤ) = 0 := by
      simpa only [h, Ideal.mem_bot] using htwo
    norm_num at hz
  · intro h
    have hone := (Ideal.eq_top_iff_one _).mp h
    norm_num [Ideal.mem_span_singleton] at hone
  · rw [heval]
    norm_num
  · rw [MvPolynomial.map_C_sup_span_X_sub_C_eq_comap_eval, Ideal.mem_comap, heval]
    exact hfour

private theorem emptyVariablesCoefficientNonmember :
    (MvPolynomial.C (1 : ℤ) : MvPolynomial Empty ℤ) ∉
      Ideal.map (MvPolynomial.C : ℤ →+* MvPolynomial Empty ℤ)
          (Ideal.span ({2} : Set ℤ)) ⊔
        Ideal.span (Set.range (fun i : Empty =>
          (MvPolynomial.X i : MvPolynomial Empty ℤ) - MvPolynomial.C (0 : ℤ))) := by
  rw [MvPolynomial.map_C_sup_span_X_sub_C_eq_comap_eval, Ideal.mem_comap,
    MvPolynomial.eval_C]
  norm_num [Ideal.mem_span_singleton]

private theorem coefficientFiberTopBottom (x : ℕ → ℤ) :
    let J : Ideal (MvPolynomial ℕ ℤ) :=
      Ideal.span (Set.range (fun i : ℕ => MvPolynomial.X i - MvPolynomial.C (x i)))
    (Ideal.map (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ) ⊤ ⊔ J = ⊤) ∧
      (Ideal.map (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ) ⊥ ⊔ J =
        RingHom.ker (MvPolynomial.eval x)) := by
  dsimp only
  constructor
  · rw [MvPolynomial.map_C_sup_span_X_sub_C_eq_comap_eval, Ideal.comap_top]
  · rw [MvPolynomial.map_C_sup_span_X_sub_C_eq_comap_eval, ← RingHom.ker_eq_comap_bot]

private theorem zeroRingCoefficientFiber (I : Ideal (ZMod 1))
    (p : MvPolynomial Unit (ZMod 1)) :
    p ∈ Ideal.map (MvPolynomial.C : ZMod 1 →+* MvPolynomial Unit (ZMod 1)) I ⊔
      Ideal.span (Set.range (fun i : Unit =>
        MvPolynomial.X i - MvPolynomial.C (0 : ZMod 1))) := by
  rw [MvPolynomial.map_C_sup_span_X_sub_C_eq_comap_eval, Ideal.mem_comap]
  have h : MvPolynomial.eval (fun _ : Unit => (0 : ZMod 1)) p = 0 :=
    Subsingleton.elim _ _
  rw [h]
  exact I.zero_mem

private theorem emptyVariablesNonmember :
    (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin 0) ℤ) ∉
      Ideal.span (Set.range (fun i : Fin 0 =>
        (MvPolynomial.X i : MvPolynomial (Fin 0) ℤ) - MvPolynomial.C (0 : ℤ))) := by
  rw [MvPolynomial.mem_ideal_span_X_sub_C_iff]
  norm_num

private theorem zeroDivisors :
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (0 : ZMod 6)) ∈
      Ideal.span (Set.range (fun i : Fin 2 =>
        (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 6)) -
          MvPolynomial.C (if i = 0 then (2 : ZMod 6) else 3))) := by
  apply (MvPolynomial.mem_ideal_span_X_sub_C_iff
    (fun i : Fin 2 => if i = 0 then (2 : ZMod 6) else 3) _).2
  norm_num
  exact ZMod.natCast_self 6

private theorem zeroRing (p : MvPolynomial (Fin 2) (ZMod 1)) :
    p ∈ Ideal.span (Set.range (fun i : Fin 2 =>
      (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 1)) - MvPolynomial.C (0 : ZMod 1))) := by
  apply (MvPolynomial.mem_ideal_span_X_sub_C_iff (fun _ : Fin 2 => (0 : ZMod 1)) p).2
  exact Subsingleton.elim _ _

private theorem rationalVanishing :
    (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (7 : ℚ)) ∈
      MvPolynomial.vanishingIdeal ℚ {(fun _ : Fin 2 => (7 : ℚ))} := by
  rw [← MvPolynomial.ideal_span_X_sub_C_eq_vanishingIdeal_singleton]
  exact Ideal.subset_span (Set.mem_range_self (0 : Fin 2))

private theorem zeroPointVariableIdeal :
    Ideal.span (Set.range (fun i : ℕ =>
      (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (0 : ℤ))) =
      MvPolynomial.idealOfVars ℕ ℤ := by
  simp [MvPolynomial.idealOfVars]

/-- A finitely generated zero-evaluation ideal over `ℤ` has a non-finitely-generated
contraction when infinitely many source variables are renamed to its sole variable. -/
private theorem integer_augmentation_contraction_not_fg :
    let c : ℕ → Fin 1 := fun _ => 0
    let J := MvPolynomial.idealOfVars (Fin 1) ℤ
    J.FG ∧
      J.comap (MvPolynomial.rename (R := ℤ) c).toRingHom =
        MvPolynomial.idealOfVars ℕ ℤ ∧
      ¬ (J.comap (MvPolynomial.rename (R := ℤ) c).toRingHom).FG := by
  dsimp only
  have hcomap :
      (MvPolynomial.idealOfVars (Fin 1) ℤ).comap
        (MvPolynomial.rename (R := ℤ) (fun _ : ℕ => (0 : Fin 1))).toRingHom =
          MvPolynomial.idealOfVars ℕ ℤ := by
    rw [MvPolynomial.idealOfVars_eq_ker_constantCoeff (σ := Fin 1) (R := ℤ),
      MvPolynomial.idealOfVars_eq_ker_constantCoeff (σ := ℕ) (R := ℤ)]
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change MvPolynomial.constantCoeff
      (MvPolynomial.rename (fun _ : ℕ => (0 : Fin 1)) p) = 0 ↔
        MvPolynomial.constantCoeff p = 0
    rw [MvPolynomial.constantCoeff_rename]
  refine ⟨MvPolynomial.idealOfVars_fg (Fin 1) ℤ, hcomap, ?_⟩
  rw [hcomap]
  exact MvPolynomial.idealOfVars_not_fg ℤ ℕ

/-- A variable class has coordinate one, even with an infinite variable type. -/
private theorem integerCotangentGenerator :
    (MvPolynomial.idealOfVarsCotangentBasis ℕ ℤ).repr
      ((MvPolynomial.idealOfVars ℕ ℤ).toCotangent
        ⟨MvPolynomial.X 37, Ideal.subset_span (Set.mem_range_self 37)⟩) 37 = 1 := by
  rw [MvPolynomial.idealOfVarsCotangentBasis_repr_X]
  simp

/-- A representative with a nilpotent linear coefficient and a quadratic term. -/
private noncomputable def nilpotentAugmentationRepresentative :
    MvPolynomial.idealOfVars (Fin 2) (ZMod 4) :=
  ⟨MvPolynomial.X 0 + MvPolynomial.C 2 * MvPolynomial.X 1 +
      MvPolynomial.X 0 * MvPolynomial.X 1, by
    apply Ideal.add_mem
    · apply Ideal.add_mem
      · exact Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
      · exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_range_self (1 : Fin 2)))
    · exact Ideal.mul_mem_left _ _
        (Ideal.subset_span (Set.mem_range_self (1 : Fin 2)))⟩

/-- Only the two linear coefficients contribute to the cotangent coordinates. -/
private theorem nilpotentCotangentCoordinates :
    (MvPolynomial.idealOfVarsCotangentBasis (Fin 2) (ZMod 4)).repr
        ((MvPolynomial.idealOfVars (Fin 2) (ZMod 4)).toCotangent
          nilpotentAugmentationRepresentative) 0 = 1 ∧
      (MvPolynomial.idealOfVarsCotangentBasis (Fin 2) (ZMod 4)).repr
        ((MvPolynomial.idealOfVars (Fin 2) (ZMod 4)).toCotangent
          nilpotentAugmentationRepresentative) 1 = 2 := by
  simp only [MvPolynomial.idealOfVarsCotangentBasis_repr_toCotangent]
  norm_num [nilpotentAugmentationRepresentative, MvPolynomial.coeff_X,
    MvPolynomial.coeff_mul_X', Finsupp.single_apply,
    Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)]

-- A double zero at a nonzero integer point, with infinitely many variables.
open MvPolynomial in
example :
    ∀ d : ℕ →₀ ℕ, d.sum (fun _ k => k) < 2 →
      (eval₂Hom C (fun i : ℕ => X i + C (2 : ℤ))
        ((X 0 - C (2 : ℤ)) ^ 2)).coeff d = 0 := by
  apply (mem_pow_ker_eval_iff (fun _ : ℕ => (2 : ℤ)) 2 _).mp
  have h : X (0 : ℕ) - C (2 : ℤ) ∈
      RingHom.ker (eval (fun _ : ℕ => (2 : ℤ))) := by
    simp [RingHom.mem_ker]
  simpa only [pow_two] using Ideal.mul_mem_mul h h

-- The zeroth power also works over a semiring and an empty variable type.
open MvPolynomial in
example (p : MvPolynomial Empty ℕ) :
    p ∈ RingHom.ker (eval (fun _ : Empty => ((0 : AddUnits ℕ) : ℕ))) ^ 0 := by
  apply (mem_pow_ker_eval_addUnits_iff (fun _ : Empty => (0 : AddUnits ℕ)) 0 p).mpr
  intro d hd
  exact (Nat.not_lt_zero _ hd).elim
