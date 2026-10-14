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

universe u v

/-- The all-variable ideal is the kernel of evaluation at zero, with no ring or
nontriviality assumption on the coefficients. -/
private theorem idealOfVars_eq_ker_aeval_zero
    {σ : Type u} {R : Type v} [CommSemiring R] :
    MvPolynomial.idealOfVars σ R =
      RingHom.ker (MvPolynomial.aeval (fun _ : σ => (0 : R))).toRingHom := by
  ext p
  rw [RingHom.mem_ker]
  simpa [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq,
    Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using
    (MvPolynomial.mem_pow_idealOfVars_iff' 1 p)

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
    rw [idealOfVars_eq_ker_aeval_zero (σ := Fin 1) (R := ℤ),
      idealOfVars_eq_ker_aeval_zero (σ := ℕ) (R := ℤ)]
    simpa only [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_rename,
      MvPolynomial.constantCoeff_X, map_zero] using
      (MvPolynomial.ker_aeval_comap
        (MvPolynomial.rename (R := ℤ) (fun _ : ℕ => (0 : Fin 1)))
        (fun _ : Fin 1 => (0 : ℤ)))
  refine ⟨MvPolynomial.idealOfVars_fg (Fin 1) ℤ, hcomap, ?_⟩
  rw [hcomap]
  exact MvPolynomial.idealOfVars_not_fg ℤ ℕ
