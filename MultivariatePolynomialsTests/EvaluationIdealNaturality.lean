/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.EvaluationIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Evaluation under polynomial substitution

These clients use a quadratic substitution between different variable types,
including an infinite or empty source and coefficients with zero divisors.
The quotient square descends only at points annihilating the target ideal.

## References

* `MultivariatePolynomials.EvaluationIdeal`: substitution and point contraction.
* Mathlib, `Mathlib.Data.ZMod.Basic` and `Mathlib.Basic.Real.Basic`: finite-ring
  and field-extension boundary examples.
-/

private noncomputable def squareFirst {R : Type*} [CommSemiring R] :
    MvPolynomial (Fin 1) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval (fun _ => MvPolynomial.X (0 : Fin 2) ^ 2)

private theorem squareChangesPoint :
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (2 : ℚ) else 3)
      (squareFirst (R := ℚ) (MvPolynomial.X (0 : Fin 1))) = 4 ∧
        (4 : ℚ) ≠ 2 := by
  norm_num [squareFirst]

private theorem semiringNonmember :
    (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℕ) ∉
      (RingHom.ker (MvPolynomial.aeval (fun _ : Fin 2 => (2 : ℕ))).toRingHom).comap
        (squareFirst (R := ℕ)).toRingHom := by
  rw [MvPolynomial.ker_aeval_comap]
  norm_num [RingHom.mem_ker, squareFirst]

private theorem squareOverZeroDivisors :
    (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (4 : ZMod 6)) ∈
      (Ideal.span (Set.range (fun i : Fin 2 =>
        (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 6)) -
          MvPolynomial.C (if i = 0 then (2 : ZMod 6) else 3)))).comap
        (squareFirst (R := ZMod 6)).toRingHom := by
  rw [MvPolynomial.ideal_span_X_sub_C_comap]
  have hx : MvPolynomial.comap (squareFirst (R := ZMod 6))
      (fun i : Fin 2 => if i = 0 then (2 : ZMod 6) else 3) (0 : Fin 1) = 4 := by
    norm_num [MvPolynomial.comap_apply, squareFirst]
  rw [← hx]
  exact Ideal.subset_span (Set.mem_range_self (0 : Fin 1))

private theorem emptySourceNonmember :
    (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin 0) ℤ) ∉
      (Ideal.span (Set.range (fun i : ℕ =>
        (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (i : ℤ)))).comap
        (MvPolynomial.aeval (fun i : Fin 0 => i.elim0) :
          MvPolynomial (Fin 0) ℤ →ₐ[ℤ] MvPolynomial ℕ ℤ).toRingHom := by
  rw [MvPolynomial.ideal_span_X_sub_C_comap]
  rw [MvPolynomial.mem_ideal_span_X_sub_C_iff]
  norm_num

private theorem infiniteSourceMember :
    (MvPolynomial.X (42 : ℕ) - MvPolynomial.C (2 : ℤ)) ∈
      (Ideal.span (Set.range (fun i : Fin 1 =>
        (MvPolynomial.X i : MvPolynomial (Fin 1) ℤ) - MvPolynomial.C (2 : ℤ)))).comap
        (MvPolynomial.rename (fun _ : ℕ => (0 : Fin 1))).toRingHom := by
  rw [MvPolynomial.ideal_span_X_sub_C_comap]
  simpa [MvPolynomial.comap_rename] using
    (Ideal.subset_span (Set.mem_range_self (42 : ℕ)) :
      (MvPolynomial.X (42 : ℕ) - MvPolynomial.C
        (MvPolynomial.comap (MvPolynomial.rename (fun _ : ℕ => (0 : Fin 1)))
          (fun _ : Fin 1 => (2 : ℤ)) 42)) ∈
        Ideal.span (Set.range (fun i : ℕ =>
          (MvPolynomial.X i : MvPolynomial ℕ ℤ) -
            MvPolynomial.C (MvPolynomial.comap
              (MvPolynomial.rename (fun _ : ℕ => (0 : Fin 1)))
                (fun _ : Fin 1 => (2 : ℤ)) i))))

private theorem zeroRingContraction (p : MvPolynomial (Fin 1) (ZMod 1)) :
    p ∈ (Ideal.span (Set.range (fun i : Fin 2 =>
      (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 1)) -
        MvPolynomial.C (0 : ZMod 1)))).comap
          (squareFirst (R := ZMod 1)).toRingHom := by
  rw [MvPolynomial.ideal_span_X_sub_C_comap]
  exact (MvPolynomial.mem_ideal_span_X_sub_C_iff _ _).2 (Subsingleton.elim _ _)

private theorem rationalToRealPoint :
    PrimeSpectrum.comap (squareFirst (R := ℚ)).toRingHom
      (MvPolynomial.pointToPoint (k := ℚ)
        (fun i : Fin 2 => if i = 0 then (2 : ℝ) else 3)) =
      MvPolynomial.pointToPoint (k := ℚ) (fun _ : Fin 1 => (4 : ℝ)) := by
  have hcoordinate :
      (fun i : Fin 1 => MvPolynomial.aeval
        (fun j : Fin 2 => if j = 0 then (2 : ℝ) else 3)
        (squareFirst (R := ℚ) (MvPolynomial.X i))) =
          (fun _ : Fin 1 => (4 : ℝ)) := by
    funext i
    norm_num [squareFirst]
  rw [← hcoordinate]
  exact MvPolynomial.pointToPoint_comap (squareFirst (R := ℚ))
    (fun i : Fin 2 => if i = 0 then (2 : ℝ) else 3)

private theorem rationalPoint :
    PrimeSpectrum.comap (squareFirst (R := ℚ)).toRingHom
      (MvPolynomial.pointToPoint (k := ℚ)
        (fun i : Fin 2 => if i = 0 then (2 : ℚ) else 3)) =
      MvPolynomial.pointToPoint (k := ℚ) (fun _ : Fin 1 => (4 : ℚ)) := by
  have hcoordinate : MvPolynomial.comap (squareFirst (R := ℚ))
      (fun i : Fin 2 => if i = 0 then (2 : ℚ) else 3) =
        (fun _ : Fin 1 => (4 : ℚ)) := by
    funext i
    rw [MvPolynomial.comap_apply]
    norm_num [squareFirst]
  rw [← hcoordinate]
  exact MvPolynomial.pointToPoint_comap_self (squareFirst (R := ℚ))
    (fun i : Fin 2 => if i = 0 then (2 : ℚ) else 3)

private theorem quotientEvaluationSquare
    {R : Type*} [CommRing R] {σ τ : Type*}
    (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R)
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (hIJ : I ≤ J.comap f.toRingHom)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
    (p : MvPolynomial σ R) :
    Ideal.Quotient.lift I ((MvPolynomial.aeval x).toRingHom.comp f.toRingHom)
        (fun _ hq => RingHom.mem_ker.mp (hJ (hIJ hq)))
        (Ideal.Quotient.mk I p) =
      Ideal.Quotient.lift J (MvPolynomial.aeval x).toRingHom
        (fun _ hq => RingHom.mem_ker.mp (hJ hq))
        (Ideal.quotientMap J f.toRingHom hIJ (Ideal.Quotient.mk I p)) := by
  simp only [Ideal.Quotient.lift_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

private theorem quadraticQuotientClient (p : MvPolynomial (Fin 1) ℚ) :
    let f := squareFirst (R := ℚ)
    let x : Fin 2 → ℚ := fun i => if i = 0 then 2 else 3
    let I := RingHom.ker (MvPolynomial.aeval
      (fun i => MvPolynomial.aeval x (f (MvPolynomial.X i)))).toRingHom
    let J := RingHom.ker (MvPolynomial.aeval x).toRingHom
    Ideal.Quotient.lift I ((MvPolynomial.aeval x).toRingHom.comp f.toRingHom)
        (fun _ hq => RingHom.mem_ker.mp
          ((show I ≤ J.comap f.toRingHom from
            (MvPolynomial.ker_aeval_comap f x).ge) hq))
        (Ideal.Quotient.mk I p) =
      Ideal.Quotient.lift J (MvPolynomial.aeval x).toRingHom
        (fun _ hq => RingHom.mem_ker.mp hq)
        (Ideal.quotientMap J f.toRingHom
          (MvPolynomial.ker_aeval_comap f x).ge (Ideal.Quotient.mk I p)) := by
  dsimp only
  exact quotientEvaluationSquare _ _ _ _ (MvPolynomial.ker_aeval_comap _ _).ge le_rfl p

/-- Without vanishing, evaluation need not descend through a polynomial quotient. -/
public theorem MultivariatePolynomialsTests.noEvaluationAtOneOnQuotientByX :
    ¬ (Ideal.span {(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ)} ≤
        RingHom.ker (MvPolynomial.aeval (fun _ : Fin 1 => (1 : ℚ))).toRingHom) := by
  intro h
  have hx := h (Ideal.subset_span (Set.mem_singleton _))
  norm_num [RingHom.mem_ker] at hx
