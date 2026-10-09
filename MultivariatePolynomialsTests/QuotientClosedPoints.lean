/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.QuotientClosedPoints

/-!
# Boundary examples for closed points of polynomial quotients

These ordinary-import clients use the standalone closed-point maps and the
coordinate equivalence. They include rational coefficients with infinitely many
variables, the unit quotient, the empty variable type and a nonreduced quotient
whose closed-point coordinates satisfy a square-zero equation.
-/

@[expose] public section

noncomputable section

namespace MultivariatePolynomialsTests

universe u

variable (K : Type u) [Field K]

private theorem fieldOnlyCoordinateDifference {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) (a : MvPolynomial.zeroLocus K I) (s : σ) :
    (Ideal.Quotient.mkₐ K I (MvPolynomial.X s - MvPolynomial.C (a.val s))) ∈
      (MvPolynomial.zeroLocusClosedPoint I a).val.asIdeal := by
  rw [MvPolynomial.zeroLocusClosedPoint_mem_iff]
  simp

private def rationalInfiniteZero : MvPolynomial.zeroLocus ℚ
    (⊥ : Ideal (MvPolynomial ℕ ℚ)) :=
  ⟨fun _ => 0, by simp⟩

private theorem rationalInfiniteVariableVanishes (s : ℕ) :
    (Ideal.Quotient.mkₐ ℚ (⊥ : Ideal (MvPolynomial ℕ ℚ)) (MvPolynomial.X s)) ∈
      (MvPolynomial.zeroLocusClosedPoint _ rationalInfiniteZero).val.asIdeal := by
  rw [MvPolynomial.zeroLocusClosedPoint_mem_iff]
  simp [rationalInfiniteZero]

private theorem rationalInfiniteVariableInKernel (s : ℕ) :
    (Ideal.Quotient.mkₐ ℚ (⊥ : Ideal (MvPolynomial ℕ ℚ)) (MvPolynomial.X s)) ∈
      RingHom.ker (MvPolynomial.zeroLocusQuotientEval
        (⊥ : Ideal (MvPolynomial ℕ ℚ)) rationalInfiniteZero).toRingHom := by
  rw [← MvPolynomial.zeroLocusClosedPoint_asIdeal]
  exact rationalInfiniteVariableVanishes s

private def zeroTuple : MvPolynomial.zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) K)) :=
  ⟨fun _ => 0, by simp⟩

private def oneTuple : MvPolynomial.zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) K)) :=
  ⟨fun _ => 1, by simp⟩

private theorem zeroTuple_ne_oneTuple : zeroTuple K ≠ oneTuple K := by
  intro h
  exact zero_ne_one (congrFun (congrArg Subtype.val h) 0)

theorem distinctClosedPoints [IsAlgClosed K] :
    ∃ x y : closedPoints (PrimeSpectrum
        (MvPolynomial (Fin 1) K ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) K)))),
      x ≠ y := by
  refine ⟨MvPolynomial.zeroLocusEquivClosedPoints _ (zeroTuple K),
    MvPolynomial.zeroLocusEquivClosedPoints _ (oneTuple K), ?_⟩
  intro h
  apply zeroTuple_ne_oneTuple K
  exact (MvPolynomial.zeroLocusEquivClosedPoints
    (⊥ : Ideal (MvPolynomial (Fin 1) K))).injective h

private theorem zeroTupleStandaloneRoundTrip [IsAlgClosed K] :
    MvPolynomial.closedPointZeroLocus _
      (MvPolynomial.zeroLocusClosedPoint _ (zeroTuple K)) = zeroTuple K := by
  rw [← MvPolynomial.zeroLocusEquivClosedPoints_apply,
    ← MvPolynomial.zeroLocusEquivClosedPoints_symm_apply]
  exact MvPolynomial.zeroLocusEquivClosedPoints_symm_apply_apply _ (zeroTuple K)

private theorem zeroTupleInverseCoordinate [IsAlgClosed K] :
    (MvPolynomial.closedPointZeroLocus _
      (MvPolynomial.zeroLocusClosedPoint _ (zeroTuple K))).val 0 = 0 := by
  apply (MvPolynomial.closedPointZeroLocus_coordinate _ _ 0 0).2
  rw [MvPolynomial.zeroLocusClosedPoint_mem_iff]
  simp [zeroTuple]

private theorem noZerosOfUnitIdeal {σ : Type*} :
    IsEmpty (MvPolynomial.zeroLocus K (⊤ : Ideal (MvPolynomial σ K))) := by
  constructor
  intro a
  have h := a.property (1 : MvPolynomial σ K) (by simp)
  simp at h

private theorem noClosedPointsOfUnitIdeal [IsAlgClosed K] {σ : Type*} [Finite σ] :
    IsEmpty (closedPoints (PrimeSpectrum
      (MvPolynomial σ K ⧸ (⊤ : Ideal (MvPolynomial σ K))))) := by
  constructor
  intro x
  exact (noZerosOfUnitIdeal K).false
    ((MvPolynomial.zeroLocusEquivClosedPoints
      (⊤ : Ideal (MvPolynomial σ K))).symm x)

private def emptyTuple : MvPolynomial.zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 0) K)) :=
  ⟨fun s => s.elim0, by simp⟩

private theorem emptyTuple_unique
    (a : MvPolynomial.zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 0) K))) :
    a = emptyTuple K := by
  apply Subtype.ext
  funext s
  exact s.elim0

private theorem uniqueEmptyCoordinateClosedPoint [IsAlgClosed K] :
    ∃! _ : closedPoints (PrimeSpectrum
        (MvPolynomial (Fin 0) K ⧸ (⊥ : Ideal (MvPolynomial (Fin 0) K)))),
      True := by
  let e := MvPolynomial.zeroLocusEquivClosedPoints
    (⊥ : Ideal (MvPolynomial (Fin 0) K))
  refine ⟨e (emptyTuple K), trivial, ?_⟩
  intro x _
  calc
    x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = e (emptyTuple K) := congrArg e (emptyTuple_unique K (e.symm x))

private def squareZeroTuple : MvPolynomial.zeroLocus K (Ideal.span
    {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)}) :=
  ⟨fun _ => 0, by
    rw [MvPolynomial.zeroLocus_span]
    simp⟩

private theorem squareZeroCoordinate
    (a : MvPolynomial.zeroLocus K (Ideal.span
      {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)})) :
    a.val 0 = 0 := by
  have hp : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2 ∈
      Ideal.span {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)} :=
    Ideal.subset_span (Set.mem_singleton _)
  have hsq : (a.val 0) ^ 2 = 0 := by
    simpa only [map_pow, MvPolynomial.aeval_X] using a.property _ hp
  exact eq_zero_of_pow_eq_zero hsq

private theorem nonreducedClosedPoint [IsAlgClosed K] :
    ∃ x : closedPoints (PrimeSpectrum (MvPolynomial (Fin 1) K ⧸ Ideal.span
      {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)})),
      ((MvPolynomial.zeroLocusEquivClosedPoints (Ideal.span
        {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)})).symm x).val 0 = 0 := by
  refine ⟨MvPolynomial.zeroLocusEquivClosedPoints _ (squareZeroTuple K), ?_⟩
  rw [MvPolynomial.zeroLocusEquivClosedPoints_symm_apply_apply]
  exact squareZeroCoordinate K (squareZeroTuple K)

private theorem squareZeroClosedPrimeCoordinate [IsAlgClosed K]
    (x : closedPoints (PrimeSpectrum (MvPolynomial (Fin 1) K ⧸ Ideal.span
      {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)}))) :
    (MvPolynomial.closedPointZeroLocus _ x).val 0 = 0 := by
  have hp : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2 ∈
      Ideal.span {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)} :=
    Ideal.subset_span (Set.mem_singleton _)
  have hmem : (Ideal.Quotient.mkₐ K _
      ((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)) ∈ x.val.asIdeal := by
    rw [show Ideal.Quotient.mkₐ K _
      ((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    exact (x.val.asIdeal).zero_mem
  have hsq := (MvPolynomial.closedPointZeroLocus_mem_iff _ x _).mp hmem
  exact eq_zero_of_pow_eq_zero (by simpa only [map_pow, MvPolynomial.aeval_X] using hsq)

private theorem squareZeroClosedPrimeVariable [IsAlgClosed K]
    (x : closedPoints (PrimeSpectrum (MvPolynomial (Fin 1) K ⧸ Ideal.span
      {((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2)}))) :
    (Ideal.Quotient.mkₐ K _ (MvPolynomial.X (0 : Fin 1))) ∈ x.val.asIdeal := by
  have h := (MvPolynomial.closedPointZeroLocus_coordinate _ x 0 0).mp
    (squareZeroClosedPrimeCoordinate K x)
  simpa using h

end MultivariatePolynomialsTests
