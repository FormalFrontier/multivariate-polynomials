/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.WeightOneNaturality

/-!
# Clients for weight-one valuation naturality

Finite and infinite variable sets, proper embeddings and the empty-source
case exercise the polynomial, fraction and residue interfaces. Failure cases
distinguish injective renaming from identifying variables and distinguish the
two directions of preservation of weighted-variable membership.
-/

@[expose] public section

open scoped WithZero

namespace MvPolynomialTests.WeightOneNaturality

open MvPolynomial

private def sourceSet : Set (Fin 2) := {0}
private def targetSet : Set (Fin 4) := {0, 2}

private def properEmbedding : Fin 2 ↪ Fin 4 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b hab := Fin.ext (by
    simpa only [Fin.val_mk] using congrArg (fun j : Fin 4 => j.val) hab)

private theorem properEmbedding_zero : properEmbedding (0 : Fin 2) = (0 : Fin 4) := rfl
private theorem properEmbedding_one : properEmbedding (1 : Fin 2) = (1 : Fin 4) := rfl

private theorem properEmbedding_weights (j : Fin 2) :
    properEmbedding j ∈ targetSet ↔ j ∈ sourceSet := by
  fin_cases j <;> simp [properEmbedding_zero, properEmbedding_one, targetSet, sourceSet]

private def largerEmbedding : Fin 4 ↪ Fin 5 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b hab := Fin.ext (by
    simpa only [Fin.val_mk] using congrArg (fun j : Fin 5 => j.val) hab)

/-- The polynomial map composes across genuinely different coefficient fields
and successive proper variable embeddings. -/
example :
    weightOnePolynomialMap
      ((algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))).comp
        (algebraMap ℚ (RatFunc ℚ))) (properEmbedding.trans largerEmbedding)
        (X (1 : Fin 2) + C (3 / 2 : ℚ)) =
      weightOnePolynomialMap (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)))
        largerEmbedding
        (weightOnePolynomialMap (algebraMap ℚ (RatFunc ℚ)) properEmbedding
          (X (1 : Fin 2) + C (3 / 2 : ℚ))) := by
  rw [weightOnePolynomialMap_comp]
  rfl

/-- The identity law holds on a nonconstant polynomial. -/
example :
    weightOnePolynomialMap (RingHom.id ℚ)
      (⟨id, Function.injective_id⟩ : Fin 2 ↪ Fin 2)
        (X 0 + C (2 : ℚ)) = X 0 + C 2 := by
  rw [weightOnePolynomialMap_id]
  rfl

private def sourcePivot : sourceSet := ⟨0, by simp [sourceSet]⟩
private def targetPivot : targetSet := ⟨0, by simp [targetSet]⟩
private def otherTargetPivot : targetSet := ⟨2, by simp [targetSet]⟩
private theorem targetPivots_ne : (targetPivot : Fin 4) ≠ otherTargetPivot := by
  decide

/-- A proper embedding sends a weighted source generator to a weighted target
generator with the same nontrivial valuation. -/
example :
    weightOneValuation (k := ℚ) targetSet targetPivot
      (weightOneFractionMap (RingHom.id ℚ) properEmbedding
        (algebraMap (MvPolynomial (Fin 2) ℚ)
          (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 0))) = WithZero.exp (-1 : ℤ) := by
  rw [weightOneValuation_map (RingHom.id ℚ) properEmbedding
    sourceSet targetSet properEmbedding_weights sourcePivot targetPivot]
  simpa [sourceSet] using
    (weightOneValuation_X (k := ℚ) sourceSet sourcePivot (0 : Fin 2))

/-- An extra weighted target variable has a ratio coordinate, although it is
not in the source variable image. -/
example : properEmbedding (0 : Fin 2) ≠ (2 : Fin 4) ∧
    weightOneValuation (k := ℚ) targetSet targetPivot
      (algebraMap (MvPolynomial (Fin 4) ℚ)
        (FractionRing (MvPolynomial (Fin 4) ℚ)) (X 2)) = WithZero.exp (-1 : ℤ) := by
  constructor
  · decide
  · simpa [targetSet] using
      (weightOneValuation_X (k := ℚ) targetSet targetPivot (2 : Fin 4))

/-- The extra unweighted target variable has value one. -/
example : properEmbedding (1 : Fin 2) ≠ (3 : Fin 4) ∧
    weightOneValuation (k := ℚ) targetSet targetPivot
      (algebraMap (MvPolynomial (Fin 4) ℚ)
        (FractionRing (MvPolynomial (Fin 4) ℚ)) (X 3)) = 1 := by
  constructor
  · decide
  · simpa [targetSet] using
      (weightOneValuation_X (k := ℚ) targetSet targetPivot (3 : Fin 4))

/-- Infinite weighted and unweighted index classes cause no finite-variable
requirement: the image of a single even variable retains weight one. -/
example :
    weightOneOrder {j : ℕ | Even j}
      (weightOnePolynomialMap (RingHom.id ℚ)
        (⟨id, Function.injective_id⟩ : ℕ ↪ ℕ) (X 2)) = 1 := by
  rw [weightOneOrder_map (RingHom.id ℚ) (RingHom.id ℚ).injective]
  simp [weightOneOrder_X]

/-- Zero retains infinite order even when both infinite index classes occur. -/
example :
    weightOneOrder {j : ℕ | Even j}
      (weightOnePolynomialMap (RingHom.id ℚ)
        (⟨id, Function.injective_id⟩ : ℕ ↪ ℕ)
          (0 : MvPolynomial ℕ ℚ)) = ⊤ := by
  simp

/-- The natural order law also applies to zero, where the finite order is zero. -/
example :
    weightOneNatOrder targetSet
      (weightOnePolynomialMap (RingHom.id ℚ) properEmbedding
        (0 : MvPolynomial (Fin 2) ℚ)) =
      weightOneNatOrder (properEmbedding ⁻¹' targetSet)
        (0 : MvPolynomial (Fin 2) ℚ) := by
  exact weightOneNatOrder_map (RingHom.id ℚ) (RingHom.id ℚ).injective
    properEmbedding targetSet 0

/-- Identity renaming acts as the identity on a genuinely nonconstant
coefficient-field residue. -/
example :
    weightOneResidueMap (RingHom.id ℚ)
      (⟨id, Function.injective_id⟩ : Fin 2 ↪ Fin 2)
      sourceSet sourceSet (fun _ => Iff.rfl) sourcePivot sourcePivot
      (IsLocalRing.residue _
        (weightOneCoefficientSection (k := ℚ) sourceSet sourcePivot
          (algebraMap (MvPolynomial
              (WeightOneCoefficientVariables sourceSet sourcePivot) ℚ)
            (WeightOneCoefficientField ℚ sourceSet sourcePivot)
              (X (Sum.inl (⟨1, by simp [sourceSet]⟩ :
                {j : Fin 2 // j ∉ sourceSet})))))) =
      IsLocalRing.residue _
        (weightOneCoefficientSection (k := ℚ) sourceSet sourcePivot
          (algebraMap (MvPolynomial
              (WeightOneCoefficientVariables sourceSet sourcePivot) ℚ)
            (WeightOneCoefficientField ℚ sourceSet sourcePivot)
              (X (Sum.inl (⟨1, by simp [sourceSet]⟩ :
                {j : Fin 2 // j ∉ sourceSet}))))) := by
  rw [weightOneResidueMap_id]
  rfl

/-- The aligned coefficient map carries a concrete source unweighted
generator to the target unweighted coefficient coordinate. -/
example :
    weightOneCoefficientFieldMap (RingHom.id ℚ) properEmbedding
      sourceSet targetSet properEmbedding_weights sourcePivot
      (algebraMap (MvPolynomial
          (WeightOneCoefficientVariables sourceSet sourcePivot) ℚ)
        (WeightOneCoefficientField ℚ sourceSet sourcePivot)
          (X (Sum.inl (⟨1, by simp [sourceSet]⟩ :
            {j : Fin 2 // j ∉ sourceSet})))) =
      algebraMap (MvPolynomial
          (WeightOneCoefficientVariables targetSet
            (weightOneAlignedPivot properEmbedding sourceSet targetSet
              properEmbedding_weights sourcePivot)) ℚ)
        (WeightOneCoefficientField ℚ targetSet
          (weightOneAlignedPivot properEmbedding sourceSet targetSet
            properEmbedding_weights sourcePivot))
          (X (Sum.inl (⟨1, by simp [targetSet]⟩ :
            {j : Fin 4 // j ∉ targetSet}))) := by
  simp [properEmbedding_one]

/-- On two distinct target pivots the extra weighted ratio transforms into
the inverse ratio, while an unweighted coordinate remains unchanged. -/
example :
    weightOneCoefficientChangePivot (l := ℚ) targetSet targetPivot otherTargetPivot
      (algebraMap (MvPolynomial (WeightOneCoefficientVariables targetSet targetPivot) ℚ)
          (WeightOneCoefficientField ℚ targetSet targetPivot)
          (X (Sum.inr (⟨otherTargetPivot, otherTargetPivot.property,
            Ne.symm targetPivots_ne⟩ :
            {j : Fin 4 // j ∈ targetSet ∧ j ≠ (targetPivot : Fin 4)}))) +
        algebraMap (MvPolynomial (WeightOneCoefficientVariables targetSet targetPivot) ℚ)
          (WeightOneCoefficientField ℚ targetSet targetPivot)
          (X (Sum.inl (⟨3, by simp [targetSet]⟩ : {j : Fin 4 // j ∉ targetSet})))) =
      (algebraMap (MvPolynomial (WeightOneCoefficientVariables targetSet otherTargetPivot) ℚ)
          (WeightOneCoefficientField ℚ targetSet otherTargetPivot)
          (X (Sum.inr (⟨targetPivot, targetPivot.property, targetPivots_ne⟩ :
            {j : Fin 4 // j ∈ targetSet ∧ j ≠ (otherTargetPivot : Fin 4)}))))⁻¹ +
        algebraMap (MvPolynomial (WeightOneCoefficientVariables targetSet otherTargetPivot) ℚ)
          (WeightOneCoefficientField ℚ targetSet otherTargetPivot)
          (X (Sum.inl (⟨3, by simp [targetSet]⟩ : {j : Fin 4 // j ∉ targetSet}))) := by
  rw [map_add, weightOneCoefficientChangePivot_ratio_pivot
    (T := targetSet) targetPivot otherTargetPivot targetPivots_ne,
    weightOneCoefficientChangePivot_unweighted]

private def emptyEmbedding : Empty ↪ Fin 4 where
  toFun := Empty.elim
  inj' a := a.elim

/-- A function field with no variables embeds into the target residue field
using only the target pivot. There is no source pivot to supply. -/
example :
    weightOneZeroResidueMap (RingHom.id ℚ) emptyEmbedding targetSet
      (fun j => j.elim) targetPivot
      (1 : FractionRing (MvPolynomial Empty ℚ)) ≠ 0 := by
  simp

/-- Reduction of an empty-variable function field transports a nonconstant
rational-function coefficient through a genuine field extension. -/
example :
    weightOneResidueEquiv targetSet targetPivot
      (weightOneZeroResidueMap
        (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))) emptyEmbedding targetSet
        (fun j => j.elim) targetPivot
        (algebraMap (MvPolynomial Empty (RatFunc ℚ))
          (FractionRing (MvPolynomial Empty (RatFunc ℚ)))
          (C (RatFunc.X : RatFunc ℚ)))) =
      algebraMap
        (MvPolynomial (WeightOneCoefficientVariables targetSet targetPivot)
          (RatFunc (RatFunc ℚ)))
        (WeightOneCoefficientField (RatFunc (RatFunc ℚ)) targetSet targetPivot)
        (C ((algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)))
          (RatFunc.X : RatFunc ℚ))) := by
  rw [weightOneZeroResidueMap_coordinates, weightOneZeroCoefficientFieldMap_C]

private def weightedXY : Set (Fin 3) := {0, 1}
private def pivotX : weightedXY := ⟨0, by simp [weightedXY]⟩

private def zEmbedding : Fin 1 ↪ Fin 3 where
  toFun _ := 2
  inj' a b _ := by fin_cases a; fin_cases b; rfl

private theorem zEmbedding_zero : zEmbedding (0 : Fin 1) = (2 : Fin 3) := rfl

private theorem zUnweighted (j : Fin 1) : zEmbedding j ∉ weightedXY := by
  fin_cases j
  simp [zEmbedding_zero, weightedXY]

private def ratioY : {j : Fin 3 // j ∈ weightedXY ∧ j ≠ (pivotX : Fin 3)} :=
  ⟨1, by simp [weightedXY, pivotX]⟩

private def unweightedZ : {j : Fin 3 // j ∉ weightedXY} :=
  ⟨2, by simp [weightedXY]⟩

/-- In target coefficient coordinates, the ratio `y/x` differs from the
source generator `z`. This detects the additional residue direction. -/
example :
    weightOneResidueEquiv (k := ℚ) weightedXY pivotX
      (IsLocalRing.residue _
        (weightOneCoefficientSection weightedXY pivotX
          (algebraMap (MvPolynomial
              (WeightOneCoefficientVariables weightedXY pivotX) ℚ)
            (WeightOneCoefficientField ℚ weightedXY pivotX)
              (X (Sum.inr ratioY))))) ≠
    weightOneResidueEquiv (k := ℚ) weightedXY pivotX
      (weightOneZeroResidueMap (RingHom.id ℚ) zEmbedding
        weightedXY zUnweighted pivotX
        (algebraMap (MvPolynomial (Fin 1) ℚ)
          (FractionRing (MvPolynomial (Fin 1) ℚ)) (X 0))) := by
  rw [weightOneResidueEquiv_section, weightOneZeroResidueMap_coordinates,
    weightOneZeroCoefficientFieldMap_X]
  have hvars : (X (Sum.inr ratioY) :
      MvPolynomial (WeightOneCoefficientVariables weightedXY pivotX) ℚ) ≠
      X (Sum.inl unweightedZ) := by
    intro heq
    have hindices := X_injective heq
    cases hindices
  exact (IsFractionRing.injective _ _).ne hvars

/-- The full target residue contains the ratio `y/x` strictly outside the
image of the source function field `ℚ(z)`. -/
example :
    (weightOneResidueEquiv (k := ℚ) weightedXY pivotX).symm
      (algebraMap (MvPolynomial
          (WeightOneCoefficientVariables weightedXY pivotX) ℚ)
        (WeightOneCoefficientField ℚ weightedXY pivotX)
          (X (Sum.inr ratioY))) ∉
      Set.range (weightOneZeroResidueMap (RingHom.id ℚ) zEmbedding
        weightedXY zUnweighted pivotX) := by
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply weightOneZeroCoefficientFieldMap_ratio_not_mem_range
    (RingHom.id ℚ) zEmbedding weightedXY zUnweighted pivotX ratioY
  refine ⟨q, ?_⟩
  rw [← weightOneZeroResidueMap_coordinates
    (RingHom.id ℚ) zEmbedding weightedXY zUnweighted pivotX q,
    hq, RingEquiv.apply_symm_apply]

/-- Identifying variables kills a nonzero polynomial in every field
characteristic, so the renaming cannot embed the function field. -/
theorem rename_identification_kills_sub {k : Type*} [Field k] :
    (X (0 : Fin 2) - X 1 : MvPolynomial (Fin 2) k) ≠ 0 ∧
      rename (fun _ : Fin 2 => (0 : Fin 1))
        (X (0 : Fin 2) - X 1 : MvPolynomial (Fin 2) k) = 0 := by
  constructor
  · intro h
    have hvars : (X (0 : Fin 2) : MvPolynomial (Fin 2) k) = X 1 := sub_eq_zero.mp h
    exact (by decide : (0 : Fin 2) ≠ 1) (X_injective hvars)
  · simp

/-- If an unweighted source variable acquires weight, its inverse is no
longer target-integral; the converse membership implication is essential. -/
example :
    algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ)) 1 /
      algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 1) ∈
          WeightOneValuationRing (k := ℚ) sourceSet sourcePivot ∧
    algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ)) 1 /
      algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 1) ∉
          WeightOneValuationRing (k := ℚ) ({1} : Set (Fin 2))
            (⟨1, by simp⟩ : ({1} : Set (Fin 2))) := by
  constructor
  · rw [weightOneValuation_mem_div_iff sourceSet sourcePivot (X_ne_zero 1)]
    simp [sourceSet, weightOneOrder_X]
  · rw [weightOneValuation_mem_div_iff ({1} : Set (Fin 2))
      (⟨1, by simp⟩ : ({1} : Set (Fin 2))) (X_ne_zero 1)]
    simp [weightOneOrder_X]

/-- A weighted source variable sent to an unweighted target variable does
not preserve the valuation, even though the target has another pivot. -/
example :
    weightOneValuation (k := ℚ) ({1} : Set (Fin 2))
      (⟨1, by simp⟩ : ({1} : Set (Fin 2)))
      (algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 0)) = 1 ∧
    weightOneValuation (k := ℚ) sourceSet sourcePivot
      (algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 0)) = WithZero.exp (-1 : ℤ) := by
  constructor
  · simpa using (weightOneValuation_X (k := ℚ) ({1} : Set (Fin 2))
      (⟨1, by simp⟩ : ({1} : Set (Fin 2))) (0 : Fin 2))
  · simpa [sourceSet] using
      (weightOneValuation_X (k := ℚ) sourceSet sourcePivot (0 : Fin 2))

end MvPolynomialTests.WeightOneNaturality
