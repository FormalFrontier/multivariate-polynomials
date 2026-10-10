/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.WeightOneValuation

/-!
# Weight-one valuation clients

Two-variable examples distinguish an unweighted coordinate from a weighted
ratio in the full residue field. The polynomial nonzero and support checks do
not depend on the valuation. A trivial valuation provides the empty-subset
boundary, and the same API also applies to an infinite variable family.
Distinct singleton subsets give inequivalent valuations, while changing the
pivot within a fixed subset leaves the valuation unchanged.

## References

* `MultivariatePolynomials.WeightOneValuation` and its cited Mathlib valuation
  and rational-function APIs.
-/

@[expose] public section

open scoped WithZero

namespace MultivariatePolynomialsTests.WeightOneValuation

open MvPolynomial

universe u

private def singletonSet : Set (Fin 2) := {(0 : Fin 2)}

private def singletonPivot : singletonSet := ⟨0, by simp [singletonSet]⟩

private def secondSingletonSet : Set (Fin 2) := {(1 : Fin 2)}

private def secondSingletonPivot : secondSingletonSet := ⟨1, by simp [secondSingletonSet]⟩

private theorem singletonSet_ne_secondSingletonSet : singletonSet ≠ secondSingletonSet := by
  intro h
  have hzero : (0 : Fin 2) ∈ secondSingletonSet := h ▸ (by simp [singletonSet])
  simpa [secondSingletonSet] using hzero

private def secondUnweighted : {j : Fin 2 // j ∉ singletonSet} :=
  ⟨1, by simp [singletonSet]⟩

private def bothSet : Set (Fin 2) := Set.univ

private def bothPivot : bothSet := ⟨0, by simp [bothSet]⟩

private def bothSecondPivot : bothSet := ⟨1, by simp [bothSet]⟩

private def secondRatio : {j : Fin 2 // j ∈ bothSet ∧ j ≠ (bothPivot : Fin 2)} :=
  ⟨1, by simp [bothSet, bothPivot]⟩

private instance : Unique (WeightOneCoefficientVariables singletonSet singletonPivot) := by
  refine ⟨⟨Sum.inl secondUnweighted⟩, ?_⟩
  intro index
  rcases index with j | j
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Fin.eq_one_of_ne_zero
    intro hj
    exact j.property (by simp [singletonSet, hj])
  · exfalso
    have hj : (j : Fin 2) = 0 := by simpa [singletonSet] using j.property.1
    exact j.property.2 (by simpa [singletonPivot] using hj)

private instance : Unique (WeightOneCoefficientVariables bothSet bothPivot) := by
  refine ⟨⟨Sum.inr secondRatio⟩, ?_⟩
  intro index
  rcases index with j | j
  · exact False.elim (j.property (by simp [bothSet]))
  · apply congrArg Sum.inr
    apply Subtype.ext
    apply Fin.eq_one_of_ne_zero
    simpa [bothPivot] using j.property.2

private noncomputable def uniqueCoefficientFieldEquiv
    {ι : Type*} [Unique ι] (k : Type u) [Field k] :
    FractionRing (MvPolynomial ι k) ≃+* RatFunc k :=
  (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing (MvPolynomial ι k)) (L := FractionRing (Polynomial k))
    (MvPolynomial.uniqueAlgEquiv k ι).toRingEquiv).trans
      (RatFunc.toFractionRingRingEquiv k).symm

private noncomputable def singletonResidueEquiv {k : Type u} [Field k] :
    IsLocalRing.ResidueField
        (weightOneValuation (k := k) singletonSet singletonPivot).valuationSubring ≃+*
      RatFunc k :=
  (weightOneResidueEquiv (k := k) singletonSet singletonPivot).trans
    (uniqueCoefficientFieldEquiv k)

private noncomputable def bothResidueEquiv {k : Type u} [Field k] :
    IsLocalRing.ResidueField
        (weightOneValuation (k := k) bothSet bothPivot).valuationSubring ≃+*
      RatFunc k :=
  (weightOneResidueEquiv (k := k) bothSet bothPivot).trans
    (uniqueCoefficientFieldEquiv k)

private theorem one_add_first_coeff_zero {k : Type u} [Field k] :
    (1 + X (0 : Fin 2) : MvPolynomial (Fin 2) k).coeff 0 = 1 := by
  classical
  simp [MvPolynomial.coeff_X]

private theorem one_add_first_ne_zero {k : Type u} [Field k] :
    (1 + X (0 : Fin 2) : MvPolynomial (Fin 2) k) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : MvPolynomial (Fin 2) k => p.coeff 0) h
  rw [one_add_first_coeff_zero] at hcoeff
  simp at hcoeff

private theorem first_sub_second_ne_zero {k : Type u} [Field k] :
    (X (0 : Fin 2) - X (1 : Fin 2) : MvPolynomial (Fin 2) k) ≠ 0 := by
  intro h
  have hvars : (X (0 : Fin 2) : MvPolynomial (Fin 2) k) = X 1 := sub_eq_zero.mp h
  have hindices := (MvPolynomial.X_injective (R := k)) hvars
  exact (by decide : (0 : Fin 2) ≠ 1) hindices

private theorem first_denominator_order {k : Type u} [Field k] :
    weightOneOrder singletonSet (1 + X (0 : Fin 2) : MvPolynomial (Fin 2) k) = 0 :=
  weightOneOrder_eq_zero_of_coeff_zero_ne_zero singletonSet
    (by rw [one_add_first_coeff_zero]; exact one_ne_zero)

private theorem first_fraction_equal_order {k : Type u} [Field k] :
    weightOneOrder singletonSet (1 : MvPolynomial (Fin 2) k) =
      weightOneOrder singletonSet (1 + X (0 : Fin 2) : MvPolynomial (Fin 2) k) := by
  simp [first_denominator_order]

private theorem first_expansion_pivot {k : Type u} [Field k] :
    weightOneExpansion singletonSet singletonPivot (X (0 : Fin 2) : MvPolynomial (Fin 2) k) =
      Polynomial.X := by
  simpa [singletonPivot] using
    (weightOneExpansion_pivot (k := k) singletonSet singletonPivot)

/-- The zero polynomial has infinite trailing degree also in the weight-one expansion. -/
example {k : Type u} [Field k] :
    (weightOneExpansion singletonSet singletonPivot
      (0 : MvPolynomial (Fin 2) k)).trailingDegree = ⊤ := by
  rw [weightOneExpansion_trailingDegree]
  simp

/-- Distinct variable monomials do not cancel, in any field characteristic. -/
theorem first_sub_second_support {k : Type u} [Field k] :
    (X (0 : Fin 2) - X (1 : Fin 2) : MvPolynomial (Fin 2) k).support =
      {Finsupp.single 0 1, Finsupp.single 1 1} := by
  classical
  have hdistinct : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠
      Finsupp.single 1 1 := by
    intro h
    have hcoeff := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    simp at hcoeff
  ext exponent
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_X, Finset.mem_insert, Finset.mem_singleton]
  by_cases hfirst : Finsupp.single (0 : Fin 2) 1 = exponent
  · have hsecond : Finsupp.single (1 : Fin 2) 1 ≠ exponent := by
      rw [← hfirst]
      exact hdistinct.symm
    simp [hfirst, hsecond]
  · by_cases hsecond : Finsupp.single (1 : Fin 2) 1 = exponent
    · simp [hfirst, hsecond]
    · have hfirst' : exponent ≠ Finsupp.single 0 1 := Ne.symm hfirst
      have hsecond' : exponent ≠ Finsupp.single 1 1 := Ne.symm hsecond
      simp [hfirst, hsecond, hfirst', hsecond']

private theorem first_sub_second_order {k : Type u} [Field k] :
    weightOneOrder bothSet
      (X (0 : Fin 2) - X (1 : Fin 2) : MvPolynomial (Fin 2) k) = 1 := by
  classical
  simp [weightOneOrder, first_sub_second_support, Finsupp.weight_single, bothSet]

/-- One weighted and one unweighted variable have values `exp (-1)` and `1`. -/
example {k : Type u} [Field k] :
    weightOneValuation singletonSet singletonPivot
        (algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
          (X (0 : Fin 2))) = WithZero.exp (-1 : ℤ) ∧
    weightOneValuation singletonSet singletonPivot
        (algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
          (X (1 : Fin 2))) = 1 := by
  constructor <;> rw [weightOneValuation_X] <;> simp [singletonSet]

/-- The same generator is below one for one singleton subset, but not for the other. -/
example :
    weightOneValuation (k := ℚ) singletonSet singletonPivot
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (X (0 : Fin 2))) < 1 ∧
    ¬ weightOneValuation (k := ℚ) secondSingletonSet secondSingletonPivot
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (X (0 : Fin 2))) < 1 := by
  constructor <;> rw [weightOneValuation_X_lt_one_iff] <;>
    simp [singletonSet, secondSingletonSet]

/-- Distinct singleton subsets give unequal and inequivalent valuations over `ℚ`. -/
example :
    weightOneValuation (k := ℚ) singletonSet singletonPivot ≠
      weightOneValuation (k := ℚ) secondSingletonSet secondSingletonPivot ∧
    ¬ (weightOneValuation (k := ℚ) singletonSet singletonPivot).IsEquiv
      (weightOneValuation (k := ℚ) secondSingletonSet secondSingletonPivot) := by
  constructor
  · intro h
    exact singletonSet_ne_secondSingletonSet
      ((weightOneValuation_eq_iff (k := ℚ) singletonSet secondSingletonSet
        singletonPivot secondSingletonPivot).1 h)
  · rw [weightOneValuation_isEquiv_iff]
    exact singletonSet_ne_secondSingletonSet

/-- Weighting both variables gives equal and equivalent valuations for pivots zero and one. -/
example :
    bothPivot ≠ bothSecondPivot ∧
    weightOneValuation (k := ℚ) bothSet bothPivot =
      weightOneValuation (k := ℚ) bothSet bothSecondPivot ∧
    (weightOneValuation (k := ℚ) bothSet bothPivot).IsEquiv
      (weightOneValuation (k := ℚ) bothSet bothSecondPivot) := by
  refine ⟨?_, (weightOneValuation_eq_iff bothSet bothSet bothPivot bothSecondPivot).2 rfl,
    (weightOneValuation_isEquiv_iff bothSet bothSet bothPivot bothSecondPivot).2 rfl⟩
  intro h
  have hindices := congrArg (fun i : bothSet => (i : Fin 2)) h
  simpa [bothPivot, bothSecondPivot] using hindices

/-- The full residue of one weighted variable is `k(T₁)`. -/
example {k : Type u} [Field k] :
    ∃ residueClass : IsLocalRing.ResidueField
        (weightOneValuation (k := k) singletonSet singletonPivot).valuationSubring,
      singletonResidueEquiv residueClass = RatFunc.X :=
  (singletonResidueEquiv (k := k)).surjective RatFunc.X

/-- The full residue field contains the unweighted second variable, not only constants. -/
example {k : Type u} [Field k] :
    weightOneResidueEquiv (k := k) singletonSet singletonPivot
        (IsLocalRing.residue _
          (weightOneCoefficientSection (k := k) singletonSet singletonPivot
            (algebraMap
              (MvPolynomial (WeightOneCoefficientVariables singletonSet singletonPivot) k)
              (WeightOneCoefficientField k singletonSet singletonPivot)
              (X (Sum.inl secondUnweighted))))) =
      algebraMap
        (MvPolynomial (WeightOneCoefficientVariables singletonSet singletonPivot) k)
        (WeightOneCoefficientField k singletonSet singletonPivot)
        (X (Sum.inl secondUnweighted)) := by
  exact weightOneResidueEquiv_unweighted singletonSet singletonPivot secondUnweighted

/-- A fraction tending to one at the weighted origin has residue one. -/
example {k : Type u} [Field k] :
    weightOneResidueEquiv singletonSet singletonPivot
        (IsLocalRing.residue _
          (weightOneIntegralFraction singletonSet singletonPivot
            (1 : MvPolynomial (Fin 2) k) (1 + X 0)
            one_add_first_ne_zero (le_of_eq first_fraction_equal_order.symm))) = 1 := by
  rw [weightOneResidueEquiv_div singletonSet singletonPivot one_add_first_ne_zero
    first_fraction_equal_order]
  simp [weightOneInitial, weightOneNatOrder, first_denominator_order,
    first_expansion_pivot]

/-- Both weighted variables have value `exp (-1)`, even in characteristic two. -/
example {k : Type u} [Field k] :
    weightOneValuation bothSet bothPivot
        (algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
          (X (0 : Fin 2) - X (1 : Fin 2))) = WithZero.exp (-1 : ℤ) := by
  rw [weightOneValuation_polynomial bothSet bothPivot first_sub_second_ne_zero]
  simp [weightOneNatOrder, first_sub_second_order]

/-- With two weighted variables the full residue is `k(T₁/T₀)`. -/
example {k : Type u} [Field k] :
    ∃ residueClass : IsLocalRing.ResidueField
        (weightOneValuation (k := k) bothSet bothPivot).valuationSubring,
      bothResidueEquiv residueClass = RatFunc.X :=
  (bothResidueEquiv (k := k)).surjective RatFunc.X

/-- The original fraction `T₁/T₀` is the coefficient-field ratio coordinate. -/
example {k : Type u} [Field k] :
    weightOneCoordinates (k := k) bothSet bothPivot
        (algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
          (X (1 : Fin 2)) /
          algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
            (X (0 : Fin 2))) =
      RatFunc.C
        (algebraMap (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
          (WeightOneCoefficientField k bothSet bothPivot) (X (Sum.inr secondRatio))) := by
  change weightOneCoordinates (k := k) bothSet bothPivot
    (algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
      (X (secondRatio : Fin 2)) /
      algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
        (X (bothPivot : Fin 2))) =
    RatFunc.C
      (algebraMap (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
        (WeightOneCoefficientField k bothSet bothPivot) (X (Sum.inr secondRatio)))
  rw [← weightOneCoordinates_symm_ratio (k := k) bothSet bothPivot secondRatio]
  exact (weightOneCoordinates (k := k) bothSet bothPivot).apply_symm_apply _

private theorem ratio_not_scalar {k : Type u} [Field k] (a : k) :
    algebraMap
        (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
        (WeightOneCoefficientField k bothSet bothPivot)
        (X (Sum.inr secondRatio)) ≠
      algebraMap k (WeightOneCoefficientField k bothSet bothPivot) a := by
  intro h
  have hpoly : (X (Sum.inr secondRatio) :
      MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k) = C a := by
    apply IsFractionRing.injective
      (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
      (WeightOneCoefficientField k bothSet bothPivot)
    calc
      algebraMap (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
          (WeightOneCoefficientField k bothSet bothPivot) (X (Sum.inr secondRatio)) =
        algebraMap k (WeightOneCoefficientField k bothSet bothPivot) a := h
      _ = algebraMap (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
          (WeightOneCoefficientField k bothSet bothPivot) (C a) := by
        simpa only [MvPolynomial.algebraMap_eq] using
          (IsScalarTower.algebraMap_apply k
            (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
            (WeightOneCoefficientField k bothSet bothPivot) a)
  have hcoeff := congrArg
    (fun p : MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k =>
      p.coeff (Finsupp.single (Sum.inr secondRatio) 1)) hpoly
  classical
  have hsingle : (Finsupp.single (Sum.inr secondRatio) (1 : ℕ) :
      WeightOneCoefficientVariables bothSet bothPivot →₀ ℕ) ≠ 0 := by simp
  rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_C_of_ne_zero hsingle] at hcoeff
  exact one_ne_zero hcoeff

/-- The residue of the original ratio is a transcendental generator, not a constant. -/
example {k : Type u} [Field k] (a : k) :
    weightOneResidueEquiv (k := k) bothSet bothPivot
      (IsLocalRing.residue _
        (weightOneCoefficientSection (k := k) bothSet bothPivot
          (algebraMap (MvPolynomial (WeightOneCoefficientVariables bothSet bothPivot) k)
            (WeightOneCoefficientField k bothSet bothPivot) (X (Sum.inr secondRatio))))) ≠
      algebraMap k (WeightOneCoefficientField k bothSet bothPivot) a := by
  rw [weightOneResidueEquiv_ratio]
  exact ratio_not_scalar a

open scoped Classical in
/-- Without a pivot the empty-set boundary uses Mathlib's trivial valuation. -/
example {k : Type u} [Field k] {σ : Type*}
    (x : FractionRing (MvPolynomial σ k)) :
    x ∈ (1 : Valuation (FractionRing (MvPolynomial σ k)) ℤᵐ⁰).valuationSubring := by
  classical
  exact (Valuation.mem_valuationSubring_iff _ _).2
    (Valuation.one_apply_le_one (Γ₀ := ℤᵐ⁰) x)

open scoped Classical in
/-- The empty-set valuation ring is the entire rational function field. -/
example {k : Type u} [Field k] {σ : Type*} :
    (1 : Valuation (FractionRing (MvPolynomial σ k)) ℤᵐ⁰).valuationSubring = ⊤ := by
  classical
  ext x
  simp only [ValuationSubring.mem_top]
  exact ⟨fun _ => trivial, fun _ => Valuation.one_apply_le_one (Γ₀ := ℤᵐ⁰) x⟩

open scoped Classical in
/-- The residue field of the empty-set valuation is the original function field. -/
private noncomputable def emptyResidueEquiv {k : Type u} [Field k] {σ : Type*} :
    IsLocalRing.ResidueField
        (1 : Valuation (FractionRing (MvPolynomial σ k)) ℤᵐ⁰).valuationSubring ≃+*
      FractionRing (MvPolynomial σ k) := by
  let K := FractionRing (MvPolynomial σ k)
  let V := (1 : Valuation K ℤᵐ⁰).valuationSubring
  have htop : V = ⊤ := by
    ext x
    simp only [ValuationSubring.mem_top]
    exact ⟨fun _ => trivial, fun _ => Valuation.one_apply_le_one (Γ₀ := ℤᵐ⁰) x⟩
  have hmax : IsLocalRing.maximalIdeal V = ⊥ := by
    rw [htop]
    exact IsLocalRing.maximalIdeal_eq_bot
  have hsubring : V.toSubring = (⊤ : Subring K) := by rw [htop]; rfl
  exact (Ideal.quotEquivOfEq hmax).trans
    ((RingEquiv.quotientBot V).trans
      ((RingEquiv.subringCongr hsubring).trans (Subring.topEquiv)))

open scoped Classical in
/-- Every element is the residue of an element of the trivial valuation ring. -/
example {k : Type u} [Field k] {σ : Type*}
    (x : FractionRing (MvPolynomial σ k)) :
    ∃ residueClass : IsLocalRing.ResidueField
        (1 : Valuation (FractionRing (MvPolynomial σ k)) ℤᵐ⁰).valuationSubring,
      emptyResidueEquiv residueClass = x :=
  (emptyResidueEquiv (k := k) (σ := σ)).surjective x

/-- With no variables, the function field is just the coefficient field. -/
example {k : Type u} [Field k] (a : k) :
    (IsFractionRing.ringEquivOfRingEquiv
      (MvPolynomial.isEmptyRingEquiv k Empty) :
        FractionRing (MvPolynomial Empty k) ≃+* k)
      (algebraMap (MvPolynomial Empty k) (FractionRing (MvPolynomial Empty k)) (C a)) =
      a := by
  simp

/-- Neither finiteness of the variable type nor finiteness of `S` is required. -/
example {k : Type u} [Field k] :
    weightOneValuation (k := k) ({n : ℕ | n % 2 = 0} : Set ℕ)
      ⟨0, by simp⟩
      (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k)) (X 2)) =
      WithZero.exp (-1 : ℤ) := by
  rw [weightOneValuation_X]
  simp

/-- The universal subset of infinitely many variables has pivot-independent valuation. -/
example {k : Type u} [Field k] :
    weightOneValuation (k := k) (Set.univ : Set ℕ) ⟨0, Set.mem_univ 0⟩ =
      weightOneValuation (k := k) (Set.univ : Set ℕ) ⟨1, Set.mem_univ 1⟩ := by
  exact (weightOneValuation_eq_iff (Set.univ : Set ℕ) Set.univ
    ⟨0, Set.mem_univ 0⟩ ⟨1, Set.mem_univ 1⟩).2 rfl

end MultivariatePolynomialsTests.WeightOneValuation
