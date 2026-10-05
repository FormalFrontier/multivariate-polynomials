/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Weight-one valuations of multivariate function fields

For a subset `S` of the variables, the minimum number of variables from `S` in
a monomial determines an order on multivariate polynomials. Choosing a pivot in
`S` gives birational coordinates: the pivot becomes the uniformizing variable,
the other variables in `S` become multiples of that variable by independent
ratios, and variables outside `S` become coefficient variables. The resulting
valuation on the fraction field has residue field the rational function field
in all the coefficient variables and ratios.

The coordinate change compares this valuation with Mathlib's `X`-adic
valuation on `RatFunc`; the order uses a *minimum*, unlike
`MvPolynomial.weightedTotalDegree`.

## Scope

A pivot requires `S` to be nonempty. For `S = ∅`, Mathlib's trivial valuation
has the entire function field as its valuation ring and residue field. The
coefficient ring is a field here; extending the construction to an integral
domain calls for a separate comparison with its fraction field.

## References

* Stefan Schröer, *A simple proof for Hochster's Theorem*,
  arXiv:2606.20016v1, §2: the
  specialization-valuation strategy, including Schröer's attribution to
  Y. Ershov. The uniformizer-ratio orientation and rational-fraction residue
  arguments here use independent corrections to that presentation.
* Mathlib contributors, `Polynomial.idealX`, `RatFunc.valuation_surjective`,
  `Valuation.comap`, `Valuation.valuationSubring`,
  `MvPolynomial.sumAlgEquiv`, `MvPolynomial.optionEquivLeft`,
  `IsFractionRing.ringEquivOfRingEquiv`, and local-ring residue APIs.
-/

@[expose] public section

open scoped WithZero

universe u v

namespace MvPolynomial

variable {σ : Type v}

/-- The unweighted variables and the ratios of weighted variables to a chosen pivot. -/
abbrev WeightOneCoefficientVariables (S : Set σ) (i : S) :=
  {j : σ // j ∉ S} ⊕ {j : σ // j ∈ S ∧ j ≠ (i : σ)}

/-- The rational function field in the unweighted variables and pivot ratios. -/
abbrev WeightOneCoefficientField (k : Type u) [Field k] (S : Set σ) (i : S) :=
  FractionRing (MvPolynomial (WeightOneCoefficientVariables S i) k)

section Order

variable {R : Type u} [CommSemiring R]

open scoped Classical in
/-- The least `S`-weight of a monomial of `p`, or `⊤` if `p = 0`. -/
noncomputable def weightOneOrder (S : Set σ) (p : MvPolynomial σ R) : ℕ∞ :=
  p.support.inf fun exponent =>
    (Finsupp.weight (fun j => if j ∈ S then (1 : ℕ) else 0) exponent : ℕ∞)

/-- The finite order of a nonzero polynomial, with the convention that zero maps to zero. -/
noncomputable def weightOneNatOrder (S : Set σ) (p : MvPolynomial σ R) : ℕ :=
  (weightOneOrder S p).toNat

@[simp] theorem weightOneOrder_zero (S : Set σ) :
    weightOneOrder S (0 : MvPolynomial σ R) = ⊤ := by
  simp [weightOneOrder]

@[simp] theorem weightOneNatOrder_zero (S : Set σ) :
    weightOneNatOrder S (0 : MvPolynomial σ R) = 0 := by
  simp [weightOneNatOrder]

/-- A nonzero constant coefficient forces minimum subset weight zero. -/
theorem weightOneOrder_eq_zero_of_coeff_zero_ne_zero (S : Set σ)
    {p : MvPolynomial σ R} (hp : p.coeff 0 ≠ 0) : weightOneOrder S p = 0 := by
  classical
  have hmem : (0 : σ →₀ ℕ) ∈ p.support := MvPolynomial.mem_support_iff.mpr hp
  apply le_antisymm
  · simpa [weightOneOrder] using
      (Finset.inf_le (f := fun exponent : σ →₀ ℕ =>
        (Finsupp.weight (fun j => if j ∈ S then (1 : ℕ) else 0) exponent : ℕ∞)) hmem)
  · exact bot_le

@[simp] theorem weightOneOrder_one [Nontrivial R] (S : Set σ) :
    weightOneOrder S (1 : MvPolynomial σ R) = 0 := by
  apply weightOneOrder_eq_zero_of_coeff_zero_ne_zero
  simp

/-- Finite weight-one order characterizes nonzero polynomials. -/
theorem weightOneOrder_eq_top (S : Set σ) (p : MvPolynomial σ R) :
    weightOneOrder S p = ⊤ ↔ p = 0 := by
  classical
  constructor
  · intro h
    by_contra hp
    have hne : p.support.Nonempty := by
      by_contra hempty
      exact hp (MvPolynomial.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hempty))
    obtain ⟨exponent, hmem⟩ := hne
    have hle : weightOneOrder S p ≤
        (Finsupp.weight (fun j => if j ∈ S then (1 : ℕ) else 0) exponent : ℕ∞) := by
      exact Finset.inf_le hmem
    rw [h] at hle
    simp at hle
  · rintro rfl
    simp

/-- The natural-number order agrees with the extended order away from zero. -/
theorem weightOneOrder_eq_natOrder (S : Set σ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    weightOneOrder S p = (weightOneNatOrder S p : ℕ∞) := by
  exact (ENat.natCast_toNat (mt (weightOneOrder_eq_top S p).mp hp)).symm

open scoped Classical in
/-- A variable has order one exactly when it belongs to `S`. -/
theorem weightOneOrder_X [Nontrivial R] (S : Set σ) (j : σ) :
    weightOneOrder S (X j : MvPolynomial σ R) = if j ∈ S then 1 else 0 := by
  classical
  simp [weightOneOrder, MvPolynomial.support_X, Finsupp.weight_single]

end Order

section Field

variable {k : Type u} [Field k] (S : Set σ) (i : S)

local notation "P" => MvPolynomial σ k
local notation "K" => FractionRing P
local notation "Cw" => WeightOneCoefficientField k S i
local notation "Aw" => MvPolynomial (WeightOneCoefficientVariables S i) k

private noncomputable def weightOneIndexEquiv :
    σ ≃ Option (WeightOneCoefficientVariables S i) := by
  classical
  refine {
    toFun := fun index =>
      if equal : index = (i : σ) then none
      else if member : index ∈ S then some (Sum.inr ⟨index, member, equal⟩)
      else some (Sum.inl ⟨index, member⟩)
    invFun := fun
      | none => (i : σ)
      | some (.inl index) => (index : σ)
      | some (.inr index) => (index : σ)
    left_inv := ?_
    right_inv := ?_ }
  · intro index
    by_cases equal : index = (i : σ)
    · simp [equal]
    · by_cases member : index ∈ S <;> simp [equal, member]
  · intro index
    rcases index with _ | (index | index)
    · simp
    · have unequal : (index : σ) ≠ (i : σ) :=
        fun equal => index.property (equal ▸ i.property)
      simp [unequal, index.property]
    · simp [index.property.1, index.property.2]

private noncomputable def weightOneOtherWeight (index : σ) : ℕ := by
  classical
  exact if index ∈ S ∧ index ≠ (i : σ) then 1 else 0

private noncomputable def weightOneExponentMap :
    (σ →₀ ℕ) →+ (Option (WeightOneCoefficientVariables S i) →₀ ℕ) where
  toFun exponent :=
    Finsupp.mapDomain (weightOneIndexEquiv S i) exponent +
      Finsupp.single none (Finsupp.weight (weightOneOtherWeight S i) exponent)
  map_zero' := by
    classical
    simp
  map_add' left right := by
    classical
    simp only [Finsupp.mapDomain_add, map_add, Finsupp.single_add]
    ac_rfl

private theorem weightOneExponentMap_injective :
    Function.Injective (weightOneExponentMap S i) := by
  classical
  intro left right hmap
  have hother (index : σ) (unequal : index ≠ (i : σ)) : left index = right index := by
    have hsome : weightOneIndexEquiv S i index ≠ none := by
      by_cases hmember : index ∈ S <;>
        simp [weightOneIndexEquiv, unequal, hmember]
    have heq := congrArg (fun exponents : Option (WeightOneCoefficientVariables S i) →₀ ℕ =>
      exponents (weightOneIndexEquiv S i index)) hmap
    simpa [weightOneExponentMap, hsome,
      Finsupp.mapDomain_apply_of_injective (weightOneIndexEquiv S i).injective] using heq
  let supportUnion := left.support ∪ right.support
  have hleft : Finsupp.weight (weightOneOtherWeight S i) left =
      supportUnion.sum (fun index => left index • weightOneOtherWeight S i index) := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_subset Finset.subset_union_left
    intro index _ hnot
    simp [Finsupp.notMem_support_iff.mp hnot]
  have hright : Finsupp.weight (weightOneOtherWeight S i) right =
      supportUnion.sum (fun index => right index • weightOneOtherWeight S i index) := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_subset Finset.subset_union_right
    intro index _ hnot
    simp [Finsupp.notMem_support_iff.mp hnot]
  have hweight : Finsupp.weight (weightOneOtherWeight S i) left =
      Finsupp.weight (weightOneOtherWeight S i) right := by
    rw [hleft, hright]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hpivot : index = (i : σ)
    · simp [weightOneOtherWeight, hpivot]
    · rw [hother index hpivot]
  have hpivot : left (i : σ) = right (i : σ) := by
    have hindex : weightOneIndexEquiv S i (i : σ) = none := by
      simp [weightOneIndexEquiv]
    have heq := congrArg
      (fun exponents : Option (WeightOneCoefficientVariables S i) →₀ ℕ => exponents none) hmap
    simpa [weightOneExponentMap, ← hindex,
      Finsupp.mapDomain_apply_of_injective (weightOneIndexEquiv S i).injective,
      hweight] using heq
  apply Finsupp.ext
  intro index
  by_cases equal : index = (i : σ)
  · simpa [equal] using hpivot
  · exact hother index equal

/-- Substitute the pivot by `X`, other weighted variables by `X` times their
ratio, and unweighted variables by coefficient-field generators. -/
noncomputable def weightOneExpansion : P →+* Polynomial Cw := by
  classical
  exact (aeval fun j : σ =>
    if h : j = (i : σ) then Polynomial.X
    else if hS : j ∈ S then
      Polynomial.X * Polynomial.C (algebraMap Aw Cw (X (Sum.inr ⟨j, hS, h⟩)))
    else Polynomial.C (algebraMap Aw Cw (X (Sum.inl ⟨j, hS⟩)))).toRingHom

@[simp] theorem weightOneExpansion_C (a : k) :
    weightOneExpansion S i (C a) = Polynomial.C (algebraMap k Cw a) := by
  simp [weightOneExpansion, IsScalarTower.algebraMap_eq k Cw (Polynomial Cw)]

@[simp] theorem weightOneExpansion_pivot :
    weightOneExpansion S i (X (i : σ) : P) = Polynomial.X := by
  simp [weightOneExpansion]

@[simp] theorem weightOneExpansion_unweighted (j : {j : σ // j ∉ S}) :
    weightOneExpansion S i (X (j : σ)) =
      Polynomial.C (algebraMap Aw Cw (X (Sum.inl j))) := by
  have hj : (j : σ) ≠ (i : σ) := fun h => j.property (h ▸ i.property)
  simp [weightOneExpansion, hj, j.property]

@[simp] theorem weightOneExpansion_weighted
    (j : {j : σ // j ∈ S ∧ j ≠ (i : σ)}) :
    weightOneExpansion S i (X (j : σ)) =
      Polynomial.X * Polynomial.C (algebraMap Aw Cw (X (Sum.inr j))) := by
  have hj : (j : σ) ≠ (i : σ) := j.property.2
  simp [weightOneExpansion, hj, j.property.1]

private noncomputable def weightOneMonomialExpansion : P →+* Polynomial Cw :=
  (Polynomial.mapRingHom (algebraMap Aw Cw)).comp
    ((optionEquivLeft k (WeightOneCoefficientVariables S i)).toRingHom.comp
      (AddMonoidAlgebra.mapDomainRingHom k (weightOneExponentMap S i)))

private theorem weightOneMonomialExpansion_monomial (exponent : σ →₀ ℕ) (a : k) :
    weightOneMonomialExpansion S i (monomial exponent a) =
      Polynomial.monomial ((weightOneExponentMap S i exponent) none)
        (algebraMap Aw Cw (monomial (weightOneExponentMap S i exponent).some a)) := by
  change Polynomial.map (algebraMap Aw Cw)
    (optionEquivLeft k (WeightOneCoefficientVariables S i)
      (AddMonoidAlgebra.mapDomain (weightOneExponentMap S i)
        (AddMonoidAlgebra.single exponent a))) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  change Polynomial.map (algebraMap Aw Cw)
    (optionEquivLeft k (WeightOneCoefficientVariables S i)
      (monomial (weightOneExponentMap S i exponent) a)) = _
  rw [optionEquivLeft_monomial, Polynomial.map_monomial]

private theorem weightOneExpansion_eq_monomialExpansion :
    weightOneExpansion (k := k) S i = weightOneMonomialExpansion (k := k) S i := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [weightOneExpansion_C]
    change _ = weightOneMonomialExpansion S i (monomial 0 a)
    rw [weightOneMonomialExpansion_monomial]
    simp [weightOneExponentMap, IsScalarTower.algebraMap_apply k Aw Cw]
  · intro j
    by_cases hpivot : j = (i : σ)
    · subst j
      rw [weightOneExpansion_pivot]
      change Polynomial.X = weightOneMonomialExpansion S i
        (monomial (Finsupp.single (i : σ) 1) 1)
      rw [weightOneMonomialExpansion_monomial]
      simp [weightOneExponentMap, weightOneIndexEquiv, weightOneOtherWeight,
        Finsupp.weight_single]
      rfl
    · by_cases hmember : j ∈ S
      · let index : {j : σ // j ∈ S ∧ j ≠ (i : σ)} := ⟨j, hmember, hpivot⟩
        rw [show (X j : P) = X (index : σ) from rfl,
          weightOneExpansion_weighted S i index]
        change Polynomial.X * Polynomial.C (algebraMap Aw Cw (X (Sum.inr index))) =
          weightOneMonomialExpansion S i (monomial (Finsupp.single j 1) 1)
        rw [weightOneMonomialExpansion_monomial]
        simp [weightOneExponentMap, weightOneIndexEquiv, weightOneOtherWeight,
          Finsupp.weight_single, hpivot, hmember, index]
        simp only [← Polynomial.C_mul_X_pow_eq_monomial, pow_one, MvPolynomial.X]
      · let index : {j : σ // j ∉ S} := ⟨j, hmember⟩
        rw [show (X j : P) = X (index : σ) from rfl,
          weightOneExpansion_unweighted S i index]
        change Polynomial.C (algebraMap Aw Cw (X (Sum.inl index))) =
          weightOneMonomialExpansion S i (monomial (Finsupp.single j 1) 1)
        rw [weightOneMonomialExpansion_monomial]
        simp [weightOneExponentMap, weightOneIndexEquiv, weightOneOtherWeight,
          Finsupp.weight_single, hpivot, hmember, index]
        rfl

/-- Distinct polynomials retain distinct exponent-and-coefficient data under pivot expansion. -/
theorem weightOneExpansion_injective :
    Function.Injective (weightOneExpansion (k := k) S i) := by
  rw [weightOneExpansion_eq_monomialExpansion]
  exact ((Polynomial.map_injective (algebraMap Aw Cw)
    (FaithfulSMul.algebraMap_injective Aw Cw)).comp
      (optionEquivLeft k (WeightOneCoefficientVariables S i)).injective).comp
        (AddMonoidAlgebra.mapDomain_injective (weightOneExponentMap_injective S i))

open scoped Classical in
private theorem weightOneExponentMap_weight (exponent : σ →₀ ℕ) :
    weightOneExponentMap S i exponent none =
      Finsupp.weight (fun j => if j ∈ S then (1 : ℕ) else 0) exponent := by
  classical
  have hpivot : weightOneIndexEquiv S i (i : σ) = none := by
    simp [weightOneIndexEquiv]
  have hweight : exponent (i : σ) + Finsupp.weight (weightOneOtherWeight S i) exponent =
      Finsupp.weight (fun j => if j ∈ S then (1 : ℕ) else 0) exponent := by
    rw [← Finsupp.weight_single_one_apply (i : σ) exponent]
    simp only [Finsupp.weight_apply, Finsupp.sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← smul_add]
    congr 1
    by_cases heq : j = (i : σ)
    · subst j
      simp [weightOneOtherWeight, i.property]
    · by_cases hmember : j ∈ S <;>
        simp [weightOneOtherWeight, heq, hmember]
  simpa [weightOneExponentMap, ← hpivot,
    Finsupp.mapDomain_apply_of_injective (weightOneIndexEquiv S i).injective] using hweight

/-- Embed the original function field into the fraction field of its pivot expansion. -/
private noncomputable def weightOneForward : K →+* RatFunc Cw :=
  IsFractionRing.lift (g := (algebraMap (Polynomial Cw) (RatFunc Cw)).comp
    (weightOneExpansion S i)) ((RatFunc.algebraMap_injective Cw).comp
    (weightOneExpansion_injective S i))

private theorem weightOneForward_polynomial (p : P) :
    weightOneForward S i (algebraMap P K p) =
      algebraMap (Polynomial Cw) (RatFunc Cw) (weightOneExpansion S i p) := by
  exact IsFractionRing.lift_algebraMap (g := (algebraMap (Polynomial Cw) (RatFunc Cw)).comp
    (weightOneExpansion S i)) ((RatFunc.algebraMap_injective Cw).comp
    (weightOneExpansion_injective S i)) p

/-- Substitute the original variables and their pivot ratios for coefficient generators. -/
private noncomputable def weightOneCoefficientToK : Aw →+* K :=
  (aeval fun
    | Sum.inl j => algebraMap P K (X (j : σ))
    | Sum.inr j => algebraMap P K (X (j : σ)) / algebraMap P K (X (i : σ))).toRingHom

private theorem weightOneCoefficientToK_forward :
    (weightOneForward S i).comp (weightOneCoefficientToK S i) =
      (RatFunc.C : Cw →+* RatFunc Cw).comp (algebraMap Aw Cw) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [weightOneCoefficientToK, weightOneForward_polynomial,
      weightOneExpansion_C, IsScalarTower.algebraMap_apply k Aw Cw,
      IsScalarTower.algebraMap_apply k P K]
  · intro j
    rcases j with j | j
    · simp [weightOneCoefficientToK, weightOneForward_polynomial]
    · have hX : (RatFunc.X : RatFunc Cw) ≠ 0 := RatFunc.X_ne_zero
      simp [weightOneCoefficientToK, weightOneForward_polynomial, hX]

/-- Substituting pivot ratios embeds the independent coefficient polynomial ring. -/
private theorem weightOneCoefficientToK_injective :
    Function.Injective (weightOneCoefficientToK (k := k) S i) := by
  intro a b hab
  have h := congrArg (weightOneForward S i) hab
  have heq := weightOneCoefficientToK_forward (k := k) S i
  change ((weightOneForward S i).comp (weightOneCoefficientToK S i)) a =
    ((weightOneForward S i).comp (weightOneCoefficientToK S i)) b at h
  rw [heq] at h
  exact (IsFractionRing.injective Aw Cw) (RatFunc.C_injective h)

/-- Lift the independent coefficient generators and ratios to the original function field. -/
private noncomputable def weightOneCoefficientFieldToK : Cw →+* K :=
  IsFractionRing.lift (weightOneCoefficientToK_injective S i)

private theorem weightOneForward_coefficientField (a : Cw) :
    weightOneForward (k := k) S i (weightOneCoefficientFieldToK S i a) = RatFunc.C a := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective Aw a
  have heq := weightOneCoefficientToK_forward (k := k) S i
  have hcomp (b : Aw) :
      weightOneForward S i (weightOneCoefficientToK S i b) =
        RatFunc.C (algebraMap Aw Cw b) := by
    exact congrArg (fun f : Aw →+* RatFunc Cw => f b) heq
  simp only [map_div₀, weightOneCoefficientFieldToK,
    IsFractionRing.lift_algebraMap, hcomp]

/-- Evaluate the pivot polynomial with its coefficient field embedded in the function field. -/
private noncomputable def weightOnePolynomialToK : Polynomial Cw →+* K :=
  Polynomial.eval₂RingHom (weightOneCoefficientFieldToK S i)
    (algebraMap P K (X (i : σ)))

private theorem weightOnePolynomialToK_forward :
    (weightOneForward (k := k) S i).comp (weightOnePolynomialToK S i) =
      algebraMap (Polynomial Cw) (RatFunc Cw) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [weightOnePolynomialToK, weightOneForward_coefficientField]
  · simp [weightOnePolynomialToK, weightOneForward_polynomial]

/-- Evaluation of the pivot polynomial over its ratio field is injective. -/
private theorem weightOnePolynomialToK_injective :
    Function.Injective (weightOnePolynomialToK (k := k) S i) := by
  intro a b hab
  have h := congrArg (weightOneForward S i) hab
  change ((weightOneForward S i).comp (weightOnePolynomialToK S i)) a =
    ((weightOneForward S i).comp (weightOnePolynomialToK S i)) b at h
  rw [weightOnePolynomialToK_forward] at h
  exact RatFunc.algebraMap_injective Cw h

/-- Extend coefficient-field evaluation and the chosen pivot to rational functions. -/
private noncomputable def weightOneBackward : RatFunc Cw →+* K :=
  RatFunc.liftRingHom (weightOnePolynomialToK S i)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (weightOnePolynomialToK_injective S i))

/-- The two fraction-field coordinate maps compose to the identity. -/
private theorem weightOneForward_backward :
    (weightOneForward S i).comp (weightOneBackward S i) =
      RingHom.id (RatFunc Cw) := by
  apply (IsFractionRing.ringHom_ext (A := Polynomial Cw))
  intro p
  simpa only [RingHom.comp_apply, RingHom.id_apply, weightOneBackward,
    RatFunc.liftRingHom_algebraMap] using
      congrArg (fun f : Polynomial Cw →+* RatFunc Cw => f p)
        (weightOnePolynomialToK_forward S i)

/-- The birational coordinates identifying the original function field with a
univariate rational function field over its coefficient-ratio field. -/
@[no_expose]
noncomputable def weightOneCoordinates : K ≃+* RatFunc Cw := by
  refine RingEquiv.ofRingHom (weightOneForward S i) (weightOneBackward S i)
    (weightOneForward_backward S i) ?_
  apply RingHom.ext
  intro x
  apply (weightOneForward (k := k) S i).injective
  simpa only [RingHom.comp_apply, RingHom.id_apply] using
    RingHom.congr_fun (weightOneForward_backward S i) (weightOneForward S i x)

/-- Polynomial expansion agrees with the birational coordinate equivalence. -/
theorem weightOneCoordinates_polynomial (p : P) :
    weightOneCoordinates S i (algebraMap P K p) =
      algebraMap (Polynomial Cw) (RatFunc Cw) (weightOneExpansion S i p) := by
  exact weightOneForward_polynomial S i p

@[simp] theorem weightOneCoordinates_pivot :
    weightOneCoordinates S i (algebraMap P K (X (i : σ))) = RatFunc.X := by
  rw [weightOneCoordinates_polynomial, weightOneExpansion_pivot]
  rfl

@[simp] theorem weightOneCoordinates_unweighted (j : {j : σ // j ∉ S}) :
    weightOneCoordinates S i (algebraMap P K (X (j : σ))) =
      RatFunc.C (algebraMap Aw Cw (X (Sum.inl j))) := by
  rw [weightOneCoordinates_polynomial, weightOneExpansion_unweighted]
  rfl

@[simp] theorem weightOneCoordinates_weighted
    (j : {j : σ // j ∈ S ∧ j ≠ (i : σ)}) :
    weightOneCoordinates S i (algebraMap P K (X (j : σ))) =
      RatFunc.X * RatFunc.C (algebraMap Aw Cw (X (Sum.inr j))) := by
  rw [weightOneCoordinates_polynomial, weightOneExpansion_weighted, map_mul]
  rfl

@[simp] theorem weightOneCoordinates_C (a : k) :
    weightOneCoordinates S i (algebraMap P K (C a)) =
      RatFunc.C (algebraMap k Cw a) := by
  rw [weightOneCoordinates_polynomial, weightOneExpansion_C]
  rfl

/-- The inverse coordinate map fixes the ratio of a weighted variable to the pivot. -/
theorem weightOneCoordinates_symm_ratio
    (j : {j : σ // j ∈ S ∧ j ≠ (i : σ)}) :
    (weightOneCoordinates S i).symm (RatFunc.C (algebraMap Aw Cw (X (Sum.inr j)))) =
      algebraMap P K (X (j : σ)) / algebraMap P K (X (i : σ)) := by
  apply (weightOneCoordinates S i).injective
  rw [RingEquiv.apply_symm_apply, map_div₀, weightOneCoordinates_weighted,
    weightOneCoordinates_pivot]
  have hX : (RatFunc.X : RatFunc Cw) ≠ 0 := RatFunc.X_ne_zero
  simp [hX]

/-- The inverse coordinate map fixes every unweighted variable. -/
theorem weightOneCoordinates_symm_unweighted (j : {j : σ // j ∉ S}) :
    (weightOneCoordinates S i).symm (RatFunc.C (algebraMap Aw Cw (X (Sum.inl j)))) =
      algebraMap P K (X (j : σ)) := by
  apply (weightOneCoordinates S i).injective
  simp

/-- The polynomial's minimum subset weight is the order of its expansion at `X = 0`. -/
theorem weightOneExpansion_trailingDegree (p : P) :
    (weightOneExpansion S i p).trailingDegree = weightOneOrder S p := by
  classical
  have hsupport : (weightOneExpansion S i p).support =
      p.support.image (fun exponent => weightOneExponentMap S i exponent none) := by
    rw [weightOneExpansion_eq_monomialExpansion]
    change (Polynomial.map (algebraMap Aw Cw)
      (optionEquivLeft k (WeightOneCoefficientVariables S i)
        ((AddMonoidAlgebra.mapDomainRingHom k (weightOneExponentMap S i)) p))).support = _
    rw [Polynomial.support_map_of_injective _ (FaithfulSMul.algebraMap_injective Aw Cw),
      support_optionEquivLeft]
    have hmap : (MvPolynomial.support
        (AddMonoidAlgebra.mapDomain (weightOneExponentMap S i) p :
          MvPolynomial (Option (WeightOneCoefficientVariables S i)) k)) =
        p.support.image (weightOneExponentMap S i) := by
      simpa only [MvPolynomial.support, AddMonoidAlgebra.mapDomain] using
        (Finsupp.mapDomain_support_of_injective (weightOneExponentMap_injective S i)
          p.coeff)
    change Finset.image (fun m => m none)
      (MvPolynomial.support
        (AddMonoidAlgebra.mapDomain (weightOneExponentMap S i) p :
          MvPolynomial (Option (WeightOneCoefficientVariables S i)) k)) = _
    rw [hmap]
    simp only [Finset.image_image, Function.comp_def]
  simp only [Polynomial.trailingDegree, weightOneOrder, hsupport,
    Finset.min_eq_inf_withTop, Finset.inf_image, Function.comp_def,
    weightOneExponentMap_weight]
  rfl

/-- The coefficient of the lowest-weight term in the univariate expansion. -/
noncomputable def weightOneInitial (p : P) : Cw :=
  (weightOneExpansion S i p).coeff (weightOneNatOrder S p)

@[simp] theorem weightOneInitial_zero : weightOneInitial S i (0 : P) = 0 := by
  simp [weightOneInitial]

/-- A nonzero polynomial has nonzero initial coefficient. -/
theorem weightOneInitial_ne_zero {p : P} (hp : p ≠ 0) :
    weightOneInitial S i p ≠ 0 := by
  have hne : weightOneExpansion S i p ≠ 0 := by
    intro h
    have hdegree := weightOneExpansion_trailingDegree S i p
    rw [h, Polynomial.trailingDegree_zero] at hdegree
    exact hp ((weightOneOrder_eq_top S p).mp hdegree.symm)
  have hdegree : (weightOneExpansion S i p).natTrailingDegree = weightOneNatOrder S p := by
    simpa [Polynomial.natTrailingDegree, weightOneNatOrder] using
      congrArg ENat.toNat (weightOneExpansion_trailingDegree S i p)
  simpa [weightOneInitial, ← hdegree, Polynomial.trailingCoeff] using
    (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne)

private theorem weightOneExpansion_factor (p : P) :
    ∃ r : Polynomial Cw,
      weightOneExpansion S i p = Polynomial.X ^ weightOneNatOrder S p * r ∧
        r.coeff 0 = weightOneInitial S i p := by
  have hdegree : (weightOneExpansion S i p).natTrailingDegree =
      weightOneNatOrder S p := by
    simpa [Polynomial.natTrailingDegree, weightOneNatOrder] using
      congrArg ENat.toNat (weightOneExpansion_trailingDegree S i p)
  have hdiv : (Polynomial.X : Polynomial Cw) ^ weightOneNatOrder S p ∣
      weightOneExpansion S i p := by
    apply (Polynomial.X_pow_dvd_iff).2
    intro degree hlt
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hdegree.symm ▸ hlt)
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨r, hr, ?_⟩
  rw [weightOneInitial, hr]
  simpa only [zero_add] using
    (Polynomial.coeff_X_pow_mul r (weightOneNatOrder S p) 0).symm

/-- The pullback of the `X`-adic valuation along the birational coordinates. -/
noncomputable def weightOneValuation : Valuation K ℤᵐ⁰ :=
  ((Polynomial.idealX Cw).valuation (RatFunc Cw)).comap
    (weightOneCoordinates S i).toRingHom

local notation "Vw" => Valuation.valuationSubring (weightOneValuation (k := k) S i)

@[simp] theorem weightOneValuation_apply (x : K) :
    weightOneValuation (k := k) S i x =
      (Polynomial.idealX Cw).valuation (RatFunc Cw) (weightOneCoordinates S i x) :=
  rfl

@[simp] theorem weightOneValuation_zero : weightOneValuation (k := k) S i (0 : K) = 0 := by
  simp

/-- Nonzero polynomials have valuation determined by their least subset weight. -/
theorem weightOneValuation_polynomial {p : P} (hp : p ≠ 0) :
    weightOneValuation (k := k) S i (algebraMap P K p) =
      WithZero.exp (-(weightOneNatOrder S p : ℤ)) := by
  classical
  have hexp : weightOneExpansion S i p ≠ 0 := by
    intro h
    have hd := weightOneExpansion_trailingDegree S i p
    rw [h, Polynomial.trailingDegree_zero] at hd
    exact hp ((weightOneOrder_eq_top S p).mp hd.symm)
  have hnat : (weightOneExpansion S i p).natTrailingDegree = weightOneNatOrder S p := by
    simpa [Polynomial.natTrailingDegree, weightOneNatOrder] using
      congrArg ENat.toNat (weightOneExpansion_trailingDegree S i p)
  have hmult : multiplicity (Polynomial.X : Polynomial Cw) (weightOneExpansion S i p) =
      weightOneNatOrder S p := by
    rw [← hnat, ← Polynomial.rootMultiplicity_eq_natTrailingDegree',
      Polynomial.rootMultiplicity_eq_multiplicity]
    simp [hexp]
  rw [weightOneValuation_apply, weightOneCoordinates_polynomial,
    (Polynomial.idealX Cw).valuation_of_algebraMap,
    (Polynomial.idealX Cw).intValuation_eq_exp_neg_multiplicity hexp,
    Polynomial.idealX_span, Ideal.multiplicity_span_eq_multiplicity, hmult]

/-- A quotient has the difference of its integer-valued numerator and denominator orders. -/
theorem weightOneValuation_div {p q : P} (hp : p ≠ 0) (hq : q ≠ 0) :
    weightOneValuation (k := k) S i (algebraMap P K p / algebraMap P K q) =
      WithZero.exp (-((weightOneNatOrder S p : ℤ) - (weightOneNatOrder S q : ℤ))) := by
  rw [map_div₀, weightOneValuation_polynomial S i hp,
    weightOneValuation_polynomial S i hq, ← WithZero.exp_sub]
  congr 1
  omega

@[simp] theorem weightOneValuation_zero_div (q : P) :
    weightOneValuation (k := k) S i (algebraMap P K 0 / algebraMap P K q) = 0 := by
  simp

open scoped Classical in
/-- A variable has `X`-adic value `exp (-1)` exactly when it is weighted. -/
theorem weightOneValuation_X (j : σ) :
    weightOneValuation (k := k) S i (algebraMap P K (X j)) =
      if j ∈ S then WithZero.exp (-1 : ℤ) else 1 := by
  rw [weightOneValuation_polynomial S i (X_ne_zero j)]
  by_cases hj : j ∈ S <;> simp [weightOneNatOrder, weightOneOrder_X, hj]

/-- Changing the pivot does not change the valuation on the original function field. -/
theorem weightOneValuation_pivot_eq (i' : S) :
    weightOneValuation (k := k) S i = weightOneValuation S i' := by
  apply Valuation.ext
  intro x
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective P x
  have hq' : q ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero.mp hq)
  by_cases hp : p = 0
  · subst p
    simp
  · rw [weightOneValuation_div S i hp hq', weightOneValuation_div S i' hp hq']

/-- A rational fraction belongs to the valuation subring precisely when its
numerator has at least the minimum subset weight of its denominator. -/
theorem weightOneValuation_mem_div_iff {p q : P} (hq : q ≠ 0) :
    algebraMap P K p / algebraMap P K q ∈ Vw ↔
      weightOneOrder S q ≤ weightOneOrder S p := by
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Valuation.mem_valuationSubring_iff, weightOneValuation_div S i hp hq,
      WithZero.exp_le_one_iff, weightOneOrder_eq_natOrder S hp,
      weightOneOrder_eq_natOrder S hq]
    simp only [ENat.natCast_le_natCast]
    omega

/-- Package a rational fraction with its minimum-order integrality proof. -/
noncomputable def weightOneIntegralFraction (p q : P) (hq : q ≠ 0)
    (horder : weightOneOrder S q ≤ weightOneOrder S p) :
    Vw :=
  ⟨algebraMap P K p / algebraMap P K q,
    (weightOneValuation_mem_div_iff S i hq).2 horder⟩

@[simp] theorem weightOneIntegralFraction_val (p q : P) (hq : q ≠ 0)
    (horder : weightOneOrder S q ≤ weightOneOrder S p) :
    ((weightOneIntegralFraction S i p q hq horder : Vw) : K) =
        algebraMap P K p / algebraMap P K q :=
  rfl

/-- Every value in the ambient `ℤᵐ⁰` occurs in the function field. -/
theorem weightOneValuation_surjective :
    Function.Surjective (weightOneValuation (k := k) S i) := by
  intro value
  obtain ⟨x, hx⟩ := RatFunc.valuation_surjective Cw value
  exact ⟨(weightOneCoordinates S i).symm x,
    by simpa only [weightOneValuation_apply, RingEquiv.apply_symm_apply, RatFunc.v_def] using hx⟩

/-- The value group is rank-one discrete. -/
noncomputable instance weightOneValuation_isRankOneDiscrete :
    (weightOneValuation (k := k) S i).IsRankOneDiscrete := by
  have hval : WithZero.exp (-1 : ℤ) ≠ (1 : ℤᵐ⁰) := by
    simp [← WithZero.exp_zero]
  obtain ⟨x, hx⟩ := weightOneValuation_surjective (k := k) S i (WithZero.exp (-1 : ℤ))
  have : (weightOneValuation (k := k) S i).IsNontrivial := by
    exact ⟨⟨x, by simp [hx], by rw [hx]; exact hval⟩⟩
  have : IsCyclic (MonoidWithZeroHom.valueGroup
      (.ofClass (weightOneValuation (k := k) S i))) := Subgroup.isCyclic _
  infer_instance

/-- The associated valuation subring is a discrete valuation ring. -/
theorem weightOneValuation_isDiscreteValuationRing :
    IsDiscreteValuationRing Vw := by
  infer_instance

/-- The pivot lies in the valuation subring. -/
theorem weightOneValuation_pivot_mem :
    algebraMap P K (X (i : σ)) ∈ Vw := by
  rw [Valuation.mem_valuationSubring_iff, weightOneValuation_apply,
    weightOneCoordinates_pivot, Polynomial.valuation_X_eq_neg_one]
  simp

/-- The pivot, viewed as an element of the valuation subring. -/
noncomputable def weightOneUniformizer : Vw :=
  ⟨algebraMap P K (X (i : σ)), weightOneValuation_pivot_mem S i⟩

@[simp] theorem weightOneUniformizer_val :
    ((weightOneUniformizer (k := k) S i : Vw) : K) =
      algebraMap P K (X (i : σ)) :=
  rfl

/-- The chosen pivot is a uniformizer for the weight-one valuation. -/
theorem weightOneUniformizer_isUniformizer :
    (weightOneValuation (k := k) S i).IsUniformizer
      (weightOneUniformizer (k := k) S i : K) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (weightOneValuation_surjective S i)]
  simp [weightOneUniformizer_val, weightOneValuation_apply,
    weightOneCoordinates_pivot, Polynomial.valuation_X_eq_neg_one]

/-- The maximal ideal of the valuation subring is generated by the pivot. -/
theorem weightOneUniformizer_maximalIdeal :
    IsLocalRing.maximalIdeal Vw = Ideal.span {weightOneUniformizer (k := k) S i} := by
  exact (weightOneUniformizer_isUniformizer S i).is_generator

/-- Constant rational functions in the coefficient field lift to the valuation subring. -/
noncomputable def weightOneCoefficientSection :
    Cw →+* Vw := by
  refine ((weightOneCoordinates S i).symm.toRingHom.comp
    (RatFunc.C : Cw →+* RatFunc Cw)).codRestrict Vw ?_
  intro a
  change weightOneValuation (k := k) S i
    ((weightOneCoordinates S i).symm (RatFunc.C a)) ≤ 1
  rw [weightOneValuation_apply, RingEquiv.apply_symm_apply]
  change (Polynomial.idealX Cw).valuation (RatFunc Cw)
    (algebraMap (Polynomial Cw) (RatFunc Cw) (Polynomial.C a)) ≤ 1
  exact (Polynomial.idealX Cw).valuation_le_one (Polynomial.C a)

/-- The coefficient section is inverse to the coordinate map on constants. -/
theorem weightOneCoefficientSection_val (a : Cw) :
    ((weightOneCoefficientSection S i a : Vw) : K) =
      (weightOneCoordinates S i).symm (RatFunc.C a) := by
  rfl

/-- The section's unweighted generator is the original unweighted variable. -/
theorem weightOneCoefficientSection_unweighted_val (j : {j : σ // j ∉ S}) :
    ((weightOneCoefficientSection S i (algebraMap Aw Cw (X (Sum.inl j))) : Vw) : K) =
      algebraMap P K (X (j : σ)) := by
  rw [weightOneCoefficientSection_val, weightOneCoordinates_symm_unweighted]

/-- The section's ratio generator is the weighted variable divided by the pivot. -/
theorem weightOneCoefficientSection_ratio_val
    (j : {j : σ // j ∈ S ∧ j ≠ (i : σ)}) :
    ((weightOneCoefficientSection S i (algebraMap Aw Cw (X (Sum.inr j))) : Vw) : K) =
        algebraMap P K (X (j : σ)) / algebraMap P K (X (i : σ)) := by
  rw [weightOneCoefficientSection_val, weightOneCoordinates_symm_ratio]

/-- Identify the valuation ring with the localization of pivot polynomials at `X`. -/
private noncomputable def weightOneAdicSubringEquiv :
    Vw ≃+* (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (RatFunc Cw) (Polynomial.idealX Cw)) := by
  apply RingEquiv.restrict (weightOneCoordinates S i)
  intro x
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

/-- The pivot-polynomial ideal is maximal over the coefficient field. -/
theorem weightOneIdealX_isMaximal :
    ((Polynomial.idealX Cw).asIdeal).IsMaximal := by
  rw [Polynomial.idealX_span]
  simpa using PrincipalIdealRing.isMaximal_of_irreducible
    (Polynomial.irreducible_X_sub_C (0 : Cw))

/-- The residue of the `X`-localization is its coefficient field. -/
private noncomputable def weightOneAdicResidueEquiv :
    IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (RatFunc Cw) (Polynomial.idealX Cw)) ≃+* Cw := by
  letI : ((Polynomial.idealX Cw).asIdeal).IsMaximal := weightOneIdealX_isMaximal S i
  have hideal : (Polynomial.idealX Cw).asIdeal =
      Ideal.span ({Polynomial.X - Polynomial.C (0 : Cw)} : Set (Polynomial Cw)) := by
    simp [Polynomial.idealX_span]
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal
    (Polynomial.idealX Cw).asIdeal
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (RatFunc Cw) (Polynomial.idealX Cw))).symm.trans
        ((Ideal.quotEquivOfEq hideal).trans
          (Polynomial.quotientSpanXSubCAlgEquiv (0 : Cw)).toRingEquiv)

private theorem weightOneAdicSubringEquiv_section (a : Cw) :
    weightOneAdicSubringEquiv S i (weightOneCoefficientSection S i a) =
      algebraMap (Polynomial Cw)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (RatFunc Cw) (Polynomial.idealX Cw)) (Polynomial.C a) := by
  apply Subtype.ext
  change weightOneCoordinates S i
    ((weightOneCoefficientSection S i a : Vw) : K) =
      algebraMap (Polynomial Cw) (RatFunc Cw) (Polynomial.C a)
  rw [weightOneCoefficientSection_val, RingEquiv.apply_symm_apply]
  rfl

/-- Every residue, not only a coefficient subfield, is a rational function of
unweighted variables and pivot ratios. -/
@[no_expose]
noncomputable def weightOneResidueEquiv :
    IsLocalRing.ResidueField Vw ≃+* Cw := by
  exact (IsLocalRing.ResidueField.mapEquiv (weightOneAdicSubringEquiv S i)).trans
    (weightOneAdicResidueEquiv S i)

/-- Transport residue classes through the birational `X`-adic coordinate map. -/
private theorem weightOneResidueEquiv_residue (a : Vw) :
    weightOneResidueEquiv S i (IsLocalRing.residue Vw a) =
      weightOneAdicResidueEquiv S i
        (IsLocalRing.residue _ (weightOneAdicSubringEquiv S i a)) := by
  change (weightOneAdicResidueEquiv S i)
    (IsLocalRing.ResidueField.mapEquiv (weightOneAdicSubringEquiv S i)
      (IsLocalRing.residue Vw a)) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rfl

@[simp] theorem weightOneResidueEquiv_section (a : Cw) :
    weightOneResidueEquiv S i
      (IsLocalRing.residue _ (weightOneCoefficientSection S i a)) = a := by
  let : ((Polynomial.idealX Cw).asIdeal).IsMaximal := weightOneIdealX_isMaximal S i
  rw [weightOneResidueEquiv_residue, weightOneAdicSubringEquiv_section]
  have hideal : (Polynomial.idealX Cw).asIdeal =
      Ideal.span ({Polynomial.X - Polynomial.C (0 : Cw)} : Set (Polynomial Cw)) := by
    simp [Polynomial.idealX_span]
  change ((IsLocalization.AtPrime.equivQuotMaximalIdeal
      (Polynomial.idealX Cw).asIdeal
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (RatFunc Cw) (Polynomial.idealX Cw))).symm.trans
        ((Ideal.quotEquivOfEq hideal).trans
          (Polynomial.quotientSpanXSubCAlgEquiv (0 : Cw)).toRingEquiv))
      (Ideal.Quotient.mk _
        (algebraMap (Polynomial Cw)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (RatFunc Cw) (Polynomial.idealX Cw)) (Polynomial.C a))) = a
  simp only [RingEquiv.trans_apply]
  rw [← IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk
    (p := (Polynomial.idealX Cw).asIdeal)
    (Rₚ := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (RatFunc Cw) (Polynomial.idealX Cw))]
  rw [RingEquiv.symm_apply_apply]
  change (Polynomial.quotientSpanXSubCAlgEquiv 0)
    ((Ideal.quotEquivOfEq hideal)
      (Ideal.Quotient.mk (Polynomial.idealX Cw).asIdeal (Polynomial.C a))) = a
  rw [Ideal.quotEquivOfEq_mk, Polynomial.quotientSpanXSubCAlgEquiv_mk,
    Polynomial.eval_C]

/-- Recover a residue class from any rational coefficient. -/
theorem weightOneResidueEquiv_symm_apply (a : Cw) :
    (weightOneResidueEquiv S i).symm a =
      IsLocalRing.residue _ (weightOneCoefficientSection S i a) := by
  apply (weightOneResidueEquiv S i).injective
  simp

private theorem weightOneAdicResidueEquiv_mk (p : Polynomial Cw)
    (q : (Polynomial.idealX Cw).asIdeal.primeCompl) :
    weightOneAdicResidueEquiv S i
      (IsLocalRing.residue _
        (IsLocalization.mk'
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (RatFunc Cw) (Polynomial.idealX Cw)) p q)) =
      p.eval 0 / (q : Polynomial Cw).eval 0 := by
  let : ((Polynomial.idealX Cw).asIdeal).IsMaximal := weightOneIdealX_isMaximal S i
  have hideal : (Polynomial.idealX Cw).asIdeal =
      Ideal.span ({Polynomial.X - Polynomial.C (0 : Cw)} : Set (Polynomial Cw)) := by
    simp [Polynomial.idealX_span]
  have : (Ideal.span ({Polynomial.X - Polynomial.C (0 : Cw)} : Set (Polynomial Cw))).IsMaximal :=
    hideal ▸ weightOneIdealX_isMaximal S i
  let : Field ((Polynomial Cw) ⧸ (Polynomial.idealX Cw).asIdeal) :=
    Ideal.Quotient.field _
  let : Field ((Polynomial Cw) ⧸
      Ideal.span ({Polynomial.X - Polynomial.C (0 : Cw)} : Set (Polynomial Cw))) :=
    Ideal.Quotient.field _
  change ((IsLocalization.AtPrime.equivQuotMaximalIdeal
      (Polynomial.idealX Cw).asIdeal
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (RatFunc Cw) (Polynomial.idealX Cw))).symm.trans
        ((Ideal.quotEquivOfEq hideal).trans
          (Polynomial.quotientSpanXSubCAlgEquiv (0 : Cw)).toRingEquiv))
      (Ideal.Quotient.mk _
        (IsLocalization.mk'
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (RatFunc Cw) (Polynomial.idealX Cw)) p q)) = _
  simp only [RingEquiv.trans_apply,
    IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk,
    map_mul, Ideal.quotEquivOfEq_mk]
  simp only [map_inv₀, Ideal.quotEquivOfEq_mk, div_eq_mul_inv]
  change (Polynomial.quotientSpanXSubCAlgEquiv (0 : Cw))
      (Ideal.Quotient.mk _ p) *
        ((Polynomial.quotientSpanXSubCAlgEquiv (0 : Cw))
          (Ideal.Quotient.mk _ (q : Polynomial Cw)))⁻¹ =
      p.eval 0 * ((q : Polynomial Cw).eval 0)⁻¹
  simp

/-- The residue of an unweighted generator is that generator in the coefficient field. -/
theorem weightOneResidueEquiv_unweighted (j : {j : σ // j ∉ S}) :
    weightOneResidueEquiv S i
      (IsLocalRing.residue _
        (weightOneCoefficientSection S i (algebraMap Aw Cw (X (Sum.inl j))))) =
      algebraMap Aw Cw (X (Sum.inl j)) := by
  simp

/-- The residue of a weighted-variable ratio is its ratio generator. -/
theorem weightOneResidueEquiv_ratio
    (j : {j : σ // j ∈ S ∧ j ≠ (i : σ)}) :
    weightOneResidueEquiv S i
      (IsLocalRing.residue _
        (weightOneCoefficientSection S i (algebraMap Aw Cw (X (Sum.inr j))))) =
      algebraMap Aw Cw (X (Sum.inr j)) := by
  simp

/-- The residue of a fraction of equal minimum orders is the quotient of its
initial coefficients, with no loss of ratio variables. -/
theorem weightOneResidueEquiv_div {p q : P} (hq : q ≠ 0)
    (horder : weightOneOrder S p = weightOneOrder S q) :
    weightOneResidueEquiv S i
      (IsLocalRing.residue _ (weightOneIntegralFraction S i p q hq (le_of_eq horder.symm))) =
      weightOneInitial S i p / weightOneInitial S i q := by
  obtain ⟨p₀, hp₀, hpcoeff⟩ := weightOneExpansion_factor S i p
  obtain ⟨q₀, hq₀, hqcoeff⟩ := weightOneExpansion_factor S i q
  have hqcoeff_ne : q₀.coeff 0 ≠ 0 := by
    rw [hqcoeff]
    exact weightOneInitial_ne_zero S i hq
  have hqnot : q₀ ∉ (Polynomial.idealX Cw).asIdeal := by
    rw [Polynomial.idealX_span, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    exact hqcoeff_ne
  let qLocal : (Polynomial.idealX Cw).asIdeal.primeCompl := ⟨q₀, hqnot⟩
  let adic := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
    (RatFunc Cw) (Polynomial.idealX Cw)
  have hq₀_ne : q₀ ≠ 0 := by
    intro heq
    exact hqcoeff_ne (by simp [heq])
  have hmk : ((IsLocalization.mk' adic p₀ qLocal : adic) : RatFunc Cw) =
      algebraMap (Polynomial Cw) (RatFunc Cw) p₀ /
        algebraMap (Polynomial Cw) (RatFunc Cw) q₀ := by
    apply (eq_div_iff (by simpa only [map_zero] using
      (RatFunc.algebraMap_injective Cw).ne hq₀_ne)).mpr
    have hspec := IsLocalization.mk'_spec adic p₀ qLocal
    have hspec' := congrArg (fun x : adic => (x : RatFunc Cw)) hspec
    have hmul (x y : adic) : ((x * y : adic) : RatFunc Cw) =
        (x : RatFunc Cw) * y := rfl
    simpa only [hmul,
      IsScalarTower.algebraMap_apply (Polynomial Cw) adic (RatFunc Cw),
      ValuationSubring.algebraMap_apply] using hspec'
  have hcoord : weightOneAdicSubringEquiv S i
      (weightOneIntegralFraction S i p q hq (le_of_eq horder.symm)) =
        IsLocalization.mk' adic p₀ qLocal := by
    apply Subtype.ext
    change weightOneCoordinates S i
      (algebraMap P K p / algebraMap P K q) =
        ((IsLocalization.mk' adic p₀ qLocal : adic) : RatFunc Cw)
    rw [map_div₀, weightOneCoordinates_polynomial,
      weightOneCoordinates_polynomial, hp₀, hq₀,
      map_mul, map_mul, map_pow, map_pow,
      show weightOneNatOrder S p = weightOneNatOrder S q from
        congrArg ENat.toNat horder, hmk]
    exact mul_div_mul_left _ _
      (pow_ne_zero _ (by simpa only [RatFunc.algebraMap_X] using
        (RatFunc.X_ne_zero : (RatFunc.X : RatFunc Cw) ≠ 0)))
  rw [weightOneResidueEquiv_residue, hcoord]
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using
    (weightOneAdicResidueEquiv_mk S i p₀ qLocal).trans (by
      rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
        hpcoeff, hqcoeff])

end Field

end MvPolynomial
