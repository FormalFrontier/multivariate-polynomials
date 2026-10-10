/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.FractionRingFiniteVariables

/-!
# Finite-variable fraction-ring examples

Integer coefficients and infinitely many variables give simultaneous origins for
`X₀ / 2`, `1 / (X₁ + 1)`, and zero. Empty collections and empty ambient variable
types are included. Constant `1 / 2` has an explicit origin in the empty variable
stage for any ambient variable type and any abstract commutative-ring fraction-ring
representation, without a field instance.

## References

* `MultivariatePolynomials.FractionRingFiniteVariables` and its references.
-/

@[expose] public section

universe u v

namespace MvPolynomialTests.FractionRingFiniteVariables

open MvPolynomial

local notation "P" => MvPolynomial ℕ ℤ
local notation "F" => FractionRing P

private theorem integerPolynomial_two_ne_zero {σ : Type u} :
    (2 : MvPolynomial σ ℤ) ≠ 0 := by
  intro h
  have hc : (2 : ℤ) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (fun p : MvPolynomial σ ℤ => constantCoeff p) h
  norm_num at hc

-- Both displayed denominators are valid, even though the coefficients are not a field.
example : (2 : F) ≠ 0 := by
  intro h
  apply integerPolynomial_two_ne_zero
  exact IsFractionRing.injective P F (by simpa only [map_ofNat, map_zero] using h)

example : algebraMap P F (X 1 + 1) ≠ 0 := by
  intro h
  have hp : (X 1 + 1 : P) = 0 := IsFractionRing.injective P F (by simpa using h)
  have hc := congrArg (fun p : P => constantCoeff p) hp
  norm_num at hc

-- The three fractions have witnesses in the same stage, not three unrelated stages.
/-- Integer polynomial fractions in infinitely many variables have a common finite stage. -/
theorem integer_fraction_collection_common_origin : ∃ J : Finset ℕ,
    ∃ a b c : FractionRing (MvPolynomial {i : ℕ // i ∈ J} ℤ),
      let φ := IsFractionRing.map
        (A := MvPolynomial {i : ℕ // i ∈ J} ℤ) (B := P)
        (K := FractionRing (MvPolynomial {i : ℕ // i ∈ J} ℤ)) (L := F)
        (j := (MvPolynomial.rename (R := ℤ) Subtype.val).toRingHom)
        (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)
      φ a = algebraMap P F (X 0) / 2 ∧
      φ b = 1 / algebraMap P F (X 1 + 1) ∧ φ c = 0 := by
  let E : Set F := {algebraMap P F (X 0) / 2, 1 / algebraMap P F (X 1 + 1), 0}
  have hE : E.Finite := by
    exact ((Set.finite_singleton _).insert _).insert _
  obtain ⟨J, hJ⟩ := MvPolynomial.exists_finset_fractionRing_map_range
    (R := ℤ) (σ := ℕ) hE
  obtain ⟨a, ha⟩ := hJ (show algebraMap P F (X 0) / 2 ∈ E by simp [E])
  obtain ⟨b, hb⟩ := hJ (show 1 / algebraMap P F (X 1 + 1) ∈ E by simp [E])
  obtain ⟨c, hc⟩ := hJ (show (0 : F) ∈ E by simp [E])
  exact ⟨J, a, b, c, ha, hb, hc⟩

example : ∃ J : Finset ℕ,
    (∅ : Set F) ⊆ Set.range
      (IsFractionRing.map
        (A := MvPolynomial {i : ℕ // i ∈ J} ℤ) (B := P)
        (K := FractionRing (MvPolynomial {i : ℕ // i ∈ J} ℤ)) (L := F)
        (j := (MvPolynomial.rename (R := ℤ) Subtype.val).toRingHom)
        (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)) :=
  MvPolynomial.exists_finset_fractionRing_map_range (R := ℤ) (σ := ℕ) Set.finite_empty

-- No ambient variables forces the empty stage, which still contains 1/2.
example : (1 / 2 : FractionRing (MvPolynomial Empty ℤ)) ∈ Set.range
    (IsFractionRing.map
      (A := MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ)
      (B := MvPolynomial Empty ℤ)
      (K := FractionRing (MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ))
      (L := FractionRing (MvPolynomial Empty ℤ))
      (j := (MvPolynomial.rename (R := ℤ) Subtype.val).toRingHom)
      (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)) := by
  obtain ⟨J, hJ⟩ := MvPolynomial.exists_finset_fractionRing_map_range
    (R := ℤ) (σ := Empty)
    (Set.finite_singleton (1 / 2 : FractionRing (MvPolynomial Empty ℤ)))
  have hJempty : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst J
  exact hJ (Set.mem_singleton _)

-- Constant 1/2 comes from the empty stage even when the ambient variables are arbitrary.
example {σ : Type u} {K : Type v} [CommRing K] [Algebra (MvPolynomial σ ℤ) K]
    [IsFractionRing (MvPolynomial σ ℤ) K] :
    let d : nonZeroDivisors (MvPolynomial σ ℤ) :=
      ⟨2, mem_nonZeroDivisors_iff_ne_zero.mpr integerPolynomial_two_ne_zero⟩
    IsLocalization.mk' K 1 d ∈ Set.range
      (IsFractionRing.map
        (A := MvPolynomial {i : σ // i ∈ (∅ : Finset σ)} ℤ)
        (B := MvPolynomial σ ℤ)
        (K := FractionRing (MvPolynomial {i : σ // i ∈ (∅ : Finset σ)} ℤ)) (L := K)
        (j := (MvPolynomial.rename (R := ℤ) Subtype.val).toRingHom)
        (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)) := by
  let d : nonZeroDivisors (MvPolynomial σ ℤ) :=
    ⟨2, mem_nonZeroDivisors_iff_ne_zero.mpr integerPolynomial_two_ne_zero⟩
  let d₀ : nonZeroDivisors (MvPolynomial {i : σ // i ∈ (∅ : Finset σ)} ℤ) :=
    ⟨2, mem_nonZeroDivisors_iff_ne_zero.mpr integerPolynomial_two_ne_zero⟩
  let j : MvPolynomial {i : σ // i ∈ (∅ : Finset σ)} ℤ →+* MvPolynomial σ ℤ :=
    (rename Subtype.val).toRingHom
  have hj : Function.Injective j := rename_injective Subtype.val Subtype.val_injective
  refine ⟨IsLocalization.mk'
    (FractionRing (MvPolynomial {i : σ // i ∈ (∅ : Finset σ)} ℤ)) 1 d₀, ?_⟩
  rw [IsFractionRing.map, IsLocalization.map_mk']
  have hd : (⟨j d₀, (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)
      d₀.property⟩ : nonZeroDivisors (MvPolynomial σ ℤ)) = d :=
    Subtype.ext (map_ofNat j 2)
  change IsLocalization.mk' K (j 1)
    ⟨j d₀, (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj) d₀.property⟩ =
      IsLocalization.mk' K 1 d
  rw [map_one, hd]

-- The target has exactly the abstract ring hypotheses of the theorem, not Field K.
example {K : Type*} [CommRing K] [Algebra P K] [IsFractionRing P K] :
    ∃ J : Finset ℕ,
      let d : nonZeroDivisors P :=
        ⟨2, mem_nonZeroDivisors_iff_ne_zero.mpr integerPolynomial_two_ne_zero⟩
      {IsLocalization.mk' K (X 0) d, 0} ⊆ Set.range
        (IsFractionRing.map
          (A := MvPolynomial {i : ℕ // i ∈ J} ℤ) (B := P)
          (K := FractionRing (MvPolynomial {i : ℕ // i ∈ J} ℤ)) (L := K)
          (j := (MvPolynomial.rename (R := ℤ) Subtype.val).toRingHom)
          (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)) := by
  let d : nonZeroDivisors P :=
    ⟨2, mem_nonZeroDivisors_iff_ne_zero.mpr integerPolynomial_two_ne_zero⟩
  exact MvPolynomial.exists_finset_fractionRing_map_range (R := ℤ) (σ := ℕ)
    ((Set.finite_singleton 0).insert (IsLocalization.mk' K (X 0) d))

end MvPolynomialTests.FractionRingFiniteVariables
