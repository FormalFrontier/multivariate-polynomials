/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Algebra.Ring.Int.Field

/-!
# Integer traces in rational polynomial fraction rings

The image of `ℤ` in the fraction field of `ℚ[ℕ]` has dimension one. Its trace in
every finite-variable fraction field is again an integer image of dimension one,
whereas each entire stage field has dimension zero. Both the ambient integer
image and each trace are proper: they omit `1/2`.

This example includes the empty stage, whose fraction field contains all rational
constants but whose integer trace does not. The integer image does not contain
the coefficient field `ℚ`. All its elements already come from the empty stage;
this is not an example of failure of uniform stage capture.

## References

* Mathlib's homomorphism range, injective range-comap, ring equivalence, integer
  principal ideal domain, and field Krull-dimension APIs.
* `MultivariatePolynomials.FractionRingFiniteVariables` for the canonical maps.
* `AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture` for the trace dimension
  approach.
-/

@[expose] public section

noncomputable section

namespace PolynomialFractionTraceExamples

local notation "F" => FractionRing (MvPolynomial ℕ ℚ)
local notation "FJ" J => FractionRing (MvPolynomial {i : ℕ // i ∈ J} ℚ)
local notation "φ" J => IsFractionRing.map
  (A := MvPolynomial {i : ℕ // i ∈ J} ℚ) (B := MvPolynomial ℕ ℚ)
  (K := FJ J) (L := F)
  (j := AlgHom.toRingHom (MvPolynomial.rename (R := ℚ) Subtype.val))
  (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)

private theorem integer_cast_injective {σ : Type*} :
    Function.Injective (Int.castRingHom (FractionRing (MvPolynomial σ ℚ))) := by
  intro a b hab
  have hp : (a : MvPolynomial σ ℚ) = b :=
    IsFractionRing.injective (MvPolynomial σ ℚ) (FractionRing (MvPolynomial σ ℚ))
      (by simpa only [Int.coe_castRingHom, map_intCast] using hab)
  apply Int.cast_injective (α := ℚ)
  simpa only [map_intCast] using congrArg MvPolynomial.constantCoeff hp

private theorem integer_range_dimension {S : Type*} [CommRing S]
    (h : Function.Injective (Int.castRingHom S)) :
    ringKrullDim (Int.castRingHom S).rangeS = 1 := by
  let e : ℤ ≃+* (Int.castRingHom S).rangeS :=
    RingEquiv.ofBijective (Int.castRingHom S).rangeSRestrict
      ⟨fun a b hab => h (congrArg Subtype.val hab),
        (Int.castRingHom S).rangeSRestrict_surjective⟩
  rw [← e.ringKrullDim]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

private theorem half_not_mem_integer_range {σ : Type*} :
    (1 / 2 : FractionRing (MvPolynomial σ ℚ)) ∉
      (Int.castRingHom (FractionRing (MvPolynomial σ ℚ))).rangeS := by
  let S := FractionRing (MvPolynomial σ ℚ)
  have htwo : (2 : S) ≠ 0 := by
    intro h
    have hi : (2 : ℤ) = 0 := integer_cast_injective
      (by simpa only [map_ofNat, map_zero] using h)
    norm_num at hi
  rintro ⟨n, hn⟩
  change (n : S) = 1 / 2 at hn
  have hi : (n * 2 : ℤ) = 1 := integer_cast_injective (σ := σ)
    (by simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_ofNat, Int.cast_one, hn] using
      (div_mul_cancel₀ (1 : S) htwo))
  omega

private theorem integer_range_proper {σ : Type*} :
    (Int.castRingHom (FractionRing (MvPolynomial σ ℚ))).rangeS < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  apply half_not_mem_integer_range (σ := σ)
  rw [h]
  trivial

/-- The canonical fraction-stage preimage of the integer image is exactly the
integer image in that stage. This uses injectivity, not surjectivity of the stage map. -/
theorem integer_stage_trace (J : Finset ℕ) :
    ((Int.castRingHom F).rangeS).comap (φ J) = (Int.castRingHom (FJ J)).rangeS := by
  have hmap : (Int.castRingHom (FJ J)).rangeS.map (φ J) =
      (Int.castRingHom F).rangeS := by
    rw [RingHom.map_rangeS]
    congr 1
    ext n
    simp
  rw [← hmap]
  exact Subsemiring.comap_map_eq_self_of_injective (φ J).injective _

/-- The ambient integer image and every stage trace have dimension one, although
the whole finite-variable fraction field has dimension zero. -/
theorem integer_trace_dimensions (J : Finset ℕ) :
    ringKrullDim (Int.castRingHom F).rangeS = 1 ∧
      ringKrullDim (((Int.castRingHom F).rangeS).comap (φ J)) = 1 ∧
      ringKrullDim (FJ J) = 0 := by
  refine ⟨integer_range_dimension integer_cast_injective, ?_,
    ringKrullDim_eq_zero_of_field _⟩
  rw [integer_stage_trace]
  exact integer_range_dimension integer_cast_injective

/-- The integer subsemiring and each of its fraction-stage traces are proper,
as witnessed by the missing half. -/
theorem integer_image_and_trace_proper (J : Finset ℕ) :
    (Int.castRingHom F).rangeS < ⊤ ∧
      ((Int.castRingHom F).rangeS).comap (φ J) < ⊤ := by
  refine ⟨integer_range_proper, ?_⟩
  rw [integer_stage_trace]
  exact integer_range_proper

/-- Every integer already has an origin in the empty variable fraction stage. -/
theorem integer_image_has_empty_stage_origins :
    (Int.castRingHom F).rangeS ≤ (φ (∅ : Finset ℕ)).rangeS := by
  rintro x ⟨n, rfl⟩
  exact ⟨(n : FJ (∅ : Finset ℕ)), map_intCast _ n⟩

/-- Applying the trace dimension bound to the integer image gives a bound by
integer traces, with dimension one on both sides. -/
theorem integer_trace_dimension_bound :
    ringKrullDim (Int.castRingHom F).rangeS ≤ ⨆ J : Finset ℕ,
      ringKrullDim (((Int.castRingHom F).rangeS).comap (φ J)) :=
  MvPolynomial.ringKrullDim_subsemiring_le_iSup_comap_fractionRing
    (R := ℚ) (σ := ℕ) (Int.castRingHom F).rangeS

/-- The integer subring specialization uses only the underlying subsemiring
coercions; its stage preimages are the same integer traces. -/
theorem integer_subring_dimension_bound :
    ringKrullDim (Int.castRingHom F).range ≤ ⨆ J : Finset ℕ,
      ringKrullDim (((Int.castRingHom F).range).comap (φ J)) :=
  MvPolynomial.ringKrullDim_subsemiring_le_iSup_comap_fractionRing
    (R := ℚ) (σ := ℕ) (Int.castRingHom F).range.toSubsemiring

/-- Replacing the integer traces by the entire stage fields would give a false
bound, already in the empty stage. -/
theorem not_dimension_bound_by_whole_fraction_stages :
    ¬ ringKrullDim (Int.castRingHom F).rangeS ≤
      ⨆ J : Finset ℕ, ringKrullDim (FJ J) := by
  simp only [integer_range_dimension integer_cast_injective,
    ringKrullDim_eq_zero_of_field, iSup_const]
  norm_num

end PolynomialFractionTraceExamples
