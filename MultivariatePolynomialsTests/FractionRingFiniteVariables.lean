/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.FractionRingFiniteVariables
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Finite-variable fraction-ring examples

Integer coefficients and infinitely many variables give simultaneous origins for
`X₀ / 2`, `1 / (X₁ + 1)`, and zero. Empty collections and empty ambient variable
types are included. Constant `1 / 2` has an explicit origin in the empty variable
stage for any ambient variable type and any abstract commutative-ring fraction-ring
representation, without a field instance. Further examples compare missing and full
stages over the integers and the two-element field, even-index renaming, independent
universe lifts, and the boundaries of injectivity and the domain hypothesis.

## References

* `MultivariatePolynomials.FractionRingFiniteVariables` and its references.
-/

@[expose] public section

universe u v uR uτ uσ uL uK

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

-- The coefficient-fraction examples above also apply to the ambient type Unit.
private theorem empty_integer_source_excludes_variable :
    algebraMap (MvPolynomial Unit ℤ) (FractionRing (MvPolynomial Unit ℤ)) (X ()) ∉
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial Empty ℤ) (B := MvPolynomial Unit ℤ)
          (K := FractionRing (MvPolynomial Empty ℤ))
          (L := FractionRing (MvPolynomial Unit ℤ))
          (j := (rename (R := ℤ) Empty.elim).toRingHom)
          (rename_injective Empty.elim (by intro a; exact a.elim))) := by
  apply (X_mem_range_fractionRing_map_rename_iff
    (R := ℤ) (L := FractionRing (MvPolynomial Empty ℤ))
    (K := FractionRing (MvPolynomial Unit ℤ))
    Empty.elim (by intro a; exact a.elim) ()).not.mpr
  rintro ⟨a, _⟩
  exact a.elim

private theorem full_integer_stage_surjective :
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} ℤ)
        (B := MvPolynomial (Fin 2) ℤ)
        (K := FractionRing
          (MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} ℤ))
        (L := FractionRing (MvPolynomial (Fin 2) ℤ))
        (j := (rename (R := ℤ) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) := by
  exact (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing
      (MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} ℤ))
    (L := FractionRing (MvPolynomial (Fin 2) ℤ))
    (renameEquiv ℤ
      (Equiv.subtypeUnivEquiv (fun i : Fin 2 => Finset.mem_univ i))).toRingEquiv).surjective

private theorem full_binary_stage_surjective :
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} (ZMod 2))
        (B := MvPolynomial (Fin 2) (ZMod 2))
        (K := FractionRing
          (MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} (ZMod 2)))
        (L := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
        (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) := by
  exact (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing
      (MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} (ZMod 2)))
    (L := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
    (renameEquiv (ZMod 2)
      (Equiv.subtypeUnivEquiv (fun i : Fin 2 => Finset.mem_univ i))).toRingEquiv).surjective

private theorem empty_ambient_stage_surjective :
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ)
        (B := MvPolynomial Empty ℤ)
        (K := FractionRing (MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ))
        (L := FractionRing (MvPolynomial Empty ℤ))
        (j := (rename (R := ℤ) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) := by
  exact (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing (MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ))
    (L := FractionRing (MvPolynomial Empty ℤ))
    (renameEquiv ℤ
      (Equiv.subtypeUnivEquiv (fun i : Empty => i.elim))).toRingEquiv).surjective

private theorem empty_ambient_has_no_missing_variable :
    ¬ ∃ i : Empty, i ∉ (∅ : Finset Empty) := by
  rintro ⟨i, _⟩
  exact i.elim

private theorem integer_stage_excludes_missing_variable {σ : Type u}
    (S : Finset σ) (i : σ) (hi : i ∉ S) :
    algebraMap (MvPolynomial σ ℤ) (FractionRing (MvPolynomial σ ℤ)) (X i) ∉
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial {j : σ // j ∈ S} ℤ) (B := MvPolynomial σ ℤ)
          (K := FractionRing (MvPolynomial {j : σ // j ∈ S} ℤ))
          (L := FractionRing (MvPolynomial σ ℤ))
          (j := (rename (R := ℤ) Subtype.val).toRingHom)
          (rename_injective Subtype.val Subtype.val_injective)) :=
  (X_mem_range_fractionRing_map_finset_iff (R := ℤ)
    (K := FractionRing (MvPolynomial σ ℤ)) S i).not.mpr hi

private theorem binary_stage_not_surjective {σ : Type u}
    (S : Finset σ) (i : σ) (hi : i ∉ S) :
    ¬ Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {j : σ // j ∈ S} (ZMod 2))
        (B := MvPolynomial σ (ZMod 2))
        (K := FractionRing (MvPolynomial {j : σ // j ∈ S} (ZMod 2)))
        (L := FractionRing (MvPolynomial σ (ZMod 2)))
        (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) :=
  not_surjective_fractionRing_map_finset_of_notMem (R := ZMod 2)
    (K := FractionRing (MvPolynomial σ (ZMod 2))) S i hi

private theorem integer_natural_stages_not_surjective :
    ∀ S : Finset ℕ, ¬ Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {j : ℕ // j ∈ S} ℤ) (B := P)
        (K := FractionRing (MvPolynomial {j : ℕ // j ∈ S} ℤ)) (L := F)
        (j := (rename (R := ℤ) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) :=
  not_surjective_fractionRing_map_finset_of_infinite (R := ℤ) (K := F)

private theorem binary_natural_stages_not_surjective :
    ∀ S : Finset ℕ, ¬ Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {j : ℕ // j ∈ S} (ZMod 2))
        (B := MvPolynomial ℕ (ZMod 2))
        (K := FractionRing (MvPolynomial {j : ℕ // j ∈ S} (ZMod 2)))
        (L := FractionRing (MvPolynomial ℕ (ZMod 2)))
        (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) :=
  not_surjective_fractionRing_map_finset_of_infinite (R := ZMod 2)
    (K := FractionRing (MvPolynomial ℕ (ZMod 2)))

private theorem binary_linear_denominator_ne_zero :
    algebraMap (MvPolynomial ℕ (ZMod 2)) (FractionRing (MvPolynomial ℕ (ZMod 2)))
      (X 1 + 1) ≠ 0 := by
  intro h
  have hp : (X 1 + 1 : MvPolynomial ℕ (ZMod 2)) = 0 :=
    IsFractionRing.injective (MvPolynomial ℕ (ZMod 2))
      (FractionRing (MvPolynomial ℕ (ZMod 2))) (by simpa only [map_zero] using h)
  have hc := congrArg (fun p : MvPolynomial ℕ (ZMod 2) => constantCoeff p) hp
  norm_num at hc

private theorem binary_fraction_family_common_origin :
    ∃ S : Finset ℕ,
      {algebraMap (MvPolynomial ℕ (ZMod 2)) (FractionRing (MvPolynomial ℕ (ZMod 2)))
          (X 0),
        1 / algebraMap (MvPolynomial ℕ (ZMod 2)) (FractionRing (MvPolynomial ℕ (ZMod 2)))
          (X 1 + 1), 0} ⊆ Set.range
        (IsFractionRing.map
          (A := MvPolynomial {j : ℕ // j ∈ S} (ZMod 2))
          (B := MvPolynomial ℕ (ZMod 2))
          (K := FractionRing (MvPolynomial {j : ℕ // j ∈ S} (ZMod 2)))
          (L := FractionRing (MvPolynomial ℕ (ZMod 2)))
          (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
          (rename_injective Subtype.val Subtype.val_injective)) := by
  exact exists_finset_fractionRing_map_range (R := ZMod 2) (σ := ℕ)
    (((Set.finite_singleton _).insert _).insert _)

private theorem even_index_variable_in_image (n : ℕ) :
    algebraMap P F (X (2 * n)) ∈ Set.range
      (IsFractionRing.map (A := P) (B := P) (K := F) (L := F)
        (j := (rename (R := ℤ) (fun m : ℕ => 2 * m)).toRingHom)
        (rename_injective _ (by
          intro a b h
          change 2 * a = 2 * b at h
          omega))) := by
  refine ⟨algebraMap P F (X n), ?_⟩
  simp [IsFractionRing.map]

private theorem odd_index_variable_not_in_image (n : ℕ) :
    algebraMap P F (X (2 * n + 1)) ∉ Set.range
      (IsFractionRing.map (A := P) (B := P) (K := F) (L := F)
        (j := (rename (R := ℤ) (fun m : ℕ => 2 * m)).toRingHom)
        (rename_injective _ (by
          intro a b h
          change 2 * a = 2 * b at h
          omega))) := by
  apply (X_mem_range_fractionRing_map_rename_iff (R := ℤ) (L := F) (K := F)
    (fun m : ℕ => 2 * m) (by
      intro a b h
      change 2 * a = 2 * b at h
      omega) (2 * n + 1)).not.mpr
  rintro ⟨m, hm⟩
  change 2 * m = 2 * n + 1 at hm
  omega

-- Both abstract realizations retain only the classes of the public statement.
private theorem abstract_fraction_rename_polynomial_and_fraction
    {R : Type uR} [CommRing R] [IsDomain R] {τ : Type uτ} {σ : Type uσ}
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
    [IsFractionRing (MvPolynomial τ R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K]
    (ρ : τ → σ) (hρ : Function.Injective ρ) (i : τ)
    (p : MvPolynomial τ R) (d : nonZeroDivisors (MvPolynomial τ R)) :
    let j := (rename (R := R) ρ).toRingHom
    let φ := IsFractionRing.map (A := MvPolynomial τ R) (B := MvPolynomial σ R)
      (K := L) (L := K) (j := j) (rename_injective ρ hρ)
    φ (algebraMap (MvPolynomial τ R) L (X i)) =
      algebraMap (MvPolynomial σ R) K (X (ρ i)) ∧
    φ (IsLocalization.mk' L p d) = IsLocalization.mk' K (j p)
      (⟨j d, (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j
        (rename_injective ρ hρ)) d.property⟩ : nonZeroDivisors (MvPolynomial σ R)) := by
  constructor
  · simp [IsFractionRing.map]
  · exact IsLocalization.map_mk' (Q := K)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
        (rename (R := R) ρ).toRingHom (rename_injective ρ hρ)) p d

private theorem abstract_fraction_rename_missing_variable
    {R : Type uR} [CommRing R] [IsDomain R] {τ : Type uτ} {σ : Type uσ}
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
    [IsFractionRing (MvPolynomial τ R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K]
    (ρ : τ → σ) (hρ : Function.Injective ρ) (i : σ) (hi : i ∉ Set.range ρ) :
    algebraMap (MvPolynomial σ R) K (X i) ∉ Set.range
      (IsFractionRing.map (A := MvPolynomial τ R) (B := MvPolynomial σ R)
        (K := L) (L := K) (j := (rename (R := R) ρ).toRingHom)
        (rename_injective ρ hρ)) :=
  (X_mem_range_fractionRing_map_rename_iff (R := R) (L := L) (K := K) ρ hρ i).not.mpr hi

private theorem lifted_even_index_variable_in_image (n : ℕ) :
    algebraMap (MvPolynomial (ULift.{v} ℕ) ℤ)
      (FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ)) (X (ULift.up (2 * n))) ∈
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial (ULift.{u} ℕ) ℤ) (B := MvPolynomial (ULift.{v} ℕ) ℤ)
          (K := FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ))
          (L := FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
          (j := (rename (R := ℤ)
            (fun m : ULift.{u} ℕ => (ULift.up (2 * m.down) : ULift.{v} ℕ))).toRingHom)
          (rename_injective _ (by
            intro a b h
            apply ULift.ext
            have hm := congrArg ULift.down h
            change 2 * a.down = 2 * b.down at hm
            omega))) := by
  refine ⟨algebraMap (MvPolynomial (ULift.{u} ℕ) ℤ)
    (FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ)) (X (ULift.up n)), ?_⟩
  simp [IsFractionRing.map]

private theorem lifted_odd_index_variable_not_in_image (n : ℕ) :
    algebraMap (MvPolynomial (ULift.{v} ℕ) ℤ)
      (FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ)) (X (ULift.up (2 * n + 1))) ∉
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial (ULift.{u} ℕ) ℤ) (B := MvPolynomial (ULift.{v} ℕ) ℤ)
          (K := FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ))
          (L := FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
          (j := (rename (R := ℤ)
            (fun m : ULift.{u} ℕ => (ULift.up (2 * m.down) : ULift.{v} ℕ))).toRingHom)
          (rename_injective _ (by
            intro a b h
            apply ULift.ext
            have hm := congrArg ULift.down h
            change 2 * a.down = 2 * b.down at hm
            omega))) := by
  apply (X_mem_range_fractionRing_map_rename_iff (R := ℤ)
    (L := FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ))
    (K := FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
    (fun m : ULift.{u} ℕ => (ULift.up (2 * m.down) : ULift.{v} ℕ))
    (by
      intro a b h
      apply ULift.ext
      have hm := congrArg ULift.down h
      change 2 * a.down = 2 * b.down at hm
      omega) (ULift.up (2 * n + 1))).not.mpr
  rintro ⟨m, hm⟩
  have hdown := congrArg ULift.down hm
  change 2 * m.down = 2 * n + 1 at hdown
  omega

private theorem integer_noninjective_rename_kernel :
    (X (0 : Fin 2) - X 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 ∧
    rename (fun _ : Fin 2 => ()) (X 0 - X 1 : MvPolynomial (Fin 2) ℤ) = 0 := by
  constructor
  · intro h
    have hvars := X_injective (sub_eq_zero.mp h)
    norm_num at hvars
  · simp

private theorem binary_noninjective_rename_kernel :
    (X (0 : Fin 2) - X 1 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 ∧
    rename (fun _ : Fin 2 => ()) (X 0 - X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
  constructor
  · intro h
    have hvars := X_injective (sub_eq_zero.mp h)
    norm_num at hvars
  · simp

private theorem integer_noninjective_rename_has_no_fraction_extension :
    ¬ ∃ f : FractionRing (MvPolynomial (Fin 2) ℤ) →+*
        FractionRing (MvPolynomial Unit ℤ),
      ∀ p, f (algebraMap (MvPolynomial (Fin 2) ℤ) _ p) =
        algebraMap (MvPolynomial Unit ℤ) _ (rename (fun _ : Fin 2 => ()) p) := by
  rintro ⟨f, hf⟩
  let p : MvPolynomial (Fin 2) ℤ := X 0 - X 1
  let d : nonZeroDivisors (MvPolynomial (Fin 2) ℤ) :=
    ⟨p, mem_nonZeroDivisors_iff_ne_zero.mpr integer_noninjective_rename_kernel.1⟩
  have hu := (IsLocalization.map_units (FractionRing (MvPolynomial (Fin 2) ℤ)) d).map f
  apply hu.ne_zero
  rw [hf p, integer_noninjective_rename_kernel.2, map_zero]

private theorem binary_noninjective_rename_has_no_fraction_extension :
    ¬ ∃ f : FractionRing (MvPolynomial (Fin 2) (ZMod 2)) →+*
        FractionRing (MvPolynomial Unit (ZMod 2)),
      ∀ p, f (algebraMap (MvPolynomial (Fin 2) (ZMod 2)) _ p) =
        algebraMap (MvPolynomial Unit (ZMod 2)) _ (rename (fun _ : Fin 2 => ()) p) := by
  rintro ⟨f, hf⟩
  let p : MvPolynomial (Fin 2) (ZMod 2) := X 0 - X 1
  let d : nonZeroDivisors (MvPolynomial (Fin 2) (ZMod 2)) :=
    ⟨p, mem_nonZeroDivisors_iff_ne_zero.mpr binary_noninjective_rename_kernel.1⟩
  have hu :=
    (IsLocalization.map_units (FractionRing (MvPolynomial (Fin 2) (ZMod 2))) d).map f
  apply hu.ne_zero
  rw [hf p, binary_noninjective_rename_kernel.2, map_zero]

private theorem zero_ring_variable_collapses :
    (X () : MvPolynomial Unit (ZMod 1)) = 0 ∧ ¬ IsDomain (ZMod 1) := by
  constructor
  · exact Subsingleton.elim _ _
  · intro h
    haveI := h
    exact one_ne_zero (Subsingleton.elim (1 : ZMod 1) 0)

private theorem composite_modulus_has_zero_divisors :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 ∧ ¬ IsDomain (ZMod 4) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  haveI := h
  have hz : (2 : ZMod 4) * 2 = 0 := by decide
  rcases mul_eq_zero.mp hz with htwo | htwo <;>
    exact (by decide : (2 : ZMod 4) ≠ 0) htwo

end MvPolynomialTests.FractionRingFiniteVariables
