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
    have := h
    exact one_ne_zero (Subsingleton.elim (1 : ZMod 1) 0)

private theorem composite_modulus_has_zero_divisors :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 ∧ ¬ IsDomain (ZMod 4) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have := h
  have hz : (2 : ZMod 4) * 2 = 0 := by decide
  rcases mul_eq_zero.mp hz with htwo | htwo <;>
    exact (by decide : (2 : ZMod 4) ≠ 0) htwo

end MvPolynomialTests.FractionRingFiniteVariables

namespace MvPolynomialTests.FractionRingFiniteVariables

open MvPolynomial

local notation "P" => MvPolynomial ℕ ℤ
local notation "F" => FractionRing P

-- Swapping two variables sends a nonconstant ratio to the opposite ratio.
private theorem integer_fin_two_swap_controls :
    let e := Equiv.swap (0 : Fin 2) 1
    let φ := IsFractionRing.map
      (A := MvPolynomial (Fin 2) ℤ) (B := MvPolynomial (Fin 2) ℤ)
      (K := FractionRing (MvPolynomial (Fin 2) ℤ))
      (L := FractionRing (MvPolynomial (Fin 2) ℤ))
      (j := (rename (R := ℤ) e).toRingHom) (rename_injective e e.injective)
    Function.Injective e ∧ Function.Surjective e ∧ Function.Surjective φ ∧
      (X (0 : Fin 2) + 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 ∧
      (X (1 : Fin 2) + 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 ∧
      φ (algebraMap (MvPolynomial (Fin 2) ℤ)
          (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 0 + 1) /
          algebraMap (MvPolynomial (Fin 2) ℤ)
            (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 1 + 1)) =
        algebraMap (MvPolynomial (Fin 2) ℤ)
            (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 1 + 1) /
          algebraMap (MvPolynomial (Fin 2) ℤ)
            (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 0 + 1) ∧
      ∀ a b : ℤ, b ≠ 0 → algebraMap (MvPolynomial (Fin 2) ℤ)
          (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 0 + 1) /
          algebraMap (MvPolynomial (Fin 2) ℤ)
            (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 1 + 1) ≠
          algebraMap (MvPolynomial (Fin 2) ℤ)
              (FractionRing (MvPolynomial (Fin 2) ℤ)) (C a) /
            algebraMap (MvPolynomial (Fin 2) ℤ)
              (FractionRing (MvPolynomial (Fin 2) ℤ)) (C b) := by
  dsimp only
  let e := Equiv.swap (0 : Fin 2) 1
  have h₀ : (X (0 : Fin 2) + 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff : MvPolynomial (Fin 2) ℤ → ℤ) h
    norm_num at hc
  have h₁ : (X (1 : Fin 2) + 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff : MvPolynomial (Fin 2) ℤ → ℤ) h
    norm_num at hc
  refine ⟨e.injective, e.surjective, ?_, h₀, h₁, ?_, ?_⟩
  · exact (IsFractionRing.ringEquivOfRingEquiv
      (K := FractionRing (MvPolynomial (Fin 2) ℤ))
      (L := FractionRing (MvPolynomial (Fin 2) ℤ))
      (renameEquiv ℤ e).toRingEquiv).surjective
  · simp [IsFractionRing.map, map_div₀]
  · intro a b hb h
    have hd : algebraMap (MvPolynomial (Fin 2) ℤ)
        (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 1 + 1) ≠ 0 := by
      intro hz
      exact h₁ (IsFractionRing.injective (MvPolynomial (Fin 2) ℤ)
        (FractionRing (MvPolynomial (Fin 2) ℤ)) (by simpa only [map_zero] using hz))
    have hbpoly : (C b : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
      intro hz
      exact hb (by simpa using congrArg constantCoeff hz)
    have hbf : algebraMap (MvPolynomial (Fin 2) ℤ)
        (FractionRing (MvPolynomial (Fin 2) ℤ)) (C b) ≠ 0 := by
      intro hz
      exact hbpoly (IsFractionRing.injective (MvPolynomial (Fin 2) ℤ)
        (FractionRing (MvPolynomial (Fin 2) ℤ)) (by simpa only [map_zero] using hz))
    have hm := (div_eq_div_iff hd hbf).mp h
    have hp : (X 0 + 1 : MvPolynomial (Fin 2) ℤ) * C b = C a * (X 1 + 1) :=
      IsFractionRing.injective (MvPolynomial (Fin 2) ℤ)
        (FractionRing (MvPolynomial (Fin 2) ℤ)) (by simpa only [map_mul] using hm)
    have hz := congrArg (eval₂Hom (RingHom.id ℤ) (fun _ : Fin 2 => (0 : ℤ))) hp
    have ho := congrArg (eval₂Hom (RingHom.id ℤ)
      (fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0)) hp
    norm_num at hz ho
    omega

-- A full two-variable stage contains fractions with a variable denominator.
private theorem full_fin_two_integer_fraction_controls :
    let S := (Finset.univ : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} ℤ) (B := MvPolynomial (Fin 2) ℤ)
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} ℤ))
      (L := FractionRing (MvPolynomial (Fin 2) ℤ))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    (∀ i : Fin 2, i ∈ S) ∧
      Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      Function.Surjective φ ∧ (X (1 : Fin 2) + 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 ∧
      ∃ z : FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} ℤ),
        φ z = 1 / algebraMap (MvPolynomial (Fin 2) ℤ)
          (FractionRing (MvPolynomial (Fin 2) ℤ)) (X 1 + 1) := by
  refine ⟨Finset.mem_univ, ?_, full_integer_stage_surjective, ?_, ?_⟩
  · intro i
    exact ⟨⟨i, Finset.mem_univ i⟩, rfl⟩
  · intro h
    have hc := congrArg (constantCoeff : MvPolynomial (Fin 2) ℤ → ℤ) h
    norm_num at hc
  · exact full_integer_stage_surjective _

private theorem full_fin_two_binary_fraction_controls :
    let S := (Finset.univ : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2))
      (B := MvPolynomial (Fin 2) (ZMod 2))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2)))
      (L := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
      (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    (∀ i : Fin 2, i ∈ S) ∧
      Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      Function.Surjective φ ∧
      (X (1 : Fin 2) + 1 : MvPolynomial (Fin 2) (ZMod 2)) ≠ 0 ∧
      ∃ z : FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2)),
        φ z = 1 / algebraMap (MvPolynomial (Fin 2) (ZMod 2))
          (FractionRing (MvPolynomial (Fin 2) (ZMod 2))) (X 1 + 1) := by
  refine ⟨Finset.mem_univ, ?_, full_binary_stage_surjective, ?_, ?_⟩
  · intro i
    exact ⟨⟨i, Finset.mem_univ i⟩, rfl⟩
  · intro h
    have hc := congrArg (constantCoeff : MvPolynomial (Fin 2) (ZMod 2) → ZMod 2) h
    norm_num at hc
  · exact full_binary_stage_surjective _

-- Empty variables still leave a nonzero coefficient fraction different from one.
private theorem empty_integer_half_controls :
    let Q := FractionRing (MvPolynomial Empty ℤ)
    let φ := IsFractionRing.map
      (A := MvPolynomial Empty ℤ) (B := MvPolynomial Empty ℤ) (K := Q) (L := Q)
      (j := (rename (R := ℤ) (Equiv.refl Empty)).toRingHom)
      (rename_injective _ (Equiv.refl Empty).injective)
    Function.Surjective (Equiv.refl Empty) ∧ Function.Surjective φ ∧
      (1 / 2 : Q) ≠ 0 ∧ (1 / 2 : Q) ≠ 1 ∧ φ (1 / 2) = 1 / 2 := by
  dsimp only
  let Q := FractionRing (MvPolynomial Empty ℤ)
  have htwo : (2 : Q) ≠ 0 := by
    intro h
    exact integerPolynomial_two_ne_zero
      (IsFractionRing.injective (MvPolynomial Empty ℤ) Q
        (by simpa only [map_ofNat, map_zero] using h))
  refine ⟨(Equiv.refl Empty).surjective, ?_, div_ne_zero one_ne_zero htwo, ?_, ?_⟩
  · exact (IsFractionRing.ringEquivOfRingEquiv
      (K := Q) (L := Q) (renameEquiv ℤ (Equiv.refl Empty)).toRingEquiv).surjective
  · intro h
    have hm := (div_eq_iff htwo).mp h
    have hp : (1 : MvPolynomial Empty ℤ) = 2 :=
      IsFractionRing.injective _ Q (by simpa only [one_mul, map_one, map_ofNat] using hm)
    have hc : (1 : ℤ) = 2 := by
      simpa only [map_one, map_ofNat] using
        congrArg (constantCoeff : MvPolynomial Empty ℤ → ℤ) hp
    norm_num at hc
  · simp only [map_div₀, map_one, map_ofNat]

private theorem empty_ambient_half_origin :
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ)
      (B := MvPolynomial Empty ℤ)
      (K := FractionRing (MvPolynomial {i : Empty // i ∈ (∅ : Finset Empty)} ℤ))
      (L := FractionRing (MvPolynomial Empty ℤ))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    (∀ i : Empty, i ∈ (∅ : Finset Empty)) ∧
      Function.Surjective (Subtype.val : {i : Empty // i ∈ (∅ : Finset Empty)} → Empty) ∧
      Function.Surjective φ ∧
      φ (1 / 2) = (1 / 2 : FractionRing (MvPolynomial Empty ℤ)) := by
  refine ⟨(fun i => i.elim), (fun i => i.elim), empty_ambient_stage_surjective, ?_⟩
  simp only [map_div₀, map_one, map_ofNat]

-- A proper coefficient stage has a half-fraction origin but misses the variable.
private theorem unit_integer_half_nontrivial :
    (1 / 2 : FractionRing (MvPolynomial Unit ℤ)) ≠ 0 ∧
      (1 / 2 : FractionRing (MvPolynomial Unit ℤ)) ≠ 1 := by
  let Q := FractionRing (MvPolynomial Unit ℤ)
  have htwo : (2 : Q) ≠ 0 := by
    intro h
    exact integerPolynomial_two_ne_zero
      (IsFractionRing.injective (MvPolynomial Unit ℤ) Q
        (by simpa only [map_ofNat, map_zero] using h))
  refine ⟨div_ne_zero one_ne_zero htwo, ?_⟩
  intro h
  have hm := (div_eq_iff htwo).mp h
  have hp : (1 : MvPolynomial Unit ℤ) = 2 :=
    IsFractionRing.injective _ Q (by simpa only [one_mul, map_one, map_ofNat] using hm)
  have hc : (1 : ℤ) = 2 := by
    simpa only [map_one, map_ofNat] using
      congrArg (constantCoeff : MvPolynomial Unit ℤ → ℤ) hp
  norm_num at hc

private theorem empty_to_unit_half_and_missing_variable :
    let φ := IsFractionRing.map
      (A := MvPolynomial Empty ℤ) (B := MvPolynomial Unit ℤ)
      (K := FractionRing (MvPolynomial Empty ℤ))
      (L := FractionRing (MvPolynomial Unit ℤ))
      (j := (rename (R := ℤ) Empty.elim).toRingHom)
      (rename_injective Empty.elim (by intro a; exact a.elim))
    ¬ Function.Surjective (Empty.elim : Empty → Unit) ∧ ¬ Function.Surjective φ ∧
      algebraMap (MvPolynomial Unit ℤ) (FractionRing (MvPolynomial Unit ℤ)) (X ()) ∉
        Set.range φ ∧ φ (1 / 2) = (1 / 2 : FractionRing (MvPolynomial Unit ℤ)) := by
  refine ⟨?_, ?_, empty_integer_source_excludes_variable, ?_⟩
  · intro h
    obtain ⟨a, _⟩ := h ()
    exact a.elim
  · intro h
    exact empty_integer_source_excludes_variable (h _)
  · simp only [map_div₀, map_one, map_ofNat]

private theorem empty_unit_stage_half_and_missing_variable :
    let S := (∅ : Finset Unit)
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Unit // i ∈ S} ℤ) (B := MvPolynomial Unit ℤ)
      (K := FractionRing (MvPolynomial {i : Unit // i ∈ S} ℤ))
      (L := FractionRing (MvPolynomial Unit ℤ))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    ¬ (∀ i : Unit, i ∈ S) ∧
      ¬ Function.Surjective (Subtype.val : {i : Unit // i ∈ S} → Unit) ∧
      ¬ Function.Surjective φ ∧
      algebraMap (MvPolynomial Unit ℤ) (FractionRing (MvPolynomial Unit ℤ)) (X ()) ∉
        Set.range φ ∧ φ (1 / 2) = (1 / 2 : FractionRing (MvPolynomial Unit ℤ)) := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · rintro h
    obtain ⟨a, _⟩ := h ()
    have ha : a.val ∈ (∅ : Finset Unit) := a.property
    exact (Finset.notMem_empty a.val) ha
  · exact not_surjective_fractionRing_map_finset_of_notMem (R := ℤ)
      (K := FractionRing (MvPolynomial Unit ℤ)) ∅ () (by simp)
  · exact integer_stage_excludes_missing_variable ∅ () (by simp)
  · simp only [map_div₀, map_one, map_ofNat]

-- In the singleton stage the first variable is present and the second is absent.
private theorem fin_two_singleton_controls
    {R : Type uR} [CommRing R] [IsDomain R] :
    let S := ({0} : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} R) (B := MvPolynomial (Fin 2) R)
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} R))
      (L := FractionRing (MvPolynomial (Fin 2) R))
      (j := (rename (R := R) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    algebraMap (MvPolynomial (Fin 2) R) (FractionRing (MvPolynomial (Fin 2) R)) (X 0) ∈
        Set.range φ ∧
      algebraMap (MvPolynomial (Fin 2) R) (FractionRing (MvPolynomial (Fin 2) R)) (X 1) ∉
        Set.range φ ∧ ¬ (∀ i : Fin 2, i ∈ S) ∧
      ¬ Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      ¬ Function.Surjective φ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (X_mem_range_fractionRing_map_finset_iff (R := R)
      (K := FractionRing (MvPolynomial (Fin 2) R)) {0} 0).mpr (by simp)
  · exact (X_mem_range_fractionRing_map_finset_iff (R := R)
      (K := FractionRing (MvPolynomial (Fin 2) R)) {0} 1).not.mpr (by simp)
  · intro h
    have := h 1
    simp at this
  · intro h
    obtain ⟨a, ha⟩ := h 1
    have haS : a.val ∈ ({0} : Finset (Fin 2)) := a.property
    have ha₀ : a.val = (0 : Fin 2) := Finset.mem_singleton.mp haS
    have : (1 : Fin 2) = 0 := ha.symm.trans ha₀
    norm_num at this
  · exact not_surjective_fractionRing_map_finset_of_notMem (R := R)
      (K := FractionRing (MvPolynomial (Fin 2) R)) {0} 1 (by simp)

-- Even indices have origins; odd indices prevent surjectivity on either side.
private theorem even_rename_controls :
    let ρ := fun n : ℕ => 2 * n
    let hρ : Function.Injective ρ := by
      intro a b h
      change 2 * a = 2 * b at h
      omega
    let φ := IsFractionRing.map (A := P) (B := P) (K := F) (L := F)
      (j := (rename (R := ℤ) ρ).toRingHom) (rename_injective ρ hρ)
    Function.Injective ρ ∧ ¬ Function.Surjective ρ ∧ ¬ Function.Surjective φ ∧
      ∀ n, algebraMap P F (X (2 * n)) ∈ Set.range φ ∧
        algebraMap P F (X (2 * n + 1)) ∉ Set.range φ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    change 2 * a = 2 * b at h
    omega
  · intro h
    obtain ⟨n, hn⟩ := h 1
    change 2 * n = 1 at hn
    omega
  · intro h
    exact odd_index_variable_not_in_image 0 (h _)
  · intro n
    exact ⟨even_index_variable_in_image n, odd_index_variable_not_in_image n⟩

-- The same permutation works between independent lifts and arbitrary realizations.
private theorem lifted_fin_two_swap_controls
    {R : Type uR} [CommRing R] [IsDomain R]
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial (ULift.{uτ} (Fin 2)) R) L]
    [IsFractionRing (MvPolynomial (ULift.{uτ} (Fin 2)) R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial (ULift.{uσ} (Fin 2)) R) K]
    [IsFractionRing (MvPolynomial (ULift.{uσ} (Fin 2)) R) K] :
    let e : ULift.{uτ} (Fin 2) ≃ ULift.{uσ} (Fin 2) :=
      (Equiv.ulift.trans (Equiv.swap 0 1)).trans Equiv.ulift.symm
    let j := (rename (R := R) e).toRingHom
    let φ := IsFractionRing.map
      (A := MvPolynomial (ULift.{uτ} (Fin 2)) R)
      (B := MvPolynomial (ULift.{uσ} (Fin 2)) R)
      (K := L) (L := K) (j := j) (rename_injective e e.injective)
    Function.Injective e ∧ Function.Surjective e ∧ Function.Surjective φ ∧
      (∀ r : R, (X (ULift.up (0 : Fin 2)) + 1 :
          MvPolynomial (ULift.{uτ} (Fin 2)) R) ≠ C r) ∧
      ∃ d : nonZeroDivisors (MvPolynomial (ULift.{uτ} (Fin 2)) R),
        (d : MvPolynomial (ULift.{uτ} (Fin 2)) R) = X (ULift.up (1 : Fin 2)) + 1 ∧
        j d = X (ULift.up (0 : Fin 2)) + 1 ∧
        φ (algebraMap (MvPolynomial (ULift.{uτ} (Fin 2)) R) L
            (X (ULift.up (0 : Fin 2)) + 1)) =
          algebraMap (MvPolynomial (ULift.{uσ} (Fin 2)) R) K
            (X (ULift.up (1 : Fin 2)) + 1) ∧
        φ (IsLocalization.mk' L (X (ULift.up (0 : Fin 2)) + 1) d) =
          IsLocalization.mk' K (X (ULift.up (1 : Fin 2)) + 1)
            (⟨j d, (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j
              (rename_injective e e.injective)) d.property⟩ :
                nonZeroDivisors (MvPolynomial (ULift.{uσ} (Fin 2)) R)) ∧
        ∀ a b : R, ∀ c : nonZeroDivisors (MvPolynomial (ULift.{uτ} (Fin 2)) R),
          (c : MvPolynomial (ULift.{uτ} (Fin 2)) R) = C b →
          IsLocalization.mk' L (X (ULift.up (0 : Fin 2)) + 1) d ≠
            IsLocalization.mk' L (C a) c := by
  classical
  dsimp only
  let e : ULift.{uτ} (Fin 2) ≃ ULift.{uσ} (Fin 2) :=
    (Equiv.ulift.trans (Equiv.swap 0 1)).trans Equiv.ulift.symm
  let j := (rename (R := R) e).toRingHom
  have hd : (X (ULift.up (1 : Fin 2)) + 1 :
      MvPolynomial (ULift.{uτ} (Fin 2)) R) ≠ 0 := by
    intro h
    have hc := congrArg
      (constantCoeff : MvPolynomial (ULift.{uτ} (Fin 2)) R → R) h
    simp at hc
  let d : nonZeroDivisors (MvPolynomial (ULift.{uτ} (Fin 2)) R) :=
    ⟨X (ULift.up (1 : Fin 2)) + 1, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩
  refine ⟨e.injective, e.surjective, ?_, ?_, d, rfl, ?_, ?_, ?_, ?_⟩
  · exact (IsFractionRing.ringEquivOfRingEquiv
      (K := L) (L := K) (renameEquiv R e).toRingEquiv).surjective
  · intro r h
    have h₀ := congrArg (eval₂Hom (RingHom.id R)
      (fun _ : ULift.{uτ} (Fin 2) => (0 : R))) h
    have h₁ := congrArg (eval₂Hom (RingHom.id R)
      (fun i : ULift.{uτ} (Fin 2) => if i.down = 0 then (1 : R) else 0)) h
    have h₀ : (1 : R) = r := by simpa using h₀
    have h₁ : (1 : R) + 1 = r := by simpa using h₁
    have hz : (1 : R) = 0 := by linear_combination h₁ - h₀
    exact one_ne_zero hz
  · simp [d]
  · simp [IsFractionRing.map]
  · have hm := (abstract_fraction_rename_polynomial_and_fraction
      (R := R) (L := L) (K := K) e e.injective (ULift.up (0 : Fin 2))
      (X (ULift.up (0 : Fin 2)) + 1) d).2
    simpa [e, j] using hm
  · intro a b c hc h
    have hb : b ≠ 0 := by
      intro hz
      simp [hz] at hc
    have hm := IsLocalization.mk'_eq_iff_eq'.mp h
    have hp : (X (ULift.up (0 : Fin 2)) + 1 :
        MvPolynomial (ULift.{uτ} (Fin 2)) R) * C b =
          C a * (X (ULift.up (1 : Fin 2)) + 1) :=
      IsFractionRing.injective _ L (by simpa [hc, d] using hm)
    have h₀ := congrArg (eval₂Hom (RingHom.id R)
      (fun _ : ULift.{uτ} (Fin 2) => (0 : R))) hp
    have h₁ := congrArg (eval₂Hom (RingHom.id R)
      (fun i : ULift.{uτ} (Fin 2) => if i.down = 0 then (1 : R) else 0)) hp
    have h₀ : b = a := by simpa using h₀
    have h₁ : b + b = a := by simpa [add_mul] using h₁
    have hz : b = 0 := by linear_combination h₁ - h₀
    exact hb hz

private theorem lifted_even_rename_controls :
    let ρ := fun n : ULift.{u} ℕ => (ULift.up (2 * n.down) : ULift.{v} ℕ)
    let hρ : Function.Injective ρ := by
      intro a b h
      apply ULift.ext
      have hm := congrArg ULift.down h
      change 2 * a.down = 2 * b.down at hm
      omega
    let φ := IsFractionRing.map
      (A := MvPolynomial (ULift.{u} ℕ) ℤ) (B := MvPolynomial (ULift.{v} ℕ) ℤ)
      (K := FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ))
      (L := FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
      (j := (rename (R := ℤ) ρ).toRingHom) (rename_injective ρ hρ)
    Function.Injective ρ ∧ ¬ Function.Surjective ρ ∧ ¬ Function.Surjective φ ∧
      ∀ n : ℕ, algebraMap (MvPolynomial (ULift.{v} ℕ) ℤ)
          (FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
          (X (ULift.up (2 * n))) ∈ Set.range φ ∧
        algebraMap (MvPolynomial (ULift.{v} ℕ) ℤ)
          (FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
          (X (ULift.up (2 * n + 1))) ∉ Set.range φ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    apply ULift.ext
    have hm := congrArg ULift.down h
    change 2 * a.down = 2 * b.down at hm
    omega
  · intro h
    obtain ⟨n, hn⟩ := h (ULift.up 1)
    have hm := congrArg ULift.down hn
    change 2 * n.down = 1 at hm
    omega
  · intro h
    exact lifted_odd_index_variable_not_in_image 0 (h _)
  · intro n
    exact ⟨lifted_even_index_variable_in_image n, lifted_odd_index_variable_not_in_image n⟩

example :
    let S := ({0} : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ℤ))
      (B := MvPolynomial (Fin 2) (ℤ))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ℤ)))
      (L := FractionRing (MvPolynomial (Fin 2) (ℤ)))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    algebraMap (MvPolynomial (Fin 2) (ℤ))
        (FractionRing (MvPolynomial (Fin 2) (ℤ))) (X 0) ∈ Set.range φ ∧
      algebraMap (MvPolynomial (Fin 2) (ℤ))
        (FractionRing (MvPolynomial (Fin 2) (ℤ))) (X 1) ∉ Set.range φ ∧
      ¬ Function.Surjective φ := by
  have h := fin_two_singleton_controls (R := ℤ)
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

example :
    let S := ({0} : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2))
      (B := MvPolynomial (Fin 2) (ZMod 2))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2)))
      (L := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
      (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    algebraMap (MvPolynomial (Fin 2) (ZMod 2))
        (FractionRing (MvPolynomial (Fin 2) (ZMod 2))) (X 0) ∈ Set.range φ ∧
      algebraMap (MvPolynomial (Fin 2) (ZMod 2))
        (FractionRing (MvPolynomial (Fin 2) (ZMod 2))) (X 1) ∉ Set.range φ ∧
      ¬ Function.Surjective φ := by
  have h := fin_two_singleton_controls (R := ZMod 2)
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

-- Canonical fraction rings inhabit the independent-universe permutation example.
example :
    let e : ULift.{u} (Fin 2) ≃ ULift.{v} (Fin 2) :=
      (Equiv.ulift.trans (Equiv.swap 0 1)).trans Equiv.ulift.symm
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial (ULift.{u} (Fin 2)) ℤ)
        (B := MvPolynomial (ULift.{v} (Fin 2)) ℤ)
        (K := FractionRing (MvPolynomial (ULift.{u} (Fin 2)) ℤ))
        (L := FractionRing (MvPolynomial (ULift.{v} (Fin 2)) ℤ))
        (j := (rename (R := ℤ) e).toRingHom) (rename_injective e e.injective)) := by
  exact (lifted_fin_two_swap_controls
    (R := ℤ) (L := FractionRing (MvPolynomial (ULift.{u} (Fin 2)) ℤ))
    (K := FractionRing (MvPolynomial (ULift.{v} (Fin 2)) ℤ))).2.2.1

-- The characteristic criteria apply to these permutations and finite stages.
example :
    let e := Equiv.swap (0 : Fin 2) 1
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial (Fin 2) ℤ) (B := MvPolynomial (Fin 2) ℤ)
        (K := FractionRing (MvPolynomial (Fin 2) ℤ))
        (L := FractionRing (MvPolynomial (Fin 2) ℤ))
        (j := (rename (R := ℤ) e).toRingHom) (rename_injective e e.injective)) := by
  exact (surjective_fractionRing_map_rename_iff
    (R := ℤ) (L := FractionRing (MvPolynomial (Fin 2) ℤ))
    (K := FractionRing (MvPolynomial (Fin 2) ℤ))
    (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1).injective).mpr
      (Equiv.swap (0 : Fin 2) 1).surjective

example :
    let S := (Finset.univ : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ℤ))
      (B := MvPolynomial (Fin 2) (ℤ))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ℤ)))
      (L := FractionRing (MvPolynomial (Fin 2) (ℤ)))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    Function.Surjective φ ∧
      Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      (∀ i : Fin 2, i ∈ S) := by
  have hmem : ∀ i : Fin 2, i ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ
  refine ⟨(surjective_fractionRing_map_finset_iff (R := ℤ)
    (K := FractionRing (MvPolynomial (Fin 2) (ℤ))) Finset.univ).mpr hmem, ?_, hmem⟩
  exact (surjective_fractionRing_map_rename_iff (R := ℤ)
    (L := FractionRing (MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} (ℤ)))
    (K := FractionRing (MvPolynomial (Fin 2) (ℤ)))
    (Subtype.val : {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} → Fin 2)
    Subtype.val_injective).mp full_integer_stage_surjective

example :
    let S := (Finset.univ : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2))
      (B := MvPolynomial (Fin 2) (ZMod 2))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2)))
      (L := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
      (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    Function.Surjective φ ∧
      Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      (∀ i : Fin 2, i ∈ S) := by
  have hmem : ∀ i : Fin 2, i ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ
  refine ⟨(surjective_fractionRing_map_finset_iff (R := ZMod 2)
    (K := FractionRing (MvPolynomial (Fin 2) (ZMod 2))) Finset.univ).mpr hmem, ?_, hmem⟩
  exact (surjective_fractionRing_map_rename_iff (R := ZMod 2)
    (L := FractionRing (MvPolynomial {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} (ZMod 2)))
    (K := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
    (Subtype.val : {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} → Fin 2)
    Subtype.val_injective).mp full_binary_stage_surjective

example :
    let S := (∅ : Finset (Empty))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Empty // i ∈ S} (ℤ))
      (B := MvPolynomial (Empty) (ℤ))
      (K := FractionRing (MvPolynomial {i : Empty // i ∈ S} (ℤ)))
      (L := FractionRing (MvPolynomial (Empty) (ℤ)))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    Function.Surjective φ ∧
      Function.Surjective (Subtype.val : {i : Empty // i ∈ S} → Empty) ∧
      (∀ i : Empty, i ∈ S) := by
  have hmem : ∀ i : Empty, i ∈ (∅ : Finset (Empty)) := (fun i => i.elim)
  refine ⟨(surjective_fractionRing_map_finset_iff (R := ℤ)
    (K := FractionRing (MvPolynomial (Empty) (ℤ))) ∅).mpr hmem, ?_, hmem⟩
  exact (surjective_fractionRing_map_rename_iff (R := ℤ)
    (L := FractionRing (MvPolynomial {i : Empty // i ∈ (∅ : Finset (Empty))} (ℤ)))
    (K := FractionRing (MvPolynomial (Empty) (ℤ)))
    (Subtype.val : {i : Empty // i ∈ (∅ : Finset (Empty))} → Empty)
    Subtype.val_injective).mp empty_ambient_stage_surjective

example : Function.Surjective
    (IsFractionRing.map
      (A := MvPolynomial Empty ℤ) (B := MvPolynomial Empty ℤ)
      (K := FractionRing (MvPolynomial Empty ℤ))
      (L := FractionRing (MvPolynomial Empty ℤ))
      (j := (rename (R := ℤ) (Equiv.refl Empty)).toRingHom)
      (rename_injective _ (Equiv.refl Empty).injective)) := by
  exact (surjective_fractionRing_map_rename_iff
    (R := ℤ) (L := FractionRing (MvPolynomial Empty ℤ))
    (K := FractionRing (MvPolynomial Empty ℤ)) (Equiv.refl Empty)
    (Equiv.refl Empty).injective).mpr (Equiv.refl Empty).surjective

example : ¬ Function.Surjective
    (IsFractionRing.map
      (A := MvPolynomial Empty ℤ) (B := MvPolynomial Unit ℤ)
      (K := FractionRing (MvPolynomial Empty ℤ))
      (L := FractionRing (MvPolynomial Unit ℤ))
      (j := (rename (R := ℤ) Empty.elim).toRingHom)
      (rename_injective Empty.elim (by intro a; exact a.elim))) := by
  apply (surjective_fractionRing_map_rename_iff
    (R := ℤ) (L := FractionRing (MvPolynomial Empty ℤ))
    (K := FractionRing (MvPolynomial Unit ℤ))
    Empty.elim (by intro a; exact a.elim)).not.mpr
  exact empty_to_unit_half_and_missing_variable.1

example :
    let S := (∅ : Finset (Unit))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Unit // i ∈ S} (ℤ))
      (B := MvPolynomial (Unit) (ℤ))
      (K := FractionRing (MvPolynomial {i : Unit // i ∈ S} (ℤ)))
      (L := FractionRing (MvPolynomial (Unit) (ℤ)))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    ¬ Function.Surjective φ ∧
      ¬ Function.Surjective (Subtype.val : {i : Unit // i ∈ S} → Unit) ∧
      ¬ (∀ i : Unit, i ∈ S) := by
  have hmem : ¬ ∀ i : Unit, i ∈ (∅ : Finset (Unit)) := by
    intro h
    have := h ()
    simp at this
  have hmap := (surjective_fractionRing_map_finset_iff (R := ℤ)
    (K := FractionRing (MvPolynomial (Unit) (ℤ))) ∅).not.mpr hmem
  refine ⟨hmap, ?_, hmem⟩
  exact (surjective_fractionRing_map_rename_iff (R := ℤ)
    (L := FractionRing (MvPolynomial {i : Unit // i ∈ (∅ : Finset (Unit))} (ℤ)))
    (K := FractionRing (MvPolynomial (Unit) (ℤ)))
    (Subtype.val : {i : Unit // i ∈ (∅ : Finset (Unit))} → Unit)
    Subtype.val_injective).not.mp hmap

example :
    let S := ({0} : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ℤ))
      (B := MvPolynomial (Fin 2) (ℤ))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ℤ)))
      (L := FractionRing (MvPolynomial (Fin 2) (ℤ)))
      (j := (rename (R := ℤ) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    ¬ Function.Surjective φ ∧
      ¬ Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      ¬ (∀ i : Fin 2, i ∈ S) := by
  have hmem : ¬ ∀ i : Fin 2, i ∈ ({0} : Finset (Fin 2)) := by
    intro h
    have := h 1
    simp at this
  have hmap := (surjective_fractionRing_map_finset_iff (R := ℤ)
    (K := FractionRing (MvPolynomial (Fin 2) (ℤ))) {0}).not.mpr hmem
  refine ⟨hmap, ?_, hmem⟩
  exact (surjective_fractionRing_map_rename_iff (R := ℤ)
    (L := FractionRing (MvPolynomial {i : Fin 2 // i ∈ ({0} : Finset (Fin 2))} (ℤ)))
    (K := FractionRing (MvPolynomial (Fin 2) (ℤ)))
    (Subtype.val : {i : Fin 2 // i ∈ ({0} : Finset (Fin 2))} → Fin 2)
    Subtype.val_injective).not.mp hmap

example :
    let S := ({0} : Finset (Fin 2))
    let φ := IsFractionRing.map
      (A := MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2))
      (B := MvPolynomial (Fin 2) (ZMod 2))
      (K := FractionRing (MvPolynomial {i : Fin 2 // i ∈ S} (ZMod 2)))
      (L := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
      (j := (rename (R := ZMod 2) Subtype.val).toRingHom)
      (rename_injective Subtype.val Subtype.val_injective)
    ¬ Function.Surjective φ ∧
      ¬ Function.Surjective (Subtype.val : {i : Fin 2 // i ∈ S} → Fin 2) ∧
      ¬ (∀ i : Fin 2, i ∈ S) := by
  have hmem : ¬ ∀ i : Fin 2, i ∈ ({0} : Finset (Fin 2)) := by
    intro h
    have := h 1
    simp at this
  have hmap := (surjective_fractionRing_map_finset_iff (R := ZMod 2)
    (K := FractionRing (MvPolynomial (Fin 2) (ZMod 2))) {0}).not.mpr hmem
  refine ⟨hmap, ?_, hmem⟩
  exact (surjective_fractionRing_map_rename_iff (R := ZMod 2)
    (L := FractionRing (MvPolynomial {i : Fin 2 // i ∈ ({0} : Finset (Fin 2))} (ZMod 2)))
    (K := FractionRing (MvPolynomial (Fin 2) (ZMod 2)))
    (Subtype.val : {i : Fin 2 // i ∈ ({0} : Finset (Fin 2))} → Fin 2)
    Subtype.val_injective).not.mp hmap

example :
    let ρ := fun n : ℕ => 2 * n
    let hρ : Function.Injective ρ := by
      intro a b h
      change 2 * a = 2 * b at h
      omega
    ¬ Function.Surjective
      (IsFractionRing.map (A := P) (B := P) (K := F) (L := F)
        (j := (rename (R := ℤ) ρ).toRingHom) (rename_injective ρ hρ)) := by
  apply (surjective_fractionRing_map_rename_iff (R := ℤ) (L := F) (K := F)
    (fun n : ℕ => 2 * n) (by intro a b h; change 2 * a = 2 * b at h; omega)).not.mpr
  exact even_rename_controls.2.1

example
    {R : Type uR} [CommRing R] [IsDomain R]
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial (ULift.{uτ} (Fin 2)) R) L]
    [IsFractionRing (MvPolynomial (ULift.{uτ} (Fin 2)) R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial (ULift.{uσ} (Fin 2)) R) K]
    [IsFractionRing (MvPolynomial (ULift.{uσ} (Fin 2)) R) K] :
    let e : ULift.{uτ} (Fin 2) ≃ ULift.{uσ} (Fin 2) :=
      (Equiv.ulift.trans (Equiv.swap 0 1)).trans Equiv.ulift.symm
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial (ULift.{uτ} (Fin 2)) R)
        (B := MvPolynomial (ULift.{uσ} (Fin 2)) R)
        (K := L) (L := K) (j := (rename (R := R) e).toRingHom)
        (rename_injective e e.injective)) := by
  let e : ULift.{uτ} (Fin 2) ≃ ULift.{uσ} (Fin 2) :=
    (Equiv.ulift.trans (Equiv.swap 0 1)).trans Equiv.ulift.symm
  exact (surjective_fractionRing_map_rename_iff (R := R) (L := L) (K := K)
    e e.injective).mpr e.surjective

example :
    let ρ := fun n : ULift.{u} ℕ => (ULift.up (2 * n.down) : ULift.{v} ℕ)
    let hρ : Function.Injective ρ := by
      intro a b h
      apply ULift.ext
      have hm := congrArg ULift.down h
      change 2 * a.down = 2 * b.down at hm
      omega
    ¬ Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial (ULift.{u} ℕ) ℤ) (B := MvPolynomial (ULift.{v} ℕ) ℤ)
        (K := FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ))
        (L := FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
        (j := (rename (R := ℤ) ρ).toRingHom) (rename_injective ρ hρ)) := by
  apply (surjective_fractionRing_map_rename_iff
    (R := ℤ) (L := FractionRing (MvPolynomial (ULift.{u} ℕ) ℤ))
    (K := FractionRing (MvPolynomial (ULift.{v} ℕ) ℤ))
    (fun n : ULift.{u} ℕ => (ULift.up (2 * n.down) : ULift.{v} ℕ)) (by
      intro a b h
      apply ULift.ext
      have hm := congrArg ULift.down h
      change 2 * a.down = 2 * b.down at hm
      omega)).not.mpr
  exact lifted_even_rename_controls.2.1

end MvPolynomialTests.FractionRingFiniteVariables
