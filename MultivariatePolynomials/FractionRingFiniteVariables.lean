/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Finite-variable origins of polynomial fractions

A finite set in a fraction ring of a multivariate polynomial ring over an integral
domain comes from one finite-variable fraction ring. The map is Mathlib's
`IsFractionRing.map`, induced by coefficient-preserving variable renaming.
The target may be any fraction-ring representation, and the variable type need not
be finite. An empty variable stage is a fraction ring of the coefficients, not
in general the coefficient ring itself.

The finite-family proof takes the finite union of the variable supports of
localization numerators and denominators, then uses the renaming and localization
map APIs. Variable membership in the image of an injective renaming is characterized
by membership in the image of the index map. A finite stage missing a variable is
not surjective; over an infinite variable type this applies to every finite stage.

## References

* Fujiwara and Kato, *Foundations of Rigid Geometry I* (arXiv:1308.4734v5):
  rational-function constructions motivating this finite-variable algebraic result.
* Mathlib's `MvPolynomial.vars`, `exists_rename_eq_of_vars_subset_range`,
  `IsLocalization.sec`, `mk'_sec`, and `map_mk'` supply the proof's constructions
  and their characteristic laws.
-/

@[expose] public section

universe u v w uR uτ uσ uL uK

namespace MvPolynomial

/-- A finite set of fractions of `R[σ]` has simultaneous origins over one finite set
of variables, for any integral-domain coefficient ring `R` and any fraction-ring
representation `K` of `R[σ]`. The source stages use the canonical `FractionRing`.
For an empty variable set the stage is a fraction ring of `R`, not generally `R`.
This is the finite-variable algebraic form of the rational-function constructions
motivated by Fujiwara and Kato, *Foundations of Rigid Geometry I*. -/
theorem exists_finset_fractionRing_map_range
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v}
    {K : Type w} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] {E : Set K} (hE : E.Finite) :
    ∃ J : Finset σ,
      E ⊆ Set.range
        (IsFractionRing.map
          (A := MvPolynomial {i : σ // i ∈ J} R) (B := MvPolynomial σ R)
          (K := FractionRing (MvPolynomial {i : σ // i ∈ J} R))
          (L := K) (j := (MvPolynomial.rename (R := R) Subtype.val).toRingHom)
          (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)) := by
  classical
  let s := IsLocalization.sec (nonZeroDivisors (MvPolynomial σ R)) (S := K)
  let supports := fun z : K => (s z).1.vars ∪ ((s z).2 : MvPolynomial σ R).vars
  let J := hE.toFinset.biUnion supports
  refine ⟨J, ?_⟩
  intro z hz
  have hs : supports z ⊆ J :=
    Finset.subset_biUnion_of_mem supports (hE.mem_toFinset.mpr hz)
  have hpvars : ↑(s z).1.vars ⊆ Set.range (Subtype.val : {i : σ // i ∈ J} → σ) := by
    intro i hi
    exact ⟨⟨i, hs (Finset.mem_union_left _ hi)⟩, rfl⟩
  have hqvars : ↑((s z).2 : MvPolynomial σ R).vars ⊆
      Set.range (Subtype.val : {i : σ // i ∈ J} → σ) := by
    intro i hi
    exact ⟨⟨i, hs (Finset.mem_union_right _ hi)⟩, rfl⟩
  obtain ⟨p, hp⟩ := exists_rename_eq_of_vars_subset_range (s z).1
    Subtype.val Subtype.val_injective hpvars
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range
    ((s z).2 : MvPolynomial σ R) Subtype.val Subtype.val_injective hqvars
  let j : MvPolynomial {i : σ // i ∈ J} R →+* MvPolynomial σ R :=
    (rename Subtype.val).toRingHom
  have hj : Function.Injective j := rename_injective Subtype.val Subtype.val_injective
  have hqmem : q ∈ nonZeroDivisors (MvPolynomial {i : σ // i ∈ J} R) :=
    mem_nonZeroDivisors_of_injective (f := j) hj (hq.symm ▸ (s z).2.property)
  let d : nonZeroDivisors (MvPolynomial {i : σ // i ∈ J} R) := ⟨q, hqmem⟩
  refine ⟨IsLocalization.mk' (FractionRing (MvPolynomial {i : σ // i ∈ J} R)) p d, ?_⟩
  -- This is the characteristic fraction law for the existing localization map.
  rw [IsFractionRing.map, IsLocalization.map_mk']
  have hd : (⟨j d, (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)
      d.property⟩ : nonZeroDivisors (MvPolynomial σ R)) = (s z).2 :=
    Subtype.ext hq
  change IsLocalization.mk' K (j p)
    ⟨j d, (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj) d.property⟩ = z
  rw [show j p = (s z).1 from hp, hd]
  exact IsLocalization.mk'_sec K z

/-- A variable belongs to the image of the fraction-ring map induced by an injective
renaming exactly when its index belongs to the image of the index map. Both fraction
rings may be arbitrary commutative-ring realizations. -/
theorem X_mem_range_fractionRing_map_rename_iff
    {R : Type uR} [CommRing R] [IsDomain R]
    {τ : Type uτ} {σ : Type uσ}
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
    [IsFractionRing (MvPolynomial τ R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K]
    (ρ : τ → σ) (hρ : Function.Injective ρ) (i : σ) :
    algebraMap (MvPolynomial σ R) K (X i) ∈
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial τ R) (B := MvPolynomial σ R)
          (K := L) (L := K) (j := (rename (R := R) ρ).toRingHom)
          (rename_injective ρ hρ)) ↔
      i ∈ Set.range ρ := by
  classical
  let φ := IsFractionRing.map
    (A := MvPolynomial τ R) (B := MvPolynomial σ R) (K := L) (L := K)
    (j := (rename (R := R) ρ).toRingHom) (rename_injective ρ hρ)
  have hφ (p : MvPolynomial τ R) :
      φ (algebraMap (MvPolynomial τ R) L p) =
        algebraMap (MvPolynomial σ R) K (rename ρ p) :=
    IsLocalization.map_eq (S := L) (Q := K)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
        (rename (R := R) ρ).toRingHom (rename_injective ρ hρ)) p
  constructor
  · rintro ⟨z, hz⟩
    have hz : φ z = algebraMap (MvPolynomial σ R) K (X i) := hz
    by_contra hi
    -- Outside the index image, every renamed polynomial has degree zero.
    have hdegree (p : MvPolynomial τ R) : degreeOf i (rename ρ p) = 0 := by
      by_contra hp
      obtain ⟨j, _, hj⟩ := mem_vars_rename ρ p (mem_vars_iff_degreeOf_ne_zero.mpr hp)
      exact hi ⟨j, hj⟩
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (MvPolynomial τ R)) z
    have hb : rename ρ (b : MvPolynomial τ R) ≠ 0 := by
      intro hb
      apply mem_nonZeroDivisors_iff_ne_zero.mp b.property
      apply rename_injective ρ hρ
      simpa only [map_zero] using hb
    -- Map the denominator-clearing equation and use injectivity in the target.
    have hpoly : X i * rename ρ (b : MvPolynomial τ R) = rename ρ a := by
      apply IsFractionRing.injective (MvPolynomial σ R) K
      simpa only [map_mul, hφ, hz] using congrArg φ hab
    have hdeg := congrArg (degreeOf i) hpoly
    rw [mul_comm, (degreeOf_mul_X_eq_degreeOf_add_one_iff i _).mpr hb,
      hdegree, hdegree] at hdeg
    exact Nat.one_ne_zero hdeg
  · rintro ⟨j, rfl⟩
    refine ⟨algebraMap (MvPolynomial τ R) L (X j), ?_⟩
    simpa only [rename_X] using hφ (X j)

/-- A variable belongs to a finite-variable fraction-ring stage exactly when its
index belongs to that finite set. -/
theorem X_mem_range_fractionRing_map_finset_iff
    {R : Type uR} [CommRing R] [IsDomain R] {σ : Type uσ}
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] (S : Finset σ) (i : σ) :
    algebraMap (MvPolynomial σ R) K (X i) ∈
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial {j : σ // j ∈ S} R) (B := MvPolynomial σ R)
          (K := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (L := K)
          (j := (rename (R := R) Subtype.val).toRingHom)
          (rename_injective Subtype.val Subtype.val_injective)) ↔
      i ∈ S := by
  simpa only [Subtype.range_val_subtype, Set.mem_ofPred_eq] using
    (X_mem_range_fractionRing_map_rename_iff
      (R := R) (L := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (K := K)
      (Subtype.val : {j : σ // j ∈ S} → σ) Subtype.val_injective i)

/-- A finite-variable fraction-ring stage is not surjective if it misses a variable. -/
theorem not_surjective_fractionRing_map_finset_of_notMem
    {R : Type uR} [CommRing R] [IsDomain R] {σ : Type uσ}
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K]
    (S : Finset σ) (i : σ) (hi : i ∉ S) :
    ¬ Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {j : σ // j ∈ S} R) (B := MvPolynomial σ R)
        (K := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (L := K)
        (j := (rename (R := R) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) := by
  intro h
  exact hi ((X_mem_range_fractionRing_map_finset_iff (R := R) (K := K) S i).mp
    (h (algebraMap (MvPolynomial σ R) K (X i))))

/-- Over an infinite variable type, no finite-variable fraction-ring stage is
surjective. This is compatible with simultaneous capture of each finite family:
the finite stage for such a family may depend on that family. -/
theorem not_surjective_fractionRing_map_finset_of_infinite
    {R : Type uR} [CommRing R] [IsDomain R] {σ : Type uσ} [Infinite σ]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] :
    ∀ S : Finset σ, ¬ Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {j : σ // j ∈ S} R) (B := MvPolynomial σ R)
        (K := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (L := K)
        (j := (rename (R := R) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) := by
  intro S
  obtain ⟨i, hi⟩ := S.exists_notMem
  exact not_surjective_fractionRing_map_finset_of_notMem (R := R) (K := K) S i hi

end MvPolynomial

namespace MvPolynomial

/-- The fraction-ring map induced by an injective variable renaming is surjective
exactly when the index map is surjective. The coefficient ring may be any integral
domain, and both fraction rings may be arbitrary commutative-ring realizations. -/
theorem surjective_fractionRing_map_rename_iff
    {R : Type uR} [CommRing R] [IsDomain R]
    {τ : Type uτ} {σ : Type uσ}
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
    [IsFractionRing (MvPolynomial τ R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K]
    (ρ : τ → σ) (hρ : Function.Injective ρ) :
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial τ R) (B := MvPolynomial σ R)
        (K := L) (L := K) (j := (rename (R := R) ρ).toRingHom)
        (rename_injective ρ hρ)) ↔ Function.Surjective ρ := by
  classical
  constructor
  · intro h i
    exact (X_mem_range_fractionRing_map_rename_iff
      (R := R) (L := L) (K := K) ρ hρ i).mp
      (h (algebraMap (MvPolynomial σ R) K (X i)))
  · intro honto
    let e : τ ≃ σ := Equiv.ofBijective ρ ⟨hρ, honto⟩
    let ePoly : MvPolynomial τ R ≃+* MvPolynomial σ R :=
      (renameEquiv R e).toRingEquiv
    let eFrac : L ≃+* K :=
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := K) ePoly
    have hmap :
        IsFractionRing.map
          (A := MvPolynomial τ R) (B := MvPolynomial σ R)
          (K := L) (L := K) (j := (rename (R := R) ρ).toRingHom)
          (rename_injective ρ hρ) = eFrac.toRingHom :=
      IsLocalization.map_unique (S := L) (Q := K)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
          (rename (R := R) ρ).toRingHom (rename_injective ρ hρ))
        eFrac.toRingHom fun p =>
          IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := L) (L := K) ePoly p
    rw [hmap]
    exact eFrac.surjective

/-- A finite-variable fraction-ring stage is surjective exactly when its finite set
contains every ambient variable. No finiteness assumption on the ambient variable
type is needed. The target may be any commutative-ring fraction-ring realization. -/
theorem surjective_fractionRing_map_finset_iff
    {R : Type uR} [CommRing R] [IsDomain R] {σ : Type uσ}
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] (S : Finset σ) :
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial {j : σ // j ∈ S} R) (B := MvPolynomial σ R)
        (K := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (L := K)
        (j := (rename (R := R) Subtype.val).toRingHom)
        (rename_injective Subtype.val Subtype.val_injective)) ↔ ∀ i : σ, i ∈ S := by
  rw [surjective_fractionRing_map_rename_iff Subtype.val Subtype.val_injective]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := h i
    exact j.property
  · intro h i
    exact ⟨⟨i, h i⟩, rfl⟩

end MvPolynomial
