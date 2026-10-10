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

The proof takes the finite union of the variable supports of localization
numerators and denominators, then uses the renaming and localization map APIs.

## References

* Fujiwara and Kato, *Foundations of Rigid Geometry I* (arXiv:1308.4734v5):
  rational-function constructions motivating this finite-variable algebraic result.
* Mathlib's `MvPolynomial.vars`, `exists_rename_eq_of_vars_subset_range`,
  `IsLocalization.sec`, `mk'_sec`, and `map_mk'` supply the proof's constructions
  and their characteristic laws.
-/

@[expose] public section

universe u v w

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

end MvPolynomial
