/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture
public import MultivariatePolynomials.FractionRingFiniteVariables

/-!
# Krull dimension of polynomial fraction-stage traces

For a subsemiring `A` in a fraction ring of `R[σ]`, its Krull dimension is bounded
by the supremum of the dimensions of its preimages in finite-variable fraction
rings. These preimages are the stage traces of `A`, not the whole stage fields.
The variable type may be arbitrary, the coefficient ring may be any integral
domain, and the ambient ring may be any fraction-ring representation.

An empty variable stage is a fraction ring of `R`, not generally `R`. No single
stage is required to contain all of `A`, and `A` need not contain the coefficients.
A subring is included through its underlying subsemiring.

## References

* `MultivariatePolynomials.FractionRingFiniteVariables` supplies simultaneous
  finite-variable origins, using Mathlib's polynomial renaming and localization
  map APIs, motivated by Fujiwara and Kato, *Foundations of Rigid Geometry I*.
* `AlgebraicDirectLimits.RingTheory.KrullDimension.FiniteCapture` supplies the dimension
  approach by finite witnesses to strict prime-ideal chains and restriction to
  subsemiring preimages.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

/-- The dimension of a subsemiring of a fraction ring of `R[σ]` is bounded by the
supremum of the dimensions of its finite-variable fraction-stage traces.
The maps preserve coefficients and rename subtype variables. In particular,
the empty variable stage is a fraction ring of `R`, and the preimage of `A` need
not be the entire stage. -/
theorem ringKrullDim_subsemiring_le_iSup_comap_fractionRing
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v}
    {K : Type w} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] (A : Subsemiring K) :
    ringKrullDim A ≤ ⨆ J : Finset σ,
      ringKrullDim (A.comap
        (IsFractionRing.map
          (A := MvPolynomial {i : σ // i ∈ J} R) (B := MvPolynomial σ R)
          (K := FractionRing (MvPolynomial {i : σ // i ∈ J} R)) (L := K)
          (j := (MvPolynomial.rename (R := R) Subtype.val).toRingHom)
          (MvPolynomial.rename_injective Subtype.val Subtype.val_injective))) := by
  apply ringKrullDim_subsemiring_le_iSup_comap_of_finite_subset_range
  intro E hE
  exact exists_finset_fractionRing_map_range hE

end MvPolynomial
