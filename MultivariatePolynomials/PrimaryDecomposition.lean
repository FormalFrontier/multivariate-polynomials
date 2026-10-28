/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Primary

/-!
# Primary families under coefficient extension

Over a commutative semiring, extension along `MvPolynomial.C` preserves and
reflects a supplied intersection of primary ideals when each component satisfies
`a ∈ Q i → a + b ∈ Q i → b ∈ Q i`. This subtractivity is given for arbitrary
variable types, including the empty type. When variables are nonempty, primaryness
of the extended components also recovers their subtractivity. Over a commutative
ring, subtractivity is automatic, giving the unconditional specialization.

The intersection itself need not be primary. Deletion irredundance is preserved
and reflected over any commutative semiring, without subtractivity. Deletion
means omitting exactly one index. Families may be empty or infinite, with indices
in any sort; coefficient, variable and index universes are independent. Empty
intersections are top, and componentwise clauses for an empty family are vacuous.
These results concern supplied families, not existence, uniqueness, distinct
radicals, or associated primes.

## References

* `MultivariatePolynomials.CoefficientIdeal` supplies preservation of arbitrary
  intersections and reflection of inclusion and equality along `C`.
* `MultivariatePolynomials.Primary` supplies the equivalence for Mathlib's
  `Ideal.IsPrimary` and credits the primary-ideal formalizations it builds on.

The proofs below only combine these APIs; they do not construct decompositions.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {ι : Sort w}

/-- Transport a supplied primary family with subtractive components, for any variable type. -/
theorem primary_family_map_C_iff_of_subtractive [CommSemiring R]
    (I : Ideal R) (Q : ι → Ideal R)
    (hsub : ∀ (i : ι) (a b : R), a ∈ Q i → a + b ∈ Q i → b ∈ Q i) :
    (I.map (C : R →+* MvPolynomial σ R) = (⨅ i, (Q i).map C) ∧
      ∀ i, ((Q i).map (C : R →+* MvPolynomial σ R)).IsPrimary) ↔
    (I = (⨅ i, Q i) ∧ ∀ i, (Q i).IsPrimary) := by
  have hprimary (i : ι) :
      ((Q i).map (C : R →+* MvPolynomial σ R)).IsPrimary ↔ (Q i).IsPrimary := by
    constructor
    · intro h
      simpa only [comap_map_C] using h.comap (C : R →+* MvPolynomial σ R)
    · exact fun h => isPrimary_map_C_of_subtractive (Q i) h (hsub i)
  simp only [← map_C_iInf, (map_C_injective (σ := σ)).eq_iff, hprimary]

/-- With nonempty variables, a mapped primary family also detects componentwise subtractivity. -/
theorem primary_family_map_C_iff_subtractive [CommSemiring R] [Nonempty σ]
    (I : Ideal R) (Q : ι → Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R) = (⨅ i, (Q i).map C) ∧
      ∀ i, ((Q i).map (C : R →+* MvPolynomial σ R)).IsPrimary) ↔
    (I = (⨅ i, Q i) ∧ ∀ i, (Q i).IsPrimary ∧
      (∀ a b : R, a ∈ Q i → a + b ∈ Q i → b ∈ Q i)) := by
  simp only [← map_C_iInf, (map_C_injective (σ := σ)).eq_iff,
    isPrimary_map_C_iff_subtractive]

/-- Transport a supplied primary-family intersection along coefficient extension. -/
theorem primary_family_map_C_iff [CommRing R] (I : Ideal R) (Q : ι → Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R) = (⨅ i, (Q i).map C) ∧
      ∀ i, ((Q i).map (C : R →+* MvPolynomial σ R)).IsPrimary) ↔
    (I = (⨅ i, Q i) ∧ ∀ i, (Q i).IsPrimary) := by
  exact primary_family_map_C_iff_of_subtractive I Q fun i a b ha hab => by
    simpa only [add_sub_cancel_left] using (Q i).sub_mem hab ha

/-- Transport deletion irredundance, with no primary or finiteness assumptions. -/
theorem irredundant_iInf_map_C_iff [CommSemiring R] (Q : ι → Ideal R) :
    (∀ i : ι, ¬ ((⨅ j : {j : ι // j ≠ i},
      (Q j.val).map (C : R →+* MvPolynomial σ R)) ≤ (Q i).map C)) ↔
    ∀ i : ι, ¬ ((⨅ j : {j : ι // j ≠ i}, Q j.val) ≤ Q i) := by
  simp only [← map_C_iInf, map_C_le_map_C_iff]

end MvPolynomial
