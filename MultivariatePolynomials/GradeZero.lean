/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The degree-zero homogeneous component

The coefficient algebra is canonically equivalent to the original degree-zero
homogeneous component. The forward map is the inherited coefficient algebra map,
whose ambient polynomial is `C`; the inverse takes the constant coefficient.
The usual homogeneous grading is selected locally, without transporting any
semiring or algebra structure.

## References

* Mathlib, `Mathlib.RingTheory.MvPolynomial.Homogeneous` (the grading),
  `Mathlib.Algebra.DirectSum.Internal` (the inherited component structures), and
  `Mathlib.Algebra.Algebra.Equiv` (the generic bijective algebra homomorphism
  constructor).
-/

@[expose] public section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

universe u v w

variable (σ : Type u) (R : Type v) [CommSemiring R]

/-- The coefficient algebra is canonically equivalent to the degree-zero
homogeneous component, with its inherited semiring and coefficient algebra. -/
noncomputable def gradeZeroAlgEquiv : R ≃ₐ[R] ↥(homogeneousSubmodule σ R 0) :=
  AlgEquiv.ofBijective (Algebra.ofId R ↥(homogeneousSubmodule σ R 0)) (by
    -- Bijectivity of the coefficient algebra map.
    constructor
    · intro a b hab
      apply C_injective σ R
      exact congrArg (fun q : homogeneousSubmodule σ R 0 =>
        (q : MvPolynomial σ R)) hab
    · intro p
      refine ⟨constantCoeff (p : MvPolynomial σ R), ?_⟩
      apply Subtype.ext
      change C (constantCoeff (p : MvPolynomial σ R)) = (p : MvPolynomial σ R)
      exact (totalDegree_eq_zero_iff_eq_C.mp
        ((totalDegree_zero_iff_isHomogeneous σ).mpr p.property)).symm)

/-- The forward map is the original coefficient algebra map of the component. -/
theorem gradeZeroAlgEquiv_apply (r : R) :
    gradeZeroAlgEquiv σ R r = algebraMap R ↥(homogeneousSubmodule σ R 0) r := by
  -- Coefficient-algebra-map characterization.
  rfl

/-- In the ambient polynomial algebra, the forward map is the constant embedding. -/
@[simp]
theorem coe_gradeZeroAlgEquiv (r : R) :
    (gradeZeroAlgEquiv σ R r : MvPolynomial σ R) = C r := by
  -- Forward ambient-coercion characterization.
  rw [gradeZeroAlgEquiv_apply]
  rfl

/-- The inverse reads the constant coefficient of the ambient polynomial. -/
@[simp]
theorem gradeZeroAlgEquiv_symm_apply (p : homogeneousSubmodule σ R 0) :
    (gradeZeroAlgEquiv σ R).symm p = constantCoeff (p : MvPolynomial σ R) := by
  -- Constant-coefficient characterization of the chosen inverse.
  have h := congrArg
    (fun q : homogeneousSubmodule σ R 0 => constantCoeff (q : MvPolynomial σ R))
    ((gradeZeroAlgEquiv σ R).apply_symm_apply p)
  simpa only [coe_gradeZeroAlgEquiv, constantCoeff_C] using h

/-- The coefficient equivalence commutes with coefficient homomorphisms after
coercion to the ambient polynomial algebras. -/
theorem map_coe_gradeZeroAlgEquiv {S : Type w} [CommSemiring S]
    (f : R →+* S) (r : R) :
    map f (gradeZeroAlgEquiv σ R r : MvPolynomial σ R) =
      (gradeZeroAlgEquiv σ S (f r) : MvPolynomial σ S) := by
  -- Naturality for the underlying polynomial coefficient map.
  simp only [coe_gradeZeroAlgEquiv, map_C]

end MvPolynomial
