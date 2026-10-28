/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientProductSylvester
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Factorization uniqueness from a regular crossed resultant

Two bounded polynomial factorizations with pairwise equal nominal top coefficients
are equal if the resultant of the first factor of one and the second factor of the
other is regular. The nominal degrees may be zero, and the coefficient ring may
have zero divisors.

The differences lie in the strict degree blocks of the Sylvester map. Equality of
products puts them in its kernel, which is zero when its determinant is regular.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- A regular resultant makes the Sylvester map injective, including when either
nominal degree is zero. -/
theorem sylvesterMap_injective_of_isRegular_resultant
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hres : IsRegular (resultant f g m n)) :
    Function.Injective (sylvesterMap f g hf hg) := by
  classical
  let b₁ := degreeLT.basisProd R m n
  let b₂ := degreeLT.basis R (m + n)
  have hmat : (sylvesterMap f g hf hg).toMatrix b₁ b₂ = sylvester f g m n :=
    toMatrix_sylvesterMap' f g hf hg
  have hinj := Matrix.mulVec_injective_of_det_mem_nonZeroDivisors
    (M := sylvester f g m n) hres.mem_nonZeroDivisors
  intro p q hpq
  apply b₁.repr.injective
  have hrepr : (b₁.repr p : Fin (m + n) → R) = b₁.repr q := by
    apply hinj
    rw [← hmat, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hpq]
  exact Finsupp.ext fun i ↦ congrFun hrepr i

private theorem sub_mem_degreeLT_of_natDegree_le
    {f g : R[X]} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ m)
    (htop : f.coeff m = g.coeff m) : f - g ∈ degreeLT R m := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro k hmk
  rw [coeff_sub]
  rcases hmk.eq_or_lt with rfl | hmk
  · exact sub_eq_zero.mpr htop
  · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt hmk),
      coeff_eq_zero_of_natDegree_lt (hg.trans_lt hmk), sub_self]

/-- Bounded factorizations with pairwise equal nominal top coefficients are equal
if the crossed resultant of `G'` and `H` is regular. All four degree bounds are
upper bounds; neither monicity nor positive nominal degrees are required. -/
theorem eq_and_eq_of_mul_eq_mul_of_isRegular_resultant
    (m n : ℕ) (G H G' H' : R[X])
    (hG : G.natDegree ≤ m) (hG' : G'.natDegree ≤ m)
    (hH : H.natDegree ≤ n) (hH' : H'.natDegree ≤ n)
    (hGtop : G.coeff m = G'.coeff m) (hHtop : H.coeff n = H'.coeff n)
    (hprod : G * H = G' * H') (hres : IsRegular (resultant G' H m n)) :
    G = G' ∧ H = H' := by
  let D : degreeLT R m := ⟨G - G', sub_mem_degreeLT_of_natDegree_le hG hG' hGtop⟩
  let E : degreeLT R n := ⟨H - H', sub_mem_degreeLT_of_natDegree_le hH hH' hHtop⟩
  have hzero : sylvesterMap G' H hG' hH (D, E) = 0 := by
    apply Subtype.ext
    rw [coe_sylvesterMap_apply]
    change G' * (H - H') + H * (G - G') = 0
    calc
      G' * (H - H') + H * (G - G') = G * H - G' * H' := by ring
      _ = 0 := sub_eq_zero.mpr hprod
  have hDE : (D, E) = 0 :=
    sylvesterMap_injective_of_isRegular_resultant G' H hG' hH hres
      (hzero.trans (map_zero _).symm)
  constructor
  · exact sub_eq_zero.mp (congrArg (fun p : degreeLT R m × degreeLT R n ↦
      (p.1 : R[X])) hDE)
  · exact sub_eq_zero.mp (congrArg (fun p : degreeLT R m × degreeLT R n ↦
      (p.2 : R[X])) hDE)

end Polynomial
