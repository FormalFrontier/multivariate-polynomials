/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Artinian
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Applications of the univariate Artinian criterion

The univariate criterion applies to semirings without requiring commutative
multiplication or additive inverses. Artinianity here is for the left regular
module: the polynomial semiring acts on itself, not merely through its coefficients.

Over `ZMod 1`, every polynomial is zero, and the criterion gives Artinianity.
The nonnegative reals have an infinite carrier and no additive inverse of `1`,
but their finite ideal lattice makes the coefficient semiring Artinian. Their
polynomial semiring is not Artinian. The ring of two-by-two matrices over `ZMod 2`
has sixteen elements and noncommutative multiplication; its left regular module
is Artinian, while its polynomial semiring is not.

## References

* `MultivariatePolynomials.Artinian`: the univariate semiring criterion.
* Mathlib, `Mathlib.Basic.NNReal.Defs`: the nonnegative real semifield with its
  usual operations; `Mathlib.Algebra.Order.Monoid.Canonical.Defs` and
  `Mathlib.Algebra.Group.Defs`: the order obstruction to an additive inverse.
* Mathlib, `Mathlib.RingTheory.Ideal.Basic` and `Mathlib.Data.Fintype.Card`:
  finiteness of the ideal lattice of a division semiring and well-foundedness
  of strict orders on finite types.
* Mathlib, `Mathlib.RingTheory.Artinian.Module`: finite modules are Artinian.
* Mathlib, `Mathlib.Data.ZMod.Defs`, `Mathlib.Data.Matrix.Basic`,
  `Mathlib.Data.Matrix.Mul`, `Mathlib.LinearAlgebra.Matrix.Notation`, and
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card`: coefficient and
  matrix structures, matrix multiplication, matrix literals, and matrix cardinality.
-/

universe u

open scoped NNReal

namespace MultivariatePolynomialsTests

private theorem coefficients_eq_of_polynomial_artinian (R : Type u) [Semiring R]
    [IsArtinianRing (Polynomial R)] (r s : R) : r = s := by
  have hR : Subsingleton R := (Polynomial.isArtinianRing_iff R).mp inferInstance
  exact hR.elim r s

private theorem polynomial_left_artinian_of_subsingleton (R : Type u) [Semiring R]
    [Subsingleton R] : IsArtinian (Polynomial R) (Polynomial R) := by
  apply (Polynomial.isArtinianRing_iff R).mpr
  infer_instance

private theorem zmod_one_polynomial_artinian_and_zero :
    IsArtinianRing (Polynomial (ZMod 1)) ∧ ∀ p : Polynomial (ZMod 1), p = 0 := by
  constructor
  · apply (Polynomial.isArtinianRing_iff (ZMod 1)).mpr
    infer_instance
  · intro p
    exact Subsingleton.elim p 0

private theorem nnreal_infinite : Infinite ℝ≥0 := by
  exact Infinite.of_injective (fun n : ℕ ↦ (n : ℝ≥0)) Nat.cast_injective

private theorem nnreal_ideals_finite : Finite (Ideal ℝ≥0) := by
  infer_instance

private theorem nnreal_one_has_no_additive_inverse :
    ¬ ∃ x : ℝ≥0, (1 : ℝ≥0) + x = 0 := by
  rintro ⟨x, hx⟩
  have hle : (1 : ℝ≥0) ≤ 0 := by
    calc
      (1 : ℝ≥0) ≤ 1 + x := le_self_add
      _ = 0 := hx
  exact (not_le_of_gt zero_lt_one) hle

private theorem nnreal_semiring_has_no_ring_extension :
    ¬ ∃ ring : Ring ℝ≥0, ring.toSemiring = (inferInstance : Semiring ℝ≥0) := by
  rintro ⟨ring, hring⟩
  have hinverse :
      @Add.add ℝ≥0 ring.toSemiring.toAdd 1 (@Neg.neg ℝ≥0 ring.toNeg 1) =
        @Zero.zero ℝ≥0 ring.toSemiring.toZero :=
    @add_neg_cancel ℝ≥0 ring.toAddGroup 1
  rw [hring] at hinverse
  exact nnreal_one_has_no_additive_inverse ⟨_, hinverse⟩

private theorem nnreal_coefficient_left_artinian : IsArtinianRing ℝ≥0 := by
  let : Finite (Ideal ℝ≥0) := nnreal_ideals_finite
  exact (Finite.to_wellFoundedLT : WellFoundedLT (Ideal ℝ≥0))

private theorem nnreal_polynomial_not_artinian :
    ¬ IsArtinianRing (Polynomial ℝ≥0) := by
  intro h
  have hR : Subsingleton ℝ≥0 := (Polynomial.isArtinianRing_iff ℝ≥0).mp h
  exact (zero_ne_one : (0 : ℝ≥0) ≠ 1) (hR.elim 0 1)

private theorem matrix_semiring_has_ring_extension :
    ∃ ring : Ring (Matrix (Fin 2) (Fin 2) (ZMod 2)),
      ring.toSemiring = (inferInstance : Semiring (Matrix (Fin 2) (Fin 2) (ZMod 2))) := by
  exact ⟨inferInstance, rfl⟩

private theorem matrix_nontrivial_and_finite :
    Nontrivial (Matrix (Fin 2) (Fin 2) (ZMod 2)) ∧
      Finite (Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  exact ⟨inferInstance, inferInstance⟩

private theorem matrix_card_sixteen :
    Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = 16 := by
  calc
    Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = (2 : ℕ) ^ (2 * 2) := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin] using
        (Matrix.card_matrix (m := Fin 2) (n := Fin 2) (α := ZMod 2))
    _ = 16 := by decide

private theorem matrix_mul_not_commutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  decide

private theorem matrix_coefficient_left_artinian :
    IsArtinianRing (Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  exact isArtinian_of_finite
    (R := Matrix (Fin 2) (Fin 2) (ZMod 2))
    (M := Matrix (Fin 2) (Fin 2) (ZMod 2))

private theorem matrix_polynomial_not_artinian :
    ¬ IsArtinianRing (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) := by
  intro h
  have hR : Subsingleton (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
    (Polynomial.isArtinianRing_iff (Matrix (Fin 2) (Fin 2) (ZMod 2))).mp h
  exact (zero_ne_one : (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1) (hR.elim 0 1)

end MultivariatePolynomialsTests
