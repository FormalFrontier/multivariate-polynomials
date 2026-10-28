module

public import MultivariatePolynomials.CoefficientProduct
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-!
# The action of the coefficient-product derivative matrix

The evaluated partial-derivative matrix of `MvPolynomial.coefficientProduct` acts on
an increment by taking the first `m + n` ascending coefficients of the linearized
product. The first block of
increment coefficients multiplies the second perturbed factor, and the second block
multiplies the first perturbed factor. Both coordinate vectors are expressed in the
existing product basis of degree-bounded polynomials.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MvPolynomial

universe u v

variable {C : Type u} [CommSemiring C]

private theorem eval₂Hom_pderiv_coefficientProduct_column
    {R : Type v} [CommSemiring R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (m + n) → R)
    (r c : Fin (m + n)) :
    let q := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    eval₂Hom φ a (pderiv c (coefficientProduct m n g h r)) =
      ((h.map φ + (q.2 : Polynomial R)) *
          ((Polynomial.degreeLT.basisProd R m n c).1 : Polynomial R) +
        (g.map φ + (q.1 : Polynomial R)) *
          ((Polynomial.degreeLT.basisProd R m n c).2 : Polynomial R)).coeff r.val := by
  dsimp only
  by_cases hc : c.val < m
  · let i : Fin m := ⟨c.val, hc⟩
    have hci : c = i.castAdd n := by
      apply Fin.ext
      rfl
    rw [hci]
    simpa [Polynomial.degreeLT.basisProd_castAdd, Polynomial.degreeLT.basis_val,
      Polynomial.coeff_mul_X_pow'] using
      (eval₂Hom_pderiv_castAdd_coefficientProduct m n g h φ a r i)
  · have hmc : m ≤ c.val := Nat.le_of_not_gt hc
    have hbound : c.val < m + n := c.isLt
    let j : Fin n := ⟨c.val - m, by omega⟩
    have hcj : c = j.natAdd m := by
      apply Fin.ext
      change c.val = m + (c.val - m)
      omega
    rw [hcj]
    simpa [Polynomial.degreeLT.basisProd_natAdd, Polynomial.degreeLT.basis_val,
      Polynomial.coeff_mul_X_pow'] using
      (eval₂Hom_pderiv_natAdd_coefficientProduct m n g h φ a r j)

/-- The evaluated partial-derivative matrix of `coefficientProduct` sends an
increment to the first `m + n` ascending coefficients of the linearized product. The
base point and increment use the same product basis, without degree restrictions on
the seed polynomials or restrictions on the coefficient homomorphism. -/
theorem eval₂Hom_pderiv_coefficientProduct_mulVec
    {R : Type v} [CommSemiring R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a z : Fin (m + n) → R) :
    let qa := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    let qz := ∑ s : Fin (m + n), z s • Polynomial.degreeLT.basisProd R m n s
    Matrix.mulVec
        (fun r s : Fin (m + n) =>
          eval₂Hom φ a (pderiv s (coefficientProduct m n g h r))) z =
      fun r =>
        ((h.map φ + (qa.2 : Polynomial R)) * (qz.1 : Polynomial R) +
          (g.map φ + (qa.1 : Polynomial R)) * (qz.2 : Polynomial R)).coeff r.val := by
  classical
  dsimp only
  let b := Polynomial.degreeLT.basisProd R m n
  let qa := ∑ s : Fin (m + n), a s • b s
  let qz := ∑ s : Fin (m + n), z s • b s
  let H : Polynomial R := h.map φ + (qa.2 : Polynomial R)
  let G : Polynomial R := g.map φ + (qa.1 : Polynomial R)
  funext r
  erw [Matrix.mulVec_apply_eq_sum]
  change (∑ c : Fin (m + n),
      eval₂Hom φ a (pderiv c (coefficientProduct m n g h r)) * z c) =
    (H * (qz.1 : Polynomial R) + G * (qz.2 : Polynomial R)).coeff r.val
  have hcol (c : Fin (m + n)) :
      eval₂Hom φ a (pderiv c (coefficientProduct m n g h r)) =
        (H * ((b c).1 : Polynomial R) + G * ((b c).2 : Polynomial R)).coeff r.val :=
    eval₂Hom_pderiv_coefficientProduct_column m n g h φ a r c
  have hsmul (p q : Polynomial R) (t : R) : p * (t • q) = t • (p * q) := by
    simp only [Polynomial.smul_eq_C_mul]
    ac_rfl
  simp_rw [hcol]
  calc
    (∑ c : Fin (m + n),
        (H * ((b c).1 : Polynomial R) + G * ((b c).2 : Polynomial R)).coeff r.val *
          z c) =
        ∑ c : Fin (m + n), z c •
          (H * ((b c).1 : Polynomial R) + G * ((b c).2 : Polynomial R)).coeff r.val := by
      apply Finset.sum_congr rfl
      intro c hc
      change
        (H * ((b c).1 : Polynomial R) + G * ((b c).2 : Polynomial R)).coeff r.val *
            z c =
          z c *
            (H * ((b c).1 : Polynomial R) + G * ((b c).2 : Polynomial R)).coeff r.val
      exact mul_comm _ _
    _ = (∑ c : Fin (m + n), z c •
        (H * ((b c).1 : Polynomial R) + G * ((b c).2 : Polynomial R))).coeff r.val := by
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
    _ = (H * (qz.1 : Polynomial R) + G * (qz.2 : Polynomial R)).coeff r.val := by
      apply congrArg (fun p : Polynomial R => p.coeff r.val)
      dsimp only [qz]
      induction (Finset.univ : Finset (Fin (m + n))) using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
        simp only [Finset.sum_insert hc]
        rw [ih]
        simp [mul_add, smul_add, hsmul]
        ac_rfl

end MvPolynomial
