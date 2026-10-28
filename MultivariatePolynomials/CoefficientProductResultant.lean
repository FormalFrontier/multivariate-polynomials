module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import MultivariatePolynomials.CoefficientProduct
public import MultivariatePolynomials.CoefficientProductSylvester

/-!
# Coefficient-product Jacobian determinants and resultants

At an arbitrary target point, the evaluated partial-derivative matrix of
`MvPolynomial.coefficientProduct` has determinant equal to the resultant of the
mapped, perturbed seeds at explicit nominal bounds, provided their target natural
degrees satisfy those bounds.

When either block has bound zero, the determinant is a constant-coefficient
power and equals the resultant of the mapped seeds with the same explicit
nominal bounds, without degree restrictions on either seed.

The source coefficients need only form a commutative semiring, and the target a
commutative ring. The statements include empty matrices and the zero ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

/-- The determinant of a finite lower coefficient-Toeplitz matrix. -/
private lemma det_coefficient_toeplitz {R : Type u} [CommRing R]
    (c : ℕ → R) (n : ℕ) :
    Matrix.det (fun i j : Fin n =>
      if (j : ℕ) ≤ (i : ℕ) then c ((i : ℕ) - (j : ℕ)) else 0) =
      (c 0) ^ n := by
  induction n with
  | zero =>
      simpa only [pow_zero] using (Matrix.det_fin_zero
        (A := fun i j : Fin 0 =>
          if (j : ℕ) ≤ (i : ℕ) then c ((i : ℕ) - (j : ℕ)) else 0))
  | succ n ih =>
      let A : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
        if (j : ℕ) ≤ (i : ℕ) then c ((i : ℕ) - (j : ℕ)) else 0
      have hminor : A.submatrix Fin.succ (0 : Fin (n + 1)).succAbove =
          (fun i j : Fin n =>
            if (j : ℕ) ≤ (i : ℕ) then c ((i : ℕ) - (j : ℕ)) else 0) := by
        funext i j
        simp [A, Matrix.submatrix, Nat.succ_sub_succ_eq_sub]
      change Matrix.det A = _
      calc
        Matrix.det A =
            ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) * A 0 j *
              Matrix.det (A.submatrix Fin.succ j.succAbove) :=
          Matrix.det_succ_row_zero A
        _ = c 0 * Matrix.det (A.submatrix Fin.succ (0 : Fin (n + 1)).succAbove) := by
          rw [Finset.sum_eq_single (0 : Fin (n + 1))]
          · simp [A]
          · intro j _ hj
            simp [A, hj]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        _ = c 0 * (c 0) ^ n := by rw [hminor, ih]
        _ = (c 0) ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- Every element of a module with this empty-index basis is zero. -/
private lemma coe_degreeLT_zero_eq_zero {R : Type v} [Semiring R]
    (p : Polynomial.degreeLT R 0) : (p : Polynomial R) = 0 := by
  have hp : p = 0 := by
    apply (Polynomial.degreeLT.basis R 0).repr.injective
    apply Finsupp.ext
    intro i
    exact Fin.elim0 i
  rw [hp]
  rfl

namespace MvPolynomial

variable {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]

/-- With the first block empty, the evaluated coefficient-product Jacobian has
constant-coefficient power determinant at every target point. -/
theorem det_eval₂Hom_pderiv_coefficientProduct_zero_left_bound
    (n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (0 + n) → R) :
    Matrix.det (fun r s : Fin (0 + n) =>
      eval₂Hom φ a (pderiv s (coefficientProduct 0 n g h r))) =
      (φ (g.coeff 0)) ^ n := by
  let q := ∑ s : Fin (0 + n), a s • Polynomial.degreeLT.basisProd R 0 n s
  have hq : (q.1 : Polynomial R) = 0 := coe_degreeLT_zero_eq_zero q.1
  have hJ :
      (fun r s : Fin (0 + n) =>
        eval₂Hom φ a (pderiv s (coefficientProduct 0 n g h r))) =
      (fun r s : Fin (0 + n) =>
        if s.val ≤ r.val then φ (g.coeff (r.val - s.val)) else 0) := by
    funext r s
    let j : Fin n := ⟨s.val, by simpa only [Nat.zero_add] using s.isLt⟩
    have hs : j.natAdd 0 = s := by
      apply Fin.ext
      simp [j]
    have he := eval₂Hom_pderiv_natAdd_coefficientProduct 0 n g h φ a r j
    change eval₂Hom φ a (pderiv (j.natAdd 0) (coefficientProduct 0 n g h r)) =
      (if j.val ≤ r.val then
        (g.map φ + (q.1 : Polynomial R)).coeff (r.val - j.val) else 0) at he
    simpa only [hs, hq, add_zero, Polynomial.coeff_map] using he
  rw [hJ]
  simpa only [Nat.zero_add] using
    det_coefficient_toeplitz (fun k => φ (g.coeff k)) (0 + n)

/-- With the second block empty, the evaluated coefficient-product Jacobian has
constant-coefficient power determinant at every target point. -/
theorem det_eval₂Hom_pderiv_coefficientProduct_zero_right_bound
    (m : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (m + 0) → R) :
    Matrix.det (fun r s : Fin (m + 0) =>
      eval₂Hom φ a (pderiv s (coefficientProduct m 0 g h r))) =
      (φ (h.coeff 0)) ^ m := by
  let q := ∑ s : Fin (m + 0), a s • Polynomial.degreeLT.basisProd R m 0 s
  have hq : (q.2 : Polynomial R) = 0 := coe_degreeLT_zero_eq_zero q.2
  have hJ :
      (fun r s : Fin (m + 0) =>
        eval₂Hom φ a (pderiv s (coefficientProduct m 0 g h r))) =
      (fun r s : Fin (m + 0) =>
        if s.val ≤ r.val then φ (h.coeff (r.val - s.val)) else 0) := by
    funext r s
    let i : Fin m := ⟨s.val, by simpa only [Nat.add_zero] using s.isLt⟩
    have hs : i.castAdd 0 = s := by
      apply Fin.ext
      rfl
    have he := eval₂Hom_pderiv_castAdd_coefficientProduct m 0 g h φ a r i
    change eval₂Hom φ a (pderiv (i.castAdd 0) (coefficientProduct m 0 g h r)) =
      (if i.val ≤ r.val then
        (h.map φ + (q.2 : Polynomial R)).coeff (r.val - i.val) else 0) at he
    simpa only [hs, hq, add_zero, Polynomial.coeff_map] using he
  rw [hJ]
  simpa only [Nat.add_zero] using
    det_coefficient_toeplitz (fun k => φ (h.coeff k)) (m + 0)

/-- The empty-first-block Jacobian determinant equals the resultant with explicit
nominal bounds `0, n`, regardless of the degrees of the mapped seeds. -/
theorem det_eval₂Hom_pderiv_coefficientProduct_zero_left_bound_eq_resultant
    (n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (0 + n) → R) :
    Matrix.det (fun r s : Fin (0 + n) =>
      eval₂Hom φ a (pderiv s (coefficientProduct 0 n g h r))) =
      (g.map φ).resultant (h.map φ) 0 n := by
  rw [det_eval₂Hom_pderiv_coefficientProduct_zero_left_bound,
    Polynomial.resultant_zero_left_deg, Polynomial.coeff_map]

/-- The empty-second-block Jacobian determinant equals the resultant with explicit
nominal bounds `m, 0`, regardless of the degrees of the mapped seeds. -/
theorem det_eval₂Hom_pderiv_coefficientProduct_zero_right_bound_eq_resultant
    (m : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (m + 0) → R) :
    Matrix.det (fun r s : Fin (m + 0) =>
      eval₂Hom φ a (pderiv s (coefficientProduct m 0 g h r))) =
      (g.map φ).resultant (h.map φ) m 0 := by
  rw [det_eval₂Hom_pderiv_coefficientProduct_zero_right_bound,
    Polynomial.resultant_zero_right_deg, Polynomial.coeff_map]

/-- The evaluated coefficient-product Jacobian determinant is the resultant of the
mapped, perturbed seeds at explicit nominal bounds, assuming their target natural
degrees satisfy those bounds. -/
theorem det_eval₂Hom_pderiv_coefficientProduct_eq_resultant
    {R : Type v} [CommRing R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R)
    (a : Fin (m + n) → R) :
    let qa := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    let G := g.map φ + (qa.1 : Polynomial R)
    let H := h.map φ + (qa.2 : Polynomial R)
    ∀ _hG : G.natDegree ≤ m, ∀ _hH : H.natDegree ≤ n,
      Matrix.det (fun r s : Fin (m + n) =>
        eval₂Hom φ a (pderiv s (coefficientProduct m n g h r))) =
      Polynomial.resultant (R := R) G H m n := by
  dsimp only
  intro hG hH
  exact congrArg Matrix.det
    (eval₂Hom_pderiv_coefficientProduct_eq_sylvester m n g h φ a hG hH)

end MvPolynomial
