/-
Copyright (c) 2026 Shuttle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuttle
-/
module

public import MultivariatePolynomials.CoefficientProductJacobian
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Coefficient-product derivatives and Sylvester matrices

The evaluated derivative of the coefficient-product map is the matrix of
`Polynomial.sylvesterMap` in ascending coefficient coordinates. The input basis
places the first perturbation block before the second: the first block is
multiplied by the second factor, and the second block by the first factor.

Only upper bounds on the target polynomials are required. The source
coefficients may lie in a commutative semiring, independently of the target
commutative ring, and the target point need not lift to the source.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

universe u v

namespace Polynomial

/-- The underlying polynomial of the Sylvester map, with its original factor
and summand order. -/
theorem coe_sylvesterMap_apply {R : Type v} [CommRing R] {m n : ℕ}
    (f g : Polynomial R) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (pq : degreeLT R m × degreeLT R n) :
    (sylvesterMap f g hf hg pq : Polynomial R) =
      f * (pq.2 : Polynomial R) + g * (pq.1 : Polynomial R) := rfl

end Polynomial

namespace MvPolynomial

variable {C : Type u} [CommSemiring C]

/-- The evaluated coefficient-product derivative is the matrix of the public
Sylvester map in the reindexed product basis. This basis agrees pointwise with
`Polynomial.degreeLT.basisProd`, so its first block records the first
perturbation and its second block records the second perturbation. -/
theorem eval₂Hom_pderiv_coefficientProduct_eq_toMatrix_sylvesterMap
    {R : Type v} [CommRing R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R)
    (a : Fin (m + n) → R) :
    let qa := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    let G := g.map φ + (qa.1 : Polynomial R)
    let H := h.map φ + (qa.2 : Polynomial R)
    ∀ hG : G.natDegree ≤ m, ∀ hH : H.natDegree ≤ n,
      (fun r s : Fin (m + n) =>
        eval₂Hom φ a (pderiv s (coefficientProduct m n g h r))) =
      (Polynomial.sylvesterMap G H hG hH).toMatrix
        (((Polynomial.degreeLT.basis R m).prod
          (Polynomial.degreeLT.basis R n)).reindex finSumFinEquiv)
        (Polynomial.degreeLT.basis R (m + n)) := by
  classical
  let qa := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
  let G := g.map φ + (qa.1 : Polynomial R)
  let H := h.map φ + (qa.2 : Polynomial R)
  let B := ((Polynomial.degreeLT.basis R m).prod
    (Polynomial.degreeLT.basis R n)).reindex finSumFinEquiv
  let J : Matrix (Fin (m + n)) (Fin (m + n)) R := fun r s =>
    eval₂Hom φ a (pderiv s (coefficientProduct m n g h r))
  change ∀ (hG : G.natDegree ≤ m) (hH : H.natDegree ≤ n),
    J = (Polynomial.sylvesterMap G H hG hH).toMatrix B
      (Polynomial.degreeLT.basis R (m + n))
  intro hG hH
  have hBleft (i : Fin m) :
      B (Fin.castAdd n i) = (Polynomial.degreeLT.basis R m i, 0) := by
    change (((Polynomial.degreeLT.basis R m).prod
      (Polynomial.degreeLT.basis R n)).reindex finSumFinEquiv) (Fin.castAdd n i) = _
    rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
      Module.Basis.prod_apply]
    rfl
  have hBright (j : Fin n) :
      B (Fin.natAdd m j) = (0, Polynomial.degreeLT.basis R n j) := by
    change (((Polynomial.degreeLT.basis R m).prod
      (Polynomial.degreeLT.basis R n)).reindex finSumFinEquiv) (Fin.natAdd m j) = _
    rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
      Module.Basis.prod_apply]
    rfl
  have hB (s : Fin (m + n)) : Polynomial.degreeLT.basisProd R m n s = B s := by
    refine Fin.addCases ?_ ?_ s
    · intro i
      calc
        _ = (Polynomial.degreeLT.basis R m i, 0) := by
          rw [Polynomial.degreeLT.basisProd_castAdd]
        _ = _ := (hBleft i).symm
    · intro j
      calc
        _ = (0, Polynomial.degreeLT.basis R n j) := by
          rw [Polynomial.degreeLT.basisProd_natAdd]
        _ = _ := (hBright j).symm
  have hdelta (s : Fin (m + n)) :
      (∑ t : Fin (m + n), (if t = s then (1 : R) else 0) •
        Polynomial.degreeLT.basisProd R m n t) =
      Polynomial.degreeLT.basisProd R m n s := by
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  have hrow (r s : Fin (m + n)) :
      (Matrix.mulVec J (fun t => if t = s then 1 else 0)) r = J r s := by
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  have hcolumn (r s : Fin (m + n)) :
      J r s =
      (H * ((Polynomial.degreeLT.basisProd R m n s).1 : Polynomial R) +
        G * ((Polynomial.degreeLT.basisProd R m n s).2 : Polynomial R)).coeff r.val := by
    have ha := congrFun (eval₂Hom_pderiv_coefficientProduct_mulVec m n g h φ a
      (fun t => if t = s then 1 else 0)) r
    change (Matrix.mulVec J (fun t => if t = s then 1 else 0)) r =
      (H * ((∑ t : Fin (m + n), (if t = s then (1 : R) else 0) •
          Polynomial.degreeLT.basisProd R m n t).1 : Polynomial R) +
        G * ((∑ t : Fin (m + n), (if t = s then (1 : R) else 0) •
          Polynomial.degreeLT.basisProd R m n t).2 : Polynomial R)).coeff r.val at ha
    rw [hrow r s, hdelta s] at ha
    exact ha
  have hentry (r s : Fin (m + n)) :
      (Polynomial.sylvesterMap G H hG hH).toMatrix B
          (Polynomial.degreeLT.basis R (m + n)) r s =
      (G * ((Polynomial.degreeLT.basisProd R m n s).2 : Polynomial R) +
        H * ((Polynomial.degreeLT.basisProd R m n s).1 : Polynomial R)).coeff r.val := by
    calc
      _ = (Polynomial.degreeLT.basis R (m + n)).repr
          (Polynomial.sylvesterMap G H hG hH (B s)) r := by
        rw [LinearMap.toMatrix_apply]
      _ = (Polynomial.degreeLT.basis R (m + n)).repr
          (Polynomial.sylvesterMap G H hG hH
            (Polynomial.degreeLT.basisProd R m n s)) r :=
        congrArg (fun pq : Polynomial.degreeLT R m × Polynomial.degreeLT R n =>
          (Polynomial.degreeLT.basis R (m + n)).repr
            (Polynomial.sylvesterMap G H hG hH pq) r) (hB s).symm
      _ = (Polynomial.sylvesterMap G H hG hH
          (Polynomial.degreeLT.basisProd R m n s) : Polynomial R).coeff r.val := by
        rw [Polynomial.degreeLT.basis_repr]
      _ = _ := congrArg (fun p : Polynomial R => p.coeff r.val)
        (Polynomial.coe_sylvesterMap_apply G H hG hH
          (Polynomial.degreeLT.basisProd R m n s))
  ext r s
  calc
    J r s = (H * ((Polynomial.degreeLT.basisProd R m n s).1 : Polynomial R) +
        G * ((Polynomial.degreeLT.basisProd R m n s).2 : Polynomial R)).coeff r.val := hcolumn r s
    _ = (G * ((Polynomial.degreeLT.basisProd R m n s).2 : Polynomial R) +
        H * ((Polynomial.degreeLT.basisProd R m n s).1 : Polynomial R)).coeff r.val :=
      congrArg (fun p : Polynomial R => p.coeff r.val)
        (add_comm (H * ((Polynomial.degreeLT.basisProd R m n s).1 : Polynomial R))
          (G * ((Polynomial.degreeLT.basisProd R m n s).2 : Polynomial R)))
    _ = _ := (hentry r s).symm

/-- The evaluated coefficient-product derivative is the canonical Sylvester
matrix with the chosen target degree bounds, even when the degrees are smaller
than those bounds. -/
theorem eval₂Hom_pderiv_coefficientProduct_eq_sylvester
    {R : Type v} [CommRing R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R)
    (a : Fin (m + n) → R) :
    let qa := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    let G := g.map φ + (qa.1 : Polynomial R)
    let H := h.map φ + (qa.2 : Polynomial R)
    ∀ _hG : G.natDegree ≤ m, ∀ _hH : H.natDegree ≤ n,
      (fun r s : Fin (m + n) =>
        eval₂Hom φ a (pderiv s (coefficientProduct m n g h r))) =
      Polynomial.sylvester G H m n := by
  let qa := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
  let G := g.map φ + (qa.1 : Polynomial R)
  let H := h.map φ + (qa.2 : Polynomial R)
  change ∀ (_hG : G.natDegree ≤ m) (_hH : H.natDegree ≤ n),
    (fun r s : Fin (m + n) =>
      eval₂Hom φ a (pderiv s (coefficientProduct m n g h r))) =
    Polynomial.sylvester G H m n
  intro hG hH
  exact (eval₂Hom_pderiv_coefficientProduct_eq_toMatrix_sylvesterMap
    m n g h φ a hG hH).trans (Polynomial.toMatrix_sylvesterMap' G H hG hH)

end MvPolynomial
