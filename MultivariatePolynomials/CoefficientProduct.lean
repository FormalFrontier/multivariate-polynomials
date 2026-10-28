/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Coefficients of products with variable perturbations

`MvPolynomial.coefficientProduct m n g h` records the first `m + n` coefficients of
`(g + δg) * (h + δh)`. The perturbations use the two blocks of
`Polynomial.degreeLT.basisProd`, with variable coefficients in degrees below `m` and `n`.
The seed polynomials and their product need not satisfy any degree bound.

Evaluation commutes with this family for any coefficient homomorphism and any target
point. Its formal partial derivatives, and hence its evaluated Jacobian entries, are
shifted coefficients of the opposite perturbed factor. The row index is the output
coefficient degree and the column index is the variable. Both blocks may be empty.

## References

The bounded input embedding is `Polynomial.degreeLT.basisProd` from Mathlib. The proofs
use the polynomial coefficient and evaluation APIs and the formal derivations
`MvPolynomial.pderiv`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MvPolynomial

universe u v w

variable {C : Type u} [CommSemiring C]

private theorem sum_smul_basisProd_fst {S : Type v} [Semiring S]
    (m n : ℕ) (a : Fin (m + n) → S) :
    ((∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd S m n s).1 :
      Polynomial S) =
        ∑ i : Fin m, Polynomial.monomial i.val (a (i.castAdd n)) := by
  classical
  let π : (Polynomial.degreeLT S m × Polynomial.degreeLT S n) →ₗ[S] Polynomial S :=
    (Polynomial.degreeLT S m).subtype.comp (LinearMap.fst S _ _)
  change π (∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd S m n s) = _
  rw [map_sum, Fin.sum_univ_add]
  simp [π, Polynomial.X_pow_eq_monomial, Polynomial.smul_monomial]

private theorem sum_smul_basisProd_snd {S : Type v} [Semiring S]
    (m n : ℕ) (a : Fin (m + n) → S) :
    ((∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd S m n s).2 :
      Polynomial S) =
        ∑ j : Fin n, Polynomial.monomial j.val (a (j.natAdd m)) := by
  classical
  let π : (Polynomial.degreeLT S m × Polynomial.degreeLT S n) →ₗ[S] Polynomial S :=
    (Polynomial.degreeLT S n).subtype.comp (LinearMap.snd S _ _)
  change π (∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd S m n s) = _
  rw [map_sum, Fin.sum_univ_add]
  simp [π, Polynomial.X_pow_eq_monomial, Polynomial.smul_monomial]

/-- The first `m + n` coefficients of a product whose factors have independent variable
perturbations in degrees below `m` and `n`. Only the perturbations are degree bounded. -/
noncomputable def coefficientProduct (m n : ℕ) (g h : Polynomial C)
    (r : Fin (m + n)) : MvPolynomial (Fin (m + n)) C :=
  let q := ∑ s : Fin (m + n),
    (X s : MvPolynomial (Fin (m + n)) C) •
      Polynomial.degreeLT.basisProd (MvPolynomial (Fin (m + n)) C) m n s
  ((g.map MvPolynomial.C + (q.1 : Polynomial (MvPolynomial (Fin (m + n)) C))) *
    (h.map MvPolynomial.C + (q.2 : Polynomial (MvPolynomial (Fin (m + n)) C)))).coeff r.val

/-- The two variable perturbations in `coefficientProduct` are the finite monomial sums
in the first and second blocks of variables. -/
@[simp]
theorem coefficientProduct_apply (m n : ℕ) (g h : Polynomial C) (r : Fin (m + n)) :
    coefficientProduct m n g h r =
      ((g.map MvPolynomial.C +
          ∑ i : Fin m, Polynomial.monomial i.val (X (i.castAdd n))) *
        (h.map MvPolynomial.C +
          ∑ j : Fin n, Polynomial.monomial j.val (X (j.natAdd m)))).coeff r.val := by
  classical
  simp only [coefficientProduct, sum_smul_basisProd_fst, sum_smul_basisProd_snd]

private theorem map_seed_add_sum_monomial {σ : Type w} {d : ℕ}
    {R : Type v} [CommSemiring R] (p : Polynomial C) (b : Fin d → σ)
    (φ : C →+* R) (a : σ → R) :
    (p.map MvPolynomial.C +
        ∑ i : Fin d, Polynomial.monomial i.val (X (b i))).map (eval₂Hom φ a) =
      p.map φ + ∑ i : Fin d, Polynomial.monomial i.val (a (b i)) := by
  classical
  ext k
  simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    map_add, map_sum, eval₂Hom_C]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hik : i.val = k
  · subst k
    simp
  · simp [Polynomial.coeff_monomial, hik]

/-- Evaluating the coefficient product at any target point gives the coefficients of
the mapped seeds with the target's own `basisProd` perturbations. -/
theorem eval₂Hom_coefficientProduct {R : Type v} [CommSemiring R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (m + n) → R)
    (r : Fin (m + n)) :
    let q := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    eval₂Hom φ a (coefficientProduct m n g h r) =
      ((g.map φ + (q.1 : Polynomial R)) * (h.map φ + (q.2 : Polynomial R))).coeff
        r.val := by
  classical
  dsimp only
  rw [sum_smul_basisProd_fst, sum_smul_basisProd_snd, coefficientProduct_apply]
  have hmap :
      (((g.map MvPolynomial.C +
            ∑ i : Fin m, Polynomial.monomial i.val (X (i.castAdd n))) *
          (h.map MvPolynomial.C +
            ∑ j : Fin n, Polynomial.monomial j.val (X (j.natAdd m)))).map
          (eval₂Hom φ a)) =
        (g.map φ + ∑ i : Fin m, Polynomial.monomial i.val (a (i.castAdd n))) *
          (h.map φ + ∑ j : Fin n, Polynomial.monomial j.val (a (j.natAdd m))) := by
    rw [Polynomial.map_mul, map_seed_add_sum_monomial, map_seed_add_sum_monomial]
  simpa only [Polynomial.coeff_map] using
    congrArg (fun p : Polynomial R => p.coeff r.val) hmap

private theorem pderiv_coeff_map_C {σ : Type w} (p : Polynomial C) (s : σ) (k : ℕ) :
    pderiv s ((p.map MvPolynomial.C).coeff k) = 0 := by
  simp

private theorem pderiv_coeff_sum_monomial {σ : Type w} {d : ℕ}
    (b : Fin d → σ) (hb : Function.Injective b) (i : Fin d) (k : ℕ) :
    pderiv (b i)
        ((∑ j : Fin d, Polynomial.monomial j.val (X (b j) : MvPolynomial σ C)).coeff k) =
      (Polynomial.X ^ i.val : Polynomial (MvPolynomial σ C)).coeff k := by
  classical
  rw [Polynomial.finsetSum_coeff, map_sum, Finset.sum_eq_single i]
  · by_cases hik : i.val = k
    · subst k
      simp
    · simp [Polynomial.coeff_monomial, hik, Ne.symm hik]
  · intro j _ hji
    by_cases hjk : j.val = k
    · subst k
      simpa using (pderiv_X_of_ne (fun h => hji (hb h)) :
        pderiv (b i) (X (b j) : MvPolynomial σ C) = 0)
    · simp [Polynomial.coeff_monomial, hjk]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem pderiv_coeff_sum_monomial_of_ne {σ : Type w} {d : ℕ}
    (s : σ) (b : Fin d → σ) (hb : ∀ i, b i ≠ s) (k : ℕ) :
    pderiv s
        ((∑ i : Fin d, Polynomial.monomial i.val (X (b i) : MvPolynomial σ C)).coeff k) =
      0 := by
  classical
  rw [Polynomial.finsetSum_coeff, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hik : i.val = k
  · subst k
    simpa using (pderiv_X_of_ne (hb i) : pderiv s (X (b i) : MvPolynomial σ C) = 0)
  · simp [Polynomial.coeff_monomial, hik]

private theorem pderiv_coeff_mul_left {σ : Type w} (s : σ)
    (F H : Polynomial (MvPolynomial σ C)) (i r : ℕ)
    (hF : ∀ k, pderiv s (F.coeff k) =
      (Polynomial.X ^ i : Polynomial (MvPolynomial σ C)).coeff k)
    (hH : ∀ k, pderiv s (H.coeff k) = 0) :
    pderiv s ((F * H).coeff r) = (Polynomial.X ^ i * H).coeff r := by
  classical
  simp only [Polynomial.coeff_mul, map_sum, pderiv_mul, hF, hH, mul_zero, add_zero]

private theorem pderiv_coeff_mul_right {σ : Type w} (s : σ)
    (F H : Polynomial (MvPolynomial σ C)) (i r : ℕ)
    (hF : ∀ k, pderiv s (F.coeff k) = 0)
    (hH : ∀ k, pderiv s (H.coeff k) =
      (Polynomial.X ^ i : Polynomial (MvPolynomial σ C)).coeff k) :
    pderiv s ((F * H).coeff r) = (Polynomial.X ^ i * F).coeff r := by
  rw [mul_comm F H]
  exact pderiv_coeff_mul_left s H F i r hH hF

private theorem castAdd_injective (m n : ℕ) :
    Function.Injective (fun i : Fin m => i.castAdd n) := by
  intro i j hij
  exact Fin.ext (congrArg (fun t : Fin (m + n) => t.val) hij)

private theorem natAdd_injective (m n : ℕ) :
    Function.Injective (fun j : Fin n => j.natAdd m) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg (fun t : Fin (m + n) => t.val) hij)

private theorem castAdd_ne_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≠ j.natAdd m := by
  intro hij
  have hval : i.val = m + j.val := congrArg (fun t : Fin (m + n) => t.val) hij
  have hle : m ≤ m + j.val := Nat.le_add_right m j.val
  rw [← hval] at hle
  exact (Nat.not_le_of_lt i.isLt) hle

/-- A partial derivative in the first variable block is the coefficient of the shifted
second perturbed factor. -/
theorem pderiv_castAdd_coefficientProduct (m n : ℕ) (g h : Polynomial C)
    (r : Fin (m + n)) (i : Fin m) :
    let q := ∑ s : Fin (m + n),
      (X s : MvPolynomial (Fin (m + n)) C) •
        Polynomial.degreeLT.basisProd (MvPolynomial (Fin (m + n)) C) m n s
    pderiv (i.castAdd n) (coefficientProduct m n g h r) =
      (Polynomial.X ^ i.val *
        (h.map MvPolynomial.C +
          (q.2 : Polynomial (MvPolynomial (Fin (m + n)) C)))).coeff r.val := by
  classical
  dsimp only
  rw [sum_smul_basisProd_snd, coefficientProduct_apply]
  apply pderiv_coeff_mul_left
  · intro k
    rw [Polynomial.coeff_add, map_add, pderiv_coeff_map_C, zero_add]
    exact pderiv_coeff_sum_monomial (fun t : Fin m => t.castAdd n)
      (castAdd_injective m n) i k
  · intro k
    rw [Polynomial.coeff_add, map_add, pderiv_coeff_map_C, zero_add]
    exact pderiv_coeff_sum_monomial_of_ne (i.castAdd n)
      (fun j : Fin n => j.natAdd m) (fun j => (castAdd_ne_natAdd i j).symm) k

/-- A partial derivative in the second variable block is the coefficient of the shifted
first perturbed factor. -/
theorem pderiv_natAdd_coefficientProduct (m n : ℕ) (g h : Polynomial C)
    (r : Fin (m + n)) (j : Fin n) :
    let q := ∑ s : Fin (m + n),
      (X s : MvPolynomial (Fin (m + n)) C) •
        Polynomial.degreeLT.basisProd (MvPolynomial (Fin (m + n)) C) m n s
    pderiv (j.natAdd m) (coefficientProduct m n g h r) =
      (Polynomial.X ^ j.val *
        (g.map MvPolynomial.C +
          (q.1 : Polynomial (MvPolynomial (Fin (m + n)) C)))).coeff r.val := by
  classical
  dsimp only
  rw [sum_smul_basisProd_fst, coefficientProduct_apply]
  apply pderiv_coeff_mul_right
  · intro k
    rw [Polynomial.coeff_add, map_add, pderiv_coeff_map_C, zero_add]
    exact pderiv_coeff_sum_monomial_of_ne (j.natAdd m)
      (fun i : Fin m => i.castAdd n) (fun i => castAdd_ne_natAdd i j) k
  · intro k
    rw [Polynomial.coeff_add, map_add, pderiv_coeff_map_C, zero_add]
    exact pderiv_coeff_sum_monomial (fun t : Fin n => t.natAdd m)
      (natAdd_injective m n) j k

/-- In the evaluated Jacobian, the first `m` columns are the guarded shifts of the
second factor perturbed at the target point. Rows are coefficient degrees. -/
theorem eval₂Hom_pderiv_castAdd_coefficientProduct {R : Type v} [CommSemiring R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (m + n) → R)
    (r : Fin (m + n)) (i : Fin m) :
    let q := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    (fun r s : Fin (m + n) => eval₂Hom φ a (pderiv s (coefficientProduct m n g h r)))
        r (i.castAdd n) =
      if i.val ≤ r.val then (h.map φ + (q.2 : Polynomial R)).coeff (r.val - i.val)
      else 0 := by
  classical
  dsimp only
  rw [pderiv_castAdd_coefficientProduct]
  simp only [sum_smul_basisProd_snd]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hir : i.val ≤ r.val
  · simp only [ite_eq_left hir]
    simpa only [Polynomial.coeff_map] using
      congrArg (fun p : Polynomial R => p.coeff (r.val - i.val))
        (map_seed_add_sum_monomial h (fun j : Fin n => j.natAdd m) φ a)
  · simp [hir]

/-- In the evaluated Jacobian, the last `n` columns are the guarded shifts of the
first factor perturbed at the target point. Rows are coefficient degrees. -/
theorem eval₂Hom_pderiv_natAdd_coefficientProduct {R : Type v} [CommSemiring R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (m + n) → R)
    (r : Fin (m + n)) (j : Fin n) :
    let q := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    (fun r s : Fin (m + n) => eval₂Hom φ a (pderiv s (coefficientProduct m n g h r)))
        r (j.natAdd m) =
      if j.val ≤ r.val then (g.map φ + (q.1 : Polynomial R)).coeff (r.val - j.val)
      else 0 := by
  classical
  dsimp only
  rw [pderiv_natAdd_coefficientProduct]
  simp only [sum_smul_basisProd_fst]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hjr : j.val ≤ r.val
  · simp only [ite_eq_left hjr]
    simpa only [Polynomial.coeff_map] using
      congrArg (fun p : Polynomial R => p.coeff (r.val - j.val))
        (map_seed_add_sum_monomial g (fun i : Fin m => i.castAdd n) φ a)
  · simp [hjr]

end MvPolynomial


universe uC uR

namespace Polynomial

private theorem product_eq_iff_coeff_eq_below
    {R : Type uR} [Semiring R]
    (m n : ℕ) (G H u v T : Polynomial R)
    (hG : G.natDegree ≤ m)
    (hH : H.natDegree ≤ n)
    (hu : u.degree < (m : WithBot ℕ))
    (hv : v.degree < (n : WithBot ℕ))
    (hT : T.natDegree ≤ m + n)
    (hTop : T.coeff (m + n) = G.coeff m * H.coeff n) :
    (∀ r : Fin (m + n),
      ((G + u) * (H + v)).coeff r.val = T.coeff r.val) ↔
      (G + u) * (H + v) = T := by
  have hu_coeff := (degree_lt_iff_coeff_zero u m).mp hu
  have hv_coeff := (degree_lt_iff_coeff_zero v n).mp hv
  have hGu : (G + u).natDegree ≤ m := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hG hk),
      hu_coeff k (Nat.le_of_lt hk), add_zero]
  have hHv : (H + v).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hH hk),
      hv_coeff k (Nat.le_of_lt hk), add_zero]
  have hProduct : ((G + u) * (H + v)).natDegree ≤ m + n :=
    (natDegree_mul_le (p := G + u) (q := H + v)).trans (Nat.add_le_add hGu hHv)
  have hTopProduct :
      ((G + u) * (H + v)).coeff (m + n) = G.coeff m * H.coeff n := by
    simp only [coeff_mul_add_eq_of_natDegree_le hGu hHv, coeff_add,
      hu_coeff m le_rfl, hv_coeff n le_rfl, add_zero]
  constructor
  · intro hFinite
    apply (ext_iff_natDegree_le hProduct hT).mpr
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact hFinite ⟨k, hk⟩
    · exact hTopProduct.trans hTop.symm
  · intro hProduct r
    exact congrArg (fun P : Polynomial R => P.coeff r.val) hProduct

end Polynomial

namespace MvPolynomial

/-- Under target-side nominal degree bounds and a fixed nominal top coefficient,
the evaluated coefficient-product equations hold exactly when the entire perturbed
ordinary polynomial product equals the target. -/
theorem eval₂Hom_coefficientProduct_eq_iff
    {C : Type uC} {R : Type uR} [CommSemiring C] [CommSemiring R]
    (m n : ℕ) (g h : Polynomial C) (φ : C →+* R)
    (a : Fin (m + n) → R) (T : Polynomial R)
    (hg : (g.map φ).natDegree ≤ m)
    (hh : (h.map φ).natDegree ≤ n)
    (hT : T.natDegree ≤ m + n)
    (hTop : T.coeff (m + n) = (g.map φ).coeff m * (h.map φ).coeff n) :
    let q := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
    (∀ r : Fin (m + n),
      eval₂Hom φ a (coefficientProduct m n g h r) = T.coeff r.val) ↔
      (g.map φ + (q.1 : Polynomial R)) *
        (h.map φ + (q.2 : Polynomial R)) = T := by
  let q := ∑ s : Fin (m + n), a s • Polynomial.degreeLT.basisProd R m n s
  have hu : (q.1 : Polynomial R).degree < (m : WithBot ℕ) :=
    Polynomial.mem_degreeLT.mp q.1.property
  have hv : (q.2 : Polynomial R).degree < (n : WithBot ℕ) :=
    Polynomial.mem_degreeLT.mp q.2.property
  simpa only [eval₂Hom_coefficientProduct] using
    (Polynomial.product_eq_iff_coeff_eq_below m n (g.map φ) (h.map φ)
      (q.1 : Polynomial R) (q.2 : Polynomial R) T hg hh hu hv hT hTop)

end MvPolynomial
