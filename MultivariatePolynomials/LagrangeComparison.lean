/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Interpolation
public import MultivariatePolynomials.UniqueAlgEquiv
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Comparison with univariate Lagrange interpolation

For a unique variable type over a field, prescribed values at distinct nodes determine
any multivariate polynomial of total degree strictly below the number of nodes. Its image
under `MvPolynomial.uniqueAlgEquiv` is Mathlib's Lagrange interpolant.

For a nonempty selection, the bound `totalDegree ≤ s.card - 1` from finite interpolation
implies this strict bound. For an empty selection, zero agrees with the interpolant, but a
degree-zero bound alone does not determine the polynomial. The comparison applies to any bounded
witness supplied by the commutative-ring interpolation theorem on a nonempty selection.

## References

The degree conversion uses `MvPolynomial.natDegree_uniqueAlgEquiv`. Evaluation is transported
by Mathlib's `MvPolynomial.eval₂_const_uniqueAlgEquiv`, and uniqueness is Mathlib's
`Lagrange.eq_interpolate_of_eval_eq` from `Mathlib.LinearAlgebra.Lagrange`.
-/

@[expose] public section

namespace MvPolynomial

universe uR uσ uι

variable {F : Type uR} {σ : Type uσ} {ι : Type uι} [Field F] [Unique σ]

/-- A polynomial of total degree strictly below the number of distinct nodes, with the
prescribed values there, becomes Mathlib's Lagrange interpolant under the canonical
single-variable equivalence. The univariate degree bound is derived from total degree. -/
theorem uniqueAlgEquiv_eq_interpolate_of_eval_eq
    (s : Finset ι) (a v : ι → F) (p : MvPolynomial σ F)
    (ha : Set.InjOn a (↑s : Set ι)) (hdeg : p.totalDegree < s.card)
    (heval : ∀ i ∈ s, eval (fun _ : σ => a i) p = v i) :
    uniqueAlgEquiv F σ p =
      @Lagrange.interpolate F _ ι (Classical.decEq ι) s a v := by
  classical
  refine @Lagrange.eq_interpolate_of_eval_eq F _ ι (Classical.decEq ι)
    s a v (uniqueAlgEquiv F σ p) ha ?_ ?_
  · calc
      (uniqueAlgEquiv F σ p).degree ≤
          ((uniqueAlgEquiv F σ p).natDegree : WithBot ℕ) :=
        Polynomial.degree_le_natDegree
      _ = (p.totalDegree : WithBot ℕ) := by rw [natDegree_uniqueAlgEquiv]
      _ < (s.card : WithBot ℕ) := by
        simpa only [Nat.cast_withBot, WithBot.coe_lt_coe] using hdeg
  · intro i hi
    calc
      Polynomial.eval (a i) (uniqueAlgEquiv F σ p) =
          eval (fun _ : σ => a i) p := by
        simpa only [Polynomial.eval₂_id, eval₂_id] using
          (eval₂_const_uniqueAlgEquiv (f := p) (φ := RingHom.id F) (a := a i))
      _ = v i := heval i hi

/-- On a nonempty selection, the finite-interpolation bound `s.card - 1` suffices to
identify a witness with Mathlib's Lagrange interpolant. Nonemptiness is needed because
subtraction in this bound is saturating subtraction on natural numbers. -/
theorem uniqueAlgEquiv_eq_interpolate_of_eval_eq_of_totalDegree_le
    (s : Finset ι) (a v : ι → F) (p : MvPolynomial σ F) (hs : s.Nonempty)
    (ha : Set.InjOn a (↑s : Set ι)) (hdeg : p.totalDegree ≤ s.card - 1)
    (heval : ∀ i ∈ s, eval (fun _ : σ => a i) p = v i) :
    uniqueAlgEquiv F σ p =
      @Lagrange.interpolate F _ ι (Classical.decEq ι) s a v := by
  exact uniqueAlgEquiv_eq_interpolate_of_eval_eq s a v p ha
    (hdeg.trans_lt (Nat.sub_lt hs.card_pos zero_lt_one)) heval

end MvPolynomial
