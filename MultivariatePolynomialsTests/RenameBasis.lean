/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameBasis
import Mathlib.Data.ZMod.Basic

/-!
# Examples of the monomial basis for renaming

For `ℤ[u] → ℤ[x,y]` sending `u` to `x`, the basis vectors are `y^n` and
`5x²y³` has coordinate `5u²` at the missing exponent `3`.
A Boolean variable swap checks the same-carrier, nonidentity scalar action.
-/

noncomputable section

namespace MvPolynomial.RenameBasisExamples

private def includeX : Unit ↪ Bool where
  toFun _ := false
  inj' _ _ _ := Subsingleton.elim _ _

private def missingY : {j : Bool // j ∉ Set.range includeX} :=
  ⟨true, by rintro ⟨i, hi⟩; cases hi⟩

-- These input data do not use the basis or either characteristic equation.
private def inputExponent : Bool →₀ ℕ :=
  Finsupp.single false 2 + Finsupp.single true 3

private def input : MvPolynomial Bool ℤ := monomial inputExponent 5

example (n : ℕ) :
    (renameMonomialBasis (R := ℤ) includeX :
      @Module.Basis ({j : Bool // j ∉ Set.range includeX} →₀ ℕ)
        (MvPolynomial Unit ℤ) (MvPolynomial Bool ℤ) _ _
        (@Algebra.toModule (MvPolynomial Unit ℤ) (MvPolynomial Bool ℤ) _ _
          (rename (R := ℤ) (includeX : Unit → Bool)).toRingHom.toAlgebra))
      (Finsupp.single missingY n) = (X true : MvPolynomial Bool ℤ) ^ n := by
  rw [renameMonomialBasis_apply, Finsupp.embDomain_eq_mapDomain,
    Finsupp.mapDomain_single]
  exact X_pow_eq_monomial.symm

example :
    input = C (5 : ℤ) * X false ^ 2 * X true ^ 3 ∧ input ≠ 0 ∧
      (@Module.Basis.repr ({j : Bool // j ∉ Set.range includeX} →₀ ℕ)
        (MvPolynomial Unit ℤ) (MvPolynomial Bool ℤ) _ _
        (@Algebra.toModule (MvPolynomial Unit ℤ) (MvPolynomial Bool ℤ) _ _
          (rename (R := ℤ) (includeX : Unit → Bool)).toRingHom.toAlgebra)
        (renameMonomialBasis (R := ℤ) includeX)) input =
        Finsupp.single (Finsupp.single missingY 3)
          (C (5 : ℤ) * (X () : MvPolynomial Unit ℤ) ^ 2) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp only [input, inputExponent, monomial_add_single, C_mul_X_pow_eq_monomial]
  · simp only [input, ne_eq, monomial_eq_zero]
    decide
  · have hmissing :
        Finsupp.comapDomain
          (Function.Embedding.subtype (fun j => j ∉ Set.range includeX)) inputExponent
          (Function.Embedding.subtype
            (fun j => j ∉ Set.range includeX)).injective.injOn =
          Finsupp.single missingY 3 := by
      ext j
      rcases j with ⟨j, hj⟩
      cases j with
      | false => exact False.elim (hj ⟨(), rfl⟩)
      | true => simp [inputExponent, missingY]
    have hsource :
        Finsupp.comapDomain includeX inputExponent includeX.injective.injOn =
          Finsupp.single () 2 := by
      refine Finsupp.ext fun i => ?_
      cases i
      change inputExponent false = (Finsupp.single () 2 : Unit →₀ ℕ) ()
      simp [inputExponent]
    rw [input, renameMonomialBasis_repr_monomial, hmissing, hsource,
      C_mul_X_pow_eq_monomial]

private def swap : Bool ↪ Bool where
  toFun := Bool.not
  inj' a b h := by simpa using congrArg Bool.not h

-- Although source and target carriers agree, scalars act by swapping variables.
-- Its empty complement has only the zero exponent.
example :
    (@Module.Basis.repr ({j : Bool // j ∉ Set.range swap} →₀ ℕ)
      (MvPolynomial Bool ℤ) (MvPolynomial Bool ℤ) _ _
      (@Algebra.toModule (MvPolynomial Bool ℤ) (MvPolynomial Bool ℤ) _ _
        (rename (R := ℤ) (swap : Bool → Bool)).toRingHom.toAlgebra)
      (renameMonomialBasis (R := ℤ) swap)) (X false) =
      Finsupp.single 0 (X true : MvPolynomial Bool ℤ) := by
  classical
  have hmissing :
      Finsupp.comapDomain
        (Function.Embedding.subtype (fun j => j ∉ Set.range swap))
        (Finsupp.single false 1 : Bool →₀ ℕ)
        (Function.Embedding.subtype (fun j => j ∉ Set.range swap)).injective.injOn =
        0 := by
    ext j
    exact False.elim (j.property ⟨!j.val, by
      change (!(!j.val)) = j.val
      cases j.val <;> rfl⟩)
  have hsource :
      Finsupp.comapDomain swap (Finsupp.single false 1 : Bool →₀ ℕ) swap.injective.injOn =
        Finsupp.single true 1 := by
    refine Finsupp.ext fun i => ?_
    change (Finsupp.single false 1 : Bool →₀ ℕ) (!i) = Finsupp.single true 1 i
    cases i <;> simp
  simpa only [X, hmissing, hsource] using
    renameMonomialBasis_repr_monomial (R := ℤ) swap (Finsupp.single false 1) 1

-- With no source or target variables and zero coefficients, every vector is zero.
example :
    (renameMonomialBasis (R := ZMod 1) (Function.Embedding.refl PEmpty) :
      @Module.Basis
        ({j : PEmpty // j ∉ Set.range (Function.Embedding.refl PEmpty)} →₀ ℕ)
        (MvPolynomial PEmpty (ZMod 1)) (MvPolynomial PEmpty (ZMod 1)) _ _
        (@Algebra.toModule (MvPolynomial PEmpty (ZMod 1))
          (MvPolynomial PEmpty (ZMod 1)) _ _
          (rename (R := ZMod 1)
            (Function.Embedding.refl PEmpty : PEmpty → PEmpty)).toRingHom.toAlgebra)) 0 =
      0 := by
  exact Subsingleton.elim _ _

end MvPolynomial.RenameBasisExamples
