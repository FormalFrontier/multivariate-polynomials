/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameFinitePresentation
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Applications of the finite-presentation renaming criterion

With integer coefficients, shifting natural-number indices by one is finitely
presented: only the zeroth target variable is missed and no source indices
collide. Predecessor renaming is also finitely presented: no target variable is
missed and the collision participants are exactly `0` and `1`. Projection from
`ℕ × Bool` to `ℕ` is not finitely presented, since every source index participates
in a collision. All these examples have infinitely many source variables.

Each application uses `MvPolynomial.finitePresentation_rename_iff` through its
public interface. The algebra structure is induced by the displayed renaming,
with the source polynomial ring as base. Shifting indices sends `X n` to
`X (n + 1)`, not to a power of `X n`. All declarations are private.

## References

* `MultivariatePolynomials.RenameFinitePresentation`: the finite-presentation
  criterion for variable renaming over commutative rings.
* Mathlib, `Mathlib.Data.Set.Finite.Basic`: finite subsets and infinite universes.
* Mathlib, `Mathlib.Data.Nat.Basic` and `Mathlib.Data.Bool.Basic`: predecessor
  fibres and opposite Boolean coordinates.
-/

namespace MultivariatePolynomialsTests

private theorem finitePresentation_rename_succ_int :
    @Algebra.FinitePresentation (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) _ _
      (MvPolynomial.rename (R := ℤ) Nat.succ).toRingHom.toAlgebra := by
  apply (MvPolynomial.finitePresentation_rename_iff (R := ℤ) Nat.succ).mpr
  right
  constructor
  · refine (Set.finite_singleton (0 : ℕ)).subset ?_
    intro n hn
    cases n with
    | zero => exact Set.mem_singleton 0
    | succ n => exact (hn ⟨n, rfl⟩).elim
  · refine Set.finite_empty.subset ?_
    rintro i ⟨j, hij, h⟩
    exact (hij (Nat.succ.inj h)).elim

private theorem finitePresentation_rename_pred_int :
    @Algebra.FinitePresentation (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) _ _
      (MvPolynomial.rename (R := ℤ) Nat.pred).toRingHom.toAlgebra := by
  apply (MvPolynomial.finitePresentation_rename_iff (R := ℤ) Nat.pred).mpr
  right
  constructor
  · refine Set.finite_empty.subset ?_
    intro n hn
    exact (hn ⟨n + 1, rfl⟩).elim
  · refine ((Set.finite_singleton (1 : ℕ)).insert 0).subset ?_
    rintro i ⟨j, hij, hpred⟩
    cases i <;> cases j <;> simp_all

private theorem not_finitePresentation_rename_fst_int :
    ¬ @Algebra.FinitePresentation (MvPolynomial (ℕ × Bool) ℤ) (MvPolynomial ℕ ℤ) _ _
      (MvPolynomial.rename (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  intro hfp
  rcases (MvPolynomial.finitePresentation_rename_iff
    (R := ℤ) (Prod.fst : ℕ × Bool → ℕ)).mp hfp with hR | ⟨_, hfinite⟩
  · exact (not_subsingleton ℤ) hR
  · apply Set.infinite_univ (α := ℕ × Bool)
    apply hfinite.subset
    rintro ⟨n, b⟩ _
    exact ⟨(n, !b), fun h => Bool.self_ne_not b (congrArg Prod.snd h), rfl⟩

end MultivariatePolynomialsTests
