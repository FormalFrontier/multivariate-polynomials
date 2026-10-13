/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.FiniteSupport
import Mathlib.Data.ZMod.Defs

/-!
# Applications of finite coefficient aggregation

The injectivity criterion for `Finsupp.mapDomain` preserves natural-number
coefficient families under the identity index map, but rules out injectivity
for the constant map from `Fin 2` to `ℕ`.

The joint total-degree and support-cardinality profile of bivariate monomials
has no total decoder for natural-number coefficients. For the zero ring
`ZMod 1`, the recovery criterion instead supplies a total left inverse.
All four applications use the finite-support theorem API directly.

## References

* `MultivariatePolynomials.FiniteSupport`: injectivity of coefficient aggregation
  and the bivariate recovery criterion.
* Mathlib, `Mathlib.Logic.Function.Basic` and `Mathlib.Basic.Nontrivial.Defs`:
  injectivity of the identity and nontriviality excluding subsingleton coefficients.
* Mathlib, `Mathlib.Data.ZMod.Defs`: the canonical zero-ring structure on `ZMod 1`.
-/

namespace MultivariatePolynomialsTests

private theorem mapDomain_id_nat_injective :
    Function.Injective (Finsupp.mapDomain (id : ℕ → ℕ) :
      (ℕ →₀ ℕ) → (ℕ →₀ ℕ)) :=
  (Finsupp.mapDomain_injective_iff (M := ℕ) (id : ℕ → ℕ)).2
    (Or.inl Function.injective_id)

private theorem mapDomain_const_nat_not_injective :
    ¬ Function.Injective (Finsupp.mapDomain (fun _ : Fin 2 => (0 : ℕ)) :
      (Fin 2 →₀ ℕ) → (ℕ →₀ ℕ)) := by
  intro h
  rcases (Finsupp.mapDomain_injective_iff (M := ℕ)
    (fun _ : Fin 2 => (0 : ℕ))).1 h with hinj | hsub
  · have hzero_one : (0 : Fin 2) = 1 := hinj rfl
    exact Nat.zero_ne_one (congrArg Fin.val hzero_one)
  · exact not_subsingleton ℕ hsub

private theorem degree_support_nat_no_decoder :
    ¬ ∃ recover : ((ℕ × ℕ) →₀ ℕ) → ((Fin 2 →₀ ℕ) →₀ ℕ),
      ∀ p : (Fin 2 →₀ ℕ) →₀ ℕ,
        recover (Finsupp.mapDomain
          (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) p) = p := by
  intro h
  exact not_subsingleton ℕ
    ((Finsupp.mapDomain_degree_support_hasLeftInverse_iff ℕ).1 h)

private theorem degree_support_zmod_one_recovery :
    ∃ recover : ((ℕ × ℕ) →₀ ZMod 1) → ((Fin 2 →₀ ℕ) →₀ ZMod 1),
      ∀ p : (Fin 2 →₀ ℕ) →₀ ZMod 1,
        recover (Finsupp.mapDomain
          (fun d : Fin 2 →₀ ℕ => (d.degree, d.support.card)) p) = p := by
  exact (Finsupp.mapDomain_degree_support_hasLeftInverse_iff (ZMod 1)).2
    (inferInstance : Subsingleton (ZMod 1))

end MultivariatePolynomialsTests
