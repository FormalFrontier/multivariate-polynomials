/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IdealOfVars

/-!
# Direct-leaf clients

Test-only declarations exercise generic and concrete applications via the
direct theorem import. The unequal-universe client checks that the coefficient
and variable types need not lie in the same universe. The concrete client is
public; the other two are private by the module default.

## References

* `MultivariatePolynomials.IdealOfVars`: the variable-ideal theorem and its
  cited mathematical motivation and Mathlib dependencies.
-/

universe u v

theorem leafGeneric (k : Type u) (σ : Type v)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

public theorem MultivariatePolynomialsTests.rationalInfiniteVariables :
    ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ

theorem leafUnequalUniverses (k : Type) (σ : Type 1)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ
