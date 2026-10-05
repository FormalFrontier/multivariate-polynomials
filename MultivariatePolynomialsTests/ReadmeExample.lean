/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IdealOfVars

/-!
# A generic variable-ideal client and its rational specialization

## References

* `MultivariatePolynomials.IdealOfVars`: non-finite generation; see its
  references for Vakil's motivation and the Mathlib ideal API.
-/

universe u v

private theorem readmeVariables (k : Type u) (σ : Type v)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

public theorem MultivariatePolynomialsTests.rationalVariableIdealNotFG :
    ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ
