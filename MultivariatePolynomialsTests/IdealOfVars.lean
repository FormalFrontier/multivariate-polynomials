/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials

/-!
# Aggregate-import clients

Test theorems check the generic semiring/infinite-variable interface and its
specialization to polynomials over `ℚ` indexed by `ℕ`. The concrete client is
public in the test namespace; neither is additional production API.
-/

private theorem aggregateGeneric (k : Type*) (σ : Type*)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

public theorem MultivariatePolynomialsTests.idealOfVarsRatNotFG :
    ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ
