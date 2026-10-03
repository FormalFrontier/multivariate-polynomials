/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials

/-!
# Aggregate-import clients

Private-by-module test theorems check the generic semiring/infinite-variable
interface and its specialization to polynomials over `ℚ` indexed by `ℕ`.
These are build-checked clients, not additional public API.
-/

private theorem aggregateGeneric (k : Type*) (σ : Type*)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

private theorem aggregateConcrete : ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ
