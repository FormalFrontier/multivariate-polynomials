/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.IdealOfVars

/-!
# Direct-leaf clients

Test-only declarations exercise generic and concrete applications via the
direct theorem import. The unequal-universe client checks that the coefficient
and variable types need not lie in the same universe. All three declarations
are private by the module default, even without an explicit `private` keyword.
-/

universe u v

theorem leafGeneric (k : Type u) (σ : Type v)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ

theorem leafConcrete : ¬ (MvPolynomial.idealOfVars ℕ ℚ).FG :=
  MvPolynomial.idealOfVars_not_fg ℚ ℕ

theorem leafUnequalUniverses (k : Type) (σ : Type 1)
    [CommSemiring k] [Nontrivial k] [Infinite σ] :
    ¬ (MvPolynomial.idealOfVars σ k).FG :=
  MvPolynomial.idealOfVars_not_fg k σ
