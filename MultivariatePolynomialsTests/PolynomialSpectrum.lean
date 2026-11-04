/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.PrimeSpectrum
import Mathlib.Data.ZMod.Basic

/-!
# Boundary uses of polynomial maximal-spectrum infinitude

The finite field `ZMod 2` has only two scalar evaluation points, but its
univariate polynomial ring has infinitely many maximal ideals. With no
variables, a polynomial algebra can still have infinite maximal spectrum:
the coefficient ring `Polynomial (ZMod 2)` supplies it. In contrast, the zero
coefficient ring prevents infinitude even when a variable is present.
-/

example : Infinite (MaximalSpectrum (Polynomial (ZMod 2))) :=
  MaximalSpectrum.infinite_polynomial _

example : Infinite (MaximalSpectrum (MvPolynomial PEmpty (Polynomial (ZMod 2)))) :=
  (MaximalSpectrum.infinite_mvPolynomial_iff _ _).mpr
    ⟨inferInstance, Or.inr (MaximalSpectrum.infinite_polynomial _)⟩

example : ¬ Infinite (MaximalSpectrum (MvPolynomial Unit (ZMod 1))) := by
  intro h
  have : Nontrivial (ZMod 1) := (MaximalSpectrum.infinite_mvPolynomial_iff _ _).mp h |>.1
  exact (zero_ne_one : (0 : ZMod 1) ≠ 1) (Subsingleton.elim _ _)
