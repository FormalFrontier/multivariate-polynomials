/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.PointSquareZeroQuotient
public import Mathlib.Data.ZMod.Basic

/-!
# Instances of the separated polynomial point quotient

The empty, singleton, zero-ring and infinite-indexed examples exercise the
separated-equivalence interface and its boundary cases.
-/

@[expose] public section

open scoped Polynomial TrivSqZeroExt

namespace PointSquareZeroHeadline

private def emptyPoints : Empty → ℤ := Empty.elim

private noncomputable def empty_equivalence :
    MvPolynomial.pointSquareZeroQuotient emptyPoints ≃ₐ[ℤ[X]]
      TrivSqZeroExt ℤ[X] (MvPolynomial.pointSquareZeroModule emptyPoints) :=
  MvPolynomial.pointSquareZeroAlgEquiv emptyPoints (fun i => i.elim)

private def singletonPoints : PUnit → ℤ := fun _ => 0

private noncomputable def singleton_equivalence :
    MvPolynomial.pointSquareZeroQuotient singletonPoints ≃ₐ[ℤ[X]]
      TrivSqZeroExt ℤ[X] (MvPolynomial.pointSquareZeroModule singletonPoints) :=
  MvPolynomial.pointSquareZeroAlgEquiv singletonPoints (by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim)

private def zeroRingPoints : Bool → ZMod 1 := fun _ => 0

private noncomputable def zeroRing_equivalence :
    MvPolynomial.pointSquareZeroQuotient zeroRingPoints ≃ₐ[(ZMod 1)[X]]
      TrivSqZeroExt (ZMod 1)[X] (MvPolynomial.pointSquareZeroModule zeroRingPoints) :=
  MvPolynomial.pointSquareZeroAlgEquiv zeroRingPoints (by
    intro _ _ _
    have : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
    simpa [zeroRingPoints, this] using (isUnit_one : IsUnit (1 : ZMod 1)))

private def infiniteSeparatedPoints : ℕ → ℚ := fun n => n

private noncomputable def infinite_equivalence :
    MvPolynomial.pointSquareZeroQuotient infiniteSeparatedPoints ≃ₐ[ℚ[X]]
      TrivSqZeroExt ℚ[X] (MvPolynomial.pointSquareZeroModule infiniteSeparatedPoints) :=
  MvPolynomial.pointSquareZeroAlgEquiv infiniteSeparatedPoints (by
    intro i j hij
    apply isUnit_iff_ne_zero.mpr
    apply sub_ne_zero.mpr
    change (i : ℚ) ≠ (j : ℚ)
    exact_mod_cast hij)

end PointSquareZeroHeadline
