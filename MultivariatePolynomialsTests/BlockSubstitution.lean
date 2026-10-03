/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.BlockSubstitution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

namespace BlockSubstitutionClient

open MvPolynomial

private theorem twoBlocksStructural {R : Type*} [CommSemiring R]
    (q : MvPolynomial (Fin 2) R) :
    blockSubst (X (0 : Fin 2) + X 1) q =
      rename (Prod.mk (0 : Fin 2)) q + rename (Prod.mk (1 : Fin 2)) q := by
  simp [blockSubst]

private theorem twoBlocks {R : Type*} [CommSemiring R]
    (q : MvPolynomial (Fin 2) R) (x : Fin 2 × Fin 2 → R) :
    eval x (blockSubst (X (0 : Fin 2) + X 1) q) =
      eval (fun j => x (0, j)) q + eval (fun j => x (1, j)) q := by
  rw [eval_blockSubst]
  simp

private theorem twoStages {ι κ υ R : Type*} [CommSemiring R]
    (p : MvPolynomial ι R) (q : MvPolynomial κ R) (r : MvPolynomial υ R)
    (x : (ι × κ) × υ → R) :
    eval x (blockSubst (blockSubst p q) r) =
      eval (fun i => eval (fun j => eval (fun k => x ((i, j), k)) r) q) p := by
  simp only [eval_blockSubst]

private theorem twoStagesForward {ι κ υ R : Type*} [CommSemiring R]
    (p : MvPolynomial ι R) (q : MvPolynomial κ R) (r : MvPolynomial υ R)
    (hp : ∀ y : ι → R, eval y p = 0 → y = 0)
    (hq : ∀ z : κ → R, eval z q = 0 → z = 0)
    (hr : ∀ w : υ → R, eval w r = 0 → w = 0)
    (x : (ι × κ) × υ → R) :
    eval x (blockSubst (blockSubst p q) r) = 0 → x = 0 :=
  eval_blockSubst_eq_zero_imp _ r
    (fun y => eval_blockSubst_eq_zero_imp p q hp hq y) hr x

private theorem twoStagesIff {ι κ υ R : Type*} [CommSemiring R]
    (p : MvPolynomial ι R) (q : MvPolynomial κ R) (r : MvPolynomial υ R)
    (hp : ∀ y : ι → R, eval y p = 0 ↔ y = 0)
    (hq : ∀ z : κ → R, eval z q = 0 ↔ z = 0)
    (hr : ∀ w : υ → R, eval w r = 0 ↔ w = 0)
    (x : (ι × κ) × υ → R) :
    eval x (blockSubst (blockSubst p q) r) = 0 ↔ x = 0 :=
  eval_blockSubst_eq_zero_iff _ r
    (fun y => eval_blockSubst_eq_zero_iff p q hp hq y) hr x

private theorem homogeneousDegree {ι κ R : Type*} [CommSemiring R]
    (p : MvPolynomial ι R) (q : MvPolynomial κ R) (d e : ℕ)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) :
    (blockSubst p q).IsHomogeneous (e * d) := by
  change (aeval (fun i => rename (Prod.mk i) q) p).IsHomogeneous (e * d)
  exact hp.aeval _ (fun i => hq.rename_isHomogeneous)

private theorem exactTotalDegree {ι κ R : Type*} [CommSemiring R]
    [Nontrivial R] [Nonempty ι] [Nonempty κ]
    (p : MvPolynomial ι R) (q : MvPolynomial κ R) (d e : ℕ)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e)
    (hpzero : ∀ y : ι → R, eval y p = 0 → y = 0)
    (hqzero : ∀ z : κ → R, eval z q = 0 → z = 0) :
    (blockSubst p q).totalDegree = e * d := by
  have hnonzero : blockSubst p q ≠ 0 :=
    ne_zero_of_eval_eq_zero_imp _
      (fun x => eval_blockSubst_eq_zero_imp p q hpzero hqzero x)
  exact (homogeneousDegree p q d e hp hq).totalDegree hnonzero

private theorem singleVariableZeroIff {R : Type*} [CommSemiring R]
    (z : Fin 1 → R) :
    eval z (X (0 : Fin 1) : MvPolynomial (Fin 1) R) = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hi, eval_X, Pi.zero_apply] using hz
  · intro hz
    subst z
    simp

private theorem finiteField (x : Fin 1 × Fin 1 → ZMod 2) :
    eval x (blockSubst (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 2))
      (X (0 : Fin 1))) = 0 ↔ x = 0 :=
  eval_blockSubst_eq_zero_iff _ _ singleVariableZeroIff singleVariableZeroIff x

private theorem emptyOuter {R : Type*} [CommSemiring R]
    (x : PEmpty × Fin 1 → R) :
    eval x (blockSubst (0 : MvPolynomial PEmpty R)
      (X (0 : Fin 1))) = 0 ↔ x = 0 := by
  apply eval_blockSubst_eq_zero_iff
  · intro y
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by simp⟩
  · exact singleVariableZeroIff

private theorem zeroRing (p q : MvPolynomial (Fin 2) PUnit)
    (x : Fin 2 × Fin 2 → PUnit) :
    eval x (blockSubst p q) = 0 ↔ x = 0 := by
  apply eval_blockSubst_eq_zero_iff
  · intro y
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  · intro z
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

private theorem constantBlockForward (x : Fin 1 × Fin 1 → ZMod 2) :
    eval x (blockSubst (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 2))
      (C 1 : MvPolynomial (Fin 1) (ZMod 2))) = 0 → x = 0 := by
  apply eval_blockSubst_eq_zero_imp
  · intro y hy
    exact (singleVariableZeroIff y).mp hy
  · intro z hz
    exact (one_ne_zero (by simpa only [eval_C] using hz)).elim

private theorem constantBlockNotIff :
    ¬ ∀ x : Fin 1 × Fin 1 → ZMod 2,
      eval x (blockSubst (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 2))
        (C 1 : MvPolynomial (Fin 1) (ZMod 2))) = 0 ↔ x = 0 := by
  intro h
  have hc : (1 : ZMod 2) = 0 := by
    simpa only [eval_blockSubst, eval_X, eval_C] using (h 0).mpr rfl
  exact one_ne_zero hc

end BlockSubstitutionClient
