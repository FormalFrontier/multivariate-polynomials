/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Finite generation under split ideal extension

Extending an ideal along a semiring homomorphism with a retraction preserves and
reflects finite generation. The source and target semirings may be noncommutative
and lie in independent universes. No finiteness or nontriviality hypotheses on
the semirings are required.

## References

* Johan Commelin's `Mathlib.RingTheory.Finiteness.Ideal` supplies
  `Ideal.FG.map`, which preserves finite generation under ideal extension.
* Kenny Lau's `Mathlib.RingTheory.Ideal.Maps` supplies `Ideal.map` and
  its composition and identity laws `Ideal.map_map` and `Ideal.map_id`.
  Mapping back along the retraction and applying these laws reflects finite
  generation.
-/

@[expose] public section

universe u v

namespace Ideal

/-- Finite generation is preserved and reflected by extension along a semiring
homomorphism that admits a retraction. -/
theorem fg_map_iff_of_comp_eq_id {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (I : Ideal R) (f : R →+* S) (g : S →+* R) (hcomp : g.comp f = RingHom.id R) :
    (I.map f).FG ↔ I.FG := by
  constructor
  · intro hfg
    simpa only [Ideal.map_map, hcomp, Ideal.map_id] using Ideal.FG.map hfg g
  · intro hfg
    exact Ideal.FG.map hfg f

end Ideal
