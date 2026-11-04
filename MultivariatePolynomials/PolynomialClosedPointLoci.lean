/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.PolynomialClosedPoints
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Polynomial zero loci and algebraic-closure orbits

For an algebraic closure `L` of a field `K`, the closed point corresponding to the
orbit of `a : L` has ideal equal to the kernel of evaluation at `a`. It is also the
contraction of the ideal `(X - C a)` along the coefficient map `K[X] → L[X]`.
The evaluation-kernel fibre over any closed point is its corresponding orbit.

For every polynomial over `K`, the equivalence sends its roots modulo algebra
automorphisms to the closed points whose ideals contain that polynomial. These
are set-level statements, with no separability or topological assumptions.

## Implementation notes

The representative ideal has the minimal-polynomial ideal as its simp normal form.
The kernel and coefficient-comap formulas below are explicit alternative rewrites.

## References

This module uses the correspondence in
`MultivariatePolynomials.PolynomialClosedPoints` together with Mathlib's
minimal-polynomial and scalar-evaluation kernels, orbit quotient, and equivalence APIs.
-/

@[expose] public section

universe u v

namespace Polynomial

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]

/-- The ideal of the closed point associated to the orbit of `a` is the kernel of
polynomial evaluation at `a` over `K`. -/
theorem algAutOrbitEquivMaximalSpectrum_asIdeal_ker_aeval (a : L) :
    (algAutOrbitEquivMaximalSpectrum K L
      (Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L) a)).asIdeal =
      RingHom.ker ((aeval a : Polynomial K →ₐ[K] L).toRingHom) := by
  exact (algAutOrbitEquivMaximalSpectrum_asIdeal_mk K L a).trans
    (minpoly.ker_aeval_eq_span_minpoly K a).symm

/-- The ideal associated to the orbit of `a` is the contraction of `(X - C a)`
along the polynomial coefficient map induced by the given `K`-algebra structure on `L`. -/
theorem algAutOrbitEquivMaximalSpectrum_asIdeal_comap (a : L) :
    (algAutOrbitEquivMaximalSpectrum K L
      (Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L) a)).asIdeal =
      Ideal.comap (mapRingHom (algebraMap K L))
        (Ideal.span ({X - C a} : Set (Polynomial L))) := by
  have hcomp :
      (evalRingHom a).comp (mapRingHom (algebraMap K L)) =
        (aeval a : Polynomial K →ₐ[K] L).toRingHom :=
    RingHom.ext fun p => eval_map_algebraMap p a
  rw [algAutOrbitEquivMaximalSpectrum_asIdeal_ker_aeval K L a,
    ← ker_evalRingHom a, RingHom.comap_ker, hcomp]

/-- A polynomial belongs to the ideal of the closed point associated to `a`
if and only if it vanishes at `a`. -/
theorem mem_algAutOrbitEquivMaximalSpectrum_asIdeal_mk (a : L) (p : Polynomial K) :
    p ∈ (algAutOrbitEquivMaximalSpectrum K L
      (Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L) a)).asIdeal ↔
      aeval a p = 0 := by
  rw [algAutOrbitEquivMaximalSpectrum_asIdeal_ker_aeval K L a, RingHom.mem_ker]
  rfl

/-- The elements whose evaluation kernel is the ideal corresponding to an orbit
class `q` form exactly the orbit attached to `q`. -/
theorem algAutOrbitEquivMaximalSpectrum_fiber_ker_aeval
    (q : MulAction.orbitRel.Quotient (L ≃ₐ[K] L) L) :
    {a : L | RingHom.ker ((aeval a : Polynomial K →ₐ[K] L).toRingHom) =
      (algAutOrbitEquivMaximalSpectrum K L q).asIdeal} = q.orbit := by
  ext a
  rw [Set.mem_ofPred_eq, ← algAutOrbitEquivMaximalSpectrum_asIdeal_ker_aeval K L a,
    MulAction.orbitRel.Quotient.mem_orbit]
  constructor
  · intro h
    exact (algAutOrbitEquivMaximalSpectrum K L).injective (MaximalSpectrum.ext h)
  · intro h
    exact congrArg (fun r => (algAutOrbitEquivMaximalSpectrum K L r).asIdeal) h

/-- The closed points whose ideals contain `p` are the images of the roots of `p`
in the algebraic closure, first under the orbit quotient and then under the
orbit-to-closed-point equivalence. This includes zero and constant polynomials. -/
theorem algAutOrbitEquivMaximalSpectrum_image_roots (p : Polynomial K) :
    algAutOrbitEquivMaximalSpectrum K L ''
        ((Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L)) ''
          {a : L | aeval a p = 0}) =
      {m : MaximalSpectrum (Polynomial K) | p ∈ m.asIdeal} := by
  ext m
  constructor
  · rintro ⟨q, ⟨a, ha, rfl⟩, rfl⟩
    exact (mem_algAutOrbitEquivMaximalSpectrum_asIdeal_mk K L a p).mpr ha
  · intro hm
    obtain ⟨q, rfl⟩ := (algAutOrbitEquivMaximalSpectrum K L).surjective m
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    exact ⟨_, ⟨a, (mem_algAutOrbitEquivMaximalSpectrum_asIdeal_mk K L a p).mp hm, rfl⟩,
      rfl⟩

end Polynomial
