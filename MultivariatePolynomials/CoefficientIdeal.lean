/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Coefficient ideals over commutative semirings

Extending an ideal along `MvPolynomial.C` gives exactly the polynomials with
coefficients in that ideal. As an `R`-submodule, this extension is Mathlib's
`MvPolynomial.coeffsIn`, for the canonical action `r • p = C r * p`.
Contraction along `C` recovers the coefficient ideal. The kernel of a map on
coefficients is its coefficient kernel extended along `C`.

The coefficient and variable universes are independent; for coefficient maps,
the source and target coefficient universes are independent as well. No
finiteness, nontriviality, cancellation or additive inverses are required.

## References

* Mathlib's `Mathlib.Algebra.MvPolynomial.Basic`, by Johannes Hölzl,
  Johan Commelin and Mario Carneiro, supplies `coeffsIn`, its monomial-span
  characterization and its compatibility with submodule multiplication.
* Kenny Lau's `Mathlib.RingTheory.Ideal.Maps` supplies ideal extension,
  contraction and homomorphism kernels. His `Mathlib.RingTheory.Polynomial.Basic`
  contains the ring versions `MvPolynomial.mem_map_C_iff` and
  `MvPolynomial.ker_map`. The submodule identifications below recover those
  statements for rings and also apply to semirings. The extension argument
  uses the `coeffsIn` span and multiplication APIs, rather than a separate
  coefficient-by-coefficient induction on the extended ideal.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {S : Type v} {σ : Type w}
variable [CommSemiring R] [CommSemiring S]

/-- A coefficient ideal extended along `C`, with scalars restricted to `R`,
is precisely the coefficient submodule. The `R`-action is the canonical
polynomial action through `C`. -/
theorem coeffsIn_eq_restrictScalars_map_C (I : Ideal R) :
    coeffsIn σ (I : Submodule R R) =
      (Ideal.map (C : R →+* MvPolynomial σ R) I).restrictScalars R := by
  refine le_antisymm (coeffsIn_le.mpr ?_) ?_
  · intro r hr d
    have hC : C r ∈ Ideal.map (C : R →+* MvPolynomial σ R) I :=
      Ideal.mem_map_of_mem C hr
    simpa only [Submodule.restrictScalars_mem, C_mul_monomial, mul_one] using
      (Ideal.map (C : R →+* MvPolynomial σ R) I).mul_mem_right (monomial d 1) hC
  · intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨r, hr, rfl⟩
      exact C_mem_coeffsIn.mpr hr
    · exact Submodule.zero_mem _
    · intro p q _ _ hp hq
      exact Submodule.add_mem _ hp hq
    · intro q p _ hp
      rw [smul_eq_mul]
      have hmul : (⊤ : Submodule R R) * (I : Submodule R R) ≤ I :=
        Submodule.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs
      have hqp : q * p ∈ coeffsIn σ ((⊤ : Submodule R R) * (I : Submodule R R)) := by
        rw [coeffsIn_mul]
        exact Submodule.mul_mem_mul (mem_coeffsIn.mpr fun _ => Submodule.mem_top) hp
      exact mem_coeffsIn.mpr fun d => hmul (mem_coeffsIn.mp hqp d)

/-- Membership in the extension of a coefficient ideal is coefficientwise
membership, over any commutative semiring. This is the elementwise form of
`coeffsIn_eq_restrictScalars_map_C`. -/
theorem mem_map_C_iff_coeff_mem {I : Ideal R} {p : MvPolynomial σ R} :
    p ∈ Ideal.map (C : R →+* MvPolynomial σ R) I ↔ ∀ d, p.coeff d ∈ I := by
  rw [← mem_coeffsIn, coeffsIn_eq_restrictScalars_map_C, Submodule.restrictScalars_mem]

/-- Extending a coefficient ideal to polynomials and contracting along `C`
recovers the original ideal, including for empty variable types. -/
@[simp]
theorem comap_map_C (I : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) I).comap C = I := by
  ext r
  rw [Ideal.mem_comap, ← C_mem_coeffsIn (σ := σ) (M := (I : Submodule R R)),
    coeffsIn_eq_restrictScalars_map_C, Submodule.restrictScalars_mem]

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/-- After restricting the polynomial kernel to the canonical coefficient
scalars, it is the submodule of polynomials with coefficients in the kernel.
This applies to any homomorphism class admitting a ring-homomorphism coercion. -/
theorem restrictScalars_ker_map (f : F) :
    (RingHom.ker (map (f : R →+* S) : MvPolynomial σ R →+* MvPolynomial σ S)).restrictScalars R =
      coeffsIn σ (RingHom.ker f : Submodule R R) := by
  ext p
  simp only [Submodule.restrictScalars_mem, RingHom.mem_ker, mem_coeffsIn,
    MvPolynomial.ext_iff, coeff_map, RingHom.coe_coe, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply]

/-- The ideal kernel of a polynomial coefficient map is the extension of the
coefficient kernel along `C`. This generalizes `MvPolynomial.ker_map` from
commutative rings to commutative semirings. The two submodule identifications
`restrictScalars_ker_map` and `coeffsIn_eq_restrictScalars_map_C` recover the
ideal equality because restriction of scalars is injective on submodules. -/
theorem ker_map_eq_map_C (f : F) :
    RingHom.ker (map (f : R →+* S) : MvPolynomial σ R →+* MvPolynomial σ S) =
      Ideal.map (C : R →+* MvPolynomial σ R) (RingHom.ker f) := by
  apply Submodule.restrictScalars_injective R (MvPolynomial σ R) (MvPolynomial σ R)
  rw [restrictScalars_ker_map, ← coeffsIn_eq_restrictScalars_map_C]

end MvPolynomial
