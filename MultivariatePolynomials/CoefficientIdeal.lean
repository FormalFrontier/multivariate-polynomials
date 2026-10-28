/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
public import MultivariatePolynomials.IdealFiniteGeneration

/-!
# Coefficient ideals over commutative semirings

Extending an ideal along `MvPolynomial.C` gives exactly the polynomials with
coefficients in that ideal. As an `R`-submodule, this extension is Mathlib's
`MvPolynomial.coeffsIn`, for the canonical action `r • p = C r * p`.
Extension along `C` preserves arbitrary intersections of coefficient ideals and
reflects their inclusion and equality. Contraction along `C` recovers the
coefficient ideal. Pullback along a map on coefficients commutes with extension
along `C`; the coefficient-kernel identity is its zero-ideal specialization.

More generally, extending ideals along a semiring homomorphism with a retraction
preserves and reflects finite generation. This equivalence allows independent
source and target universes and does not require commutativity.

The coefficient and variable universes are independent; for coefficient maps,
the source and target coefficient universes are independent as well. No
finiteness, nontriviality, cancellation or additive inverses are required.

Extension along `C` also commutes with ideal colon, by testing constant
generators and using coefficientwise membership. The arithmetic examples below
show `(4) : (2) = (2)` over the integers and distinguish `2 * X` from a
constant and from membership in the extension of `(4)`. They also cover empty
variables, zero and top ideals, and the trivial coefficient ring.

## References

* Mathlib's `Mathlib.Algebra.MvPolynomial.Basic`, by Johannes Hölzl,
  Johan Commelin and Mario Carneiro, supplies `coeffsIn`, its monomial-span
  characterization and its compatibility with submodule multiplication.
* Kenny Lau's `Mathlib.RingTheory.Ideal.Colon` supplies colon membership
  and reduction to span generators; Mathlib supplies `coeff_C_mul` and the
  principal-ideal and cancellative-divisibility APIs used below.
* Kenny Lau's `Mathlib.RingTheory.Ideal.Maps` supplies ideal extension,
  contraction and homomorphism kernels. His `Mathlib.RingTheory.Polynomial.Basic`
  contains the ring versions `MvPolynomial.mem_map_C_iff` and
  `MvPolynomial.ker_map`. The submodule identifications below recover those
  statements for rings and also apply to semirings. The extension argument
  uses the `coeffsIn` span and multiplication APIs, rather than a separate
  coefficient-by-coefficient induction on the extended ideal. The order
  reflection uses the same extension-contraction adjunction.
* Mathlib's `Mathlib.RingTheory.Finiteness.Ideal` supplies `Ideal.FG.map`;
  applying it along a homomorphism and its retraction gives the
  finite-generation equivalence.
* Mathlib's `coeff_map` identifies coefficients after a coefficient map; together
  with coefficientwise extension membership this gives the pullback identity.
* Mathlib's complete-lattice API supplies `sInf_eq_iInf'` and `sInf_image'`
  to express set intersections in terms of indexed intersections.
-/

@[expose] public section

universe u v w x

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

/-- Extension of coefficient ideals along `C` preserves arbitrary indexed
intersections, including the empty intersection. -/
theorem map_C_iInf {ι : Sort x} (I : ι → Ideal R) :
    Ideal.map (C : R →+* MvPolynomial σ R) (⨅ i, I i) =
      ⨅ i, Ideal.map (C : R →+* MvPolynomial σ R) (I i) := by
  ext p
  simp only [mem_map_C_iff_coeff_mem, Ideal.mem_iInf]
  exact forall_comm

/-- Extension of coefficient ideals along `C` preserves the intersection of
any set of ideals, expressed as the intersection of its image. -/
theorem map_C_sInf (A : Set (Ideal R)) :
    Ideal.map (C : R →+* MvPolynomial σ R) (sInf A) =
      sInf (Ideal.map (C : R →+* MvPolynomial σ R) '' A) := by
  rw [sInf_eq_iInf' A, map_C_iInf, sInf_image']

/-- Extending a coefficient ideal to polynomials and contracting along `C`
recovers the original ideal, including for empty variable types. -/
@[simp]
theorem comap_map_C (I : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) I).comap C = I := by
  ext r
  rw [Ideal.mem_comap, ← C_mem_coeffsIn (σ := σ) (M := (I : Submodule R R)),
    coeffsIn_eq_restrictScalars_map_C, Submodule.restrictScalars_mem]

/-- Inclusion of extensions of coefficient ideals is equivalent to inclusion
of the coefficient ideals themselves. -/
@[simp]
theorem map_C_le_map_C_iff {I J : Ideal R} :
    Ideal.map (C : R →+* MvPolynomial σ R) I ≤
      Ideal.map (C : R →+* MvPolynomial σ R) J ↔ I ≤ J := by
  rw [Ideal.map_le_iff_le_comap, comap_map_C]

/-- Extension along `C` is injective on coefficient ideals. In particular,
its `Function.Injective.eq_iff` reflects equality of coefficient ideals. -/
theorem map_C_injective :
    Function.Injective (Ideal.map (C : R →+* MvPolynomial σ R)) :=
  Function.LeftInverse.injective (comap_map_C (σ := σ))

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/-- Pullback of a coefficient ideal extension along a coefficient map is the
extension of its pullback. No injectivity or surjectivity is required. -/
theorem comap_map_C_eq_map_C_comap (f : F) (J : Ideal S) :
    (Ideal.map (C : S →+* MvPolynomial σ S) J).comap (map (f : R →+* S)) =
      Ideal.map (C : R →+* MvPolynomial σ R) (J.comap f) := by
  ext p
  simp only [Ideal.mem_comap, mem_map_C_iff_coeff_mem, coeff_map, RingHom.coe_coe]

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
commutative rings to commutative semirings, by specializing
`comap_map_C_eq_map_C_comap` to the zero ideal. -/
theorem ker_map_eq_map_C (f : F) :
    RingHom.ker (map (f : R →+* S) : MvPolynomial σ R →+* MvPolynomial σ S) =
      Ideal.map (C : R →+* MvPolynomial σ R) (RingHom.ker f) := by
  simpa only [Ideal.map_bot, RingHom.ker_eq_comap_bot] using
    (comap_map_C_eq_map_C_comap (σ := σ) f (⊥ : Ideal S))

private theorem emptyVariables_coefficientComap (f : F) (J : Ideal S) (r : R) :
    (C r : MvPolynomial Empty R) ∈
        (Ideal.map (C : S →+* MvPolynomial Empty S) J).comap (map (f : R →+* S)) ↔
      f r ∈ J := by
  rw [comap_map_C_eq_map_C_comap]
  change r ∈ (Ideal.map (C : R →+* MvPolynomial Empty R) (J.comap f)).comap C ↔ _
  rw [comap_map_C, Ideal.mem_comap]

private theorem top_coefficientComap (f : F) :
    (Ideal.map (C : S →+* MvPolynomial σ S) ⊤).comap (map (f : R →+* S)) = ⊤ := by
  rw [comap_map_C_eq_map_C_comap, Ideal.comap_top, Ideal.map_top]

private theorem trivialTarget_coefficientComap [Subsingleton S] (f : F) (J : Ideal S) :
    (Ideal.map (C : S →+* MvPolynomial σ S) J).comap (map (f : R →+* S)) = ⊤ := by
  rw [show J = ⊤ from Subsingleton.elim _ _, top_coefficientComap]

private theorem trivialSource_coefficientComap [Subsingleton R] (f : F) (J : Ideal S) :
    (Ideal.map (C : S →+* MvPolynomial σ S) J).comap (map (f : R →+* S)) = ⊤ := by
  rw [comap_map_C_eq_map_C_comap]
  exact Subsingleton.elim _ _

/-- Extension of coefficient ideals along `C` commutes with ideal colon.
The denominator of each colon is the underlying set of the corresponding
ideal. This holds for arbitrary ideals over a commutative semiring. -/
theorem map_C_colon (I J : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) I).colon
        (Ideal.map (C : R →+* MvPolynomial σ R) J : Set (MvPolynomial σ R)) =
      Ideal.map (C : R →+* MvPolynomial σ R) (I.colon (J : Set R)) := by
  change (Ideal.map (C : R →+* MvPolynomial σ R) I).colon
    (Ideal.span ((C : R →+* MvPolynomial σ R) '' (J : Set R))) = _
  rw [Ideal.colon_span]
  ext p
  simp only [Submodule.mem_colon, Set.forall_mem_image, smul_eq_mul,
    mem_map_C_iff_coeff_mem]
  constructor
  · intro h d b hb
    have hd := h hb d
    rw [mul_comm p, coeff_C_mul, mul_comm b] at hd
    exact hd
  · intro h b hb d
    rw [mul_comm p, coeff_C_mul, mul_comm b]
    exact h d b hb

end MvPolynomial

open MvPolynomial

private theorem integer_four_colon_two :
    (Ideal.span ({4} : Set ℤ)).colon (Ideal.span ({2} : Set ℤ) : Set ℤ) =
      Ideal.span ({2} : Set ℤ) := by
  ext a
  simp only [Ideal.mem_colon_span_singleton, Ideal.mem_span_singleton]
  simpa only [show (2 : ℤ) * 2 = 4 from rfl] using
    (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0) :
      (2 : ℤ) * 2 ∣ a * 2 ↔ (2 : ℤ) ∣ a)

private theorem integerPolynomialColon (σ : Type v) :
    (Ideal.map (C : ℤ →+* MvPolynomial σ ℤ) (Ideal.span ({4} : Set ℤ))).colon
        (Ideal.map (C : ℤ →+* MvPolynomial σ ℤ) (Ideal.span ({2} : Set ℤ)) :
          Set (MvPolynomial σ ℤ)) =
      Ideal.map (C : ℤ →+* MvPolynomial σ ℤ) (Ideal.span ({2} : Set ℤ)) := by
  rw [map_C_colon, integer_four_colon_two]

private theorem twiceVariable_integerColon_facts :
    (C 2 * X () : MvPolynomial Unit ℤ) ∉
        Set.range (C : ℤ →+* MvPolynomial Unit ℤ) ∧
      (C 2 * X () : MvPolynomial Unit ℤ) ∈
        (Ideal.map (C : ℤ →+* MvPolynomial Unit ℤ) (Ideal.span ({4} : Set ℤ))).colon
          (Ideal.map (C : ℤ →+* MvPolynomial Unit ℤ) (Ideal.span ({2}
            : Set ℤ)) : Set (MvPolynomial Unit ℤ)) ∧
      (C 2 * X () : MvPolynomial Unit ℤ) ∉
        Ideal.map (C : ℤ →+* MvPolynomial Unit ℤ) (Ideal.span ({4} : Set ℤ)) := by
  have h2 : (2 : ℤ) ∈ Ideal.span ({2} : Set ℤ) := Ideal.subset_span (by simp)
  have h2not4 : (2 : ℤ) ∉ Ideal.span ({4} : Set ℤ) := by
    norm_num [Ideal.mem_span_singleton]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    have hd : (Finsupp.single () 1 : Unit →₀ ℕ) ≠ 0 := by simp
    have hc := congrArg (fun p : MvPolynomial Unit ℤ => p.coeff (Finsupp.single () 1)) ha
    rw [coeff_C_of_ne_zero hd, coeff_C_mul, coeff_X_same, mul_one] at hc
    norm_num at hc
  · rw [integerPolynomialColon]
    exact (Ideal.map (C : ℤ →+* MvPolynomial Unit ℤ)
      (Ideal.span ({2} : Set ℤ))).mul_mem_right (X ()) (Ideal.mem_map_of_mem C h2)
  · intro hp
    have hc := (mem_map_C_iff_coeff_mem.mp hp) (Finsupp.single () 1)
    exact h2not4 (by simpa only [coeff_C_mul, coeff_X_same, mul_one] using hc)

private theorem emptyVariables_integerColon :
    (C 2 : MvPolynomial Empty ℤ) ∈
        (Ideal.map (C : ℤ →+* MvPolynomial Empty ℤ) (Ideal.span ({4} : Set ℤ))).colon
          (Ideal.map (C : ℤ →+* MvPolynomial Empty ℤ) (Ideal.span ({2}
            : Set ℤ)) : Set (MvPolynomial Empty ℤ)) ∧
      (C 1 : MvPolynomial Empty ℤ) ∉
        (Ideal.map (C : ℤ →+* MvPolynomial Empty ℤ) (Ideal.span ({4} : Set ℤ))).colon
          (Ideal.map (C : ℤ →+* MvPolynomial Empty ℤ) (Ideal.span ({2}
            : Set ℤ)) : Set (MvPolynomial Empty ℤ)) := by
  simp only [integerPolynomialColon]
  constructor
  · exact Ideal.mem_map_of_mem C (Ideal.subset_span (by simp))
  · intro h
    have hc := (mem_map_C_iff_coeff_mem.mp h) 0
    norm_num [Ideal.mem_span_singleton] at hc

-- The non-surjective map from a semiring to the integers, with the proper
-- nonzero ideal (2), gives a nonconstant member whose image is not zero.
private theorem twiceVariable_coefficientComap :
    (C 2 * X () : MvPolynomial Unit ℕ) ∈
        Ideal.map (C : ℕ →+* MvPolynomial Unit ℕ)
          ((Ideal.span ({2} : Set ℤ)).comap (Nat.castRingHom ℤ)) ∧
      map (Nat.castRingHom ℤ) (C 2 * X () : MvPolynomial Unit ℕ) ≠ 0 ∧
      map (Nat.castRingHom ℤ) (C 2 * X () : MvPolynomial Unit ℕ) ∉
        Set.range (C : ℤ →+* MvPolynomial Unit ℤ) := by
  have hmap : map (Nat.castRingHom ℤ) (C 2 * X () : MvPolynomial Unit ℕ) =
      (C 2 * X () : MvPolynomial Unit ℤ) := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← comap_map_C_eq_map_C_comap, Ideal.mem_comap]
    have hm := twiceVariable_integerColon_facts.2.1
    rw [integerPolynomialColon] at hm
    simpa using hm
  · rw [hmap]
    intro h
    apply twiceVariable_integerColon_facts.1
    exact ⟨0, by simpa using h.symm⟩
  · rw [hmap]
    exact twiceVariable_integerColon_facts.1

variable {R : Type u} {σ : Type v} [CommSemiring R]

private theorem zeroDenominator (I : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) I).colon
        (Ideal.map (C : R →+* MvPolynomial σ R) (⊥ : Ideal R) : Set (MvPolynomial σ R)) = ⊤ := by
  rw [map_C_colon, Submodule.colon_bot, Ideal.map_top]

private theorem topNumerator (J : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) (⊤ : Ideal R)).colon
        (Ideal.map (C : R →+* MvPolynomial σ R) J : Set (MvPolynomial σ R)) = ⊤ := by
  rw [map_C_colon, Submodule.top_colon, Ideal.map_top]

private theorem topDenominator (I : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) I).colon
        (Ideal.map (C : R →+* MvPolynomial σ R) (⊤ : Ideal R) : Set (MvPolynomial σ R)) =
      Ideal.map (C : R →+* MvPolynomial σ R) I := by
  rw [map_C_colon, Submodule.top_coe, Submodule.colon_univ]

private theorem trivialCoefficientColon (I J : Ideal (ZMod 1)) :
    (Ideal.map (C : ZMod 1 →+* MvPolynomial Unit (ZMod 1)) I).colon
        (Ideal.map (C : ZMod 1 →+* MvPolynomial Unit (ZMod 1)) J
            : Set (MvPolynomial Unit (ZMod 1))) = ⊤ := by
  rw [map_C_colon]
  exact Subsingleton.elim _ _
