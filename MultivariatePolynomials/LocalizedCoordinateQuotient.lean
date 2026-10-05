/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing a polynomial coordinate quotient

After inverting the class of `r`, evaluation at zero identifies the quotient
`R[X] / ⟨C r * X⟩` with the localization of its coefficient ring. The equivalence
and its representative and fraction laws hold for zero rings, nilpotent elements,
and zero divisors.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise
  3.2.L (p. 109): localization of the complex coordinate axes. The equivalence
  here generalizes the example to an arbitrary commutative ring and element.
* Mathlib, `Mathlib.RingTheory.Polynomial.Quotient` (quotient evaluation) and
  `Mathlib.RingTheory.Localization.Away.Basic` (localization and fractions).
  The localization equivalence is a separate project construction.
-/

@[expose] public section

namespace Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- In `R[X] / ⟨C r * X⟩`, a polynomial whose constant term vanishes is annihilated
by the image of `r`. This is the kernel calculation behind the equivalence. -/
theorem quotientSpanCMulX_mul_mk_eq_zero_of_eval_zero (r : R) (p : R[X])
    (hp : p.eval 0 = 0) :
    algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r *
      Ideal.Quotient.mk (Ideal.span ({C r * X} : Set R[X])) p = 0 := by
  obtain ⟨q, rfl⟩ := X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using hp)
  change Ideal.Quotient.mk _ (C r) * Ideal.Quotient.mk _ (X * q) = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.mpr ⟨q, by ring⟩

/-- Evaluation at zero on the quotient by `C r * X`. -/
noncomputable def quotientSpanCMulXEval (r : R) :
    (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (0 : R)) (by
    intro p hp
    have hle : Ideal.span ({C r * X} : Set R[X]) ≤
        RingHom.ker (aeval (0 : R)).toRingHom :=
      Ideal.span_le.mpr (by
        intro q hq
        have hq' : q = C r * X := by simpa only [Set.mem_singleton_iff] using hq
        subst q
        simp [RingHom.mem_ker])
    exact RingHom.mem_ker.mp (hle hp))

/-- The evaluation map evaluates a quotient representative at zero. -/
@[simp] theorem quotientSpanCMulXEval_mk (r : R) (p : R[X]) :
    quotientSpanCMulXEval r (Ideal.Quotient.mk _ p) = p.eval 0 := by
  simp [quotientSpanCMulXEval]

/-- Evaluation at `X = 0` after inverting the image of `r` in `R[X] / ⟨C r * X⟩`.
The construction does not require `r` to be regular or nonnilpotent. This
generalizes Vakil's complex-coordinate-axes example in *The Rising Sea*,
Exercise 3.2.L; the abstract ring-level equivalence is not printed there. -/
noncomputable def quotientSpanCMulXAwayAlgEquiv (r : R) :
    Localization.Away
        (algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r)
      ≃ₐ[R] Localization.Away r := by
  let quotient := R[X] ⧸ Ideal.span ({C r * X} : Set R[X])
  let coefficient : quotient := algebraMap R quotient r
  let evalMap := quotientSpanCMulXEval r
  have heval : evalMap coefficient = r := by
    change quotientSpanCMulXEval r (Ideal.Quotient.mk _ (C r)) = r
    simp
  have hinj : Function.Injective (Localization.awayMap evalMap.toRingHom coefficient) :=
    (Localization.awayMap_injective_iff).mpr (by
      intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨1, ?_⟩
      have hp : p.eval 0 = 0 := by
        change quotientSpanCMulXEval r (Ideal.Quotient.mk _ p) = 0 at hq
        simpa using hq
      simpa only [pow_one] using
        quotientSpanCMulX_mul_mk_eq_zero_of_eval_zero r p hp)
  have hsurj : Function.Surjective (Localization.awayMap evalMap.toRingHom coefficient) :=
    (Localization.awayMap_surjective_iff).mpr (by
      intro b
      refine ⟨algebraMap R quotient b, 0, ?_⟩
      simp only [pow_zero, one_mul]
      change evalMap (algebraMap R quotient b) = b
      exact evalMap.commutes b)
  have hbij : Function.Bijective
      (Localization.awayMapₐ evalMap coefficient) := by
    change Function.Bijective (Localization.awayMap evalMap.toRingHom coefficient)
    exact ⟨hinj, hsurj⟩
  have equivalence : Localization.Away coefficient ≃ₐ[R]
      Localization.Away (evalMap coefficient) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ evalMap coefficient) hbij
  exact (congrArg (fun b : R => Localization.Away coefficient ≃ₐ[R] Localization.Away b)
    heval).mp equivalence

/-- On quotient representatives, the forward equivalence evaluates the variable at zero. -/
@[simp] theorem quotientSpanCMulXAwayAlgEquiv_mk (r : R) (p : R[X]) :
    quotientSpanCMulXAwayAlgEquiv r
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span ({C r * X} : Set R[X])) p)) =
      algebraMap R (Localization.Away r) (p.eval 0) := by
  let quotient := R[X] ⧸ Ideal.span ({C r * X} : Set R[X])
  let source := Localization.Away (algebraMap R quotient r)
  let target := Localization.Away r
  let quotientToSource : quotient →ₐ[R] source :=
    (Algebra.ofId quotient source).restrictScalars R
  let polynomialMap : R[X] →ₐ[R] target :=
    (quotientSpanCMulXAwayAlgEquiv r).toAlgHom.comp
      (quotientToSource.comp (Ideal.Quotient.mkₐ R _))
  have hzero : algebraMap quotient source (Ideal.Quotient.mk _ (X : R[X])) = 0 := by
    have h := quotientSpanCMulX_mul_mk_eq_zero_of_eval_zero r X (by simp)
    have h' := congrArg (algebraMap quotient source) h
    simp only [map_mul, map_zero] at h'
    exact (IsUnit.mul_right_inj
      (IsLocalization.Away.algebraMap_isUnit (S := source) (algebraMap R quotient r))).mp
        (by simpa only [mul_zero] using h')
  have heval : polynomialMap = aeval (0 : target) := by
    apply Polynomial.algHom_ext
    change quotientSpanCMulXAwayAlgEquiv r
      (algebraMap quotient source (Ideal.Quotient.mk _ (X : R[X]))) =
        aeval (0 : target) X
    rw [hzero, map_zero, aeval_X]
  have hvalue := congrArg (fun f : R[X] →ₐ[R] target => f p) heval
  change quotientSpanCMulXAwayAlgEquiv r
    (algebraMap quotient source (Ideal.Quotient.mk _ p)) = aeval (0 : target) p at hvalue
  exact hvalue.trans (by
    simpa only [map_zero] using
      (aeval_algebraMap_apply_eq_algebraMap_eval (A := target) (0 : R) p))

/-- The inverse equivalence sends a localized coefficient to its constant polynomial class. -/
@[simp] theorem quotientSpanCMulXAwayAlgEquiv_symm_algebraMap (r b : R) :
    (quotientSpanCMulXAwayAlgEquiv r).symm
        (algebraMap R (Localization.Away r) b) =
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span ({C r * X} : Set R[X])) (C b)) := by
  apply (quotientSpanCMulXAwayAlgEquiv r).injective
  simp

/-- The forward equivalence evaluates the numerator and retains the power denominator. -/
@[simp] theorem quotientSpanCMulXAwayAlgEquiv_mk' (r : R) (p : R[X]) (n : ℕ) :
    quotientSpanCMulXAwayAlgEquiv r
        (IsLocalization.mk'
          (Localization.Away
            (algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r))
          (Ideal.Quotient.mk (Ideal.span ({C r * X} : Set R[X])) p)
          (Submonoid.pow (algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r) n)) =
      IsLocalization.mk' (Localization.Away r) (p.eval 0) (Submonoid.pow r n) := by
  let quotient := R[X] ⧸ Ideal.span ({C r * X} : Set R[X])
  let source := Localization.Away (algebraMap R quotient r)
  let target := Localization.Away r
  let e := quotientSpanCMulXAwayAlgEquiv r
  let coefficient : quotient := algebraMap R quotient r
  let representative : quotient := Ideal.Quotient.mk _ p
  have hcoefficient : e (algebraMap quotient source coefficient) =
      algebraMap R target r := by
    change quotientSpanCMulXAwayAlgEquiv r
      (algebraMap quotient source (Ideal.Quotient.mk _ (C r))) = _
    simpa only [eval_C] using quotientSpanCMulXAwayAlgEquiv_mk r (C r)
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
  calc
    algebraMap R target (p.eval 0) = e (algebraMap quotient source representative) :=
      (quotientSpanCMulXAwayAlgEquiv_mk r p).symm
    _ = e (IsLocalization.mk' source representative (Submonoid.pow coefficient n) *
        algebraMap quotient source (coefficient ^ n)) := by
      congr 1
      simpa only [Submonoid.pow_apply, Subtype.coe_mk] using
        (IsLocalization.mk'_spec source representative (Submonoid.pow coefficient n)).symm
    _ = e (IsLocalization.mk' source representative (Submonoid.pow coefficient n)) *
        algebraMap R target (r ^ n) := by
      simp only [map_mul, map_pow, hcoefficient]

/-- The inverse equivalence lifts a fraction as a constant-polynomial fraction. -/
@[simp] theorem quotientSpanCMulXAwayAlgEquiv_symm_mk' (r b : R) (n : ℕ) :
    (quotientSpanCMulXAwayAlgEquiv r).symm
        (IsLocalization.mk' (Localization.Away r) b (Submonoid.pow r n)) =
      IsLocalization.mk'
        (Localization.Away
          (algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r))
        (Ideal.Quotient.mk (Ideal.span ({C r * X} : Set R[X])) (C b))
        (Submonoid.pow (algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r) n) := by
  apply (quotientSpanCMulXAwayAlgEquiv r).injective
  simp

/-- The polynomial variable maps to zero after the coefficient is inverted. -/
@[simp] theorem quotientSpanCMulXAwayAlgEquiv_X (r : R) :
    quotientSpanCMulXAwayAlgEquiv r
        (algebraMap _ _
          (Ideal.Quotient.mk (Ideal.span ({C r * X} : Set R[X])) X)) = 0 := by
  simp [quotientSpanCMulXAwayAlgEquiv_mk]

/-- The chosen inverse of the inverted coefficient is preserved by evaluation. -/
@[simp] theorem quotientSpanCMulXAwayAlgEquiv_invSelf (r : R) :
    quotientSpanCMulXAwayAlgEquiv r
        (IsLocalization.Away.invSelf
          (algebraMap R (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) r)) =
      IsLocalization.Away.invSelf r := by
  simpa [IsLocalization.Away.invSelf, Submonoid.pow_apply] using
    quotientSpanCMulXAwayAlgEquiv_mk' r (C 1) 1

end Polynomial
