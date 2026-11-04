/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Nilpotent
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import MinimalPrimes.RingTheory.Spectrum.Maximal.Map
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.SetTheory.Cardinal.Order

/-!
# Prime and maximal spectra of polynomial rings

The prime spectrum of a multivariate polynomial semiring is irreducible
exactly when the prime spectrum of its coefficient semiring is irreducible.
The variable type is arbitrary, including the empty type.

A univariate polynomial ring over a nontrivial commutative ring has infinitely
many maximal ideals. For an arbitrary variable type, the maximal spectrum is
infinite exactly when the coefficient ring is nontrivial and either there is a
variable or the coefficient ring already has infinitely many maximal ideals.

The coefficient criterion `MvPolynomial.isNilpotent_iff_coeff` describes the
polynomial nilradical. Irreducibility is detected by primality of this special
ideal, rather than by extending arbitrary prime ideals of a semiring.

## References

* Mathlib, `Mathlib.RingTheory.Spectrum.Prime.Topology`, Johan Commelin and
  contributors' formalization of the Zariski topology and
  `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.
* `MultivariatePolynomials.Nilpotent`, for the coefficient criterion for
  polynomial nilpotents over commutative semirings.
* Mathlib, `Mathlib.RingTheory.Spectrum.Prime.Jacobson` and
  `Mathlib.RingTheory.Spectrum.Maximal.Topology`, for the Jacobson-space
  argument giving infinitely many maximal ideals over a field.
* Minimal Primes, `MinimalPrimes.RingTheory.Spectrum.Maximal.Map`, for
  `MaximalSpectrum.comapEmbeddingOfSurjective`, used with residue fields,
  polynomial evaluation and constant coefficients.
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- Adjoining an arbitrary family of polynomial variables to a commutative
semiring preserves and reflects irreducibility of its prime spectrum.
Irreducibility includes nonemptiness, so both sides are false for a trivial
coefficient semiring. -/
theorem irreducibleSpace_mvPolynomial_iff (σ : Type v) (R : Type u) [CommSemiring R] :
    IrreducibleSpace (PrimeSpectrum (MvPolynomial σ R)) ↔
      IrreducibleSpace (PrimeSpectrum R) := by
  classical
  simp only [irreducibleSpace_iff_isPrime_nilradical]
  have hC : (nilradical (MvPolynomial σ R)).comap
      (MvPolynomial.C : R →+* MvPolynomial σ R) = nilradical R := by
    ext a
    simp only [Ideal.mem_comap, mem_nilradical]
    exact IsNilpotent.map_iff (MvPolynomial.C_injective σ R)
  constructor
  · intro h
    simpa only [hC] using h.comap (MvPolynomial.C : R →+* MvPolynomial σ R)
  · intro hR
    obtain ⟨lo, wf⟩ := exists_wellFoundedGT σ
    let := lo
    let := wf
    let m : MonomialOrder σ := MonomialOrder.lex
    -- Separate the nilpotent coefficients from the remaining coefficients.
    let n (p : MvPolynomial σ R) : MvPolynomial σ R :=
      AddMonoidAlgebra.ofCoeff (p.coeff.filter fun d => IsNilpotent (p.coeff d))
    let r (p : MvPolynomial σ R) : MvPolynomial σ R :=
      AddMonoidAlgebra.ofCoeff (p.coeff.filter fun d => ¬ IsNilpotent (p.coeff d))
    have hsplit (p : MvPolynomial σ R) : n p + r p = p := by
      apply MvPolynomial.ext
      intro d
      exact congrArg (fun c : (σ →₀ ℕ) →₀ R => c d)
        (Finsupp.filter_add_filter_not p.coeff fun d => IsNilpotent (p.coeff d))
    have hn (p : MvPolynomial σ R) : IsNilpotent (n p) := by
      apply (MvPolynomial.isNilpotent_iff_coeff (n p)).mpr
      intro d
      change IsNilpotent (if IsNilpotent (p.coeff d) then p.coeff d else 0)
      by_cases hd : IsNilpotent (p.coeff d)
      · simpa only [ite_eq_left hd] using hd
      · simpa only [ite_eq_right hd] using (IsNilpotent.zero : IsNilpotent (0 : R))
    have hc (p : MvPolynomial σ R) (d : σ →₀ ℕ) (hd : (r p).coeff d ≠ 0) :
        ¬ IsNilpotent ((r p).coeff d) := by
      by_cases h : IsNilpotent (p.coeff d)
      · exfalso
        apply hd
        change (if ¬ IsNilpotent (p.coeff d) then p.coeff d else 0) = 0
        simp only [h, not_true_eq_false, ite_false]
      · change ¬ IsNilpotent (if ¬ IsNilpotent (p.coeff d) then p.coeff d else 0)
        simpa only [ite_eq_left h] using h
    have hlead (p : MvPolynomial σ R) (hp : ¬ IsNilpotent p) :
        ¬ IsNilpotent (m.leadingCoeff (r p)) := by
      have hr : r p ≠ 0 := by
        intro hz
        apply hp
        rw [← hsplit p, hz, add_zero]
        exact hn p
      exact hc p _ (m.leadingCoeff_ne_zero_iff.mpr hr)
    refine ⟨?_, ?_⟩
    · intro htop
      apply hR.ne_top
      rw [← hC, htop, Ideal.comap_top]
    · intro p q hpq
      simp only [mem_nilradical] at hpq ⊢
      by_contra h
      obtain ⟨hp, hq⟩ := not_or.mp h
      have hmul : ¬ IsNilpotent (m.leadingCoeff (r p) * m.leadingCoeff (r q)) := by
        intro hnil
        rcases hR.mem_or_mem (mem_nilradical.mpr hnil) with hleft | hright
        · exact hlead p hp (mem_nilradical.mp hleft)
        · exact hlead q hq (mem_nilradical.mp hright)
      have hnonzero : m.leadingCoeff (r p) * m.leadingCoeff (r q) ≠ 0 := by
        intro hz
        apply hmul
        rw [hz]
        exact IsNilpotent.zero
      -- Every other summand in the product contains a nilpotent polynomial.
      have hpert : IsNilpotent (n p * q + r p * n q) :=
        (Commute.all _ _).isNilpotent_add
          ((Commute.all _ _).isNilpotent_mul_right (hn p))
          ((Commute.all _ _).isNilpotent_mul_left (hn q))
      have heq : (n p * q + r p * n q) + r p * r q = p * q := by
        rw [add_assoc, ← mul_add, hsplit q, ← add_mul, hsplit p]
      have hprod : IsNilpotent ((n p * q + r p * n q) + r p * r q) := by
        rwa [heq]
      have hresprod : IsNilpotent (r p * r q) :=
        ((Commute.all _ _).isNilpotent_add_right_iff hpert).mp
          (by simpa only [add_comm] using hprod)
      have hcoeff := (MvPolynomial.isNilpotent_iff_coeff (r p * r q)).mp hresprod
        (m.degree (r p * r q))
      change IsNilpotent (m.leadingCoeff (r p * r q)) at hcoeff
      rw [m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero hnonzero] at hcoeff
      exact hmul hcoeff

end PrimeSpectrum

private theorem infinite_polynomial_field (K : Type u) [Field K] :
    Infinite (MaximalSpectrum (Polynomial K)) := by
  classical
  by_contra h
  let : Finite (MaximalSpectrum (Polynomial K)) := not_infinite_iff_finite.mp h
  have hclosed : (closedPoints (PrimeSpectrum (Polynomial K))).Finite := by
    change {x : PrimeSpectrum (Polynomial K) | IsClosed ({x} : Set _)}.Finite
    rw [← MaximalSpectrum.toPrimeSpectrum_range]
    exact Set.finite_range _
  let : DiscreteTopology (PrimeSpectrum (Polynomial K)) :=
    JacobsonSpace.discreteTopology hclosed
  have hfield : IsField (Polynomial K) :=
    PrimeSpectrum.t1Space_iff_isField.mp inferInstance
  exact Polynomial.not_isUnit_X
    (isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel Polynomial.X_ne_zero))

private theorem eval₂Hom_const_X_surjective
    {σ : Type v} {R : Type u} [CommSemiring R] (i : σ) :
    Function.Surjective
      (MvPolynomial.eval₂Hom (Polynomial.C : R →+* Polynomial R)
        (fun _ : σ => (Polynomial.X : Polynomial R))) := by
  let s : Polynomial R →+* MvPolynomial σ R :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
  have hs :
      (MvPolynomial.eval₂Hom (Polynomial.C : R →+* Polynomial R)
        (fun _ : σ => (Polynomial.X : Polynomial R))).comp s =
        RingHom.id (Polynomial R) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [s]
    · simp [s]
  intro p
  exact ⟨s p, RingHom.congr_fun hs p⟩

namespace MaximalSpectrum

/-- A polynomial ring over a nontrivial commutative ring has infinitely many maximal ideals. -/
theorem infinite_polynomial (R : Type u) [CommRing R] [Nontrivial R] :
    Infinite (MaximalSpectrum (Polynomial R)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let : m.IsMaximal := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Infinite (MaximalSpectrum (Polynomial (R ⧸ m))) := infinite_polynomial_field _
  exact Infinite.of_injective _
    (comapEmbeddingOfSurjective (Polynomial.mapRingHom (Ideal.Quotient.mk m))
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)).injective

/-- The maximal spectrum of a multivariable polynomial ring is infinite exactly when the
coefficient ring is nontrivial and either a variable exists or its maximal spectrum is infinite. -/
theorem infinite_mvPolynomial_iff (σ : Type v) (R : Type u) [CommRing R] :
    Infinite (MaximalSpectrum (MvPolynomial σ R)) ↔
      Nontrivial R ∧ (Nonempty σ ∨ Infinite (MaximalSpectrum R)) := by
  constructor
  · intro h
    let : Infinite (MaximalSpectrum (MvPolynomial σ R)) := h
    have hR : Nontrivial R := by
      cases subsingleton_or_nontrivial R with
      | inl hR =>
          let : Subsingleton R := hR
          obtain ⟨x⟩ := (inferInstance : Nonempty (MaximalSpectrum (MvPolynomial σ R)))
          exact (x.isMaximal.ne_top (Subsingleton.elim _ _)).elim
      | inr hR => exact hR
    refine ⟨hR, ?_⟩
    by_cases hσ : Nonempty σ
    · exact Or.inl hσ
    · right
      let : IsEmpty σ := not_nonempty_iff.mp hσ
      exact Infinite.of_injective _
        (comapEmbeddingOfSurjective (MvPolynomial.isEmptyRingEquiv R σ).symm.toRingHom
          (MvPolynomial.isEmptyRingEquiv R σ).symm.surjective).injective
  · rintro ⟨hR, hσ | hbase⟩
    · let : Nontrivial R := hR
      obtain ⟨i⟩ := hσ
      let : Infinite (MaximalSpectrum (Polynomial R)) := infinite_polynomial R
      exact Infinite.of_injective _
        (comapEmbeddingOfSurjective
          (MvPolynomial.eval₂Hom (Polynomial.C : R →+* Polynomial R)
            (fun _ : σ => (Polynomial.X : Polynomial R)))
          (eval₂Hom_const_X_surjective i)).injective
    · let : Infinite (MaximalSpectrum R) := hbase
      exact Infinite.of_injective _
        (comapEmbeddingOfSurjective
          (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R)
          (fun r => ⟨MvPolynomial.C r, MvPolynomial.constantCoeff_C σ r⟩)).injective

end MaximalSpectrum
