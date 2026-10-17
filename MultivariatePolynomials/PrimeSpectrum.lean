/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Nilpotent
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.SetTheory.Cardinal.Order

/-!
# Irreducibility of the spectrum of a polynomial semiring

The prime spectrum of a multivariate polynomial semiring is irreducible
exactly when the prime spectrum of its coefficient semiring is irreducible.
The variable type is arbitrary, including the empty type.

The coefficient criterion `MvPolynomial.isNilpotent_iff_coeff` describes the
polynomial nilradical. Irreducibility is detected by primality of this special
ideal, rather than by extending arbitrary prime ideals of a semiring.

## References

* Mathlib, `Mathlib.RingTheory.Spectrum.Prime.Topology`, Johan Commelin and
  contributors' formalization of the Zariski topology and
  `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.
* `MultivariatePolynomials.Nilpotent`, for the coefficient criterion for
  polynomial nilpotents over commutative semirings.
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
    letI := lo
    letI := wf
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
      · simpa only [if_pos hd] using hd
      · simpa only [if_neg hd] using (IsNilpotent.zero : IsNilpotent (0 : R))
    have hc (p : MvPolynomial σ R) (d : σ →₀ ℕ) (hd : (r p).coeff d ≠ 0) :
        ¬ IsNilpotent ((r p).coeff d) := by
      by_cases h : IsNilpotent (p.coeff d)
      · exfalso
        apply hd
        change (if ¬ IsNilpotent (p.coeff d) then p.coeff d else 0) = 0
        simp only [h, not_true_eq_false, if_false]
      · change ¬ IsNilpotent (if ¬ IsNilpotent (p.coeff d) then p.coeff d else 0)
        simpa only [if_pos h] using h
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
