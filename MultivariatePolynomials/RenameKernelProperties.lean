/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Maps
import MultivariatePolynomials.Nilpotent

/-!
# Prime and radical kernels of variable renaming

The kernel of variable renaming is prime exactly when the zero ideal of the
coefficient semiring is prime, and radical exactly when the coefficient semiring
is reduced. Both criteria hold for arbitrary commutative semirings and arbitrary
variable maps, with independent coefficient and variable universes.

Prime zero ideals require absence of zero divisors and nontriviality, not
multiplicative cancellation. In particular, the prime criterion is not stated
using `IsDomain` over semirings. The radical criterion also includes the zero
semiring. Neither criterion requires the variable map to be injective or
surjective, or either variable type to be inhabited.

## References

* Mathlib, `Mathlib.RingTheory.Ideal.Prime` and
  `Mathlib.RingTheory.Ideal.Maps`: prime ideals and contraction of prime and
  radical ideals.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic`: the coefficient embedding and
  polynomial no-zero-divisors instance.
* `MultivariatePolynomials.Nilpotent`: the coefficientwise nilpotence criterion
  over commutative semirings, extending the prior formalizations by Andrew Yang,
  Emilie Uthaiwat and Oliver Nash.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]

private theorem comap_C_ker_rename (f : σ → τ) :
    (RingHom.ker (rename (R := R) f).toRingHom).comap
      (C : R →+* MvPolynomial σ R) = ⊥ := by
  ext r
  simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
  change rename (R := R) f (C r) = 0 ↔ r = 0
  rw [rename_C, C_eq_zero]

/-- The kernel of variable renaming is prime if and only if the zero ideal of the
coefficient semiring is prime. No multiplicative cancellation is required. -/
theorem isPrime_ker_rename_iff (f : σ → τ) :
    (RingHom.ker (rename (R := R) f).toRingHom).IsPrime ↔
      (⊥ : Ideal R).IsPrime := by
  constructor
  · intro h
    let := h
    have hC : ((RingHom.ker (rename (R := R) f).toRingHom).comap
        (C : R →+* MvPolynomial σ R)).IsPrime := inferInstance
    simpa only [comap_C_ker_rename] using hC
  · intro h
    let : Nontrivial R := ⟨⟨1, 0, fun h10 => h.one_notMem (Ideal.mem_bot.mpr h10)⟩⟩
    let : NoZeroDivisors R := ⟨fun {x y} hxy => by
      simpa only [Ideal.mem_bot] using
        h.mem_or_mem (show x * y ∈ (⊥ : Ideal R) from Ideal.mem_bot.mpr hxy)⟩
    change (Ideal.comap (rename (R := R) f).toRingHom ⊥).IsPrime
    infer_instance

/-- The kernel of variable renaming is radical if and only if the coefficient
semiring is reduced, including for empty variable types and the zero semiring. -/
theorem isRadical_ker_rename_iff (f : σ → τ) :
    (RingHom.ker (rename (R := R) f).toRingHom).IsRadical ↔ IsReduced R := by
  constructor
  · intro h
    apply Ideal.isRadical_bot_iff.mp
    have hC := Ideal.IsRadical.comap (f := (C : R →+* MvPolynomial σ R)) h
    simpa only [comap_C_ker_rename] using hC
  · intro h
    let := h
    intro p hp
    apply RingHom.mem_ker.mpr
    have hnil : IsNilpotent ((rename (R := R) f).toRingHom p) := by
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
      refine ⟨n, ?_⟩
      simpa only [map_pow] using (RingHom.mem_ker.mp hn)
    apply MvPolynomial.ext
    intro d
    simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      ((isNilpotent_iff_coeff _).mp hnil d).eq_zero

end MvPolynomial
