/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Jacobson.Ideal
public import MultivariatePolynomials.CoefficientIdeal

/-!
# Jacobson radical of a nonempty-variable polynomial ring

Over any commutative coefficient ring, the Jacobson radical of an extended
coefficient ideal in a polynomial ring with a nonempty variable type is the
extension of its radical. In particular, the Jacobson radical of zero is the
nilradical. This is an ideal equality, not a vanishing assertion: the nonzero
square-zero constant `C (2 : ZMod 4)` supplies nonvacuity data in the test module.

Coefficient and variable universes are independent. No Jacobson-base, domain,
Noetherian, finite-variable, reducedness, or nontriviality premise is imposed;
the zero coefficient ring is included.

The nonempty-variable premise matters. With no variables the ring is the
coefficient ring. The localization of the integers at `(2)` is a reduced local
nonfield with nonzero Jacobson radical `(2)`. This contrast is paper-only;
no localization construction is introduced here.

The coefficient criteria are `MvPolynomial.isNilpotent_iff` and
`MvPolynomial.isUnit_iff`. The extension theorem follows by mapping to the
polynomial ring over the coefficient quotient. The inclusions
`Ideal.map_radical_le` and `Ideal.radical_le_jacobson` give the reverse bound.

## References

* Andrew Yang's `Mathlib.Algebra.MvPolynomial.Nilpotent` (2025) supplies the
  coefficient criteria for nilpotence and invertibility used in the zero-ideal
  argument.
* `Mathlib.RingTheory.Jacobson.Ideal`, by Kenny Lau, Devon Tuma and Wojciech
  Nawrocki, supplies the Jacobson membership criterion and its compatibility
  with contraction along surjective ring homomorphisms.
-/

@[expose] public section

universe u v

namespace Ideal

/-- The Jacobson radical of zero in a nonempty-variable multivariate polynomial
ring over any commutative ring is the radical of zero.

For a polynomial in the Jacobson radical, multiplying by a variable and adding
one gives a unit. Its coefficients at the shifted, nonzero exponents show that
every coefficient of the original polynomial is nilpotent. -/
private theorem jacobson_bot_mvPolynomial_eq_radical {R : Type u} [CommRing R]
    {σ : Type v} [Nonempty σ] :
    jacobson (⊥ : Ideal (MvPolynomial σ R)) =
      (⊥ : Ideal (MvPolynomial σ R)).radical := by
  classical
  apply le_antisymm ?_ radical_le_jacobson
  intro p hp
  rw [mem_radical_iff]
  have hnil : IsNilpotent p := by
    apply MvPolynomial.isNilpotent_iff.mpr
    intro d
    let j : σ := Classical.choice ‹Nonempty σ›
    have hd : d + Finsupp.single j 1 ≠ 0 := by
      intro h
      have h' := congrArg (fun e : σ →₀ ℕ => e j) h
      simpa using h'
    have hu := (mem_jacobson_bot.mp hp) (MvPolynomial.X j)
    have hn := (MvPolynomial.isUnit_iff.mp hu).2 (d + Finsupp.single j 1) hd
    simpa only [MvPolynomial.coeff_add, MvPolynomial.coeff_mul_X,
      MvPolynomial.coeff_one, if_neg (Ne.symm hd), add_zero] using hn
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, by simpa only [mem_bot] using hn⟩

/-- For a nonempty variable type, the Jacobson radical of an extended coefficient
ideal consists exactly of the polynomials whose coefficients lie in the radical
of that ideal. The coefficient ring and the ideal are arbitrary, including the
unit ideal and the zero ring.

Nonemptiness is essential: with no variables this would assert that every ideal
of every commutative ring has equal Jacobson radical and radical. A reduced local
nonfield with nonzero maximal ideal already contradicts the zero-ideal case. -/
theorem jacobson_map_mvPolynomial_C {R : Type u} [CommRing R]
    {σ : Type v} [Nonempty σ] (I : Ideal R) :
    jacobson (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) =
      I.radical.map (MvPolynomial.C : R →+* MvPolynomial σ R) := by
  let f : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ I) :=
    MvPolynomial.map (Ideal.Quotient.mk I)
  have hf : Function.Surjective f :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = I.map (MvPolynomial.C : R →+* MvPolynomial σ R) := by
    dsimp only [f]
    have hmk : RingHomClass.toRingHom (Ideal.Quotient.mk I) = Ideal.Quotient.mk I :=
      RingHom.coe_inj (RingHom.coe_coe (Ideal.Quotient.mk I))
    simpa only [hmk, mk_ker] using
      (MvPolynomial.ker_map_eq_map_C (σ := σ) (Ideal.Quotient.mk I))
  apply le_antisymm ?_
    ((map_radical_le (MvPolynomial.C : R →+* MvPolynomial σ R)).trans radical_le_jacobson)
  intro p hp
  apply MvPolynomial.mem_map_C_iff_coeff_mem.mpr
  have hq : f p ∈ jacobson (⊥ : Ideal (MvPolynomial σ (R ⧸ I))) := by
    change p ∈ (jacobson (⊥ : Ideal (MvPolynomial σ (R ⧸ I)))).comap f
    rw [comap_jacobson_of_surjective hf, ← RingHom.ker_eq_comap_bot, hker]
    exact hp
  rw [jacobson_bot_mvPolynomial_eq_radical] at hq
  have hnil : IsNilpotent (f p) := by
    obtain ⟨n, hn⟩ := mem_radical_iff.mp hq
    exact ⟨n, mem_bot.mp hn⟩
  intro d
  obtain ⟨n, hn⟩ := MvPolynomial.isNilpotent_iff.mp hnil d
  refine mem_radical_iff.mpr ⟨n, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [f, MvPolynomial.coeff_map, map_pow] using hn

/-- The Jacobson radical of zero in a nonempty-variable multivariate polynomial
ring over any commutative ring is the radical of zero.

For a polynomial in the Jacobson radical, multiplying by a variable and adding
one gives a unit. Its coefficients at the shifted, nonzero exponents show that
every coefficient of the original polynomial is nilpotent. -/
theorem jacobson_bot_mvPolynomial {R : Type u} [CommRing R] {σ : Type v} [Nonempty σ] :
    jacobson (⊥ : Ideal (MvPolynomial σ R)) =
      (⊥ : Ideal (MvPolynomial σ R)).radical := by
  apply le_antisymm ?_ radical_le_jacobson
  have h := jacobson_map_mvPolynomial_C (σ := σ) (⊥ : Ideal R)
  have hle : (⊥ : Ideal R).radical.map (MvPolynomial.C : R →+* MvPolynomial σ R) ≤
      (⊥ : Ideal (MvPolynomial σ R)).radical := by
    simpa only [map_bot] using
      (map_radical_le (f := (MvPolynomial.C : R →+* MvPolynomial σ R))
        (I := (⊥ : Ideal R)))
  simpa only [map_bot] using h.le.trans hle

end Ideal
