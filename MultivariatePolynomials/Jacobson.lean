/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Jacobson radical of a nonempty-variable polynomial ring

Over any commutative coefficient ring, the Jacobson radical of zero in a
polynomial ring with a nonempty variable type is its nilradical. This is an
ideal equality, not a vanishing assertion: the nonzero square-zero constant
`C (2 : ZMod 4)` supplies independent nonvacuity data in the test module.

Coefficient and variable universes are independent. No Jacobson-base, domain,
Noetherian, finite-variable, reducedness, or nontriviality premise is imposed;
the zero coefficient ring is included.

The nonempty-variable premise matters. With no variables the ring is the
coefficient ring. The localization of the integers at `(2)` is a reduced local
nonfield with nonzero Jacobson radical `(2)`. This contrast is paper-only;
no localization construction is introduced here.

The coefficient criteria are `MvPolynomial.isNilpotent_iff` and
`MvPolynomial.isUnit_iff`. The general inclusion
`Ideal.radical_le_jacobson` supplies one direction of the equality.
-/

@[expose] public section

universe u v

namespace Ideal

/-- The Jacobson radical of zero in a nonempty-variable multivariate polynomial
ring over any commutative ring is the radical of zero.

For a polynomial in the Jacobson radical, multiplying by a variable and adding
one gives a unit. Its coefficients at the shifted, nonzero exponents show that
every coefficient of the original polynomial is nilpotent. -/
theorem jacobson_bot_mvPolynomial {R : Type u} [CommRing R] {σ : Type v} [Nonempty σ] :
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

end Ideal
