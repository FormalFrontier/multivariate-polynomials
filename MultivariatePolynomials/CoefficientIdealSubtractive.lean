/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdeal
public import MultivariatePolynomials.SubtractiveRadical
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Ring

/-!
# Subtractive coefficient ideals and radical extensions

Over a commutative semiring, a radical coefficient ideal satisfying
`a ∈ I → a + b ∈ I → b ∈ I` extends to a radical ideal in any variable type,
including the empty type. The proof removes a greatest support monomial for a
chosen monomial order. Its coefficient belongs to the ideal by the coefficient
formula for a square and radicality. Subtractivity then puts the square of the
remaining polynomial in the extended ideal, and induction on support finishes.
No additive inverses or cancellation are required.

For nonempty variable types, the converse also holds: the extension is radical
if and only if the coefficient ideal is radical and satisfies the same
membership-subtraction condition.

If the extension of a coefficient ideal to a polynomial semiring with at least
one variable is radical, then membership of `a` and `a + b` forces membership of
`b`. For a variable `X`, the square of
`P = C a + C b * X + C (a + b) * X ^ 2` belongs to the extended ideal:
it is a sum of multiples of `C a` and `C (a + b)`. Radicality puts `P` in the
ideal, and its linear coefficient is `b`. The prime-extension statement follows
because prime ideals are radical. The construction is exposed as
`subtractiveWitness`, with its linear coefficient, square-membership and
nonmembership laws. The square-membership law needs only `a ∈ I` and
`a + b ∈ I`; nonmembership needs only `b ∉ I`.

The nonempty variable hypothesis is essential. In the natural numbers, the
ideal consisting of zero and all numbers at least two is prime: its complement
is the multiplicatively closed singleton containing one. This ideal contains
two and three but not one. With no variables, the constant map is an
isomorphism, so the extension of this ideal is still prime and hence radical.

Primaryness of a coefficient extension also forces this membership-subtraction
condition when there is a variable. Its proof uses a separate polynomial
`C a + C b * X + C a * X ^ 2`, multiplied by `1 + X`. The latter factor
is outside the radical because every power has constant coefficient one.
No radicality of the primary ideal is assumed.

## References

* `MultivariatePolynomials.CoefficientIdeal` for
  `MvPolynomial.mem_map_C_iff_coeff_mem`.
* Mathlib's `AddMonoidAlgebra.coeff_add` and the coefficient lemmas in
  `Mathlib.Algebra.MvPolynomial.Basic`.
* `Mathlib.RingTheory.Ideal.Operations` for `Ideal.IsRadical`, its square-root
  criterion, and `Ideal.IsPrime.isRadical`.
* Antoine Chambert-Loir's Mathlib monomial-order formalization supplies
  `MonomialOrder.coeff_pow_nsmul_degree`. Mathlib's well-ordering theorem
  supplies an order on any variable type; the erasure and support APIs come
  from `AddMonoidAlgebra` and `Finsupp`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

section Witness

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- The polynomial `C a + C b * X i + C (a + b) * X i ^ 2` detecting failure
of subtractivity at `i`. It is independent of any coefficient ideal. -/
noncomputable def subtractiveWitness (i : σ) (a b : R) : MvPolynomial σ R :=
  C a + C b * X i + C (a + b) * X i ^ 2

/-- The chosen linear coefficient of the subtractivity witness is `b`. -/
@[simp]
theorem coeff_subtractiveWitness (i : σ) (a b : R) :
    (subtractiveWitness i a b).coeff (Finsupp.single i 1) = b := by
  classical
  have h01 : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro heq
    simpa using congrArg (fun d : σ →₀ ℕ => d i) heq
  have h21 : (Finsupp.single i 2 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro heq
    simpa using congrArg (fun d : σ →₀ ℕ => d i) heq
  dsimp only [subtractiveWitness]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C, ite_eq_right h01,
    coeff_C_mul, coeff_X_same, coeff_X_pow, ite_eq_right h21, mul_one, mul_zero,
    zero_add, add_zero]

/-- The witness square lies in the coefficient-ideal extension as soon as
`a` and `a + b` belong to the ideal. -/
theorem subtractiveWitness_sq_mem_map_C (I : Ideal R) (i : σ) {a b : R}
    (ha : a ∈ I) (hab : a + b ∈ I) :
    subtractiveWitness i a b ^ 2 ∈ I.map (C : R →+* MvPolynomial σ R) := by
  let J : Ideal (MvPolynomial σ R) := I.map (C : R →+* MvPolynomial σ R)
  have haC : C a ∈ J := Ideal.mem_map_of_mem C ha
  have habC : C (a + b) ∈ J := Ideal.mem_map_of_mem C hab
  have hsquare :
      subtractiveWitness i a b ^ 2 =
        C a * (C a + C (b + b) * X i + C (a + a + b) * X i ^ 2) +
          C (a + b) *
            (C b * X i ^ 2 + C (b + b) * X i ^ 3 + C (a + b) * X i ^ 4) := by
    dsimp only [subtractiveWitness]
    simp only [map_add]
    ring
  rw [hsquare]
  exact J.add_mem (J.mul_mem_right _ haC) (J.mul_mem_right _ habC)

/-- Failure of membership of `b` excludes the witness from the extended ideal. -/
theorem subtractiveWitness_not_mem_map_C (I : Ideal R) (i : σ) {a b : R}
    (hb : b ∉ I) :
    subtractiveWitness i a b ∉ I.map (C : R →+* MvPolynomial σ R) := by
  intro hp
  exact hb (by simpa only [coeff_subtractiveWitness] using
    (mem_map_C_iff_coeff_mem.mp hp) (Finsupp.single i 1))

end Witness

/-- A radical extension to polynomials in a nonempty variable type forces
subtraction of ideal membership: if `a` and `a + b` lie in the coefficient
ideal, then so does `b`. -/
theorem mem_of_add_mem_of_isRadical_map_C {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R)
    (h : (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)).IsRadical)
    {a b : R} (ha : a ∈ I) (hab : a + b ∈ I) : b ∈ I := by
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hp : subtractiveWitness i a b ∈ I.map (C : R →+* MvPolynomial σ R) :=
    h ⟨2, subtractiveWitness_sq_mem_map_C I i ha hab⟩
  simpa only [coeff_subtractiveWitness] using
    (mem_map_C_iff_coeff_mem.mp hp) (Finsupp.single i 1)

/-- A primary extension to polynomials in a nonempty variable type forces
subtraction of ideal membership. Multiplication of a quadratic polynomial by
`1 + X` gives the cubic obstruction, while evaluation at zero rules out
radical membership of the latter factor. -/
theorem mem_of_add_mem_of_isPrimary_map_C {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R)
    (hI : (I.map (C : R →+* MvPolynomial σ R)).IsPrimary)
    {a b : R} (ha : a ∈ I) (hab : a + b ∈ I) : b ∈ I := by
  classical
  obtain ⟨i⟩ := ‹Nonempty σ›
  let J : Ideal (MvPolynomial σ R) := I.map (C : R →+* MvPolynomial σ R)
  let w : MvPolynomial σ R := C a + C b * X i + C a * X i ^ 2
  let q : MvPolynomial σ R := 1 + X i
  have haC : C a ∈ J := Ideal.mem_map_of_mem C ha
  have habC : C (a + b) ∈ J := Ideal.mem_map_of_mem C hab
  have hcubic : w * q =
      C a + C (a + b) * X i + C (a + b) * X i ^ 2 + C a * X i ^ 3 := by
    dsimp only [w, q]
    simp only [map_add]
    ring
  have hwq : w * q ∈ J := by
    rw [hcubic]
    exact J.add_mem
      (J.add_mem (J.add_mem haC (J.mul_mem_right _ habC))
        (J.mul_mem_right _ habC)) (J.mul_mem_right _ haC)
  rcases Ideal.isPrimary_iff.mp hI with ⟨hproper, hmul⟩
  have hq : q ∉ J.radical := by
    intro hrad
    rcases Ideal.mem_radical_iff.mp hrad with ⟨n, hn⟩
    have hconstant := (mem_map_C_iff_coeff_mem.mp hn) 0
    change constantCoeff (q ^ n) ∈ I at hconstant
    have hone : (1 : R) ∈ I := by
      simpa only [q, map_pow, map_add, map_one, constantCoeff_X, add_zero,
        one_pow] using hconstant
    have honeJ : (1 : MvPolynomial σ R) ∈ J := by
      simpa only [map_one] using
        (Ideal.mem_map_of_mem (C : R →+* MvPolynomial σ R) hone)
    apply hproper
    apply top_unique
    intro p _
    simpa only [mul_one] using J.mul_mem_left p honeJ
  have hw : w ∈ J := by
    have hor : w ∈ J ∨ q ∈ J.radical := by
      apply hmul
      exact hwq
    exact hor.resolve_right hq
  have h01 : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro heq
    simpa using congrArg (fun d : σ →₀ ℕ => d i) heq
  have h21 : (Finsupp.single i 2 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro heq
    simpa using congrArg (fun d : σ →₀ ℕ => d i) heq
  have hcoeff : w.coeff (Finsupp.single i 1) = b := by
    dsimp only [w]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C,
      ite_eq_right h01, coeff_C_mul, coeff_X_same, coeff_X_pow,
      ite_eq_right h21, mul_one, mul_zero, zero_add, add_zero]
  simpa only [hcoeff] using
    (mem_map_C_iff_coeff_mem.mp hw) (Finsupp.single i 1)

/-- A prime extension to polynomials in a nonempty variable type forces
subtraction of ideal membership: if `a` and `a + b` lie in the coefficient
ideal, then so does `b`. -/
theorem mem_of_add_mem_of_isPrime_map_C {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R)
    (h : (I.map (C : R →+* MvPolynomial σ R)).IsPrime)
    {a b : R} (ha : a ∈ I) (hab : a + b ∈ I) : b ∈ I := by
  exact mem_of_add_mem_of_isRadical_map_C I h.isRadical ha hab

/-- A radical coefficient ideal satisfying membership subtraction extends to a
radical ideal over any variable type, including the empty type. -/
theorem isRadical_map_C_of_subtractive {R : Type u} {σ : Type v}
    [CommSemiring R] (I : Ideal R) (hI : I.IsRadical)
    (hsub : ∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) :
    (I.map (C : R →+* MvPolynomial σ R)).IsRadical := by
  classical
  obtain ⟨ord, hwf⟩ := exists_wellFoundedGT σ
  let := ord
  let := hwf
  let m : MonomialOrder σ := MonomialOrder.lex
  let J := I.map (C : R →+* MvPolynomial σ R)
  have hJsub {a b : MvPolynomial σ R} (ha : a ∈ J) (hab : a + b ∈ J) : b ∈ J := by
    apply mem_map_C_iff_coeff_mem.mpr
    intro d
    exact hsub _ _ (mem_map_C_iff_coeff_mem.mp ha d)
      (by simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
        mem_map_C_iff_coeff_mem.mp hab d)
  apply (Ideal.isRadical_iff_pow_one_lt (I := J) 2 (by decide)).mpr
  intro p
  induction hn : p.support.card using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hp
    by_cases hp0 : p = 0
    · simpa only [hp0] using J.zero_mem
    have hc : m.leadingCoeff p ∈ I := by
      apply hI
      refine ⟨2, ?_⟩
      have h := mem_map_C_iff_coeff_mem.mp hp (2 • m.degree p)
      rwa [m.coeff_pow_nsmul_degree] at h
    let a := monomial (m.degree p) (m.leadingCoeff p)
    let q : MvPolynomial σ R := AddMonoidAlgebra.erase (m.degree p) p
    have ha : a ∈ J := by
      rw [show a = C (m.leadingCoeff p) * monomial (m.degree p) 1 by
        simp only [a, C_mul_monomial, mul_one]]
      exact J.mul_mem_right _ (Ideal.mem_map_of_mem C hc)
    have haq : a + q = p := by
      simpa only [a, q, MonomialOrder.leadingCoeff, single_eq_monomial] using
        (AddMonoidAlgebra.single_add_erase (m.degree p) p)
    have hqcard : q.support.card < n := by
      rw [← hn]
      have hs : q.support = p.support.erase (m.degree p) := by
        simp only [q, ← finsupp_support_eq_support, AddMonoidAlgebra.coeff_erase,
          Finsupp.support_erase]
      rw [hs]
      exact Finset.card_erase_lt_of_mem (m.degree_mem_support hp0)
    have hq : q ^ 2 ∈ J := by
      apply hJsub (a := a * (a + q + q)) (J.mul_mem_right _ ha)
      have heq : a * (a + q + q) + q ^ 2 = p ^ 2 := by
        rw [← haq]
        ring
      rwa [heq]
    rw [← haq]
    exact J.add_mem ha (ih q.support.card hqcard q rfl hq)

/-- In a nonempty variable type, extension along `C` is radical exactly when
the coefficient ideal is radical and satisfies membership subtraction. -/
theorem isRadical_map_C_iff {R : Type u} {σ : Type v}
    [CommSemiring R] [Nonempty σ] (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).IsRadical ↔
      I.IsRadical ∧ (∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) := by
  constructor
  · intro h
    refine ⟨?_, fun _ _ ha hab => mem_of_add_mem_of_isRadical_map_C I h ha hab⟩
    simpa only [comap_map_C] using h.comap (f := (C : R →+* MvPolynomial σ R))
  · rintro ⟨hI, hsub⟩
    exact isRadical_map_C_of_subtractive I hI hsub

end MvPolynomial

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- Coefficient extension commutes with radicals when the coefficient ideal's radical is
subtractive. The variable type may be empty. Over a commutative ring the subtractivity
hypothesis is automatic. -/
theorem radical_map_C_of_subtractive_radical (I : Ideal R)
    (hsub : ∀ a b : R, a ∈ I.radical → a + b ∈ I.radical → b ∈ I.radical) :
    (I.map (C : R →+* MvPolynomial σ R)).radical =
      I.radical.map (C : R →+* MvPolynomial σ R) := by
  have hrad : (I.radical.map (C : R →+* MvPolynomial σ R)).IsRadical :=
    isRadical_map_C_of_subtractive I.radical (Ideal.radical_isRadical I) hsub
  exact le_antisymm
    (hrad.radical_le_iff.mpr (Ideal.map_mono Ideal.le_radical))
    (Ideal.map_radical_le (C : R →+* MvPolynomial σ R))

/-- In a nonempty variable type, coefficient extension commutes with radicals exactly when
the coefficient ideal's radical is subtractive. -/
theorem radical_map_C_eq_iff_subtractive_radical [Nonempty σ] (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).radical =
        I.radical.map (C : R →+* MvPolynomial σ R) ↔
      ∀ a b : R, a ∈ I.radical → a + b ∈ I.radical → b ∈ I.radical := by
  constructor
  · intro h
    have hrad := Ideal.radical_isRadical (I.map (C : R →+* MvPolynomial σ R))
    rw [h] at hrad
    exact ((isRadical_map_C_iff I.radical).mp hrad).2
  · exact radical_map_C_of_subtractive_radical I

end MvPolynomial

namespace MvPolynomial

/-- Extension along the coefficient map preserves and reflects the condition that
membership of `a` and `a + b` implies membership of `b`. -/
theorem subtractive_map_C_iff {R : Type u} [CommSemiring R] {σ : Type v}
    (I : Ideal R) :
    (∀ p q : MvPolynomial σ R,
      p ∈ I.map (C : R →+* MvPolynomial σ R) →
      p + q ∈ I.map C → q ∈ I.map C) ↔
    (∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) := by
  constructor
  · intro h a b ha hab
    have hCa := Ideal.mem_map_of_mem (C : R →+* MvPolynomial σ R) ha
    have hCab := Ideal.mem_map_of_mem (C : R →+* MvPolynomial σ R) hab
    rw [C_add] at hCab
    have hb : b ∈ (I.map (C : R →+* MvPolynomial σ R)).comap C :=
      Ideal.mem_comap.mpr (h (C a) (C b) hCa hCab)
    simpa only [comap_map_C I] using hb
  · intro h p q hp hpq
    apply mem_map_C_iff_coeff_mem.mpr
    intro d
    apply h (p.coeff d) (q.coeff d)
    · exact (mem_map_C_iff_coeff_mem.mp hp) d
    · simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
        (mem_map_C_iff_coeff_mem.mp hpq) d

end MvPolynomial

namespace MvPolynomial

/-- Radical closure commutes with constant extension of a raw-subtractive ideal,
for any variable type. -/
theorem radical_map_C_of_subtractive {R : Type u} {σ : Type v} [CommSemiring R]
    (I : Ideal R) (hsub : ∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) :
    (I.map (C : R →+* MvPolynomial σ R)).radical =
      I.radical.map (C : R →+* MvPolynomial σ R) :=
  radical_map_C_of_subtractive_radical I (I.subtractive_radical hsub)

end MvPolynomial
