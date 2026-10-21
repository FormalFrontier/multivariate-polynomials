/-
SPDX-License-Identifier: Apache-2.0
Portions adapted from Mathlib:
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

/-!
# Non-zero-divisors and regular differences of variables

The scalar-annihilator criterion characterizes non-zero-divisors over a
commutative semiring by the common annihilator of their coefficients in the
coefficient semiring. It does not require an individual coefficient to be a
non-zero-divisor or impose restrictions on the variable type.

Over commutative rings, membership in `nonZeroDivisors` also expresses
`IsRegular`; no such equivalence is asserted here for arbitrary semirings.

The difference of two distinct polynomial variables is regular over any
commutative ring, including the zero ring. A triangular change of variables
reduces the assertion to regularity of a single variable.

## References

* Mathlib's unary `Polynomial.mem_nonZeroDivisors_iff` scalar-annihilator criterion.
* McCoy's least-leading-monomial argument, using Mathlib's `MonomialOrder` API.
* The coefficient-isolation argument adapts Mathlib's
  `MonomialOrder.coeff_mul_of_add_of_degree_le` (Antoine Chambert-Loir, 2024).
* Mathlib's `MvPolynomial.isRegular_X` and polynomial evaluation API.
-/

universe u v

namespace MvPolynomial

open scoped MonomialOrder

/-- Reverse induction along a monomial order only needs a finite exceptional set. -/
private theorem monomial_reverse_induction {sigma : Type v} (m : MonomialOrder sigma)
    (s : Finset (sigma →₀ ℕ)) (P : (sigma →₀ ℕ) → Prop)
    (hout : ∀ a, a ∉ s → P a)
    (hstep : ∀ a, (∀ b, a ≺[m] b → P b) → P a) : ∀ a, P a := by
  classical
  have h : ∀ n : ℕ, ∀ a, (s.filter fun b => a ≺[m] b).card = n → P a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      apply hstep a
      intro b hab
      by_cases hb : b ∈ s
      · apply ih (s.filter fun c => b ≺[m] c).card ?_ b rfl
        rw [← ha]
        apply Finset.card_lt_card
        refine ⟨?_, ?_⟩
        · intro c hc
          obtain ⟨hcs, hbc⟩ := Finset.mem_filter.mp hc
          exact Finset.mem_filter.mpr ⟨hcs, lt_trans hab hbc⟩
        · intro hsub
          have hbb := Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hb, hab⟩))
          exact (lt_irrefl (m.toSyn b)) hbb.2
      · exact hout b hb
  intro a
  exact h _ a rfl

/-- At a given exponent, terms above it can be discarded when their coefficients
annihilate the other factor. No cancellation in the coefficient semiring is used. -/
private theorem coeff_mul_eq_of_higher_smul_eq_zero
    {R : Type u} {sigma : Type v} [CommSemiring R] (m : MonomialOrder sigma)
    {p q : MvPolynomial sigma R} (a : sigma →₀ ℕ)
    (hh : ∀ b, a ≺[m] b → p.coeff b • q = 0) :
    (p * q).coeff (a + m.degree q) = p.coeff a * q.coeff (m.degree q) := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (a, m.degree q)]
  · rintro ⟨b, c⟩ hbc hne
    have hsum : b + c = a + m.degree q := Finset.mem_antidiagonal.mp hbc
    rcases lt_trichotomy (m.toSyn b) (m.toSyn a) with hlt | heq | hgt
    · have hsum' : m.toSyn b + m.toSyn c = m.toSyn a + m.toSyn (m.degree q) := by
        simpa only [map_add] using congrArg m.toSyn hsum
      have hqc : m.degree q ≺[m] c := by
        apply lt_of_add_lt_add_left (a := m.toSyn b)
        calc
          m.toSyn b + m.toSyn (m.degree q) <
              m.toSyn a + m.toSyn (m.degree q) := by
                simpa only [add_comm] using add_lt_add_right hlt (m.toSyn (m.degree q))
          _ = m.toSyn b + m.toSyn c := hsum'.symm
      rw [m.coeff_eq_zero_of_lt hqc, mul_zero]
    · have hba : b = a := m.toSyn.injective heq
      subst b
      have hc : c = m.degree q := add_left_cancel hsum
      exact (hne (congrArg (Prod.mk a) hc)).elim
    · have hz := congrArg (fun f : MvPolynomial sigma R => f.coeff c) (hh b hgt)
      simpa [coeff_smul, smul_eq_mul] using hz
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim

/-- Well-founded descent on the leading exponent of an annihilator. -/
private theorem annihilator_eq_zero_by_degree
    {R : Type u} {sigma : Type v} [CommSemiring R] (m : MonomialOrder sigma)
    {p : MvPolynomial sigma R} (hp : ∀ r : R, r • p = 0 → r = 0) :
    ∀ d : m.syn, ∀ q : MvPolynomial sigma R,
      m.toSyn (m.degree q) = d → p * q = 0 → q = 0 := by
  classical
  intro d
  induction d using m.wellFoundedLT_syn.wf.induction with
  | h d ih =>
    intro q hd hq
    have hall : ∀ a, p.coeff a • q = 0 := by
      apply monomial_reverse_induction m p.support
      · intro a ha
        have hpa : p.coeff a = 0 := by
          by_contra hne
          exact ha (mem_support_iff.mpr hne)
        rw [hpa, zero_smul]
      · intro a hh
        by_contra hne
        have hmul : p * (p.coeff a • q) = 0 := by
          calc
            p * (p.coeff a • q) = C (p.coeff a) * (p * q) := by
              rw [smul_eq_C_mul]
              ac_rfl
            _ = 0 := by rw [hq, mul_zero]
        have hdeg : m.degree (p.coeff a • q) = m.degree q := by
          apply m.toSyn.injective
          apply le_antisymm m.degree_smul_le
          apply le_of_not_gt
          intro hlt
          have hlt' : m.toSyn (m.degree (p.coeff a • q)) < d := by
            simpa only [hd] using hlt
          exact hne (ih _ hlt' _ rfl hmul)
        have hz : p.coeff a * q.coeff (m.degree q) = 0 := by
          have hc := coeff_mul_eq_of_higher_smul_eq_zero m a hh
          simpa [hq] using hc.symm
        have hn := m.coeff_degree_ne_zero_iff.mpr hne
        apply hn
        simpa only [hdeg, coeff_smul, smul_eq_mul] using hz
    have hscalar : m.leadingCoeff q • p = 0 := by
      ext a
      have hz := congrArg (fun f : MvPolynomial sigma R => f.coeff (m.degree q)) (hall a)
      simpa [coeff_smul, smul_eq_mul, MonomialOrder.leadingCoeff,
        mul_comm] using hz
    exact m.leadingCoeff_eq_zero_iff.mp (hp _ hscalar)

/-- A multivariate polynomial with no nonzero scalar annihilator has no nonzero
polynomial annihilator. This is McCoy's theorem over a commutative semiring. -/
theorem eq_zero_of_mul_eq_zero_of_smul
    {R : Type u} {sigma : Type v} [CommSemiring R] {p q : MvPolynomial sigma R}
    (h : p * q = 0) (hp : ∀ r : R, r • p = 0 → r = 0) : q = 0 := by
  classical
  obtain ⟨lo, hwf⟩ := exists_wellFoundedGT sigma
  let := lo
  let := hwf
  let m : MonomialOrder sigma := MonomialOrder.lex
  exact annihilator_eq_zero_by_degree m hp _ q rfl h

/-- A multivariate polynomial is a non-zero-divisor exactly when its coefficients
have no nonzero common annihilator in the coefficient semiring. -/
protected theorem mem_nonZeroDivisors_iff {R : Type u} {sigma : Type v} [CommSemiring R]
    (p : MvPolynomial sigma R) :
    p ∈ nonZeroDivisors (MvPolynomial sigma R) ↔
      ∀ r : R, (∀ d : sigma →₀ ℕ, r * p.coeff d = 0) → r = 0 := by
  constructor
  · intro hp r hr
    have hmul : C r * p = 0 := by
      ext d
      simpa [coeff_C_mul] using hr d
    have hC : C r = (0 : MvPolynomial sigma R) :=
      _root_.mem_nonZeroDivisors_iff_right.mp hp (C r) hmul
    exact (C_injective sigma R) (by simpa using hC)
  · intro hp
    apply _root_.mem_nonZeroDivisors_iff_right.mpr
    intro q hq
    apply eq_zero_of_mul_eq_zero_of_smul (p := p) (q := q)
      (by simpa only [mul_comm] using hq)
    intro r hr
    apply hp r
    intro d
    simpa [coeff_smul, smul_eq_mul] using
      congrArg (fun f : MvPolynomial sigma R => f.coeff d) hr

private noncomputable def shearForward {R : Type u} {σ : Type v}
    [CommRing R] (i j : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := by
  classical
  exact aeval (fun k => if k = i then X i + X j else X k)

private noncomputable def shearBackward {R : Type u} {σ : Type v}
    [CommRing R] (i j : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := by
  classical
  exact aeval (fun k => if k = i then X i - X j else X k)

private theorem shear_leftInverse {R : Type u} {σ : Type v}
    [CommRing R] {i j : σ} (hij : i ≠ j) :
    Function.LeftInverse (shearBackward (R := R) i j) (shearForward (R := R) i j) := by
  classical
  have h : (shearBackward (R := R) i j).comp (shearForward (R := R) i j) =
      AlgHom.id R (MvPolynomial σ R) := by
    apply algHom_ext
    intro k
    by_cases hki : k = i
    · subst k
      simp [shearForward, shearBackward, Ne.symm hij]
    · simp [shearForward, shearBackward, hki]
  intro p
  exact DFunLike.congr_fun h p

/-- The difference of two distinct variables is regular over every commutative ring. -/
theorem isRegular_X_sub_X {R : Type u} {σ : Type v} [CommRing R]
    {i j : σ} (hij : i ≠ j) : IsRegular (X i - X j : MvPolynomial σ R) := by
  classical
  rw [← isLeftRegular_iff_isRegular]
  intro p q hpq
  apply (shear_leftInverse (R := R) hij).injective
  apply (isRegular_X (R := R) (n := i)).1
  simpa [shearForward, hij, Ne.symm hij] using
    congrArg (shearForward (R := R) i j) hpq

end MvPolynomial
