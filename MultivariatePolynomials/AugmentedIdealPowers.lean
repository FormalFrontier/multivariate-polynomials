/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
meta import Lean.Elab.Tactic.Omega

/-!
# Coefficients of powers of augmented coefficient ideals

For an ideal `I` of a commutative semiring, let `J` be its pullback along the
constant coefficient homomorphism. A polynomial belongs to `J ^ n` exactly
when its coefficient at each exponent `d` belongs to
`I ^ (n - d.sum (fun _ k => k))`.

The degree deficit uses subtraction in `ℕ`: coefficients of total degree at
least `n` are unrestricted, since `I ^ 0 = ⊤`. The coefficient semiring and
variable type have independent universes. Empty or infinite variable types,
trivial coefficient semirings, and the bottom and top coefficient ideals are
included, without finiteness or subtractivity assumptions.

The forward implication uses induction on ideal products and the convolution
formula for coefficients. For the converse, the coefficient and variable
parts of a monomial supply complementary powers of `J`; the variable part
uses Mathlib's existing power criterion for `idealOfVars`. The bottom-ideal
agreement below reduces the coefficient condition to Mathlib's vanishing
criterion in degrees less than `n`.

## References

* Eric Wieser's `Mathlib.RingTheory.MvPolynomial.Ideal` supplies the
  variable-ideal power criterion `MvPolynomial.mem_pow_idealOfVars_iff` and
  its coefficient-vanishing form `MvPolynomial.mem_pow_idealOfVars_iff'`.
  The monomial argument follows this formalization's support approach.
* Mathlib's `Mathlib.Algebra.MvPolynomial.Basic`, by Johannes Hölzl,
  Johan Commelin and Mario Carneiro, supplies coefficient convolution and
  the finite-support monomial expansion.
* Mathlib's submodule-product induction and ideal extension, multiplication
  and power APIs supply the remaining ideal operations.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- A coefficient of a polynomial in the `n`th power of a constant-term
pullback ideal lies in the power of the coefficient ideal given by its total
degree deficit. The deficit is truncated subtraction in `ℕ`, so the bound is
vacuous in total degrees at least `n`. -/
theorem coeff_mem_pow_of_mem_pow_comap_constantCoeff
    {I : Ideal R} {n : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ (I.comap (constantCoeff : MvPolynomial σ R →+* R)) ^ n)
    (d : σ →₀ ℕ) : p.coeff d ∈ I ^ (n - d.sum fun _ k => k) := by
  classical
  change p.coeff d ∈ I ^ (n - Finsupp.degree d)
  induction n generalizing p d with
  | zero => simp [Ideal.one_eq_top]
  | succ n ih =>
      rw [pow_succ] at hp
      have h : ∀ d, p.coeff d ∈ I ^ (n + 1 - Finsupp.degree d) := by
        refine Submodule.mul_induction_on hp ?_ ?_
        · intro a ha b hb d
          have hb0 : b.coeff 0 ∈ I := by
            simpa only [Ideal.mem_comap, constantCoeff_eq] using hb
          rw [coeff_mul]
          refine Ideal.sum_mem _ fun e he => ?_
          have hdegree : Finsupp.degree e.1 + Finsupp.degree e.2 =
              Finsupp.degree d := by
            simpa only [map_add] using
              congrArg Finsupp.degree (Finset.mem_antidiagonal.mp he)
          by_cases he0 : e.2 = 0
          · have hprod : a.coeff e.1 * b.coeff 0 ∈
                I ^ (n - Finsupp.degree e.1 + 1) := by
              rw [pow_succ]
              exact Ideal.mul_mem_mul (ih ha e.1) hb0
            simp only [he0, map_zero, add_zero] at hdegree
            rw [he0]
            exact (Ideal.pow_le_pow_right (I := I) (by omega)) hprod
          · have hpos : 0 < Finsupp.degree e.2 :=
              Nat.pos_of_ne_zero fun hzero =>
                he0 ((Finsupp.degree_eq_zero_iff e.2).mp hzero)
            have hprod : a.coeff e.1 * b.coeff e.2 ∈
                I ^ (n - Finsupp.degree e.1) :=
              (I ^ (n - Finsupp.degree e.1)).mul_mem_right _ (ih ha e.1)
            exact (Ideal.pow_le_pow_right (I := I) (by omega)) hprod
        · intro a b ha hb d
          simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
            (I ^ (n + 1 - Finsupp.degree d)).add_mem (ha d) (hb d)
      exact h d

/-- A monomial belongs to the `n`th power of the pullback of a coefficient ideal
if its coefficient belongs to the power given by the truncated degree deficit. -/
theorem monomial_mem_pow_comap_constantCoeff
    {I : Ideal R} {n : ℕ} {d : σ →₀ ℕ} {r : R}
    (hr : r ∈ I ^ (n - d.sum (fun _ k => k))) :
    monomial d r ∈ (I.comap (constantCoeff : MvPolynomial σ R →+* R)) ^ n := by
  classical
  let J : Ideal (MvPolynomial σ R) := I.comap constantCoeff
  let k : ℕ := d.sum (fun _ k => k)
  have hC : Ideal.map (C : R →+* MvPolynomial σ R) I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change constantCoeff (C a : MvPolynomial σ R) ∈ I
    simpa only [constantCoeff_C] using ha
  have hvars : idealOfVars σ R ≤ J := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change constantCoeff (X i : MvPolynomial σ R) ∈ I
    simpa only [constantCoeff_X] using I.zero_mem
  have hcoeff : C r ∈ J ^ (n - k) := by
    have hm : C r ∈ Ideal.map (C : R →+* MvPolynomial σ R) (I ^ (n - k)) :=
      Ideal.mem_map_of_mem C hr
    rw [Ideal.map_pow] at hm
    exact (Ideal.pow_right_mono hC (n - k)) hm
  have hmonic : monomial d (1 : R) ∈ idealOfVars σ R ^ k := by
    refine (mem_pow_idealOfVars_iff k _).mpr ?_
    intro e he
    have hed : e = d := Finset.mem_singleton.mp (support_monomial_subset he)
    subst e
    exact le_rfl
  have hvariable : monomial d (1 : R) ∈ J ^ k :=
    (Ideal.pow_right_mono hvars k) hmonic
  have hprod : C r * monomial d (1 : R) ∈ J ^ (n - k + k) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hcoeff hvariable
  have hn : n ≤ n - k + k := le_tsub_add
  apply Ideal.pow_le_pow_right (I := J) hn
  simpa only [C_mul_monomial, mul_one] using hprod

/-- Coefficient membership in the powers given by truncated degree deficits
implies polynomial membership in the corresponding power of the pullback ideal. -/
theorem mem_pow_comap_constantCoeff_of_coeff_mem
    {I : Ideal R} {n : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ d : σ →₀ ℕ, p.coeff d ∈ I ^ (n - d.sum (fun _ k => k))) :
    p ∈ (I.comap (constantCoeff : MvPolynomial σ R →+* R)) ^ n := by
  classical
  rw [p.as_sum]
  exact Ideal.sum_mem _ fun d _ => monomial_mem_pow_comap_constantCoeff (hp d)

/-- Membership in a power of the pullback of a coefficient ideal is equivalent
to coefficientwise membership in the powers given by the truncated total-degree
deficits. Coefficients in degrees at least `n` are unrestricted, since their
required ideal power is `I ^ 0 = ⊤`. -/
theorem mem_pow_comap_constantCoeff_iff_coeff_mem_pow
    (I : Ideal R) (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ (I.comap (constantCoeff : MvPolynomial σ R →+* R)) ^ n ↔
      ∀ d : σ →₀ ℕ, p.coeff d ∈ I ^ (n - d.sum (fun _ k => k)) :=
  ⟨fun hp d => coeff_mem_pow_of_mem_pow_comap_constantCoeff hp d,
    mem_pow_comap_constantCoeff_of_coeff_mem⟩

/-- For the bottom coefficient ideal, the criterion agrees with Mathlib's
variable-ideal power criterion: a positive deficit forces a zero coefficient,
whereas a zero deficit imposes no condition. -/
private theorem mem_pow_comap_bot_constantCoeff_iff_mem_pow_idealOfVars
    (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ ((⊥ : Ideal R).comap (constantCoeff : MvPolynomial σ R →+* R)) ^ n ↔
      p ∈ idealOfVars σ R ^ n := by
  rw [mem_pow_comap_constantCoeff_iff_coeff_mem_pow, mem_pow_idealOfVars_iff']
  change (∀ d, p.coeff d ∈ (⊥ : Ideal R) ^ (n - Finsupp.degree d)) ↔
    ∀ d, Finsupp.degree d < n → p.coeff d = 0
  constructor
  · intro h d hd
    have hn : n - Finsupp.degree d ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hd)
    simpa only [Ideal.bot_pow hn, Ideal.mem_bot] using h d
  · intro h d
    by_cases hd : Finsupp.degree d < n
    · have hn : n - Finsupp.degree d ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hd)
      rw [Ideal.bot_pow hn, Ideal.mem_bot]
      exact h d hd
    · have hn : n - Finsupp.degree d = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hd)
      simp [hn, Ideal.one_eq_top]

end MvPolynomial
