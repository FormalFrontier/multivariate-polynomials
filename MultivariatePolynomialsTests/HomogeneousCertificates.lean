/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.HomogeneousCertificates

/-!
# Coordinate-power systems and constant systems

Positive coordinate powers satisfy both hypotheses of the certificate theorems.
Their certificates can also be given explicitly, independently of those theorems:
each coefficient family is `Finsupp.single i 1`, of homogeneous degree zero.
The semiring example applies in particular to natural-number coefficients.
A singleton constant-one system gives a degree-zero system with empty zero locus.
-/

open MvPolynomial

universe u v

/-- Coordinate powers meet the semiring radical hypothesis, and singleton
finitely supported coefficients give degree-zero certificates, even for `d = 0`
and without finiteness of the coordinate-power family. -/
example {I : Type u} {R : Type v} [CommSemiring R] (d : ℕ) :
    (∀ i : I, (X i ^ d : MvPolynomial I R).IsHomogeneous d) ∧
    (∀ i : I, (X i : MvPolynomial I R) ∈
      (Ideal.span (Set.range (fun j : I => (X j ^ d : MvPolynomial I R)))).radical) ∧
    ∃ q : I → (I →₀ MvPolynomial I R),
      (∀ i j, (q i j).IsHomogeneous 0) ∧
      ∀ i, (q i).sum (fun j r => r * X j ^ d) = X i ^ (0 + d) := by
  classical
  refine ⟨fun i => isHomogeneous_X_pow i d, ?_, ?_⟩
  · intro i
    exact Ideal.mem_radical_iff.mpr ⟨d, Ideal.subset_span ⟨i, rfl⟩⟩
  · refine ⟨fun i => Finsupp.single i 1, ?_, ?_⟩
    · intro i j
      by_cases h : i = j
      · subst j
        simpa only [Finsupp.single_eq_same] using isHomogeneous_one I R
      · simpa only [Finsupp.single_eq_of_ne' h] using
          (isHomogeneous_zero I R 0 : (0 : MvPolynomial I R).IsHomogeneous 0)
    · intro i
      simp

/-- Over the algebraic closure, vanishing of every positive coordinate power
forces the whole tuple to vanish, not merely its rational points. -/
example {I : Type u} {K : Type v} [Field K] (d : ℕ) (hd : 0 < d) :
    ∀ x : I → AlgebraicClosure K,
      (∀ i, aeval x (X i ^ d : MvPolynomial I K) = 0) → x = 0 := by
  intro x hx
  funext i
  have hi : x i ^ d = 0 := by simpa using hx i
  exact (pow_eq_zero_iff hd.ne').mp hi

/-- A constant-one generator has degree zero, radical containing every variable,
and no common zero even over the algebraic closure. Its coefficient `1` gives
`X i ^ (0 + 0) = 1` for every coordinate. -/
example {I : Type u} {K : Type v} [Field K] :
    (1 : MvPolynomial I K).IsHomogeneous 0 ∧
    (∀ i : I, (X i : MvPolynomial I K) ∈
      (Ideal.span (Set.range (fun _ : Unit => (1 : MvPolynomial I K)))).radical) ∧
    (∀ x : I → AlgebraicClosure K,
      (∀ j : Unit, aeval x ((fun _ : Unit => (1 : MvPolynomial I K)) j) = 0) → x = 0) ∧
    (∀ i : I, ∑ _j : Unit, (1 : MvPolynomial I K) * 1 = X i ^ (0 + 0)) := by
  refine ⟨isHomogeneous_one I K, ?_, ?_, ?_⟩
  · intro i
    apply Ideal.le_radical
    have hone : (1 : MvPolynomial I K) ∈
        Ideal.span (Set.range (fun _ : Unit => (1 : MvPolynomial I K))) :=
      Ideal.subset_span ⟨(), rfl⟩
    simpa only [mul_one] using
      (Ideal.span (Set.range (fun _ : Unit => (1 : MvPolynomial I K)))).mul_mem_left
        (X i) hone
  · intro x hx
    have h : (1 : AlgebraicClosure K) = 0 := by simpa using hx ()
    exact (one_ne_zero h).elim
  · intro i
    simp
