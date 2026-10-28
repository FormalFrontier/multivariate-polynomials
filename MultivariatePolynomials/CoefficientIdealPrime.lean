/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.CoefficientIdealSubtractive
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.SetTheory.Cardinal.Order

/-!
# Prime extensions of subtractive coefficient ideals

A prime ideal `I` over a commutative semiring extends to a prime coefficient
ideal if membership satisfies `∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I`. For a nonempty
variable type, the converse also holds. The sufficiency proof splits each
polynomial into its coefficients inside and outside `I`, then applies the
membership condition at the greatest coefficient of the outside product.
Neither the variable type nor the coefficient semiring requires an additional
finiteness or cancellation hypothesis. Over a commutative ring, subtractivity is
automatic; over a commutative semiring it is recorded explicitly.

The proof uses Mathlib's degree-sum coefficient formula
`MonomialOrder.coeff_mul_of_degree_add` and its `Finsupp.filter` decomposition API.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A prime subtractive coefficient ideal extends to a prime ideal over any variable type. -/
theorem isPrime_map_C_of_subtractive
    {R : Type u} {σ : Type v} [CommSemiring R]
    (I : Ideal R) (hI : I.IsPrime)
    (hsub : ∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrime := by
  classical
  let J : Ideal (MvPolynomial σ R) := I.map C
  have hsubJ := (subtractive_map_C_iff (σ := σ) I).mpr hsub
  obtain ⟨ord, hwf⟩ := exists_wellFoundedGT σ
  let : LinearOrder σ := ord
  let : WellFoundedGT σ := hwf
  let m : MonomialOrder σ := MonomialOrder.lex
  let inside (p : MvPolynomial σ R) : MvPolynomial σ R :=
    AddMonoidAlgebra.ofCoeff (p.coeff.filter fun d => p.coeff d ∈ I)
  let outside (p : MvPolynomial σ R) : MvPolynomial σ R :=
    AddMonoidAlgebra.ofCoeff (p.coeff.filter fun d => ¬p.coeff d ∈ I)
  have coeff_inside (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
      (inside p).coeff d = if p.coeff d ∈ I then p.coeff d else 0 := by
    simp only [inside, Finsupp.filter_apply]
  have coeff_outside (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
      (outside p).coeff d = if p.coeff d ∈ I then 0 else p.coeff d := by
    simp only [outside, Finsupp.filter_apply, ite_not]
  have split (p : MvPolynomial σ R) : inside p + outside p = p := by
    dsimp only [inside, outside]
    rw [← AddMonoidAlgebra.ofCoeff_add, Finsupp.filter_add_filter_not,
      AddMonoidAlgebra.ofCoeff_coeff]
  have inside_mem (p : MvPolynomial σ R) : inside p ∈ J := by
    apply mem_map_C_iff_coeff_mem.mpr
    intro d
    rw [coeff_inside]
    split_ifs with h
    · exact h
    · exact I.zero_mem
  have outside_nonzero (p : MvPolynomial σ R) (hp : p ∉ J) : outside p ≠ 0 := by
    intro h
    apply hp
    have heq := split p
    rw [h, add_zero] at heq
    exact heq ▸ inside_mem p
  have outside_coeff_notMem (p : MvPolynomial σ R) (d : σ →₀ ℕ)
      (hd : (outside p).coeff d ≠ 0) : (outside p).coeff d ∉ I := by
    by_cases h : p.coeff d ∈ I
    · simp [coeff_outside, h] at hd
    · simp [coeff_outside, h]
  refine ⟨?_, ?_⟩
  · intro h
    apply hI.ne_top
    simpa only [comap_map_C, Ideal.comap_top] using
      congrArg (Ideal.comap (C : R →+* MvPolynomial σ R)) h
  · intro f g hfg
    by_cases hf : f ∈ J
    · exact Or.inl hf
    by_cases hg : g ∈ J
    · exact Or.inr hg
    exfalso
    have hfl : m.leadingCoeff (outside f) ∉ I :=
      outside_coeff_notMem f _
        ((MonomialOrder.coeff_degree_ne_zero_iff (m := m)).mpr (outside_nonzero f hf))
    have hgl : m.leadingCoeff (outside g) ∉ I :=
      outside_coeff_notMem g _
        ((MonomialOrder.coeff_degree_ne_zero_iff (m := m)).mpr (outside_nonzero g hg))
    have hout : outside f * outside g ∉ J := by
      intro h
      have hc := mem_map_C_iff_coeff_mem.mp h (m.degree (outside f) + m.degree (outside g))
      rw [MonomialOrder.coeff_mul_of_degree_add (m := m)] at hc
      exact hI.mul_notMem hfl hgl hc
    let rest := inside f * inside g + inside f * outside g + outside f * inside g
    have hrest : rest ∈ J := by
      exact J.add_mem
        (J.add_mem (J.mul_mem_left _ (inside_mem g))
          (J.mul_mem_right _ (inside_mem f)))
        (J.mul_mem_left _ (inside_mem g))
    have hprod : f * g = rest + outside f * outside g := by
      calc
        f * g = (inside f + outside f) * (inside g + outside g) := by
          rw [split, split]
        _ = rest + outside f * outside g := by
          simp only [rest, add_mul, mul_add]
          ac_rfl
    exact hout (hsubJ rest (outside f * outside g) hrest (hprod ▸ hfg))

private theorem isPrime_and_subtractive_of_isPrime_map_C
    {R : Type u} {σ : Type v} [CommSemiring R] [Nonempty σ]
    (I : Ideal R) (h : (I.map (C : R →+* MvPolynomial σ R)).IsPrime) :
    I.IsPrime ∧ (∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) := by
  let : (I.map (C : R →+* MvPolynomial σ R)).IsPrime := h
  constructor
  · rw [← comap_map_C (σ := σ) I]
    exact Ideal.IsPrime.comap (C : R →+* MvPolynomial σ R)
  · intro a b ha hab
    exact mem_of_add_mem_of_isPrime_map_C I h ha hab

/-- For nonempty variables, a coefficient extension is prime exactly when the
coefficient ideal is prime and subtractive. -/
theorem isPrime_map_C_iff
    {R : Type u} {σ : Type v} [CommSemiring R] [Nonempty σ]
    (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrime ↔
      I.IsPrime ∧ (∀ a b : R, a ∈ I → a + b ∈ I → b ∈ I) := by
  constructor
  · exact isPrime_and_subtractive_of_isPrime_map_C I
  · rintro ⟨hI, hsub⟩
    exact isPrime_map_C_of_subtractive I hI hsub

end MvPolynomial
