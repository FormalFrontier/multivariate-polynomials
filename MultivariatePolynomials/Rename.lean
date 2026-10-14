/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
import MultivariatePolynomials.FiniteSupport
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Injectivity and surjectivity of polynomial variable renaming

For a map `f : σ → τ` and a commutative semiring `R`, variable renaming is the
homomorphism from the full polynomial semiring `MvPolynomial σ R` to the full
polynomial semiring `MvPolynomial τ R` that sends `X i` to `X (f i)`.

Its underlying function is injective exactly when `f` is injective or `R` is
subsingleton, and surjective exactly when `f` is surjective or `R` is subsingleton.
The coefficient and two variable types may lie in independent universes. Neither
variable type is required to be finite or inhabited, and the coefficients need
not form a ring or be nontrivial.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: variable renaming and its
  injectivity and surjectivity for injective and surjective variable maps.
-/

@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]

/-- Polynomial variable renaming is injective exactly when the variable map is
injective or the coefficient semiring is subsingleton. -/
theorem injective_rename_iff (f : σ → τ) :
    Function.Injective (rename (R := R) f) ↔
      Function.Injective f ∨ Subsingleton R := by
  have hcoeff (p : MvPolynomial σ R) :
      AddMonoidAlgebra.coeffEquiv (rename (R := R) f p) =
        Finsupp.mapDomain (Finsupp.mapDomain f) (AddMonoidAlgebra.coeffEquiv p) := by
    change (AddMonoidAlgebra.mapDomain (Finsupp.mapDomain f) p).coeff = _
    rfl
  have hrename :
      Function.Injective (rename (R := R) f) ↔
        Function.Injective (Finsupp.mapDomain (Finsupp.mapDomain f) :
          ((σ →₀ ℕ) →₀ R) → ((τ →₀ ℕ) →₀ R)) := by
    constructor
    · intro h p q hpq
      apply AddMonoidAlgebra.ofCoeff_injective
      apply h
      apply AddMonoidAlgebra.coeffEquiv.injective
      simpa only [hcoeff, AddMonoidAlgebra.coeffEquiv_apply,
        AddMonoidAlgebra.coeff_ofCoeff] using hpq
    · intro h p q hpq
      apply AddMonoidAlgebra.coeffEquiv.injective
      apply h
      rw [← hcoeff, ← hcoeff, hpq]
  have hNat : ¬ Subsingleton ℕ := by
    intro h
    exact Nat.zero_ne_one (h.elim _ _)
  rw [hrename, Finsupp.mapDomain_injective_iff, Finsupp.mapDomain_injective_iff]
  simp only [hNat, or_false]

/-- Polynomial variable renaming is surjective exactly when the variable map is
surjective or the coefficient semiring is subsingleton. -/
theorem surjective_rename_iff (f : σ → τ) :
    Function.Surjective (rename (R := R) f) ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · left
      intro t
      obtain ⟨p, hp⟩ := h (X t)
      have ht : t ∈ (rename f p).vars := by
        rw [hp, vars_X]
        exact Finset.mem_singleton_self t
      obtain ⟨s, _, hs⟩ := mem_vars_rename f p ht
      exact ⟨s, hs⟩
  · rintro (hf | hR)
    · exact rename_surjective f hf
    · have : Nonempty (MvPolynomial σ R) := ⟨0⟩
      exact Function.surjective_to_subsingleton _

end MvPolynomial
