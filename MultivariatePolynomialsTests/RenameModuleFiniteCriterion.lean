/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameModuleFinite

@[expose] public section

/-!
# Applications of the module-finiteness criterion for renaming

The successor map on natural-number indices misses `0`, so its renaming gives
a finite module over the source polynomial semiring exactly when the
coefficients are subsingleton. In contrast, the projection `ℕ × Bool → ℕ`
is surjective and noninjective, and its renaming gives a finite module even
though both variable types are infinite.

Both applications below use `MvPolynomial.moduleFinite_rename_iff`. In each
statement, the module structure is explicitly induced by the displayed
renaming homomorphism, rather than by coefficient scalar multiplication.

## References

* `MultivariatePolynomials.RenameModuleFinite`: the module-finiteness criterion.
-/

universe u

namespace MultivariatePolynomialsTests

private theorem moduleFinite_rename_succ_iff {R : Type u} [CommSemiring R] :
    @Module.Finite (MvPolynomial ℕ R) (MvPolynomial ℕ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ R) (MvPolynomial ℕ R)
        inferInstance inferInstance
        (MvPolynomial.rename (R := R) Nat.succ).toRingHom.toAlgebra) ↔
      Subsingleton R := by
  constructor
  · intro h
    rcases (MvPolynomial.moduleFinite_rename_iff (R := R) Nat.succ).mp h with hf | hR
    · obtain ⟨n, hn⟩ := hf 0
      cases hn
    · exact hR
  · intro hR
    exact (MvPolynomial.moduleFinite_rename_iff (R := R) Nat.succ).mpr (Or.inr hR)

private theorem moduleFinite_rename_fst {R : Type u} [CommSemiring R] :
    @Module.Finite (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R)
        inferInstance inferInstance
        (MvPolynomial.rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra) := by
  apply (MvPolynomial.moduleFinite_rename_iff (R := R) (Prod.fst : ℕ × Bool → ℕ)).mpr
  exact Or.inl fun n => ⟨(n, false), rfl⟩

end MultivariatePolynomialsTests
