/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.RenameIntegral

/-!
# Applications of the variable-renaming integrality criterion

Every integrality conclusion below is obtained from
`MvPolynomial.isIntegral_rename_iff`; these are applications of that equivalence,
not independent proofs of it. The base in each conclusion is the full source
polynomial ring, not the coefficient ring.

Surjective maps give integral renamings even when they identify variables.
Successor renaming on the natural numbers is integral precisely for
subsingleton coefficients, although its source and target variable types agree.
The paired successor `(n, b) ↦ n + 1` is also nonintegral over nontrivial
coefficients, despite identifying source variables.
The general application clients retain independent coefficient, source-variable
and target-variable universes.

## References

* `MultivariatePolynomials.RenameIntegral`: the variable-renaming integrality criterion.
-/

universe u v w

namespace MultivariatePolynomialsTests

private theorem isIntegral_rename_of_surjective
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]
    (f : σ → τ) (hf : Function.Surjective f) :
    RingHom.IsIntegral ((MvPolynomial.rename (R := R) f).toRingHom) := by
  exact (MvPolynomial.isIntegral_rename_iff (R := R) f).mpr (Or.inl hf)

private theorem isIntegral_rename_of_subsingleton
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] [Subsingleton R]
    (f : σ → τ) :
    RingHom.IsIntegral ((MvPolynomial.rename (R := R) f).toRingHom) := by
  exact (MvPolynomial.isIntegral_rename_iff (R := R) f).mpr (Or.inr inferInstance)

private theorem isIntegral_rename_projection {R : Type u} [CommRing R] :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom) := by
  exact isIntegral_rename_of_surjective _ (fun n => ⟨(n, false), rfl⟩)

private theorem isIntegral_rename_empty {R : Type u} [CommRing R] :
    RingHom.IsIntegral
      ((MvPolynomial.rename (R := R) (Empty.elim : Empty → Empty)).toRingHom) := by
  exact isIntegral_rename_of_surjective _ (fun e => e.elim)

private theorem successor_not_surjective : ¬ Function.Surjective Nat.succ := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

private theorem isIntegral_rename_succ_iff {R : Type u} [CommRing R] :
    RingHom.IsIntegral ((MvPolynomial.rename (R := R) Nat.succ).toRingHom) ↔
      Subsingleton R := by
  constructor
  · intro h
    rcases (MvPolynomial.isIntegral_rename_iff (R := R) Nat.succ).mp h with hf | hR
    · exact (successor_not_surjective hf).elim
    · exact hR
  · intro hR
    exact (MvPolynomial.isIntegral_rename_iff (R := R) Nat.succ).mpr (Or.inr hR)

private theorem not_isIntegral_rename_succ
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ RingHom.IsIntegral ((MvPolynomial.rename (R := R) Nat.succ).toRingHom) := by
  intro h
  haveI : Subsingleton R := (isIntegral_rename_succ_iff (R := R)).mp h
  exact zero_ne_one (Subsingleton.elim (0 : R) 1)

private theorem not_isIntegral_rename_pair_successor
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ RingHom.IsIntegral
      ((MvPolynomial.rename (R := R) (fun p : ℕ × Bool => p.1 + 1)).toRingHom) := by
  intro h
  rcases (MvPolynomial.isIntegral_rename_iff (R := R)
    (fun p : ℕ × Bool => p.1 + 1)).mp h with hf | hR
  · obtain ⟨p, hp⟩ := hf 0
    exact Nat.succ_ne_zero p.1 hp
  · haveI : Subsingleton R := hR
    exact zero_ne_one (Subsingleton.elim (0 : R) 1)

end MultivariatePolynomialsTests
