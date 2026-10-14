/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Rename
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Applications of the injectivity and surjectivity criteria for renaming

The criteria apply to the actual map between the full source and target
polynomial semirings, whether written by application or through the underlying
ring homomorphism. They recover the sufficient contracts for injective and
surjective variable maps. For nontrivial coefficients, each criterion reduces
to the corresponding property of the variable map.

With subsingleton coefficients both properties hold for every actual variable
map. In particular, over `ZMod 1` the map `(n, b) ↦ n + 1` induces an injective
and surjective polynomial map.

## References

* `MultivariatePolynomials.Rename`: the polynomial renaming criteria.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: the sufficient injectivity
  and surjectivity contracts for renaming.
-/

universe u v w

namespace MultivariatePolynomialsTests

open MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]

private theorem injective_rename_apply_iff (f : σ → τ) :
    Function.Injective (fun p : MvPolynomial σ R => rename (R := R) f p) ↔
      Function.Injective f ∨ Subsingleton R :=
  MvPolynomial.injective_rename_iff (R := R) f

private theorem surjective_rename_toRingHom_iff (f : σ → τ) :
    Function.Surjective
        ((rename (R := R) f).toRingHom : MvPolynomial σ R → MvPolynomial τ R) ↔
      Function.Surjective f ∨ Subsingleton R :=
  MvPolynomial.surjective_rename_iff (R := R) f

private theorem injective_rename_recover_stock_contract (f : σ → τ)
    (hf : Function.Injective f) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  (MvPolynomial.injective_rename_iff (R := R) f).mpr (Or.inl hf)

private theorem surjective_rename_recover_stock_contract (f : σ → τ)
    (hf : Function.Surjective f) :
    Function.Surjective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  (MvPolynomial.surjective_rename_iff (R := R) f).mpr (Or.inl hf)

private theorem injective_rename_iff_of_nontrivial [Nontrivial R] (f : σ → τ) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) ↔
      Function.Injective f := by
  have hR : ¬ Subsingleton R := not_subsingleton_iff_nontrivial.mpr inferInstance
  simpa only [hR, or_false] using MvPolynomial.injective_rename_iff (R := R) f

private theorem surjective_rename_iff_of_nontrivial [Nontrivial R] (f : σ → τ) :
    Function.Surjective (rename f : MvPolynomial σ R → MvPolynomial τ R) ↔
      Function.Surjective f := by
  have hR : ¬ Subsingleton R := not_subsingleton_iff_nontrivial.mpr inferInstance
  simpa only [hR, or_false] using MvPolynomial.surjective_rename_iff (R := R) f

private theorem injective_rename_of_subsingleton [Subsingleton R] (f : σ → τ) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  (MvPolynomial.injective_rename_iff (R := R) f).mpr (Or.inr inferInstance)

private theorem surjective_rename_of_subsingleton [Subsingleton R] (f : σ → τ) :
    Function.Surjective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  (MvPolynomial.surjective_rename_iff (R := R) f).mpr (Or.inr inferInstance)

private def criterionPairSuccessor (p : ℕ × Bool) : ℕ := p.1 + 1

private theorem zero_coeff_pair_successor_properties :
    Function.Injective
        (rename (R := ZMod 1) criterionPairSuccessor :
          MvPolynomial (ℕ × Bool) (ZMod 1) → MvPolynomial ℕ (ZMod 1)) ∧
      Function.Surjective
        ((rename (R := ZMod 1) criterionPairSuccessor).toRingHom :
          MvPolynomial (ℕ × Bool) (ZMod 1) → MvPolynomial ℕ (ZMod 1)) := by
  exact ⟨(MvPolynomial.injective_rename_iff (R := ZMod 1) criterionPairSuccessor).mpr
      (Or.inr inferInstance),
    (MvPolynomial.surjective_rename_iff (R := ZMod 1) criterionPairSuccessor).mpr
      (Or.inr inferInstance)⟩

end MultivariatePolynomialsTests
