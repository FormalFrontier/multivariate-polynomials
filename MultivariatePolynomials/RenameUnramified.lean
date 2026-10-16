/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Rename
public import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Formal unramifiedness of polynomial variable renaming

For a map `f : σ → τ` and a commutative ring `R`, variable renaming from
`MvPolynomial σ R` to `MvPolynomial τ R` is formally unramified exactly when
it is surjective. By `MvPolynomial.surjective_rename_iff`, this means that
`f` is surjective or `R` is subsingleton. Collisions of variables are allowed.
The coefficient and variable types may lie in independent universes; neither
variable type is required to be finite or inhabited.

If a target variable is omitted, partial differentiation in that variable kills
the image of renaming. It is therefore a derivation relative to the source
polynomial ring. Formal unramifiedness forces it to vanish, contradicting its
value on the omitted variable over a nontrivial coefficient ring.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: variable renaming.
* Mathlib, `Mathlib.RingTheory.RingHom.Unramified`: formal unramifiedness of
  ring homomorphisms and its consequence for surjective homomorphisms.
* Mathlib, `Mathlib.Algebra.MvPolynomial.PDeriv`: partial differentiation and
  its vanishing outside the variables of a polynomial.
* Mathlib, `Mathlib.RingTheory.Kaehler.Basic`: factorization of derivations
  through Kähler differentials.
* `MultivariatePolynomials.Rename`: the surjectivity criterion for renaming.
-/

@[expose] public section

universe uR uσ uτ

namespace MvPolynomial

variable {R : Type uR} {σ : Type uσ} {τ : Type uτ} [CommRing R]

/-- Polynomial variable renaming is formally unramified exactly when its
underlying function on polynomial rings is surjective. The forward implication
uses Mathlib's `pderiv_eq_zero_of_notMem_vars` and the universal property
`Derivation.liftKaehlerDifferential_comp_D` of Kähler differentials; the reverse
implication is `RingHom.FormallyUnramified.of_surjective`. -/
theorem formallyUnramified_rename_iff_surjective (f : σ → τ) :
    RingHom.FormallyUnramified (MvPolynomial.rename (R := R) f).toRingHom ↔
      Function.Surjective (MvPolynomial.rename (R := R) f) := by
  classical
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact (surjective_rename_iff f).2 (Or.inr hR)
    · letI : Nontrivial R := hR
      apply (surjective_rename_iff f).2
      left
      intro j
      by_contra hj
      letI : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
        (rename (R := R) f).toRingHom.toAlgebra
      letI : Algebra.FormallyUnramified (MvPolynomial σ R) (MvPolynomial τ R) := h
      have hkill (p : MvPolynomial σ R) : pderiv j (rename f p) = 0 := by
        apply pderiv_eq_zero_of_notMem_vars
        intro hjp
        obtain ⟨i, _, hi⟩ := mem_vars_rename f p hjp
        exact hj ⟨i, hi⟩
      -- The scalar action here is multiplication by the renamed polynomial.
      let d : Derivation (MvPolynomial σ R) (MvPolynomial τ R) (MvPolynomial τ R) :=
        { toLinearMap :=
            { toFun := pderiv j
              map_add' := fun p q => map_add (pderiv j) p q
              map_smul' := by
                intro a p
                change pderiv j (rename f a * p) = rename f a * pderiv j p
                rw [pderiv_mul, hkill, zero_mul, zero_add] }
          map_one_eq_zero' := pderiv_one
          leibniz' := fun p q => (pderiv j).leibniz p q }
      have hzero :
          KaehlerDifferential.D (MvPolynomial σ R) (MvPolynomial τ R) (X j) = 0 :=
        Subsingleton.elim _ _
      have hd : d (X j) = 0 := by
        rw [← d.liftKaehlerDifferential_comp_D (X j), hzero, map_zero]
      change pderiv j (X j : MvPolynomial τ R) = 0 at hd
      exact one_ne_zero (by simpa only [pderiv_X_self] using hd)
  · intro h
    exact RingHom.FormallyUnramified.of_surjective h

end MvPolynomial
