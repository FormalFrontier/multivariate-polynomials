/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Rename
public import MultivariatePolynomials.RenameModuleFinite
public import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic

/-!
# Formal unramifiedness of polynomial variable renaming

For a map `f : σ → τ` and a commutative ring `R`, variable renaming from
`MvPolynomial σ R` to `MvPolynomial τ R` is formally unramified exactly when
it is surjective. The direct criterion `MvPolynomial.formallyUnramified_rename_iff`
expresses this as surjectivity of `f` or subsingleton coefficients. Equivalently,
the full target polynomial ring is a finite module over the full source polynomial
ring via renaming, as in `MvPolynomial.formallyUnramified_rename_iff_moduleFinite`.
Collisions of variables are allowed.
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
* Mathlib, `Mathlib.Data.ZMod.Basic`: the zero coefficient ring `ZMod 1`.
* Mathlib, `Mathlib.RingTheory.Kaehler.Basic`: factorization of derivations
  through Kähler differentials.
* `MultivariatePolynomials.Rename`: the surjectivity criterion for renaming.
* `MultivariatePolynomials.RenameModuleFinite`: the finite-module criterion with
  scalars acting through renaming.
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
    · let : Nontrivial R := hR
      apply (surjective_rename_iff f).2
      left
      intro j
      by_contra hj
      let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
        (rename (R := R) f).toRingHom.toAlgebra
      let : Algebra.FormallyUnramified (MvPolynomial σ R) (MvPolynomial τ R) := h
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

/-- Polynomial variable renaming is formally unramified exactly when the variable
map is surjective or the coefficient ring is subsingleton. In particular, no
injectivity assumption on the variable map is needed. -/
theorem formallyUnramified_rename_iff (f : σ → τ) :
    RingHom.FormallyUnramified (rename (R := R) f).toRingHom ↔
      Function.Surjective f ∨ Subsingleton R :=
  (formallyUnramified_rename_iff_surjective f).trans (surjective_rename_iff f)

/-- For variable renaming, formal unramifiedness is equivalent to module finiteness
of the full target polynomial ring over the full source polynomial ring. The
source acts by multiplication by the renamed polynomial, not just by coefficients.
This equivalence is special to renaming: both properties are characterized by
surjectivity of the variable map or subsingleton coefficients. -/
theorem formallyUnramified_rename_iff_moduleFinite (f : σ → τ) :
    RingHom.FormallyUnramified (rename (R := R) f).toRingHom ↔
      @Module.Finite (MvPolynomial σ R) (MvPolynomial τ R)
        inferInstance inferInstance
        (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R)
          inferInstance inferInstance
          (rename (R := R) f).toRingHom.toAlgebra) :=
  (formallyUnramified_rename_iff f).trans (moduleFinite_rename_iff f).symm

end MvPolynomial

end

/-!
## Boundary models

For `A = MvPolynomial σ R` and `B = MvPolynomial τ R`, the algebra structure
is `(rename f).toRingHom.toAlgebra`, so the action is
`p • q = rename f p * q`. Module finiteness means finite generation over `A`,
not finite cardinality or finite generation over the coefficient ring alone.

Over the integers, the constant map from `Bool` to `Unit` gives a formally
unramified renaming despite identifying two variables. The finite-module comparison
also applies to this surjection, with scalars from the full source polynomial ring.
The map from `Empty` to `Unit` does not give a formally unramified renaming over
the integers, but does over the zero coefficient ring `ZMod 1`. In the zero-ring
case, failure of injectivity of a variable map would not imply failure of
injectivity of its polynomial renaming.
-/

private theorem integer_collision_formallyUnramified :
    (¬ Function.Injective (fun _ : Bool => ())) ∧
      RingHom.FormallyUnramified
        (MvPolynomial.rename (R := ℤ) (fun _ : Bool => ())).toRingHom := by
  constructor
  · intro h
    have hfalse : (false : Bool) = true := h rfl
    cases hfalse
  · apply (MvPolynomial.formallyUnramified_rename_iff_moduleFinite
      (R := ℤ) (fun _ : Bool => ())).2
    apply (MvPolynomial.moduleFinite_rename_iff (R := ℤ) (fun _ : Bool => ())).2
    left
    intro t
    exact ⟨false, Subsingleton.elim _ _⟩

private theorem integer_omitted_variable_not_formallyUnramified :
    ¬ RingHom.FormallyUnramified
      (MvPolynomial.rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom := by
  intro h
  have hs := (MvPolynomial.formallyUnramified_rename_iff (R := ℤ)
    (Empty.elim : Empty → Unit)).1 h
  rcases hs with hs | hR
  · obtain ⟨e, _⟩ := hs ()
    exact Empty.elim e
  · exact zero_ne_one (hR.elim 0 1)

private theorem zero_coefficients_omitted_variable_formallyUnramified :
    RingHom.FormallyUnramified
      (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → Unit)).toRingHom :=
  (MvPolynomial.formallyUnramified_rename_iff
    (R := ZMod 1) (Empty.elim : Empty → Unit)).2
      (Or.inr (ZMod.subsingleton_iff.mpr rfl))
