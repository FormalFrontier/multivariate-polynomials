/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.RingHom.QuasiFinite

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.QuasiFinite.Polynomial
import MultivariatePolynomials.RenameModuleFinite

@[expose] public section

/-!
# Quasi-finiteness of variable renaming

The quasi-finiteness criterion concerns the original homomorphism between the
full polynomial rings. Its induced action is `p • q = MvPolynomial.rename f p * q`,
with scalars in the source polynomial ring, not merely in the coefficient ring.
The coefficient and two variable types have independent universes.

Here quasi-finiteness is Mathlib's finiteness of every residue-field fiber as a
module over that residue field. Mathlib's predicate does not include a
`FiniteType` hypothesis; no finite-type convention is added here.

`MvPolynomial.rename_quasiFinite_iff_finite` identifies quasi-finiteness of a
renaming with finiteness of that same ring homomorphism, hence with finite
generation over the full source polynomial ring. This equivalence is specific
to renaming; quasi-finite ring homomorphisms need not be finite in general.

Module finiteness gives the positive direction. Over nontrivial coefficients,
an omitted target variable gives a split surjective evaluation onto `R[X]`
that kills every renamed variable. Composition and restriction of scalars
would then make the coefficient map `R →+* R[X]` quasi-finite, contradicting
Mathlib's polynomial obstruction at a maximal ideal.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename` and
  `Mathlib.Algebra.Polynomial.AlgebraMap`: variable renaming and evaluation.
* Andrew Yang's Mathlib quasi-finite algebra, polynomial and ring-homomorphism
  APIs in `Mathlib.RingTheory.QuasiFinite.Basic`,
  `Mathlib.RingTheory.QuasiFinite.Polynomial` and
  `Mathlib.RingTheory.RingHom.QuasiFinite`.
* Johan Commelin's Mathlib finiteness API in
  `Mathlib.RingTheory.Finiteness.Basic`.
* Mathlib's multivariate-polynomial API by Johannes Hölzl, Johan Commelin
  and Mario Carneiro, and its induced-algebra action API by Kenny Lau and
  Yury Kudryashov.
* Formal Frontier Agents, the compositional polynomial obstruction.
  The evaluation section and factorization follow the proof patterns in this
  library's `RenameModuleFinite` and `RenameIntegral` modules.
-/

universe u v w

/-- The original renaming homomorphism between full polynomial rings over a
commutative ring is quasi-finite exactly when the variable map is surjective or
the coefficient ring is subsingleton. Quasi-finiteness uses the full
source-polynomial action induced by this homomorphism and Mathlib's
residue-field-fiber convention, which does not require `FiniteType`. -/
theorem MvPolynomial.rename_quasiFinite_iff
    {σ : Type u} {τ : Type v} {R : Type w} [CommRing R] (f : σ → τ) :
    RingHom.QuasiFinite (MvPolynomial.rename (R := R) f).toRingHom ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  constructor
  · intro hφ
    by_cases hR : Subsingleton R
    · exact Or.inr hR
    · left
      let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      by_contra hf
      simp only [Function.Surjective, not_forall, not_exists] at hf
      obtain ⟨j, hj⟩ := hf
      let φ : MvPolynomial σ R →+* MvPolynomial τ R :=
        (MvPolynomial.rename (R := R) f).toRingHom
      let ψa : MvPolynomial τ R →ₐ[R] Polynomial R :=
        MvPolynomial.aeval (fun k => if k = j then Polynomial.X else 0)
      let ψ := ψa.toRingHom
      let ε : MvPolynomial σ R →+* R := MvPolynomial.constantCoeff
      have hψ : Function.Surjective ψ := by
        intro p
        refine ⟨Polynomial.aeval (MvPolynomial.X j : MvPolynomial τ R) p, ?_⟩
        have hsec : ψa.comp (Polynomial.aeval (MvPolynomial.X j)) =
            AlgHom.id R (Polynomial R) := by
          apply Polynomial.algHom_ext
          simp [ψa]
        exact DFunLike.congr_fun hsec p
      -- All source variables vanish, so the composite factors through augmentation.
      have hcomp : ψ.comp φ = Polynomial.C.comp ε := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [ψ, ψa, φ, ε]
        · intro i
          simp [ψ, ψa, φ, ε, hj i]
      have hψq : ψ.QuasiFinite :=
        RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective ψ hψ)
      have hψφ : (ψ.comp φ).QuasiFinite := hψq.comp hφ
      rw [hcomp] at hψφ
      -- Restriction of scalars retains the outer map, with no assumption on ε.
      have hC : (Polynomial.C : R →+* Polynomial R).QuasiFinite :=
        RingHom.QuasiFinite.of_comp hψφ
      have hA : Algebra.QuasiFinite R (Polynomial R) :=
        RingHom.quasiFinite_algebraMap.mp
          (by simpa only [Polynomial.algebraMap_eq] using hC)
      let : Algebra.QuasiFinite R (Polynomial R) := hA
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (Polynomial R)
      let : P.IsMaximal := hP
      exact Polynomial.not_quasiFiniteAt P
        (inferInstance : Algebra.QuasiFiniteAt R P)
  · intro h
    exact RingHom.QuasiFinite.of_finite
      ((MvPolynomial.moduleFinite_rename_iff (R := R) f).mpr h)

/-- Quasi-finiteness of a variable renaming is equivalent to finiteness of the
same ring homomorphism. Thus its residue-field fibers are finite exactly when
the full target polynomial ring is a finite module over the full source
polynomial ring under `p • q = MvPolynomial.rename f p * q`. No `FiniteType`
hypothesis or finiteness assumption on the variable types is needed. -/
theorem MvPolynomial.rename_quasiFinite_iff_finite
    {σ : Type u} {τ : Type v} {R : Type w} [CommRing R] (f : σ → τ) :
    RingHom.QuasiFinite (MvPolynomial.rename (R := R) f).toRingHom ↔
      RingHom.Finite (MvPolynomial.rename (R := R) f).toRingHom := by
  exact (MvPolynomial.rename_quasiFinite_iff (R := R) f).trans
    (MvPolynomial.moduleFinite_rename_iff (R := R) f).symm

/-! ## Applications

The following three boundaries concern the original full polynomial-ring map.
An omitted variable over the integers obstructs both quasi-finiteness and
finiteness. A collision, on the other hand, can give a finite, quasi-finite map
with a nonzero source polynomial annihilating every target polynomial. Finally,
the same omitted-variable map is quasi-finite and finite over `ZMod 1`: it still
misses `()`, but the coefficient-ring exception in the criterion applies.
-/

namespace MvPolynomial

/-- With integer coefficients, the map from no variables to one variable misses
`()`, and its renaming is neither quasi-finite nor finite. -/
private theorem empty_unit_int_boundary :
    ¬ Function.Surjective (Empty.elim : Empty → Unit) ∧
      ¬ RingHom.QuasiFinite
        (rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom ∧
      ¬ RingHom.Finite
        (rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom := by
  have hmiss : ¬ Function.Surjective (Empty.elim : Empty → Unit) := by
    intro h
    obtain ⟨i, _⟩ := h ()
    exact Empty.elim i
  have hnotqf : ¬ RingHom.QuasiFinite
      (rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom := by
    intro hqf
    rcases (rename_quasiFinite_iff (R := ℤ) (Empty.elim : Empty → Unit)).mp hqf with
      hsurj | hzero
    · exact hmiss hsurj
    · exact zero_ne_one (@Subsingleton.elim ℤ hzero 0 1)
  refine ⟨hmiss, hnotqf, ?_⟩
  intro hfinite
  exact hnotqf
    ((rename_quasiFinite_iff_finite (R := ℤ) (Empty.elim : Empty → Unit)).mpr hfinite)

/-- Collapsing two integer variables to one is noninjective but surjective,
finite and quasi-finite. The nonzero polynomial `X false - X true` kills every
target polynomial under the induced full source-polynomial action. -/
private theorem bool_unit_int_boundary :
    ¬ Function.Injective (fun _ : Bool => ()) ∧
      Function.Surjective (fun _ : Bool => ()) ∧
      RingHom.Finite (rename (R := ℤ) (fun _ : Bool => ())).toRingHom ∧
      RingHom.QuasiFinite (rename (R := ℤ) (fun _ : Bool => ())).toRingHom ∧
      ∃ a : MvPolynomial Bool ℤ, a ≠ 0 ∧
        ∀ b : MvPolynomial Unit ℤ,
          @SMul.smul (MvPolynomial Bool ℤ) (MvPolynomial Unit ℤ)
            (rename (R := ℤ) (fun _ : Bool => ())).toRingHom.toAlgebra.toSMul a b = 0 := by
  let f : Bool → Unit := fun _ => ()
  let φ : MvPolynomial Bool ℤ →+* MvPolynomial Unit ℤ :=
    (rename (R := ℤ) f).toRingHom
  have hf : Function.Surjective f := by
    rintro ⟨⟩
    exact ⟨false, rfl⟩
  have hqf : φ.QuasiFinite :=
    (rename_quasiFinite_iff (R := ℤ) f).mpr (Or.inl hf)
  have hfinite : φ.Finite := (rename_quasiFinite_iff_finite (R := ℤ) f).mp hqf
  refine ⟨?_, hf, hfinite, hqf, X false - X true, ?_, ?_⟩
  · intro h
    have hft : false = true := h (show f false = f true from rfl)
    cases hft
  · intro hz
    have hX : (X false : MvPolynomial Bool ℤ) = X true := sub_eq_zero.mp hz
    have hft : false = true := MvPolynomial.X_injective hX
    cases hft
  · intro b
    change φ (X false - X true) * b = 0
    simp [φ, f]

/-- Over `ZMod 1`, the same map still misses `()`, but its renaming is
quasi-finite and finite because the coefficients are subsingleton. -/
private theorem empty_unit_zmod_one_boundary :
    ¬ Function.Surjective (Empty.elim : Empty → Unit) ∧
      RingHom.QuasiFinite
        (rename (R := ZMod 1) (Empty.elim : Empty → Unit)).toRingHom ∧
      RingHom.Finite
        (rename (R := ZMod 1) (Empty.elim : Empty → Unit)).toRingHom := by
  have hqf : RingHom.QuasiFinite
      (rename (R := ZMod 1) (Empty.elim : Empty → Unit)).toRingHom :=
    (rename_quasiFinite_iff (R := ZMod 1) (Empty.elim : Empty → Unit)).mpr
      (Or.inr inferInstance)
  refine ⟨?_, hqf,
    (rename_quasiFinite_iff_finite (R := ZMod 1) (Empty.elim : Empty → Unit)).mp hqf⟩
  intro h
  obtain ⟨i, _⟩ := h ()
  exact Empty.elim i

end MvPolynomial
