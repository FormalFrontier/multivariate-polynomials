/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.QuasiFinite.Polynomial
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Quasi-finite renaming and integer boundary models

Over the integers, the map from no variables to one variable is not quasi-finite.
Collapsing two variables to one is surjective, finite and quasi-finite, although a
nonzero source polynomial annihilates every target polynomial under the full
renaming-induced action. With zero coefficients, even the map from no variables
to one variable is quasi-finite.

These proofs do not import the renaming criterion. The negative example uses
Mathlib's obstruction to quasi-finiteness of a univariate polynomial algebra at
any prime, together with a surjective evaluation and composition of ring maps.
Quasi-finiteness means Mathlib's residue-field-fiber finiteness, without an
additional `FiniteType` hypothesis.

## References

* Andrew Yang's Mathlib quasi-finite algebra, polynomial and ring-homomorphism
  APIs; Johan Commelin's Mathlib finiteness API.
* Mathlib's multivariate-polynomial and evaluation APIs by Johannes Hölzl,
  Johan Commelin and Mario Carneiro, and its polynomial evaluation APIs by
  Chris Hughes, Johannes Hölzl, Kim Morrison and Jens Wagemaker.
* Mathlib's induced-algebra action API by Kenny Lau and Yury Kudryashov, and its
  maximal-ideal and prime-localization APIs by Kenny Lau, Chris Hughes,
  Mario Carneiro, Johan Commelin, Amelia Livingston and Anne Baanen.
* Formal Frontier Agents, the compositional polynomial obstruction.
  The section and empty-source factorization follow the private proof patterns
  in this library's `RenameModuleFinite` and `RenameIntegralNegative` modules;
  the zero-coefficient argument follows `RenameModuleFinitePositive`.
-/

namespace MultivariatePolynomialsTests.RenameQuasiFiniteModels

open MvPolynomial

/-- An omitted variable over the integers gives a non-quasi-finite map. -/
private theorem int_empty_unit_data :
    ¬ Function.Surjective (Empty.elim : Empty → Unit) ∧
      ¬ RingHom.QuasiFinite
        (rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom := by
  constructor
  · intro h
    obtain ⟨i, _⟩ := h ()
    exact Empty.elim i
  · intro hφ
    let φ : MvPolynomial Empty ℤ →+* MvPolynomial Unit ℤ :=
      (rename (R := ℤ) (Empty.elim : Empty → Unit)).toRingHom
    let ψa : MvPolynomial Unit ℤ →ₐ[ℤ] Polynomial ℤ :=
      MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial ℤ))
    let ψ := ψa.toRingHom
    let ε : MvPolynomial Empty ℤ →+* ℤ := constantCoeff
    have hψ : Function.Surjective ψ := by
      intro p
      refine ⟨Polynomial.aeval (X () : MvPolynomial Unit ℤ) p, ?_⟩
      have hsec : ψa.comp (Polynomial.aeval (X () : MvPolynomial Unit ℤ)) =
          AlgHom.id ℤ (Polynomial ℤ) := by
        apply Polynomial.algHom_ext
        simp [ψa]
      exact DFunLike.congr_fun hsec p
    have hcomp : ψ.comp φ = Polynomial.C.comp ε := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [ψ, ψa, φ, ε]
      · intro i
        exact Empty.elim i
    have hψq : ψ.QuasiFinite :=
      RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective ψ hψ)
    have hψφ : (ψ.comp φ).QuasiFinite := hψq.comp hφ
    rw [hcomp] at hψφ
    -- Restriction of scalars retains the outer coefficient map, with no
    -- quasi-finiteness assumption on the augmentation `ε`.
    have hC : (Polynomial.C : ℤ →+* Polynomial ℤ).QuasiFinite :=
      RingHom.QuasiFinite.of_comp hψφ
    have hA : Algebra.QuasiFinite ℤ (Polynomial ℤ) :=
      RingHom.quasiFinite_algebraMap.mp
        (by simpa only [Polynomial.algebraMap_eq] using hC)
    let : Algebra.QuasiFinite ℤ (Polynomial ℤ) := hA
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (Polynomial ℤ)
    let : P.IsMaximal := hP
    exact Polynomial.not_quasiFiniteAt P
      (inferInstance : Algebra.QuasiFiniteAt ℤ P)

/-- A finite, quasi-finite integer renaming can have a nonzero scalar that kills
its entire target under the original full source-polynomial action. -/
private theorem int_collision_data :
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
  have hφ : Function.Surjective φ := MvPolynomial.rename_surjective f hf
  have hfinite : φ.Finite := RingHom.Finite.of_surjective φ hφ
  refine ⟨?_, hf, hfinite, RingHom.QuasiFinite.of_finite hfinite,
    X false - X true, ?_, ?_⟩
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

/-- Subsingleton coefficients make the same omitted-variable map quasi-finite. -/
private theorem zero_coefficients_empty_unit_quasiFinite :
    RingHom.QuasiFinite
      (rename (R := ZMod 1) (Empty.elim : Empty → Unit)).toRingHom := by
  let : Subsingleton (MvPolynomial Unit (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial Unit (ZMod 1))
  apply RingHom.QuasiFinite.of_finite
  apply RingHom.Finite.of_surjective
  intro p
  exact ⟨0, Subsingleton.elim _ _⟩

end MultivariatePolynomialsTests.RenameQuasiFiniteModels
