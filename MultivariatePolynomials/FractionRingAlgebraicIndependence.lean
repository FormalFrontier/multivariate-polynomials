/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Algebraic independence over renamed fraction fields

Variables outside the image of an injective renaming remain algebraically independent
in the target fraction ring over the source fraction ring. The scalar action of the
source fraction ring must agree with the map induced by renaming.

The proof uses Mathlib's algebraic independence of polynomial variables, its description
of independence over an adjoin, and scalar extension along an algebraic algebra.
-/

@[expose] public section

namespace MvPolynomial

universe uR uτ uσ uL uK

private theorem algebraicIndependent_rename_compl
    {R : Type uR} [CommRing R] {τ : Type uτ} {σ : Type uσ}
    [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
    (ρ : τ → σ) (hρ : Function.Injective ρ)
    (hrename : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) =
      (rename (R := R) ρ).toRingHom) :
    AlgebraicIndependent (MvPolynomial τ R)
      (fun i : {i : σ // i ∉ Set.range ρ} => (X i.1 : MvPolynomial σ R)) := by
  have hx := algebraicIndependent_X σ R
  have hy := hx.comp ρ hρ
  have ha : AlgebraicIndependent
      (Algebra.adjoin R (Set.range ((X : σ → MvPolynomial σ R) ∘ ρ)))
      (fun i : {i : σ // i ∉ Set.range ρ} => (X i.1 : MvPolynomial σ R)) := by
    have h := ((AlgebraicIndependent.iff_adjoin_image
      (R := R) (x := (X : σ → MvPolynomial σ R)) (Set.range ρ)).mp hx).2
    change AlgebraicIndependent
      (Algebra.adjoin R ((X : σ → MvPolynomial σ R) '' Set.range ρ))
      (fun i : {i : σ // i ∉ Set.range ρ} => (X i.1 : MvPolynomial σ R)) at h
    rw [Set.range_comp]
    exact h
  let A := Algebra.adjoin R (Set.range ((X : σ → MvPolynomial σ R) ∘ ρ))
  let : Algebra (MvPolynomial τ R) A := hy.aevalEquiv.toRingHom.toAlgebra
  have : IsScalarTower (MvPolynomial τ R) A (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change algebraMap (MvPolynomial τ R) (MvPolynomial σ R) p =
        algebraMap A (MvPolynomial σ R) (hy.aevalEquiv p)
      rw [hrename, hy.algebraMap_aevalEquiv]
      exact DFunLike.congr_fun (rename_eq_aeval ρ) p
  exact ha.restrictScalars (R := MvPolynomial τ R) hy.aevalEquiv.injective

/-- The variables outside the image of an injective renaming are algebraically
independent over the source fraction ring in the target fraction ring. The given
`L`-algebra structure on `K` must induce exactly the fraction-ring map of the renaming,
as expressed by `hmap`. -/
theorem algebraicIndependent_fractionRing_map_rename_compl
    {R : Type uR} [CommRing R] [IsDomain R]
    {τ : Type uτ} {σ : Type uσ}
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
    [IsFractionRing (MvPolynomial τ R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] [Algebra L K]
    (ρ : τ → σ) (hρ : Function.Injective ρ)
    (hmap : algebraMap L K = IsFractionRing.map
      (A := MvPolynomial τ R) (B := MvPolynomial σ R) (K := L) (L := K)
      (j := (rename (R := R) ρ).toRingHom) (rename_injective ρ hρ)) :
    AlgebraicIndependent L (fun i : {i : σ // i ∉ Set.range ρ} =>
      algebraMap (MvPolynomial σ R) K (X i.1)) := by
  let : Algebra (MvPolynomial τ R) (MvPolynomial σ R) :=
    (rename (R := R) ρ).toRingHom.toAlgebra
  have hpoly := algebraicIndependent_rename_compl (R := R) ρ hρ rfl
  let : Algebra (MvPolynomial τ R) K :=
    ((algebraMap (MvPolynomial σ R) K).comp (rename (R := R) ρ).toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx : AlgebraicIndependent (MvPolynomial τ R)
      (fun i : {i : σ // i ∉ Set.range ρ} =>
        algebraMap (MvPolynomial σ R) K (X i.1)) :=
    hpoly.map' (f := IsScalarTower.toAlgHom (MvPolynomial τ R) (MvPolynomial σ R) K)
      (IsFractionRing.injective (MvPolynomial σ R) K)
  have : IsScalarTower (MvPolynomial τ R) L K :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change algebraMap (MvPolynomial σ R) K (rename ρ p) =
        algebraMap L K (algebraMap (MvPolynomial τ R) L p)
      rw [hmap]
      simp only [IsFractionRing.map, IsLocalization.map_eq,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  let : IsDomain L := IsFractionRing.isDomain (MvPolynomial τ R)
  let : Algebra.IsAlgebraic (MvPolynomial τ R) L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors (MvPolynomial τ R))
  exact hx.extendScalars L

end MvPolynomial
