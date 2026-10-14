/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.FractionRingAlgebraicIndependence
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Relative independence and fraction-ring scalar structures

These examples describe the scalar structure associated to an injective renaming.
The family indexed by the complement of its range is considered over a fraction
ring of the source polynomial ring, not merely over the original coefficient ring.
The algebra map between the fraction rings must be the map of that same renaming.

The examples apply relative independence to a nonempty complement over the fraction
ring of `ℤ`, identity renamings, and independently lifted index types. The source
fraction structure over `ℤ` is transported along Mathlib's empty-variable algebra
equivalence. The identity controls also compare the canonical fraction map with the
identity by Mathlib's localization extensionality theorem.

Two renamings from `Unit` to `Bool` give different scalar structures on the same
fraction rings. For the renaming at `false`, the variable at `true` is independent.
For the scalar structure coming from the renaming at `true`, that variable belongs
to the coefficient image. The nonzero polynomial `X - C(T)` then evaluates to zero.
Mathlib's `AlgebraicIndependent.transcendental` and `transcendental_iff_injective`
turn this relation into failure of independence for the complementary family.
-/

@[expose] public section

universe uR uτ uσ uL uK

namespace MvPolynomial

section CompatibleScalars

variable {R : Type uR} [CommRing R] [IsDomain R]
variable {τ : Type uτ} {σ : Type uσ}
variable {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
variable [IsFractionRing (MvPolynomial τ R) L]
variable {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
variable [IsFractionRing (MvPolynomial σ R) K] [Algebra L K]
variable (ρ : τ → σ) (hρ : Function.Injective ρ)
variable (hmap : algebraMap L K = IsFractionRing.map
  (A := MvPolynomial τ R) (B := MvPolynomial σ R) (K := L) (L := K)
  (j := (rename (R := R) ρ).toRingHom) (rename_injective ρ hρ))

example (p : MvPolynomial τ R) :
    algebraMap L K (algebraMap (MvPolynomial τ R) L p) =
      algebraMap (MvPolynomial σ R) K (rename ρ p) := by
  rw [hmap]
  simp only [IsFractionRing.map, IsLocalization.map_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

example : Function.Injective (algebraMap L K) := by
  letI : Field L := IsFractionRing.toField (MvPolynomial τ R)
  letI : IsDomain K := IsFractionRing.isDomain (MvPolynomial σ R)
  exact (algebraMap L K).injective

example (hsurj : Function.Surjective ρ) : IsEmpty {i : σ // i ∉ Set.range ρ} :=
  ⟨fun i => i.2 (hsurj i.1)⟩

-- This empty-family control uses only Mathlib's empty-index criterion.
example (hsurj : Function.Surjective ρ) :
    AlgebraicIndependent L (fun i : {i : σ // i ∉ Set.range ρ} =>
      algebraMap (MvPolynomial σ R) K (X i.1)) := by
  letI : IsEmpty {i : σ // i ∉ Set.range ρ} := ⟨fun i => i.2 (hsurj i.1)⟩
  apply algebraicIndependent_empty_type_iff.mpr
  letI : Field L := IsFractionRing.toField (MvPolynomial τ R)
  letI : IsDomain K := IsFractionRing.isDomain (MvPolynomial σ R)
  exact (algebraMap L K).injective

end CompatibleScalars

section IntegerConstants

local notation "P₀" => MvPolynomial Empty ℤ
local notation "P₁" => MvPolynomial Unit ℤ
local notation "L₀" => FractionRing ℤ
local notation "K₁" => FractionRing P₁

-- Transport the polynomial-source algebra along the empty-variable equivalence.
private noncomputable abbrev integerSourceAlgebra : Algebra P₀ L₀ :=
  ((algebraMap ℤ L₀).comp (isEmptyAlgEquiv (R := ℤ) Empty).toRingHom).toAlgebra

attribute [local instance] integerSourceAlgebra

private theorem integerSourceFraction : IsFractionRing P₀ L₀ :=
  IsFractionRing.of_ringEquiv_left (isEmptyAlgEquiv (R := ℤ) Empty).toRingEquiv
    (fun _ => rfl)

attribute [local instance] integerSourceFraction

private noncomputable abbrev integerTargetAlgebra : Algebra L₀ K₁ :=
  (IsFractionRing.map (A := P₀) (B := P₁) (K := L₀) (L := K₁)
    (j := (rename (R := ℤ) Empty.elim).toRingHom)
    (rename_injective Empty.elim (by intro a; exact a.elim))).toAlgebra

attribute [local instance] integerTargetAlgebra

example : algebraMap L₀ K₁ = IsFractionRing.map
    (A := P₀) (B := P₁) (K := L₀) (L := K₁)
    (j := (rename (R := ℤ) Empty.elim).toRingHom)
    (rename_injective Empty.elim (by intro a; exact a.elim)) := rfl

example : Nonempty (FractionRing P₀ ≃+* FractionRing ℤ) :=
  ⟨IsFractionRing.ringEquivOfRingEquiv (isEmptyAlgEquiv (R := ℤ) Empty).toRingEquiv⟩

example : Nonempty {i : Unit // i ∉ Set.range (Empty.elim : Empty → Unit)} := by
  refine ⟨⟨(), ?_⟩⟩
  rintro ⟨a, _⟩
  exact a.elim

example (p : P₀) : algebraMap L₀ K₁ (algebraMap P₀ L₀ p) =
    algebraMap P₁ K₁ (rename Empty.elim p) := by
  change IsFractionRing.map _ (algebraMap P₀ L₀ p) = _
  simp only [IsFractionRing.map, IsLocalization.map_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

example : AlgebraicIndependent L₀
    (fun i : {i : Unit // i ∉ Set.range (Empty.elim : Empty → Unit)} =>
      algebraMap P₁ K₁ (X i.1)) := by
  exact algebraicIndependent_fractionRing_map_rename_compl
    (R := ℤ) (L := L₀) (K := K₁) Empty.elim (by intro a; exact a.elim) rfl

end IntegerConstants

section EmptyComplements

variable (ι : Type uτ)

private theorem identityFractionMap :
    algebraMap (FractionRing (MvPolynomial ι ℤ)) (FractionRing (MvPolynomial ι ℤ)) =
    IsFractionRing.map (A := MvPolynomial ι ℤ) (B := MvPolynomial ι ℤ)
      (K := FractionRing (MvPolynomial ι ℤ)) (L := FractionRing (MvPolynomial ι ℤ))
      (j := (rename (R := ℤ) (id : ι → ι)).toRingHom)
      (rename_injective id Function.injective_id) := by
  apply IsLocalization.ringHom_ext (M := nonZeroDivisors (MvPolynomial ι ℤ))
  apply RingHom.ext
  intro p
  simp [RingHom.comp_apply, IsFractionRing.map,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

example : IsEmpty {i : ι // i ∉ Set.range (id : ι → ι)} :=
  ⟨fun i => i.2 ⟨i.1, rfl⟩⟩

-- Both boundaries use the localized variable family and the canonical map.
example : AlgebraicIndependent (FractionRing (MvPolynomial Unit ℤ))
    (fun i : {i : Unit // i ∉ Set.range (id : Unit → Unit)} =>
      algebraMap (MvPolynomial Unit ℤ) (FractionRing (MvPolynomial Unit ℤ)) (X i.1)) := by
  exact algebraicIndependent_fractionRing_map_rename_compl
    (R := ℤ) id Function.injective_id (identityFractionMap Unit)

example : AlgebraicIndependent (FractionRing (MvPolynomial Empty ℤ))
    (fun i : {i : Empty // i ∉ Set.range (id : Empty → Empty)} =>
      algebraMap (MvPolynomial Empty ℤ) (FractionRing (MvPolynomial Empty ℤ)) (X i.1)) := by
  exact algebraicIndependent_fractionRing_map_rename_compl
    (R := ℤ) id Function.injective_id (identityFractionMap Empty)

example : IsEmpty {i : Empty // i ∉ Set.range (id : Empty → Empty)} := inferInstance

end EmptyComplements

section LiftedIndices

private def liftedEmptyRenaming : ULift.{uτ} Empty → ULift.{uσ} Unit :=
  fun i => i.down.elim

private theorem liftedEmptyRenaming_injective :
    Function.Injective (liftedEmptyRenaming : ULift.{uτ} Empty → ULift.{uσ} Unit) := by
  intro a
  exact a.down.elim

private noncomputable abbrev liftedEmptyAction :
    Algebra (FractionRing (MvPolynomial (ULift.{uτ} Empty) ℤ))
      (FractionRing (MvPolynomial (ULift.{uσ} Unit) ℤ)) :=
  (IsFractionRing.map
    (A := MvPolynomial (ULift.{uτ} Empty) ℤ) (B := MvPolynomial (ULift.{uσ} Unit) ℤ)
    (K := FractionRing (MvPolynomial (ULift.{uτ} Empty) ℤ))
    (L := FractionRing (MvPolynomial (ULift.{uσ} Unit) ℤ))
    (j := (rename (R := ℤ) liftedEmptyRenaming).toRingHom)
    (rename_injective liftedEmptyRenaming liftedEmptyRenaming_injective)).toAlgebra

attribute [local instance] liftedEmptyAction

example : Nonempty
    {i : ULift.{uσ} Unit // i ∉ Set.range
      (liftedEmptyRenaming : ULift.{uτ} Empty → ULift.{uσ} Unit)} := by
  refine ⟨⟨⟨()⟩, ?_⟩⟩
  rintro ⟨a, _⟩
  exact a.down.elim

example : AlgebraicIndependent (FractionRing (MvPolynomial (ULift.{uτ} Empty) ℤ))
    (fun i : {i : ULift.{uσ} Unit // i ∉ Set.range
        (liftedEmptyRenaming : ULift.{uτ} Empty → ULift.{uσ} Unit)} =>
      algebraMap (MvPolynomial (ULift.{uσ} Unit) ℤ)
        (FractionRing (MvPolynomial (ULift.{uσ} Unit) ℤ)) (X i.1)) := by
  exact algebraicIndependent_fractionRing_map_rename_compl
    (R := ℤ) (L := FractionRing (MvPolynomial (ULift.{uτ} Empty) ℤ))
    (K := FractionRing (MvPolynomial (ULift.{uσ} Unit) ℤ))
    liftedEmptyRenaming liftedEmptyRenaming_injective rfl

end LiftedIndices

section ScalarChoice

local notation "P" => MvPolynomial Unit ℤ
local notation "Q" => MvPolynomial Bool ℤ
local notation "Ls" => FractionRing P
local notation "Ks" => FractionRing Q

private noncomputable abbrev falseAction : Algebra Ls Ks :=
  (IsFractionRing.map (A := P) (B := Q) (K := Ls) (L := Ks)
    (j := (rename (R := ℤ) (fun (_ : Unit) => false)).toRingHom)
    (rename_injective _ (by intro a b _; exact Subsingleton.elim a b))).toAlgebra

private noncomputable abbrev trueAction : Algebra Ls Ks :=
  (IsFractionRing.map (A := P) (B := Q) (K := Ls) (L := Ks)
    (j := (rename (R := ℤ) (fun (_ : Unit) => true)).toRingHom)
    (rename_injective _ (by intro a b _; exact Subsingleton.elim a b))).toAlgebra

example : true ∉ Set.range (fun (_ : Unit) => false) := by simp

section IntendedAction

attribute [local instance] falseAction

example (p : P) : algebraMap Ls Ks (algebraMap P Ls p) =
    algebraMap Q Ks (rename (fun (_ : Unit) => false) p) := by
  change IsFractionRing.map _ (algebraMap P Ls p) = _
  simp only [IsFractionRing.map, IsLocalization.map_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

example : AlgebraicIndependent Ls
    (fun i : {i : Bool // i ∉ Set.range (fun (_ : Unit) => false)} =>
      algebraMap Q Ks (X i.1)) := by
  exact algebraicIndependent_fractionRing_map_rename_compl
    (R := ℤ) (L := Ls) (K := Ks) (fun (_ : Unit) => false)
    (by intro a b _; exact Subsingleton.elim a b) rfl

end IntendedAction

section OtherAction

attribute [local instance] trueAction

example (p : P) : algebraMap Ls Ks (algebraMap P Ls p) =
    algebraMap Q Ks (rename (fun (_ : Unit) => true) p) := by
  change IsFractionRing.map _ (algebraMap P Ls p) = _
  simp only [IsFractionRing.map, IsLocalization.map_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

private theorem otherAction_X :
    algebraMap Ls Ks (algebraMap P Ls (X ())) = algebraMap Q Ks (X true) := by
  change IsFractionRing.map _ (algebraMap P Ls (X ())) = _
  simp only [IsFractionRing.map, IsLocalization.map_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X]

example : algebraMap Q Ks (X true) ∈ Set.range (algebraMap Ls Ks) :=
  ⟨algebraMap P Ls (X ()), otherAction_X⟩

private theorem otherAction_relation_ne_zero :
    (Polynomial.X - Polynomial.C (algebraMap P Ls (X ())) : Polynomial Ls) ≠ 0 :=
  Polynomial.X_sub_C_ne_zero _

private theorem otherAction_relation_aeval :
    Polynomial.aeval (algebraMap Q Ks (X true))
    (Polynomial.X - Polynomial.C (algebraMap P Ls (X ())) : Polynomial Ls) = 0 := by
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, otherAction_X, sub_self]

private theorem not_algebraicIndependent_falseComplement_trueAction :
    ¬ AlgebraicIndependent Ls
      (fun i : {i : Bool // i ∉ Set.range (fun (_ : Unit) => false)} =>
        algebraMap Q Ks (X i.1)) := by
  intro h
  have ht : Transcendental Ls (algebraMap Q Ks (X true)) :=
    h.transcendental ⟨true, by simp⟩
  have hinj := transcendental_iff_injective.mp ht
  apply otherAction_relation_ne_zero
  apply hinj
  simpa only [map_zero] using otherAction_relation_aeval

end OtherAction
end ScalarChoice

end MvPolynomial
