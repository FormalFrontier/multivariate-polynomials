/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.FractionRingTranscendenceBasis

/-!
# Using complementary fraction-ring transcendence bases

The canonical inclusion of the fraction ring of `ℤ[Unit]` in that of `ℤ[Bool]`
sends the source variable to `X false`. Its nonempty complementary family is a
transcendence basis, and the target is algebraic over its source-fraction adjoin.
The final two clients allow arbitrary fraction-ring realizations in five
independent universes with the full canonical fraction-map equality.
-/

@[expose] public section

universe uR uτ uσ uL uK

namespace MvPolynomial

section TwoVariables

local notation "P" => MvPolynomial Unit ℤ
local notation "Q" => MvPolynomial Bool ℤ

private theorem falseRenaming_injective :
    Function.Injective (fun (_ : Unit) => false) := by
  intro a b _
  exact Subsingleton.elim a b

private noncomputable abbrev falseAction : Algebra (FractionRing P) (FractionRing Q) :=
  (IsFractionRing.map (A := P) (B := Q)
    (K := FractionRing (MvPolynomial Unit ℤ)) (L := FractionRing (MvPolynomial Bool ℤ))
    (j := (rename (R := ℤ) (fun (_ : Unit) => false)).toRingHom)
    (rename_injective _ falseRenaming_injective)).toAlgebra

private theorem falseComplement_nonempty :
    Nonempty {i : Bool // i ∉ Set.range (fun (_ : Unit) => false)} :=
  ⟨⟨true, by simp⟩⟩

section CanonicalAction

attribute [local instance] falseAction

private theorem falseAction_fullMap :
    algebraMap (FractionRing P) (FractionRing Q) = IsFractionRing.map
    (A := P) (B := Q)
    (K := FractionRing (MvPolynomial Unit ℤ)) (L := FractionRing (MvPolynomial Bool ℤ))
    (j := (rename (R := ℤ) (fun (_ : Unit) => false)).toRingHom)
    (rename_injective _ falseRenaming_injective) := rfl

private theorem falseAction_polynomial (p : P) :
    algebraMap (FractionRing P) (FractionRing Q) (algebraMap P (FractionRing P) p) =
      algebraMap Q (FractionRing Q) (rename (fun (_ : Unit) => false) p) := by
  change IsFractionRing.map
    (A := P) (B := Q)
    (K := FractionRing (MvPolynomial Unit ℤ))
    (L := FractionRing (MvPolynomial Bool ℤ))
    (j := (rename (R := ℤ) (fun (_ : Unit) => false)).toRingHom)
    (rename_injective _ falseRenaming_injective) (algebraMap P (FractionRing P) p) = _
  simp only [IsFractionRing.map, IsLocalization.map_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

private theorem twoVariable_adjoin_isAlgebraic :
    Algebra.IsAlgebraic
      (Algebra.adjoin (FractionRing P) (Set.range
        (fun i : {i : Bool // i ∉ Set.range (fun (_ : Unit) => false)} =>
          algebraMap Q (FractionRing Q) (X i.1)))) (FractionRing Q) := by
  exact isAlgebraic_adjoin_fractionRing_map_rename_compl
    (R := ℤ) (L := FractionRing (MvPolynomial Unit ℤ))
    (K := FractionRing (MvPolynomial Bool ℤ)) (fun (_ : Unit) => false)
    falseRenaming_injective falseAction_fullMap

private theorem twoVariable_isTranscendenceBasis :
    IsTranscendenceBasis (FractionRing P)
      (fun i : {i : Bool // i ∉ Set.range (fun (_ : Unit) => false)} =>
        algebraMap Q (FractionRing Q) (X i.1)) := by
  exact isTranscendenceBasis_fractionRing_map_rename_compl
    (R := ℤ) (L := FractionRing (MvPolynomial Unit ℤ))
    (K := FractionRing (MvPolynomial Bool ℤ)) (fun (_ : Unit) => false)
    falseRenaming_injective falseAction_fullMap

end CanonicalAction

end TwoVariables

section ArbitraryFractionRings

variable {R : Type uR} [CommRing R] [IsDomain R]
  {τ : Type uτ} {σ : Type uσ}
  {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
  [IsFractionRing (MvPolynomial τ R) L]
  {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
  [IsFractionRing (MvPolynomial σ R) K] [Algebra L K]
  (ρ : τ → σ) (hρ : Function.Injective ρ)
  (hmap : algebraMap L K = IsFractionRing.map
    (A := MvPolynomial τ R) (B := MvPolynomial σ R) (K := L) (L := K)
    (j := (rename (R := R) ρ).toRingHom) (rename_injective ρ hρ))

include hρ hmap

private theorem arbitrary_element_isAlgebraic (x : K) :
    IsAlgebraic
      (Algebra.adjoin L (Set.range (fun i : {i : σ // i ∉ Set.range ρ} =>
        algebraMap (MvPolynomial σ R) K (X i.1)))) x := by
  obtain ⟨h⟩ := isAlgebraic_adjoin_fractionRing_map_rename_compl ρ hρ hmap
  exact h x

private theorem arbitrary_complement_transcendental
    (i : {i : σ // i ∉ Set.range ρ}) :
    Transcendental L (algebraMap (MvPolynomial σ R) K (X i.1)) := by
  exact (isTranscendenceBasis_fractionRing_map_rename_compl ρ hρ hmap).1.transcendental i

end ArbitraryFractionRings

end MvPolynomial
