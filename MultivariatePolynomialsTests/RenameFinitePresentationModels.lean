/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Noetherian
import MultivariatePolynomials.RenameKernel
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.FinitePresentation

/-!
# Finite-presentation examples for polynomial renaming

Predecessor renaming is finitely presented over every commutative coefficient
ring, including the zero ring. With nontrivial coefficients its source polynomial
ring is not Noetherian. In contrast, projection from `ℕ × Bool` to `ℕ` is of
finite type but not finitely presented over any nontrivial commutative ring:
every source index participates in a collision, although each fibre has size two.

The elimination map between empty variable types allows independent coefficient,
source-variable, and target-variable universes. Over `ZMod 1`, the map
`(n, b) ↦ 2 * n` is finitely presented despite infinitely many missed target
indices and collision participants. Over `ZMod 4`, the nonzero square-zero
coefficient `2` accompanies the negative projection example; the coefficients
need not form a domain or a reduced ring.

Finite presentation and finite type use the algebra action induced by renaming
from the source polynomial ring. Kernel finite generation is for the source
ring acting on itself, not for the coefficient-ring module action. For the
negative projection example, the common base in the surjective-kernel theorem
is the source polynomial ring itself.

## References

* Mathlib, `Mathlib.RingTheory.FinitePresentation`: finite presentation of
  surjective ring homomorphisms and finite generation of their kernels.
* Mathlib, `Mathlib.RingTheory.FiniteType`: finite type of surjections.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: surjectivity and injectivity
  of polynomial renaming.
* `MultivariatePolynomials.RenameKernel`: finite generation of renaming kernels.
* `MultivariatePolynomials.Noetherian`: finiteness of variables forced by
  Noetherianity of a polynomial ring with nontrivial coefficients.
* Mathlib, `Mathlib.Data.Set.Finite.Basic` and `Mathlib.Data.Nat.Init`:
  infinite ranges and separation of even and odd indices.
* Mathlib, `Mathlib.Data.ZMod.Basic`: the modular coefficient rings.

## Implementation notes

All declarations in this example module are private. The resulting warning
about a module without public declarations is intentional.
-/

universe u v w

open MvPolynomial

namespace MultivariatePolynomialsTests

private theorem finitePresentation_rename_pred {R : Type u} [CommRing R] :
    @Algebra.FinitePresentation (MvPolynomial ℕ R) (MvPolynomial ℕ R) _ _
      (rename (R := R) Nat.pred).toRingHom.toAlgebra := by
  have hcollision :
      {i : ℕ | ∃ j : ℕ, i ≠ j ∧ Nat.pred i = Nat.pred j} = ({0, 1} : Set ℕ) := by
    ext i
    constructor
    · rintro ⟨j, hij, hpred⟩
      cases i <;> cases j <;> simp_all
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · exact ⟨1, Nat.zero_ne_one, rfl⟩
      · exact ⟨0, Nat.one_ne_zero, rfl⟩
  have hker : (RingHom.ker (rename (R := R) Nat.pred).toRingHom).FG := by
    apply (ker_rename_fg_iff (R := R) Nat.pred).mpr
    right
    rw [hcollision]
    exact (Set.finite_singleton 1).insert 0
  exact RingHom.FinitePresentation.of_surjective
    (rename (R := R) Nat.pred).toRingHom
    (rename_surjective Nat.pred fun n => ⟨n + 1, rfl⟩) hker

private theorem pred_source_not_isNoetherianRing
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ IsNoetherianRing (MvPolynomial ℕ R) := by
  intro h
  let : IsNoetherianRing (MvPolynomial ℕ R) := h
  exact (Infinite.not_finite : ¬ Finite ℕ)
    (MvPolynomial.finite_of_isNoetherianRing (σ := ℕ) (R := R))

private theorem paired_rename_finiteType_not_finitePresentation
    {R : Type u} [CommRing R] [Nontrivial R] :
    @Algebra.FiniteType (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R) _ _
        (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra ∧
      ¬ @Algebra.FinitePresentation (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R) _ _
        (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  have hsurj : Function.Surjective
      (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)) :=
    rename_surjective _ fun n => ⟨(n, false), rfl⟩
  let : Algebra (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R) :=
    (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  constructor
  · exact RingHom.FiniteType.of_surjective
      (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom hsurj
  · intro hfp
    let : Algebra.FinitePresentation
        (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R) := hfp
    -- Both algebras are finitely presented over the source itself: the source
    -- by the self instance, the target by the assumed relative presentation.
    have hfg := Algebra.FinitePresentation.ker_fG_of_surjective
      (Algebra.ofId (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R))
      (show Function.Surjective
        (Algebra.ofId (MvPolynomial (ℕ × Bool) R) (MvPolynomial ℕ R)) from hsurj)
    change (RingHom.ker
      (rename (R := R) (Prod.fst : ℕ × Bool → ℕ)).toRingHom).FG at hfg
    rcases (ker_rename_fg_iff (R := R) (Prod.fst : ℕ × Bool → ℕ)).mp hfg with
      hR | hfinite
    · exact (not_subsingleton R) hR
    · apply Set.infinite_univ (α := ℕ × Bool)
      apply hfinite.subset
      rintro ⟨n, b⟩ _
      exact ⟨(n, !b), fun h => Bool.self_ne_not b (congrArg Prod.snd h), rfl⟩

private theorem finitePresentation_rename_pempty {R : Type u} [CommRing R] :
    @Algebra.FinitePresentation
      (MvPolynomial PEmpty.{v + 1} R) (MvPolynomial PEmpty.{w + 1} R) _ _
      (rename (R := R)
        (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1})).toRingHom.toAlgebra := by
  apply RingHom.FinitePresentation.of_bijective
    (f := (rename (R := R)
      (PEmpty.elim : PEmpty.{v + 1} → PEmpty.{w + 1})).toRingHom)
  constructor
  · apply rename_injective
    intro i j _
    exact i.elim
  · apply rename_surjective
    intro j
    exact j.elim

private theorem paired_even_zmod_one_finitePresentation :
    (Set.range (fun p : ℕ × Bool => 2 * p.1))ᶜ.Infinite ∧
      {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ 2 * i.1 = 2 * j.1}.Infinite ∧
      @Algebra.FinitePresentation
        (MvPolynomial (ℕ × Bool) (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) _ _
        (rename (R := ZMod 1) (fun p : ℕ × Bool => 2 * p.1)).toRingHom.toAlgebra := by
  constructor
  · have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
      intro m n h
      exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0) (add_right_cancel h)
    apply Set.infinite_of_injective_forall_mem hinj
    intro n
    change 2 * n + 1 ∉ Set.range (fun p : ℕ × Bool => 2 * p.1)
    rintro ⟨⟨m, b⟩, h⟩
    exact Nat.two_mul_ne_two_mul_add_one h
  constructor
  · have hcollision :
        {i : ℕ × Bool | ∃ j : ℕ × Bool, i ≠ j ∧ 2 * i.1 = 2 * j.1} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rcases i with ⟨n, b⟩
      exact ⟨(n, !b), fun h => Bool.self_ne_not b (congrArg Prod.snd h), rfl⟩
    rw [hcollision]
    exact Set.infinite_univ
  · apply RingHom.FinitePresentation.of_surjective
      (rename (R := ZMod 1) (fun p : ℕ × Bool => 2 * p.1)).toRingHom
    · intro p
      exact ⟨0, Subsingleton.elim _ _⟩
    · rw [RingHom.ker_eq_top_of_subsingleton]
      exact Ideal.fg_top _

private theorem paired_rename_zmod_four :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 ∧
      @Algebra.FiniteType
        (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4)) _ _
        (rename (R := ZMod 4) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra ∧
      ¬ @Algebra.FinitePresentation
        (MvPolynomial (ℕ × Bool) (ZMod 4)) (MvPolynomial ℕ (ZMod 4)) _ _
        (rename (R := ZMod 4) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra := by
  let : Nontrivial (ZMod 4) := ZMod.nontrivial_iff.mpr (by decide)
  exact ⟨by decide, by decide,
    paired_rename_finiteType_not_finitePresentation (R := ZMod 4)⟩

end MultivariatePolynomialsTests
