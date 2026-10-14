/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Module-finite polynomial renaming: examples

The scalars in these examples are the full source polynomial semiring. A source
polynomial `p` acts on a target polynomial `q` as `rename f p * q`, using the
module induced by the renaming homomorphism. This is not finiteness over the
coefficient semiring.

With coefficient semiring `ℕ`, the identity on natural-number variables and the
projection from paired natural variables give module-finite targets over their
source polynomial semirings, despite infinitely many variables. The projection
is surjective but not injective, and the coefficients have no additive inverse
for one. Empty variable types give another surjective example.
With coefficients `ZMod 1`, even the nonsurjective map from `Empty` to `ℕ` gives
a module-finite target.

The lifted projection places coefficients, source variables and target variables
in three independent universes. Its coefficients remain nontrivial, and its
variable map remains surjective and noninjective.

## References

* Mathlib, `Mathlib.RingTheory.Finiteness.Basic`: regular self-modules and
  transfer of module finiteness along surjective linear maps.
* Mathlib, `Mathlib.Algebra.Algebra.Defs`: the algebra induced by a ring
  homomorphism and its canonical linear map from the regular source module.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: surjectivity of polynomial
  renaming for surjective variable maps.
* Mathlib, `Mathlib.Algebra.Ring.ULift` and `Mathlib.Data.ZMod.Defs`: lifted
  coefficient semirings and the zero coefficient ring.
* Mathlib, `Mathlib.Data.Fintype.EquivFin`: infinitude of the natural-number
  variable types and their products.
-/

universe u v w

namespace MultivariatePolynomialsTests

private theorem natural_variable_types_infinite : Infinite ℕ ∧ Infinite (ℕ × Bool) :=
  ⟨inferInstance, inferInstance⟩

private theorem nat_coefficients_have_no_additive_inverse :
    ¬ ∃ n : ℕ, 1 + n = 0 := by
  rintro ⟨n, hn⟩
  exact Nat.succ_ne_zero n (by simpa only [Nat.add_comm] using hn)

private theorem nat_identity_smul (p q : MvPolynomial ℕ ℕ) :
    @SMul.smul (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      (MvPolynomial.rename (R := ℕ) (id : ℕ → ℕ)).toRingHom.toAlgebra.toSMul p q =
      p * q := by
  change MvPolynomial.rename (id : ℕ → ℕ) p * q = p * q
  rw [MvPolynomial.rename_id_apply]

private theorem nat_identity_moduleFinite :
    @Module.Finite (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℕ) (id : ℕ → ℕ)).toRingHom.toAlgebra) := by
  let φ : Algebra (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ) :=
    (MvPolynomial.rename (R := ℕ) (id : ℕ → ℕ)).toRingHom.toAlgebra
  -- The domain of this bundled map has the regular self-module structure;
  -- the codomain has the explicitly supplied renaming action.
  exact @Module.Finite.of_surjective
    (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
    inferInstance inferInstance inferInstance
    (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
    inferInstance inferInstance
    (@Algebra.toModule (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance φ)
    (RingHom.id _) (Module.Finite.self (MvPolynomial ℕ ℕ))
    (@Algebra.linearMap (MvPolynomial ℕ ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance φ)
    (MvPolynomial.rename_surjective _ (fun n => ⟨n, rfl⟩))

private theorem paired_projection_surjective :
    Function.Surjective (Prod.fst : ℕ × Bool → ℕ) := by
  intro n
  exact ⟨(n, false), rfl⟩

private theorem paired_projection_not_injective :
    ¬ Function.Injective (Prod.fst : ℕ × Bool → ℕ) := by
  intro h
  have hfalse : false = true := congrArg Prod.snd
    (h (show Prod.fst (0, false) = Prod.fst (0, true) from rfl))
  cases hfalse

private theorem paired_projection_smul
    (p : MvPolynomial (ℕ × Bool) ℕ) (q : MvPolynomial ℕ ℕ) :
    @SMul.smul (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ)
      (MvPolynomial.rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra.toSMul
      p q = MvPolynomial.rename (Prod.fst : ℕ × Bool → ℕ) p * q := rfl

private theorem paired_projection_moduleFinite :
    @Module.Finite (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ)
        inferInstance inferInstance
        (MvPolynomial.rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra) := by
  let φ : Algebra (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ) :=
    (MvPolynomial.rename (R := ℕ) (Prod.fst : ℕ × Bool → ℕ)).toRingHom.toAlgebra
  exact Module.Finite.of_surjective
    (hM := Module.Finite.self (MvPolynomial (ℕ × Bool) ℕ))
    (@Algebra.linearMap (MvPolynomial (ℕ × Bool) ℕ) (MvPolynomial ℕ ℕ)
      inferInstance inferInstance φ)
    (MvPolynomial.rename_surjective _ paired_projection_surjective)

private theorem empty_source_not_surjective :
    ¬ Function.Surjective (Empty.elim : Empty → ℕ) := by
  intro h
  obtain ⟨i, _hi⟩ := h 0
  exact Empty.elim i

private theorem zero_coefficients_empty_source_moduleFinite :
    @Module.Finite (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
        inferInstance inferInstance
        (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra) := by
  let : Subsingleton (MvPolynomial ℕ (ZMod 1)) :=
    Algebra.subsingleton (ZMod 1) (MvPolynomial ℕ (ZMod 1))
  let φ : Algebra (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1)) :=
    (MvPolynomial.rename (R := ZMod 1) (Empty.elim : Empty → ℕ)).toRingHom.toAlgebra
  apply Module.Finite.of_surjective
    (hM := Module.Finite.self (MvPolynomial Empty (ZMod 1)))
    (@Algebra.linearMap (MvPolynomial Empty (ZMod 1)) (MvPolynomial ℕ (ZMod 1))
      inferInstance inferInstance φ)
  intro q
  exact ⟨0, Subsingleton.elim _ _⟩

private theorem empty_rename_moduleFinite {R : Type u} [CommSemiring R] :
    @Module.Finite (MvPolynomial Empty R) (MvPolynomial Empty R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial Empty R) (MvPolynomial Empty R)
        inferInstance inferInstance
        (MvPolynomial.rename (R := R) (Empty.elim : Empty → Empty)).toRingHom.toAlgebra) := by
  let φ : Algebra (MvPolynomial Empty R) (MvPolynomial Empty R) :=
    (MvPolynomial.rename (R := R) (Empty.elim : Empty → Empty)).toRingHom.toAlgebra
  exact @Module.Finite.of_surjective
    (MvPolynomial Empty R) (MvPolynomial Empty R)
    inferInstance inferInstance inferInstance
    (MvPolynomial Empty R) (MvPolynomial Empty R)
    inferInstance inferInstance
    (@Algebra.toModule (MvPolynomial Empty R) (MvPolynomial Empty R)
      inferInstance inferInstance φ)
    (RingHom.id _) (Module.Finite.self (MvPolynomial Empty R))
    (@Algebra.linearMap (MvPolynomial Empty R) (MvPolynomial Empty R)
      inferInstance inferInstance φ)
    (MvPolynomial.rename_surjective _ (fun i => Empty.elim i))

private def liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ :=
  fun i => ⟨i.down.1⟩

private theorem lifted_projection_surjective :
    Function.Surjective
      (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ) := by
  rintro ⟨n⟩
  exact ⟨⟨(n, false)⟩, rfl⟩

private theorem lifted_projection_not_injective :
    ¬ Function.Injective
      (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ) := by
  intro h
  have heq : (⟨(0, false)⟩ : ULift.{v} (ℕ × Bool)) = ⟨(0, true)⟩ :=
    h (show liftedProjection (⟨(0, false)⟩ : ULift.{v} (ℕ × Bool)) =
        (liftedProjection (⟨(0, true)⟩ : ULift.{v} (ℕ × Bool)) : ULift.{w} ℕ) from rfl)
  have hfalse : false = true :=
    congrArg (fun i : ULift.{v} (ℕ × Bool) => i.down.2) heq
  cases hfalse

private theorem lifted_variable_types_infinite :
    Infinite (ULift.{v} (ℕ × Bool)) ∧ Infinite (ULift.{w} ℕ) :=
  ⟨inferInstance, inferInstance⟩

private theorem lifted_coefficients_zero_ne_one : (0 : ULift.{u} ℕ) ≠ 1 := by
  intro h
  have hnat : (0 : ℕ) = 1 := congrArg ULift.down h
  cases hnat

private theorem lifted_projection_moduleFinite :
    @Module.Finite
      (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
      inferInstance inferInstance
      (@Algebra.toModule
        (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ))
        (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
        inferInstance inferInstance
        (MvPolynomial.rename (R := ULift.{u} ℕ)
          (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ)).toRingHom.toAlgebra) := by
  let φ : Algebra
      (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ)) :=
    (MvPolynomial.rename (R := ULift.{u} ℕ)
      (liftedProjection : ULift.{v} (ℕ × Bool) → ULift.{w} ℕ)).toRingHom.toAlgebra
  exact Module.Finite.of_surjective
    (hM := Module.Finite.self (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ)))
    (@Algebra.linearMap
      (MvPolynomial (ULift.{v} (ℕ × Bool)) (ULift.{u} ℕ))
      (MvPolynomial (ULift.{w} ℕ) (ULift.{u} ℕ))
      inferInstance inferInstance φ)
    (MvPolynomial.rename_surjective _ lifted_projection_surjective)

end MultivariatePolynomialsTests
