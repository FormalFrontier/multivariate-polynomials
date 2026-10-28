/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Invertible

/-!
# Non-unital rings of additive units

The additive units of a non-unital, non-associative semiring form a non-unital,
non-associative ring, with multiplication inherited from the semiring. Associativity
and commutativity are inherited when available. The additive operations are those
of Mathlib's `AddUnits`.

`AddUnits.coeNonUnitalRingHom` is the value inclusion. For every non-unital,
non-associative ring `S`, `AddUnits.nonUnitalRingHomEquiv` identifies homomorphisms
`S →ₙ+* AddUnits R` with homomorphisms `S →ₙ+* R`: the image of an additive group
already consists of additive units. No multiplicative identity is required or preserved.

The constructions reuse Mathlib's additive lifting and `AddUnits.mulRight`.
-/

@[expose] public section

universe u v

namespace AddUnits

variable {R : Type u}

/-- Additive units inherit a non-unital, non-associative ring structure. -/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocRing (AddUnits R) :=
  { (inferInstance : AddCommGroup (AddUnits R)) with
    mul a b := a.mulRight b.val
    left_distrib a b c := AddUnits.ext (mul_add a.val b.val c.val)
    right_distrib a b c := AddUnits.ext (add_mul a.val b.val c.val)
    zero_mul a := AddUnits.ext (zero_mul a.val)
    mul_zero a := AddUnits.ext (mul_zero a.val) }

/-- Additive units inherit associativity without changing their operations. -/
instance instNonUnitalRing [NonUnitalSemiring R] : NonUnitalRing (AddUnits R) :=
  { (inferInstance : NonUnitalNonAssocRing (AddUnits R)) with
    mul_assoc a b c := AddUnits.ext (mul_assoc a.val b.val c.val) }

/-- Additive units inherit commutativity without changing their operations. -/
instance instNonUnitalCommRing [NonUnitalCommSemiring R] :
    NonUnitalCommRing (AddUnits R) :=
  { (inferInstance : NonUnitalRing (AddUnits R)) with
    mul_comm a b := AddUnits.ext (mul_comm a.val b.val) }

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp] theorem val_mul (a b : AddUnits R) : (a * b).val = a.val * b.val := rfl

/-- The value inclusion of additive units as a non-unital ring homomorphism. -/
def coeNonUnitalRingHom : AddUnits R →ₙ+* R :=
  { coeHom R with map_mul' := val_mul }

@[simp] theorem coeNonUnitalRingHom_apply (a : AddUnits R) :
    coeNonUnitalRingHom a = a.val := rfl

@[simp] theorem coeNonUnitalRingHom_toAddMonoidHom :
    (coeNonUnitalRingHom : AddUnits R →ₙ+* R).toAddMonoidHom = coeHom R := rfl

variable {S : Type v} [NonUnitalNonAssocRing S]

/-- A homomorphism from a non-unital ring factors through the additive units. -/
def liftNonUnitalRingHom (f : S →ₙ+* R) : S →ₙ+* AddUnits R :=
  { f.toAddMonoidHom.toHomAddUnits with
    map_mul' a b := AddUnits.ext (f.map_mul a b) }

@[simp] theorem val_liftNonUnitalRingHom (f : S →ₙ+* R) (s : S) :
    (liftNonUnitalRingHom f s).val = f s := rfl

/-- The lifted homomorphism factors the original homomorphism through value inclusion. -/
@[simp] theorem coeNonUnitalRingHom_comp_lift (f : S →ₙ+* R) :
    coeNonUnitalRingHom.comp (liftNonUnitalRingHom f) = f := by
  ext s
  rfl

@[simp] theorem liftNonUnitalRingHom_comp_coe (g : S →ₙ+* AddUnits R) :
    liftNonUnitalRingHom (coeNonUnitalRingHom.comp g) = g := by
  apply NonUnitalRingHom.ext
  intro s
  exact AddUnits.ext rfl

/-- A factorization through the additive units is unique. -/
theorem liftNonUnitalRingHom_unique (f : S →ₙ+* R) (g : S →ₙ+* AddUnits R)
    (h : coeNonUnitalRingHom.comp g = f) : g = liftNonUnitalRingHom f := by
  simpa using congrArg liftNonUnitalRingHom h

/-- Homomorphisms from a non-unital ring to a semiring are exactly homomorphisms
into its additive units. The source and target universes are independent. -/
def nonUnitalRingHomEquiv : (S →ₙ+* AddUnits R) ≃ (S →ₙ+* R) where
  toFun g := coeNonUnitalRingHom.comp g
  invFun := liftNonUnitalRingHom
  left_inv := liftNonUnitalRingHom_comp_coe
  right_inv := coeNonUnitalRingHom_comp_lift

@[simp] theorem nonUnitalRingHomEquiv_apply (g : S →ₙ+* AddUnits R) :
    nonUnitalRingHomEquiv g = coeNonUnitalRingHom.comp g := rfl

@[simp] theorem nonUnitalRingHomEquiv_symm_apply (f : S →ₙ+* R) :
    nonUnitalRingHomEquiv.symm f = liftNonUnitalRingHom f := rfl

end NonUnitalNonAssocSemiring

end AddUnits
