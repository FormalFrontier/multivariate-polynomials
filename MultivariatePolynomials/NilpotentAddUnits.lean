/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

/-!
# Units from nilpotent additive units

In a semiring, a nilpotent element that has an additive inverse can be added to
`1` to obtain a multiplicative unit. Only that element needs an additive inverse;
the semiring need not be a ring or have commutative multiplication. This is a
sufficient condition, not a characterization of the elements whose sum with `1`
is a unit.

The proof uses finite geometric sums, as in Mathlib's ring theorem
`IsNilpotent.isUnit_one_add`, but constructs both inverse identities without
ambient subtraction.
-/

@[expose] public section

universe u

private theorem geometric_inverse_identities {R : Type u} [Semiring R]
    (x y : R) (hxy : x + y = 0) (n : ℕ) :
    ((1 + x) * (∑ i ∈ Finset.range n, y ^ i) + y ^ n = 1) ∧
      ((∑ i ∈ Finset.range n, y ^ i) * (1 + x) + y ^ n = 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geom_sum_succ' (x := y) (n := n)]
    constructor
    · calc
        (1 + x) * (y ^ n + ∑ i ∈ Finset.range n, y ^ i) + y ^ (n + 1) =
            (y ^ n + (1 + x) * (∑ i ∈ Finset.range n, y ^ i)) +
              (x + y) * y ^ n := by
                simp only [pow_succ', mul_add, add_mul, one_mul]
                ac_rfl
        _ = ((1 + x) * (∑ i ∈ Finset.range n, y ^ i) + y ^ n) + 0 := by
          rw [hxy, zero_mul]
          ac_rfl
        _ = 1 := by rw [ih.1, add_zero]
    · calc
        (y ^ n + ∑ i ∈ Finset.range n, y ^ i) * (1 + x) + y ^ (n + 1) =
            (y ^ n + (∑ i ∈ Finset.range n, y ^ i) * (1 + x)) +
              y ^ n * (x + y) := by
                simp only [pow_succ, add_mul, mul_add, mul_one]
                ac_rfl
        _ = ((∑ i ∈ Finset.range n, y ^ i) * (1 + x) + y ^ n) + 0 := by
          rw [hxy, mul_zero]
          ac_rfl
        _ = 1 := by rw [ih.2, add_zero]

/-- In a possibly noncommutative semiring, a nilpotent element with an additive
inverse can be added to `1` to give a unit. This is a sufficient condition, not
an equivalence; no additive inverses for other elements are required. -/
theorem IsNilpotent.isUnit_one_add_of_isAddUnit {R : Type u} [Semiring R] {x : R}
    (hx : IsNilpotent x) (ha : IsAddUnit x) : IsUnit (1 + x) := by
  rcases ha with ⟨a, rfl⟩
  let y : R := ((-a : AddUnits R) : R)
  have hxy : (a : R) + y = 0 := by
    change ((a + -a : AddUnits R) : R) = 0
    rw [add_neg_cancel]
    rfl
  have hyx : y + (a : R) = 0 := by
    change ((-a + a : AddUnits R) : R) = 0
    rw [neg_add_cancel]
    rfl
  have hsquare : (a : R) ^ 2 = y ^ 2 := by
    have hleft : (a : R) * (a : R) + (a : R) * y = 0 := by
      rw [← mul_add, hxy, mul_zero]
    have hright : (a : R) * y + y * y = 0 := by
      rw [← add_mul, add_comm (a : R) y, hyx, zero_mul]
    calc
      (a : R) ^ 2 = (a : R) * (a : R) + 0 := by rw [pow_two, add_zero]
      _ = (a : R) * (a : R) + ((a : R) * y + y * y) := by rw [hright]
      _ = ((a : R) * (a : R) + (a : R) * y) + y * y := (add_assoc _ _ _).symm
      _ = y ^ 2 := by rw [hleft, zero_add, pow_two]
  obtain ⟨n, hn⟩ := hx
  have hyn : y ^ (2 * n) = 0 := by
    calc
      y ^ (2 * n) = (y ^ 2) ^ n := pow_mul _ _ _
      _ = ((a : R) ^ 2) ^ n := by rw [hsquare]
      _ = ((a : R) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm 2 n, pow_mul]
      _ = 0 := by rw [hn]; simp
  have hi := geometric_inverse_identities (a : R) y hxy (2 * n)
  simp only [hyn, add_zero] at hi
  exact ⟨⟨1 + (a : R), ∑ i ∈ Finset.range (2 * n), y ^ i, hi.1, hi.2⟩, rfl⟩

/-- The semiring construction specializes to Mathlib's ring conclusion. -/
private theorem ring_specialization {R : Type u} [Ring R] {x : R}
    (hx : IsNilpotent x) :
    let ha : IsAddUnit x := ⟨⟨x, -x, add_neg_cancel x, neg_add_cancel x⟩, rfl⟩
    hx.isUnit_one_add_of_isAddUnit ha = IsNilpotent.isUnit_one_add hx := by
  exact Subsingleton.elim _ _

/-- The additive-unit hypothesis holds for a nonzero nilpotent in a semiring
with no additive inverse for `1`. -/
private theorem product_unit : IsUnit (1 + ((0, 2) : ℕ × ZMod 4)) := by
  apply IsNilpotent.isUnit_one_add_of_isAddUnit
  · refine ⟨2, ?_⟩
    decide
  · exact ⟨⟨(0, 2), (0, 2), by decide, by decide⟩, rfl⟩
