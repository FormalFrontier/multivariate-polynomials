/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Finite
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.Algebra.DirectSum.Module

/-!
# Polynomial point quotients and square-zero coordinates

A distinguished polynomial coordinate acts on a square-zero coordinate at a
specified point. The presentation uses only the square and linear relations;
relations between distinct square-zero coordinates are not generators.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, for the
  motivating family of polynomial point quotients.
* Mathlib's multivariate evaluation and ideal quotient APIs supply the
  universal constructions.
* Coherent Modules supplies the canonical opposite action on a module used by
  the trivial square-zero extension.
-/

@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι uB

variable {R : Type uR} {ι : Type uι} [CommRing R]

/-- The square-zero point relations on the distinguished coordinate `none` and
the indexed coordinates `some i`. There are no mixed-product generators. -/
noncomputable def pointSquareZeroIdeal (a : ι → R) : Ideal (MvPolynomial (Option ι) R) :=
  Ideal.span (Set.range (fun i : ι => (X (some i) : MvPolynomial (Option ι) R) ^ 2) ∪
    Set.range (fun i : ι =>
      (X none - C (a i)) * (X (some i) : MvPolynomial (Option ι) R)))

/-- The polynomial algebra with square-zero coordinates supported at points `a i`. -/
abbrev pointSquareZeroQuotient (a : ι → R) : Type _ :=
  MvPolynomial (Option ι) R ⧸ pointSquareZeroIdeal a

/-- The direct sum of polynomial modules of point evaluations. -/
abbrev pointSquareZeroModule (a : ι → R) : Type _ :=
  ⨁ i : ι, (R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i)))

theorem pointSquareZero_sq_mem (a : ι → R) (i : ι) :
    (X (some i) : MvPolynomial (Option ι) R) ^ 2 ∈ pointSquareZeroIdeal a :=
  Ideal.subset_span (Or.inl ⟨i, rfl⟩)

theorem pointSquareZero_linear_mem (a : ι → R) (i : ι) :
    (X none - C (a i)) * (X (some i) : MvPolynomial (Option ι) R) ∈
      pointSquareZeroIdeal a :=
  Ideal.subset_span (Or.inr ⟨i, rfl⟩)

@[simp] theorem pointSquareZero_sq (a : ι → R) (i : ι) :
    (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) ^ 2 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact pointSquareZero_sq_mem a i

@[simp] theorem pointSquareZero_linear (a : ι → R) (i : ι) :
    (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none) -
      Ideal.Quotient.mk (pointSquareZeroIdeal a) (C (a i))) *
      Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i)) = 0 := by
  rw [← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact pointSquareZero_linear_mem a i

/-- The polynomial base map sends `X` to the distinguished coordinate. -/
noncomputable instance pointSquareZeroAlgebra (a : ι → R) :
    Algebra R[X] (pointSquareZeroQuotient a) :=
  (((Ideal.Quotient.mkₐ R (pointSquareZeroIdeal a)).comp
    (Polynomial.aeval (X none : MvPolynomial (Option ι) R))).toRingHom).toAlgebra

@[simp] theorem pointSquareZero_algebraMap_X (a : ι → R) :
    algebraMap R[X] (pointSquareZeroQuotient a) Polynomial.X =
      Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none) := by
  change (Ideal.Quotient.mkₐ R (pointSquareZeroIdeal a))
    (Polynomial.aeval (X none : MvPolynomial (Option ι) R) Polynomial.X) = _
  rw [Polynomial.aeval_X]
  rfl

@[simp] theorem pointSquareZero_algebraMap_C (a : ι → R) (r : R) :
    algebraMap R[X] (pointSquareZeroQuotient a) (Polynomial.C r) =
      Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r) := by
  change (Ideal.Quotient.mkₐ R (pointSquareZeroIdeal a))
    (Polynomial.aeval (X none : MvPolynomial (Option ι) R) (Polynomial.C r)) = _
  rw [Polynomial.aeval_C]
  rfl

/-- The polynomial-base algebra structure extends the quotient's original
coefficient algebra structure. -/
instance pointSquareZeroIsScalarTower (a : ι → R) :
    IsScalarTower R R[X] (pointSquareZeroQuotient a) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [show algebraMap R R[X] r = Polynomial.C r from rfl,
    pointSquareZero_algebraMap_C]
  rfl

/-- The canonical coordinate in the `i`-th evaluation summand. -/
noncomputable def pointSquareZeroDelta (a : ι → R) (i : ι) : pointSquareZeroModule a :=
  by
    classical
    exact DirectSum.lof R[X] ι (fun i => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i)))
      i (Ideal.Quotient.mk _ 1)

@[simp] theorem pointSquareZeroDelta_annihilated (a : ι → R) (i : ι) :
    (Polynomial.X - Polynomial.C (a i)) • pointSquareZeroDelta a i = 0 := by
  classical
  rw [pointSquareZeroDelta, ← map_smul]
  have h : (Polynomial.X - Polynomial.C (a i)) •
      (Ideal.Quotient.mk (RingHom.ker (Polynomial.evalRingHom (a i))) (1 : R[X])) = 0 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    simp [RingHom.mem_ker]
  rw [h, map_zero]

/-- The presentation's universal map into a commutative polynomial algebra.
The chosen elements satisfy the square and point-support relations. -/
noncomputable def pointSquareZeroLift (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    (b : ι → B) (hsq : ∀ i, b i ^ 2 = 0)
    (hlinear : ∀ i, algebraMap R[X] B (Polynomial.X - Polynomial.C (a i)) * b i = 0) :
    pointSquareZeroQuotient a →ₐ[R[X]] B := by
  let f : MvPolynomial (Option ι) R →+* B :=
    eval₂Hom ((algebraMap R[X] B).comp (Polynomial.C : R →+* R[X]))
      (fun t => t.elim (algebraMap R[X] B Polynomial.X) b)
  have hker : pointSquareZeroIdeal a ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · simpa [RingHom.mem_ker, f] using hsq i
    · simpa [RingHom.mem_ker, f, ← map_sub, ← map_mul] using hlinear i
  have hI : ∀ p, p ∈ pointSquareZeroIdeal a → f p = 0 :=
    fun _ hp => RingHom.mem_ker.mp (hker hp)
  let g : pointSquareZeroQuotient a →+* B :=
    Ideal.Quotient.lift (pointSquareZeroIdeal a) f hI
  have hbase : g.comp (algebraMap R[X] (pointSquareZeroQuotient a)) =
      algebraMap R[X] B := by
    apply Polynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, pointSquareZero_algebraMap_C]
      change f (C r) = algebraMap R[X] B (Polynomial.C r)
      simp [f]
    · rw [RingHom.comp_apply, pointSquareZero_algebraMap_X]
      change f (X none) = algebraMap R[X] B Polynomial.X
      simp [f]
  refine AlgHom.mk' g ?_
  intro s q
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  exact congrArg (fun x : B => x * g q) (RingHom.congr_fun hbase s)

@[simp] theorem pointSquareZeroLift_mk_some (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    (b : ι → B) (hsq : ∀ i, b i ^ 2 = 0)
    (hlinear : ∀ i, algebraMap R[X] B (Polynomial.X - Polynomial.C (a i)) * b i = 0)
    (i : ι) :
    pointSquareZeroLift a b hsq hlinear
        (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) = b i := by
  simp [pointSquareZeroLift]

@[simp] theorem pointSquareZeroLift_mk_none (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    (b : ι → B) (hsq : ∀ i, b i ^ 2 = 0)
    (hlinear : ∀ i, algebraMap R[X] B (Polynomial.X - Polynomial.C (a i)) * b i = 0) :
    pointSquareZeroLift a b hsq hlinear
        (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)) =
      algebraMap R[X] B Polynomial.X := by
  rw [← pointSquareZero_algebraMap_X]
  exact (pointSquareZeroLift a b hsq hlinear).commutes Polynomial.X

@[simp] theorem pointSquareZeroLift_mk_C (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    (b : ι → B) (hsq : ∀ i, b i ^ 2 = 0)
    (hlinear : ∀ i, algebraMap R[X] B (Polynomial.X - Polynomial.C (a i)) * b i = 0)
    (r : R) :
    pointSquareZeroLift a b hsq hlinear
        (Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r)) =
      algebraMap R[X] B (Polynomial.C r) := by
  rw [← pointSquareZero_algebraMap_C]
  exact (pointSquareZeroLift a b hsq hlinear).commutes (Polynomial.C r)

/-- Polynomial-base maps from the point quotient are determined by their
images on the indexed square-zero coordinates. -/
theorem pointSquareZeroAlgHom_ext (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    {f g : pointSquareZeroQuotient a →ₐ[R[X]] B}
    (h : ∀ i, f (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) =
      g (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i)))) : f = g := by
  apply AlgHom.ext
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hfg : f.toRingHom.comp (Ideal.Quotient.mk (pointSquareZeroIdeal a)) =
      g.toRingHom.comp (Ideal.Quotient.mk (pointSquareZeroIdeal a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r)) =
        g (Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r))
      rw [← pointSquareZero_algebraMap_C, f.commutes, g.commutes]
    · intro t
      cases t with
      | none =>
        change f (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)) =
          g (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none))
        rw [← pointSquareZero_algebraMap_X, f.commutes, g.commutes]
      | some i => exact h i
  exact RingHom.congr_fun hfg p

/-- The lift is unique among polynomial-base maps taking each square-zero
coordinate to the prescribed element. -/
theorem pointSquareZeroLift_unique (a : ι → R)
    {B : Type uB} [CommRing B] [Algebra R[X] B]
    (b : ι → B) (hsq : ∀ i, b i ^ 2 = 0)
    (hlinear : ∀ i, algebraMap R[X] B (Polynomial.X - Polynomial.C (a i)) * b i = 0)
    (f : pointSquareZeroQuotient a →ₐ[R[X]] B)
    (hf : ∀ i, f (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) = b i) :
    f = pointSquareZeroLift a b hsq hlinear := by
  apply pointSquareZeroAlgHom_ext a
  intro i
  rw [hf, pointSquareZeroLift_mk_some]

/-- The generator-prescribed algebra map exists even when evaluation points
coincide or their differences are not units. -/
noncomputable def pointSquareZeroForward (a : ι → R) :
    pointSquareZeroQuotient a →ₐ[R[X]]
      TrivSqZeroExt R[X] (pointSquareZeroModule a) :=
  pointSquareZeroLift a (B := TrivSqZeroExt R[X] (pointSquareZeroModule a))
    (fun i => TrivSqZeroExt.inr (pointSquareZeroDelta a i))
    (fun i => by rw [pow_two, TrivSqZeroExt.inr_mul_inr])
    (fun i => by
      rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr,
        pointSquareZeroDelta_annihilated,
        TrivSqZeroExt.inr_zero])

@[simp] theorem pointSquareZeroForward_mk_some (a : ι → R) (i : ι) :
    pointSquareZeroForward a
      (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) =
        TrivSqZeroExt.inr (pointSquareZeroDelta a i) :=
  pointSquareZeroLift_mk_some a _ _ _ i

@[simp] theorem pointSquareZeroForward_mk_none (a : ι → R) :
    pointSquareZeroForward a (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)) =
      TrivSqZeroExt.inl (Polynomial.X : R[X]) := by
  rw [pointSquareZeroForward, pointSquareZeroLift_mk_none,
    TrivSqZeroExt.algebraMap_eq_inl]

@[simp] theorem pointSquareZeroForward_mk_C (a : ι → R) (r : R) :
    pointSquareZeroForward a (Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r)) =
      TrivSqZeroExt.inl (Polynomial.C r : R[X]) := by
  rw [pointSquareZeroForward, pointSquareZeroLift_mk_C,
    TrivSqZeroExt.algebraMap_eq_inl]

end MvPolynomial
