/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import MultivariatePolynomials.HomogeneousEvaluation

import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Projective maps defined by homogeneous polynomial families

A family of homogeneous polynomials of one common degree defines a map on projective
coordinate spaces whenever its evaluation tuple is nonzero at every nonzero input.
The coefficient semiring, the field of points and the two coordinate types have
independent universes. The coordinate types need not be finite or nonempty, and the
degree may be zero.

The map sends the class of a nonzero tuple to the class of its evaluation tuple.
Its values on these classes characterize it uniquely. Substituting homogeneous
families corresponds to composing the induced maps.

For coefficients in the field of points, the absence of nonzero common zeros over
an algebraic closure implies the required nonvanishing over the base field. This
implication requires neither homogeneity nor finite coordinate types.

## References

* Mathlib, `Mathlib.LinearAlgebra.Projectivization.Basic`: the projective carrier,
  `Projectivization.lift`, and equality of classes under scalar multiplication.
* `MultivariatePolynomials.HomogeneousEvaluation`:
  `MvPolynomial.IsHomogeneous.eval₂Hom_mul_left` supplies the scaling law.
* Mathlib, `Mathlib.RingTheory.MvPolynomial.Homogeneous` and
  `Mathlib.Algebra.MvPolynomial.Eval`: homogeneity and evaluation under substitution;
  `MvPolynomial.eval₂_comp` transfers evaluation along a coefficient embedding.
-/

@[expose] public section

universe uB uK uI uO uT

namespace MvPolynomial

/-- A polynomial family with no nonzero common zero over an algebraic closure has
nonzero evaluation tuple at every nonzero tuple over the base field. Neither
homogeneity nor finiteness of the coordinate types is required. -/
theorem eval_ne_zero_of_forall_eval₂_eq_zero
    {K : Type uK} {I : Type uI} {O : Type uO} [Field K]
    (p : O → MvPolynomial I K)
    (hzero : ∀ x : I → AlgebraicClosure K,
      (∀ o, MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x (p o) = 0) →
        x = 0) :
    ∀ x : I → K, x ≠ 0 →
      (fun o => MvPolynomial.eval₂ (RingHom.id K) x (p o)) ≠ 0 := by
  intro x hx heval
  apply hx
  have hbar : (algebraMap K (AlgebraicClosure K)) ∘ x = 0 :=
    hzero ((algebraMap K (AlgebraicClosure K)) ∘ x) (fun o => by
      rw [← MvPolynomial.eval₂_comp]
      have ho : MvPolynomial.eval x (p o) = 0 := congrFun heval o
      rw [ho, map_zero])
  funext i
  apply (algebraMap K (AlgebraicClosure K)).injective
  simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hbar i

variable {B : Type uB} {K : Type uK} {I : Type uI} {O : Type uO}
  [CommSemiring B] [Field K]

/-- The map on projective coordinate spaces defined by a homogeneous polynomial
family whose evaluation is nonzero on every nonzero input. -/
noncomputable def projectivize
    (p : O → MvPolynomial I B) (d : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d) (σ : B →+* K)
    (hnv : ∀ x : I → K, x ≠ 0 → (fun o => eval₂ σ x (p o)) ≠ 0) :
    Projectivization K (I → K) → Projectivization K (O → K) :=
  Projectivization.lift
    (fun x : {x : I → K // x ≠ 0} =>
      Projectivization.mk K (fun o => eval₂ σ x.val (p o)) (hnv x.val x.property))
    (by
      intro x y a hxy
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
      refine ⟨a ^ d, ?_⟩
      funext o
      change a ^ d * eval₂ σ y.val (p o) = eval₂ σ x.val (p o)
      rw [hxy]
      exact (IsHomogeneous.eval₂Hom_mul_left d (p o) (hp o) σ y.val a).symm)

/-- On a class represented by a nonzero tuple, `projectivize` is the class of the
polynomial evaluation tuple. -/
@[simp]
theorem projectivize_mk
    (p : O → MvPolynomial I B) (d : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d) (σ : B →+* K)
    (hnv : ∀ x : I → K, x ≠ 0 → (fun o => eval₂ σ x (p o)) ≠ 0)
    (x : I → K) (hx : x ≠ 0) :
    projectivize p d hp σ hnv (Projectivization.mk K x hx) =
      Projectivization.mk K (fun o => eval₂ σ x (p o)) (hnv x hx) := rfl

/-- The value of `projectivize` is represented by evaluation at any chosen
representative of the input point. This is an equality of classes, not of chosen
representatives in the output coordinate space. -/
theorem projectivize_eq_mk_rep
    (p : O → MvPolynomial I B) (d : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d) (σ : B →+* K)
    (hnv : ∀ x : I → K, x ≠ 0 → (fun o => eval₂ σ x (p o)) ≠ 0)
    (P : Projectivization K (I → K)) :
    projectivize p d hp σ hnv P =
      Projectivization.mk K (fun o => eval₂ σ P.rep (p o))
        (hnv P.rep P.rep_nonzero) := by
  simpa only [Projectivization.mk_rep] using
    projectivize_mk p d hp σ hnv P.rep P.rep_nonzero

/-- A function on projective coordinate spaces equals `projectivize` if and only
if it sends every nonzero tuple's class to the class of its evaluation tuple. -/
theorem eq_projectivize_iff
    (p : O → MvPolynomial I B) (d : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d) (σ : B →+* K)
    (hnv : ∀ x : I → K, x ≠ 0 → (fun o => eval₂ σ x (p o)) ≠ 0)
    (f : Projectivization K (I → K) → Projectivization K (O → K)) :
    f = projectivize p d hp σ hnv ↔
      ∀ (x : I → K) (hx : x ≠ 0),
        f (Projectivization.mk K x hx) =
          Projectivization.mk K (fun o => eval₂ σ x (p o)) (hnv x hx) := by
  constructor
  · rintro rfl x hx
    exact projectivize_mk p d hp σ hnv x hx
  · intro hf
    funext P
    refine Projectivization.ind (fun x hx => ?_) P
    exact (hf x hx).trans (projectivize_mk p d hp σ hnv x hx).symm

/-- The coordinate variables, of common degree one, induce the identity map.
This applies to arbitrary coordinate types and coefficient homomorphisms. -/
@[simp]
theorem projectivize_X (σ : B →+* K) :
    projectivize (fun i : I => (X i : MvPolynomial I B)) 1
      (fun i => isHomogeneous_X B i) σ
      (by
        intro x hx
        simpa only [eval₂_X] using hx) = id := by
  symm
  apply (eq_projectivize_iff _ _ _ _ _ id).2
  intro x hx
  simp only [eval₂_X, id_eq]

/-- Substitution of a degree-`d` homogeneous family into a degree-`e` family
induces the composite projective map. The substituted family has degree `d * e`;
both families use the same coefficient semiring and coefficient homomorphism. -/
theorem projectivize_comp {T : Type uT}
    (p : O → MvPolynomial I B) (q : T → MvPolynomial O B) (d e : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d) (hq : ∀ t, (q t).IsHomogeneous e)
    (σ : B →+* K)
    (hpv : ∀ x : I → K, x ≠ 0 → (fun o => eval₂ σ x (p o)) ≠ 0)
    (hqv : ∀ y : O → K, y ≠ 0 → (fun t => eval₂ σ y (q t)) ≠ 0) :
    projectivize (fun t => eval₂ C p (q t)) (d * e)
      (fun t => (hq t).eval₂ C p (fun b => isHomogeneous_C I b) hp) σ
      (by
        intro x hx
        simpa only [eval₂_assoc] using
          hqv (fun o => eval₂ σ x (p o)) (hpv x hx)) =
      projectivize q e hq σ hqv ∘ projectivize p d hp σ hpv := by
  symm
  apply (eq_projectivize_iff _ _ _ _ _ _).2
  intro x hx
  simp only [Function.comp_apply, projectivize_mk, eval₂_assoc]

end MvPolynomial
