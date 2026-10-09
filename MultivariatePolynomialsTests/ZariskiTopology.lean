/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.ZariskiTopology
import Mathlib.Algebra.DualNumber
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Polynomial coordinate topology examples

The parabola `y = x²` uses polynomial graph substitution and projection, and
its closed points carry the subspace topology of the quotient spectrum.
Boundary examples include empty variables, the unit ideal, and a square-zero
coordinate quotient with a nonzero nilpotent. A quadratic quotient with a
closed point but no rational zero illustrates why the closed-point
homeomorphism requires algebraic closure.
-/

@[expose] public section

noncomputable section

namespace MultivariatePolynomialsTests

universe u

variable (K : Type u) [Field K]

private def parabolaIdeal : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) -
    MvPolynomial.X (0 : Fin 2) ^ 2}

private def parabolaGraphHom :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 1) K :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X (0 : Fin 1) else MvPolynomial.X (0 : Fin 1) ^ 2)

private def parabolaProjectionHom :
    MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (fun _ => MvPolynomial.X (0 : Fin 2))

private theorem parabolaGraph_continuous :
    Continuous (MvPolynomial.ZariskiSpace.substitution (parabolaGraphHom K)) :=
  MvPolynomial.ZariskiSpace.continuous_substitution _

private theorem parabola_embedding :
    Topology.IsEmbedding (MvPolynomial.ZariskiSpace.zeroLocusClosedPoint (parabolaIdeal K)) :=
  MvPolynomial.ZariskiSpace.isEmbedding_zeroLocusClosedPoint _

private theorem rational_infinite_embedding :
    Topology.IsEmbedding (MvPolynomial.ZariskiSpace.pointToPoint (K := ℚ) (σ := ℕ)) :=
  MvPolynomial.ZariskiSpace.isEmbedding_pointToPoint

private theorem parabolaProjection_continuous :
    Continuous (MvPolynomial.ZariskiSpace.substitution (parabolaProjectionHom K)) :=
  MvPolynomial.ZariskiSpace.continuous_substitution _

private theorem graph_first_coordinate (x : MvPolynomial.ZariskiSpace K (Fin 1)) :
    MvPolynomial.ZariskiSpace.substitution (parabolaGraphHom K) x 0 = x 0 := by
  simp [parabolaGraphHom]

private theorem graph_second_coordinate (x : MvPolynomial.ZariskiSpace K (Fin 1)) :
    MvPolynomial.ZariskiSpace.substitution (parabolaGraphHom K) x 1 = x 0 ^ 2 := by
  simp [parabolaGraphHom]

private def parabolaGraph (x : MvPolynomial.ZariskiSpace K (Fin 1)) :
    MvPolynomial.ZariskiSpace.zeroLocus (parabolaIdeal K) :=
  ⟨MvPolynomial.ZariskiSpace.substitution (parabolaGraphHom K) x, by
    change (MvPolynomial.ZariskiSpace.substitution (parabolaGraphHom K) x).toFun ∈
      MvPolynomial.zeroLocus K (Ideal.span
        {(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) -
          MvPolynomial.X (0 : Fin 2) ^ 2})
    rw [MvPolynomial.zeroLocus_span]
    intro p hp
    have hp' : p = (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) -
        MvPolynomial.X (0 : Fin 2) ^ 2 := hp
    subst p
    simp only [map_sub, map_pow, MvPolynomial.aeval_X, graph_first_coordinate,
      graph_second_coordinate, sub_self]⟩

private theorem parabola_equation
    (x : MvPolynomial.ZariskiSpace.zeroLocus (parabolaIdeal K)) :
    x.val 1 = x.val 0 ^ 2 := by
  have hx : x.val.toFun ∈ MvPolynomial.zeroLocus K (parabolaIdeal K) :=
    MvPolynomial.ZariskiSpace.mem_zeroLocus.mp x.property
  change x.val.toFun ∈ MvPolynomial.zeroLocus K (Ideal.span
    {(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) -
      MvPolynomial.X (0 : Fin 2) ^ 2}) at hx
  rw [MvPolynomial.zeroLocus_span] at hx
  have heq := hx _ (Set.mem_singleton _)
  simpa only [map_sub, map_pow, MvPolynomial.aeval_X, sub_eq_zero] using heq

private theorem parabolaProjection_graph (x : MvPolynomial.ZariskiSpace K (Fin 1)) :
    MvPolynomial.ZariskiSpace.substitution (parabolaProjectionHom K)
      (parabolaGraph K x).val = x := by
  apply MvPolynomial.ZariskiSpace.ext
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  change MvPolynomial.ZariskiSpace.substitution (parabolaProjectionHom K)
    (MvPolynomial.ZariskiSpace.substitution (parabolaGraphHom K) x) 0 = x 0
  simpa only [MvPolynomial.ZariskiSpace.substitution_apply, parabolaProjectionHom,
    MvPolynomial.aeval_X] using graph_first_coordinate K x

private theorem parabolaGraph_projection
    (x : MvPolynomial.ZariskiSpace.zeroLocus (parabolaIdeal K)) :
    parabolaGraph K (MvPolynomial.ZariskiSpace.substitution
      (parabolaProjectionHom K) x.val) = x := by
  apply Subtype.ext
  apply MvPolynomial.ZariskiSpace.ext
  intro i
  fin_cases i
  · simp [parabolaGraph, parabolaGraphHom, parabolaProjectionHom]
  · simpa [parabolaGraph, parabolaGraphHom, parabolaProjectionHom] using
      (parabola_equation K x).symm

private def parabolaPoint (t : K) :
    MvPolynomial.ZariskiSpace.zeroLocus (parabolaIdeal K) :=
  parabolaGraph K ⟨fun _ => t⟩

private theorem parabolaPoint_coordinates (t : K) :
    (parabolaPoint K t).val 1 = (parabolaPoint K t).val 0 ^ 2 := by
  exact parabola_equation K (parabolaPoint K t)

private theorem parabolaGraph_closedPoint_equation [IsAlgClosed K]
    (x : MvPolynomial.ZariskiSpace K (Fin 1)) :
    Ideal.Quotient.mkₐ K (parabolaIdeal K)
      (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (x 0 ^ 2)) ∈
        (MvPolynomial.ZariskiSpace.zeroLocusHomeomorphClosedPoints
          (parabolaIdeal K) (parabolaGraph K x)).val.asIdeal := by
  rw [MvPolynomial.ZariskiSpace.zeroLocusHomeomorphClosedPoints_apply,
    MvPolynomial.ZariskiSpace.zeroLocusClosedPoint_mem_iff]
  simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Algebra.algebraMap_self_apply, parabolaGraph, graph_second_coordinate, sub_self]

private theorem parabolaPoint_membership [IsAlgClosed K] (t : K) :
    Ideal.Quotient.mkₐ K (parabolaIdeal K)
      (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (t ^ 2)) ∈
        (MvPolynomial.ZariskiSpace.zeroLocusHomeomorphClosedPoints
          (parabolaIdeal K) (parabolaPoint K t)).val.asIdeal := by
  simpa [parabolaPoint] using parabolaGraph_closedPoint_equation K
    (⟨fun _ => t⟩ : MvPolynomial.ZariskiSpace K (Fin 1))

/-- The unit ideal has no coordinate zeros, even without variables. -/
theorem unit_zeroLocus_empty {σ : Type*} :
    IsEmpty (MvPolynomial.ZariskiSpace.zeroLocus
      (⊤ : Ideal (MvPolynomial σ K))) := by
  constructor
  intro x
  have hx : x.val.toFun ∈ MvPolynomial.zeroLocus K
      (⊤ : Ideal (MvPolynomial σ K)) := x.property
  simp at hx

private theorem empty_variable_zeroLocus_nonempty :
    Nonempty (MvPolynomial.ZariskiSpace.zeroLocus
      (⊥ : Ideal (MvPolynomial (Fin 0) K))) :=
  ⟨⟨⟨fun i => i.elim0⟩, by simp⟩⟩

private def squareZeroIdeal : Ideal (MvPolynomial (Fin 1) K) :=
  Ideal.span {(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2}

private def squareZeroPoint : MvPolynomial.ZariskiSpace.zeroLocus (squareZeroIdeal K) :=
  ⟨⟨fun _ => 0⟩, by simp [squareZeroIdeal, MvPolynomial.zeroLocus_span]⟩

private theorem squareZero_X_not_mem :
    (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ∉ squareZeroIdeal K := by
  intro hx
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.mp hx
  have heps : (DualNumber.eps : DualNumber K) = 0 := by
    have h := congrArg (fun q : MvPolynomial (Fin 1) K =>
      MvPolynomial.aeval (fun _ : Fin 1 => (DualNumber.eps : DualNumber K)) q) hp
    simpa only [map_mul, map_pow, MvPolynomial.aeval_X,
      DualNumber.eps_pow_two, mul_zero] using h.symm
  have hone : (1 : K) = 0 := by
    simpa using congrArg TrivSqZeroExt.snd heps
  exact one_ne_zero hone

private theorem squareZero_class_nonzero :
    Ideal.Quotient.mkₐ K (squareZeroIdeal K)
      (MvPolynomial.X (0 : Fin 1)) ≠ 0 := by
  intro hx
  exact squareZero_X_not_mem K (Ideal.Quotient.eq_zero_iff_mem.mp hx)

private theorem squareZero_class_square_zero :
    (Ideal.Quotient.mkₐ K (squareZeroIdeal K)
      (MvPolynomial.X (0 : Fin 1))) ^ 2 = 0 := by
  have hx : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2 ∈
      squareZeroIdeal K := Ideal.mem_span_singleton_self _
  have hzero : Ideal.Quotient.mkₐ K (squareZeroIdeal K)
      ((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  simpa only [map_pow] using hzero

private theorem squareZero_quotient_not_reduced :
    ¬ IsReduced (MvPolynomial (Fin 1) K ⧸ squareZeroIdeal K) := by
  intro h
  have : IsReduced (MvPolynomial (Fin 1) K ⧸ squareZeroIdeal K) := h
  exact squareZero_class_nonzero K (eq_zero_of_pow_eq_zero (squareZero_class_square_zero K))

private theorem squareZero_closedPoint_nilpotent [IsAlgClosed K] :
    ∃ q : MvPolynomial (Fin 1) K ⧸ squareZeroIdeal K,
      q ≠ 0 ∧ q ^ 2 = 0 ∧
        q ∈ (MvPolynomial.ZariskiSpace.zeroLocusHomeomorphClosedPoints
          (squareZeroIdeal K) (squareZeroPoint K)).val.asIdeal := by
  refine ⟨Ideal.Quotient.mkₐ K (squareZeroIdeal K) (MvPolynomial.X (0 : Fin 1)),
    squareZero_class_nonzero K, squareZero_class_square_zero K, ?_⟩
  rw [MvPolynomial.ZariskiSpace.zeroLocusHomeomorphClosedPoints_apply,
    MvPolynomial.ZariskiSpace.zeroLocusClosedPoint_mem_iff]
  simp [squareZeroPoint]

private def rationalQuadraticIdeal : Ideal (MvPolynomial (Fin 1) ℚ) :=
  Ideal.span {(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ^ 2 + 1}

private theorem rational_quadratic_zeroLocus_empty :
    IsEmpty (MvPolynomial.ZariskiSpace.zeroLocus
      rationalQuadraticIdeal) := by
  constructor
  intro x
  have hx : x.val.toFun ∈ MvPolynomial.zeroLocus ℚ
      rationalQuadraticIdeal :=
    x.property
  change x.val.toFun ∈ MvPolynomial.zeroLocus ℚ (Ideal.span
    {(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ^ 2 + 1}) at hx
  rw [MvPolynomial.zeroLocus_span] at hx
  have h := hx _ (Set.mem_singleton _)
  simp only [map_add, map_pow, MvPolynomial.aeval_X, map_one] at h
  nlinarith [sq_nonneg (x.val 0)]

private theorem rationalQuadraticIdeal_ne_top : rationalQuadraticIdeal ≠ ⊤ := by
  have hker : rationalQuadraticIdeal ≤
      RingHom.ker (MvPolynomial.aeval
        (fun _ : Fin 1 => Complex.I)).toRingHom := by
    change Ideal.span
      {(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ^ 2 + 1} ≤ _
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ^ 2 + 1 := hp
    subst p
    simp [RingHom.mem_ker, Complex.I_sq]
  apply (Ideal.ne_top_iff_one rationalQuadraticIdeal).mpr
  intro hone
  have hzero : (1 : ℂ) = 0 := by
    simpa only [RingHom.mem_ker, map_one] using hker hone
  exact one_ne_zero hzero

private theorem rational_quadratic_quotient_closedPoint :
    Nonempty (closedPoints (PrimeSpectrum
      (MvPolynomial (Fin 1) ℚ ⧸ rationalQuadraticIdeal))) := by
  have : Nontrivial (MvPolynomial (Fin 1) ℚ ⧸ rationalQuadraticIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr rationalQuadraticIdeal_ne_top
  obtain ⟨maxIdeal, hmaxIdeal⟩ :=
    Ideal.exists_maximal (MvPolynomial (Fin 1) ℚ ⧸ rationalQuadraticIdeal)
  exact ⟨⟨⟨maxIdeal, hmaxIdeal.isPrime⟩,
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmaxIdeal⟩⟩

private theorem rational_quadratic_evaluation_not_surjective :
    ¬ Function.Surjective (MvPolynomial.ZariskiSpace.zeroLocusClosedPoint
      rationalQuadraticIdeal) := by
  intro hsurj
  obtain ⟨point⟩ := rational_quadratic_quotient_closedPoint
  obtain ⟨x, _⟩ := hsurj point
  have : IsEmpty (MvPolynomial.ZariskiSpace.zeroLocus rationalQuadraticIdeal) :=
    rational_quadratic_zeroLocus_empty
  exact isEmptyElim x

end MultivariatePolynomialsTests
