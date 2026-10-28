/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IdealOfVars
public import Mathlib.RingTheory.Polynomial.Basic

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Data.Matrix.Basis

/-!
# Noetherian polynomial semirings

Over a nontrivial commutative semiring, Noetherianity of the multivariate
polynomial semiring forces the variable type to be finite. Over a commutative
ring, the polynomial ring is Noetherian exactly when its coefficient ring is
Noetherian and either the variable type is finite or the coefficient ring is
trivial. In the nontrivial case, the trivial-ring alternative disappears.

As a module over the coefficient semiring, the polynomial semiring is Noetherian
exactly when its coefficients are Noetherian and either there are no variables
or the coefficient semiring is trivial. This holds for arbitrary commutative
semirings: even one variable over nontrivial coefficients gives infinitely many
linearly independent monomials. In contrast to the self-module criterion,
finitely many nonempty variables do not suffice for the coefficient action.

The coefficient and variable types have independent universes. Empty variables
recover the coefficient ring. The finite-variable implication for commutative
rings is Mathlib's Hilbert basis theorem; no analogous sufficiency statement for
arbitrary commutative semirings is asserted here. The univariate negative result
concerns nontrivial semirings whose only additive unit is zero, with Noetherianity
understood for the left self-module.

For an arbitrary ring, left Noetherianity of the coefficient ring implies left
Noetherianity of its univariate polynomial ring, generalizing Mathlib's
commutative-ring Hilbert basis theorem. The proof uses Mathlib's coefficient-image
ideals, stabilization of ascending chains of submodules, and the coefficient
linear equivalence for bounded-degree polynomials. Powers of the central variable
act on the left, so all ideal-membership arguments apply to left ideals.

## References

* Mathlib, `Mathlib.RingTheory.Polynomial.Basic`: `MvPolynomial.isNoetherianRing`,
  the finite-variable Hilbert basis theorem.
* Mathlib, `Mathlib.RingTheory.Polynomial.Basic`: `Polynomial.isNoetherianRing`,
  the commutative-ring univariate Hilbert basis theorem.
* Mathlib, `Mathlib.RingTheory.Noetherian.Defs` and
  `Mathlib.RingTheory.Noetherian.Basic`: the ideal finite-generation criterion,
  descent along surjective ring homomorphisms, transfer along injective linear
  maps and linear equivalences, and the trivial-coefficient case.
* Mathlib, `Mathlib.RingTheory.MvPolynomial.Basic`: the coefficient-linear
  monomial basis; `Mathlib.RingTheory.Finiteness.Cardinality`: an infinite basis
  obstructs finite generation of a module over nontrivial coefficients.
* `MultivariatePolynomials.IdealOfVars`: finite generation of ideals generated
  by subsets of variables over nontrivial commutative semirings.
* Mathlib, `Mathlib.NumberTheory.FrobeniusNumber`: Noetherianity of the regular
  natural-number semimodule.
* Mathlib, `Mathlib.Data.Matrix.Basis`: matrix units and their products.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- The multivariate polynomial semiring is Noetherian as a module over its
coefficient semiring exactly when the coefficient semiring is Noetherian and
either there are no variables or the coefficient semiring is trivial. The scalar
action is the canonical coefficient action, not polynomial multiplication as a
self-module. In particular, finitely many nonempty variables do not suffice for
nontrivial coefficients. -/
theorem isNoetherian_iff
    {σ : Type u} {R : Type v} [CommSemiring R] :
    IsNoetherian R (MvPolynomial σ R) ↔
      IsNoetherianRing R ∧ (IsEmpty σ ∨ Subsingleton R) := by
  constructor
  · intro h
    let : IsNoetherian R (MvPolynomial σ R) := h
    have hR : IsNoetherianRing R :=
      isNoetherian_of_injective (monomial (0 : σ →₀ ℕ)) (C_injective σ R)
    refine ⟨hR, ?_⟩
    rcases subsingleton_or_nontrivial R with hsub | hnontriv
    · exact Or.inr hsub
    · let : Nontrivial R := hnontriv
      refine Or.inl ⟨fun x => ?_⟩
      let : Nonempty σ := ⟨x⟩
      exact Module.not_finite_of_infinite_basis (basisMonomials σ R)
        (inferInstance : Module.Finite R (MvPolynomial σ R))
  · rintro ⟨hR, hσ | hsub⟩
    · let : IsNoetherianRing R := hR
      let : IsEmpty σ := hσ
      exact isNoetherian_of_linearEquiv (isEmptyAlgEquiv R σ).toLinearEquiv.symm
    · let : Subsingleton R := hsub
      exact isNoetherian_of_subsingleton R (MvPolynomial σ R)

-- Empty variables preserve the regular coefficient module. In particular, this
-- applies to the natural-number semiring, using Mathlib's Frobenius provider.
example : IsNoetherian ℕ (MvPolynomial Empty ℕ) := by
  exact MvPolynomial.isNoetherian_iff.mpr ⟨inferInstance, Or.inl inferInstance⟩

-- Trivial coefficients allow arbitrary variables, including infinitely many.
example : IsNoetherian (ZMod 1) (MvPolynomial ℕ (ZMod 1)) := by
  exact MvPolynomial.isNoetherian_iff.mpr ⟨inferInstance, Or.inr inferInstance⟩

-- Two integer variables give a Noetherian polynomial ring for its self-action,
-- but not for its coefficient action: even one variable is an obstruction.
example : ¬ IsNoetherian ℤ (MvPolynomial (Fin 2) ℤ) := by
  intro h
  rcases (MvPolynomial.isNoetherian_iff.mp h).2 with hσ | hR
  · exact hσ.false 0
  · exact (not_subsingleton ℤ) hR

/-- Over a nontrivial commutative semiring, Noetherianity of the multivariate
polynomial semiring forces the variable type to be finite. This is a theorem,
not an instance, so it does not form a typeclass cycle with finite-variable
Noetherianity. The coefficient semiring need not be a ring or a domain. -/
theorem finite_of_isNoetherianRing
    {σ : Type u} {R : Type v} [CommSemiring R] [Nontrivial R]
    [IsNoetherianRing (MvPolynomial σ R)] : Finite σ := by
  exact Set.finite_univ_iff.mp
    ((ideal_span_X_image_fg_iff (R := R) (Set.univ : Set σ)).mp
      (Ideal.fg_of_isNoetherianRing _))

/-- A multivariate polynomial ring is Noetherian exactly when its coefficient
ring is Noetherian and either its variable type is finite or its coefficient
ring is trivial. The trivial-ring alternative is essential for infinitely many
variables. The finite-variable implication is Mathlib's Hilbert basis theorem. -/
theorem isNoetherianRing_iff
    {σ : Type u} {R : Type v} [CommRing R] :
    IsNoetherianRing (MvPolynomial σ R) ↔
      IsNoetherianRing R ∧ (Finite σ ∨ Subsingleton R) := by
  constructor
  · intro h
    let : IsNoetherianRing (MvPolynomial σ R) := h
    have hR : IsNoetherianRing R :=
      isNoetherianRing_of_surjective (MvPolynomial σ R) R constantCoeff
        (fun r => ⟨C r, constantCoeff_C σ r⟩)
    refine ⟨hR, ?_⟩
    rcases subsingleton_or_nontrivial R with hsub | hnontriv
    · exact Or.inr hsub
    · let : Nontrivial R := hnontriv
      exact Or.inl (finite_of_isNoetherianRing (σ := σ) (R := R))
  · rintro ⟨hR, hσ | hsub⟩
    · let : IsNoetherianRing R := hR
      let : Finite σ := hσ
      infer_instance
    · let : Subsingleton R := hsub
      infer_instance

/-- Over a nontrivial commutative ring, a multivariate polynomial ring is
Noetherian exactly when its coefficient ring is Noetherian and its variable type
is finite. This form eliminates the trivial-ring alternative for applications
with nontrivial coefficients, including coefficient rings with zero divisors. -/
theorem isNoetherianRing_iff_of_nontrivial
    {σ : Type u} {R : Type v} [CommRing R] [Nontrivial R] :
    IsNoetherianRing (MvPolynomial σ R) ↔
      IsNoetherianRing R ∧ Finite σ := by
  exact isNoetherianRing_iff.trans
    (and_congr_right fun _ => or_iff_left (not_subsingleton R))

-- The coefficient condition is already known for ZMod 6, despite its nonzero
-- zero divisors 2 and 3. Only finiteness of the variable type remains.
example {σ : Type u} :
    IsNoetherianRing (MvPolynomial σ (ZMod 6)) ↔ Finite σ := by
  let : Fact (1 < 6) := ⟨by decide⟩
  constructor
  · intro h
    exact (MvPolynomial.isNoetherianRing_iff_of_nontrivial.mp h).2
  · intro h
    exact MvPolynomial.isNoetherianRing_iff_of_nontrivial.mpr ⟨inferInstance, h⟩

-- With infinitely many variables, the full criterion forces the coefficient
-- ring to be trivial; no nontriviality premise is appropriate here.
example {R : Type v} [CommRing R] [IsNoetherianRing (MvPolynomial ℕ R)] :
    (1 : R) = 0 := by
  have hsub : Subsingleton R :=
    (MvPolynomial.isNoetherianRing_iff.mp
      (inferInstance : IsNoetherianRing (MvPolynomial ℕ R))).2.resolve_left
        Infinite.not_finite
  exact @Subsingleton.elim R hsub 1 0

end MvPolynomial

namespace Polynomial

/-- A polynomial semiring is Noetherian as a module over its coefficient semiring
exactly when the coefficient semiring is subsingleton. The scalar action is the
canonical left coefficient action, and coefficient multiplication need not commute. -/
theorem isNoetherian_iff (R : Type u) [Semiring R] :
    IsNoetherian R (Polynomial R) ↔ Subsingleton R := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hsub | hnontriv
    · exact hsub
    · let : Nontrivial R := hnontriv
      let : IsNoetherian R (Polynomial R) := h
      exact (Polynomial.not_finite (R := R)
        (Module.IsNoetherian.finite R (Polynomial R))).elim
  · intro h
    let : Subsingleton R := h
    exact isNoetherian_of_subsingleton R (Polynomial R)

private theorem mem_leadingCoeffNth_iff_coeff
    {R : Type u} [Semiring R] (I : Ideal (Polynomial R)) (n : ℕ) (r : R) :
    r ∈ I.leadingCoeffNth n ↔
      ∃ p : Polynomial R, p.degree ≤ n ∧ p ∈ I ∧ p.coeff n = r := by
  simp only [Ideal.leadingCoeffNth, Ideal.degreeLE, Submodule.mem_map,
    Submodule.mem_inf, mem_degreeLE, Ideal.mem_ofPolynomial, lcoeff_apply, and_assoc]

-- Shifting by a power of the central variable preserves a left ideal. In
-- particular, this does not use closure under right multiplication by coefficients.
private theorem leadingCoeffNth_mono_of_le
    {R : Type u} [Semiring R] (I : Ideal (Polynomial R)) {m n : ℕ} (hmn : m ≤ n) :
    I.leadingCoeffNth m ≤ I.leadingCoeffNth n := by
  intro r hr
  obtain ⟨p, hpdeg, hpI, hpr⟩ := (mem_leadingCoeffNth_iff_coeff I m r).mp hr
  apply (mem_leadingCoeffNth_iff_coeff I n r).mpr
  refine ⟨X ^ (n - m) * p, ?_, I.mul_mem_left _ hpI, ?_⟩
  · calc
      (X ^ (n - m) * p).degree ≤ ((n - m : ℕ) : WithBot ℕ) + (m : WithBot ℕ) :=
        degree_mul_le_of_le (degree_X_pow_le _) hpdeg
      _ = (n : WithBot ℕ) := by rw [← Nat.cast_add, tsub_add_cancel_of_le hmn]
  · simpa only [add_tsub_cancel_of_le hmn] using
      (coeff_X_pow_mul p (n - m) m).trans hpr

/-- A polynomial ring over a left-Noetherian ring is left-Noetherian. The variable
is central, and coefficient multiplication need not be commutative. This
generalizes Mathlib's commutative-ring Hilbert basis theorem
`Polynomial.isNoetherianRing`. It is registered as an instance at priority 100,
so Mathlib's commutative-ring instance is preferred when available. The theorem
can also be applied explicitly. -/
theorem isNoetherianRing_of_isNoetherianRing
    {R : Type u} [Ring R] [IsNoetherianRing R] : IsNoetherianRing (Polynomial R) := by
  classical
  apply (isNoetherianRing_iff_ideal_fg (Polynomial R)).mpr
  intro I
  -- The coefficient images form an ascending chain in the Noetherian left
  -- self-module of R. Beyond N, every top coefficient comes from degree ≤ N.
  let coefficients : ℕ →o Ideal R :=
    ⟨I.leadingCoeffNth, fun _ _ h => leadingCoeffNth_mono_of_le I h⟩
  obtain ⟨N, hN⟩ :=
    monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherianRing R) coefficients
  -- Bounded-degree polynomials are a finite free coefficient module, although
  -- the full polynomial ring need not be finite as a coefficient module.
  have hnoeth : IsNoetherian R (Polynomial.degreeLE R (N : WithBot ℕ)) := by
    rw [← degreeLT_succ_eq_degreeLE]
    exact isNoetherian_of_linearEquiv (degreeLTEquiv R (N + 1)).symm
  have hfg : (I.degreeLE N).FG :=
    (isNoetherian_submodule_left.mp hnoeth) I.ofPolynomial
  obtain ⟨s, hs⟩ := hfg
  let J : Ideal (Polynomial R) := Ideal.span (s : Set (Polynomial R))
  have hbounded : I.degreeLE N ≤ J.ofPolynomial := by
    rw [← hs]
    exact Submodule.span_le.mpr fun p hp => Ideal.subset_span hp
  refine ⟨s, ?_⟩
  change J = I
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    have hps : p ∈ I.degreeLE N := hs ▸ Submodule.subset_span hp
    exact hps.2
  · have hmem : ∀ n, ∀ p : Polynomial R, p.natDegree = n → p ∈ I → p ∈ J := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro p hn hp
        have hpdeg : p.degree ≤ (n : WithBot ℕ) := by
          rw [← hn]
          exact degree_le_natDegree
        by_cases hnN : n ≤ N
        · exact hbounded ⟨mem_degreeLE.mpr
            (hpdeg.trans (WithBot.coe_le_coe.mpr hnN)), hp⟩
        · have hNn : N ≤ n := (lt_of_not_ge hnN).le
          have hstabilize : I.leadingCoeffNth N = I.leadingCoeffNth n := hN n hNn
          have hc : p.coeff n ∈ I.leadingCoeffNth N := by
            rw [hstabilize]
            exact (mem_leadingCoeffNth_iff_coeff I n (p.coeff n)).mpr
              ⟨p, hpdeg, hp, rfl⟩
          obtain ⟨q, hqdeg, hqI, hqc⟩ :=
            (mem_leadingCoeffNth_iff_coeff I N (p.coeff n)).mp hc
          let qshift : Polynomial R := X ^ (n - N) * q
          have hqshiftI : qshift ∈ I := I.mul_mem_left _ hqI
          have hqshiftJ : qshift ∈ J :=
            J.mul_mem_left _ (hbounded ⟨mem_degreeLE.mpr hqdeg, hqI⟩)
          have hqshiftdeg : qshift.degree ≤ (n : WithBot ℕ) := by
            calc
              qshift.degree ≤ ((n - N : ℕ) : WithBot ℕ) + (N : WithBot ℕ) :=
                degree_mul_le_of_le (degree_X_pow_le _) hqdeg
              _ = (n : WithBot ℕ) := by
                rw [← Nat.cast_add, tsub_add_cancel_of_le hNn]
          have hqshiftcoeff : qshift.coeff n = p.coeff n := by
            simpa only [qshift, add_tsub_cancel_of_le hNn] using
              (coeff_X_pow_mul q (n - N) N).trans hqc
          -- Cancelling the top coefficient strictly lowers the degree; the
          -- argument also covers zero rings and coefficients with zero divisors.
          have hsubdeg : (p - qshift).degree < (n : WithBot ℕ) := by
            apply (degree_lt_iff_coeff_zero _ _).mpr
            intro m hnm
            rcases hnm.eq_or_lt with hnm | hnm
            · subst m
              rw [coeff_sub, hqshiftcoeff, sub_self]
            · have hm : (n : WithBot ℕ) < (m : WithBot ℕ) :=
                WithBot.coe_lt_coe.mpr hnm
              rw [coeff_sub, coeff_eq_zero_of_degree_lt (hpdeg.trans_lt hm),
                coeff_eq_zero_of_degree_lt (hqshiftdeg.trans_lt hm), sub_self]
          have hsubJ : p - qshift ∈ J := by
            by_cases hzero : p - qshift = 0
            · rw [hzero]
              exact J.zero_mem
            · exact ih (p - qshift).natDegree
                ((natDegree_lt_iff_degree_lt hzero).mpr hsubdeg)
                (p - qshift) rfl (I.sub_mem hp hqshiftI)
          simpa only [sub_add_cancel] using J.add_mem hsubJ hqshiftJ
    exact fun p hp => hmem p.natDegree p rfl hp

attribute [instance 100] isNoetherianRing_of_isNoetherianRing

/-- On commutative rings, the general Hilbert basis theorem agrees with Mathlib's
`Polynomial.isNoetherianRing`. -/
theorem isNoetherianRing_of_isNoetherianRing_eq_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    isNoetherianRing_of_isNoetherianRing (R := R) =
      Polynomial.isNoetherianRing (R := R) := by
  exact Subsingleton.elim _ _

-- For the usual matrix multiplication, E01 * E10 and E10 * E01 differ at
-- entry (0,0). Thus this Hilbert basis application uses genuinely noncommutative
-- coefficients. The polynomial ring is Noetherian for its regular left action,
-- not for the matrix coefficient action, even though the matrix ring is finite.
example :
    IsNoetherianRing
      (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) := by
  let : IsNoetherianRing (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
    isNoetherian_of_finite
      (Matrix (Fin 2) (Fin 2) (ZMod 2))
      (Matrix (Fin 2) (Fin 2) (ZMod 2))
  exact Polynomial.isNoetherianRing_of_isNoetherianRing
    (R := Matrix (Fin 2) (Fin 2) (ZMod 2))

-- A zero coefficient at the generator's positive exponent forces the left
-- multiplier's constant coefficient to vanish: there is no additive cancellation.
private theorem coeff_zero_of_mul_one_add_X_pow
    {R : Type u} [Semiring R] [Subsingleton (AddUnits R)]
    (a : Polynomial R) (n : ℕ)
    (h : (a * (1 + X ^ (n + 1))).coeff (n + 1) = 0) : a.coeff 0 = 0 := by
  have hshift : (a * X ^ (n + 1)).coeff (n + 1) = a.coeff 0 := by
    simpa only [zero_add] using coeff_mul_X_pow a (n + 1) 0
  rw [mul_add, mul_one, coeff_add, hshift] at h
  have hu : IsAddUnit (a.coeff (n + 1) + a.coeff 0) := by
    rw [h]
    exact isAddUnit_zero
  exact (IsAddUnit.add_iff.mp hu).2.eq_zero

/-- A polynomial semiring over a nontrivial semiring whose only additive unit is
zero is not Noetherian as a left module over itself. Multiplication of the
coefficient semiring need not be commutative. -/
theorem not_isNoetherianRing_of_subsingleton_addUnits
    {R : Type u} [Semiring R] [Nontrivial R] [Subsingleton (AddUnits R)] :
    ¬ IsNoetherianRing (Polynomial R) := by
  classical
  intro hNoeth
  let : IsNoetherianRing (Polynomial R) := hNoeth
  let g : ℕ → Polynomial R := fun n => 1 + X ^ (n + 1)
  -- Finite generation gives a finite subset of the original generators, not
  -- merely an arbitrary finite generating family of the same left ideal.
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := Polynomial R) (Set.range g)).mp
      (Ideal.fg_of_isNoetherianRing (Ideal.span (Set.range g)))
  have hfamily : ∀ p : s, ∃ n : ℕ, g n = p.1 := fun p => hs p.2
  choose n hn using hfamily
  let N : ℕ := (Finset.univ.sup fun p : s => n p + 1) + 1
  have hlt (p : s) : n p + 1 < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun p : s => n p + 1) (Finset.mem_univ p))
  have hN : 0 < N := Nat.zero_lt_succ _
  have hmem : (1 + X ^ N : Polynomial R) ∈
      Submodule.span (Polynomial R) (s : Set (Polynomial R)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨Finset.univ.sup (fun p : s => n p + 1), rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp hmem
  have hsum : ∑ p : s, a p * (1 + X ^ (n p + 1)) = (1 + X ^ N : Polynomial R) := by
    simpa only [← hn, g, smul_eq_mul] using ha
  have ha0 (p : s) : (a p).coeff 0 = 0 := by
    have hz : (∑ q : s, a q * (1 + X ^ (n q + 1))).coeff (n p + 1) = 0 := by
      rw [hsum]
      simp [coeff_one, (hlt p).ne]
    rw [finsetSum_coeff] at hz
    have hp := (Finset.sum_eq_zero_iff.mp hz) p (Finset.mem_univ p)
    exact coeff_zero_of_mul_one_add_X_pow (a p) (n p) hp
  have h10 : (1 : R) = 0 := by
    have hc := congrArg (fun p : Polynomial R => p.coeff 0) hsum
    simpa [ha0, coeff_one, hN.ne'] using hc.symm
  exact one_ne_zero h10

end Polynomial
