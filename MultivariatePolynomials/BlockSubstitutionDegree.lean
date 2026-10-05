/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.BlockSubstitution
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Exact degree of substitution into disjoint variable blocks

The public theorem covers arbitrary polynomial and index types, including zero and
constant inputs, over commutative semirings without zero divisors.

## References

* `MultivariatePolynomials.BlockSubstitution`: the disjoint-block substitution.
* Mathlib, `Mathlib.RingTheory.MvPolynomial.Homogeneous` (homogeneous
  components) and `Mathlib.Algebra.MvPolynomial.NoZeroDivisors` (nonzero
  products). The exact-degree argument combines these for disjoint blocks.

-/

@[expose] public section

set_option warningAsError true

namespace MvPolynomial

universe u v w

variable {I : Type u} {J : Type v} {R : Type w} [CommSemiring R]

private theorem totalDegree_rename_block (i : I) (q : MvPolynomial J R) :
    (rename (Prod.mk i) q).totalDegree = q.totalDegree := by
  rw [← weightedTotalDegree_one (rename (Prod.mk i) q),
    weightedTotalDegree_rename_of_injective (fun _ _ h => Prod.mk.inj h |>.2)]
  change weightedTotalDegree (1 : J → ℕ) q = q.totalDegree
  exact weightedTotalDegree_one q

private noncomputable def blockWeight (x : I × J) : I →₀ ℕ := Finsupp.single x.1 1

private theorem blockWeight_map (i : I) (a : J →₀ ℕ) :
    Finsupp.weight (blockWeight (I := I) (J := J)) (a.mapDomain (Prod.mk i)) =
      Finsupp.single i a.degree := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_nsmul])]
  ext k
  by_cases h : i = k <;> simp [h, Finsupp.sum, Finsupp.degree_apply, blockWeight]

private theorem blockWeight_rename (i : I) (q : MvPolynomial J R) (e : ℕ)
    (hq : q.IsHomogeneous e) :
    (rename (Prod.mk i) q).IsWeightedHomogeneous (blockWeight (I := I) (J := J))
      (Finsupp.single i e) := by
  classical
  intro d hd
  obtain ⟨a, rfl, ha⟩ := coeff_rename_ne_zero (Prod.mk i) q d hd
  rw [blockWeight_map]
  have hdeg : a.degree = e := by
    simpa [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using hq ha
  rw [hdeg]

private theorem blockWeight_profile (a : I →₀ ℕ) (e : ℕ) :
    (∑ i ∈ a.support, a i • Finsupp.single i e) = e • a := by
  classical
  calc
    (∑ i ∈ a.support, a i • Finsupp.single i e) =
        ∑ i ∈ a.support, e • Finsupp.single i (a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finsupp.smul_single]
          congr 1
          simp [mul_comm]
    _ = e • (∑ i ∈ a.support, Finsupp.single i (a i)) := by rw [Finset.smul_sum]
    _ = e • a := congrArg (e • ·) (Finsupp.sum_single a)

private noncomputable def topTerm (a : I →₀ ℕ) (r : R) (q : MvPolynomial J R) :
    MvPolynomial (I × J) R :=
  C r * ∏ i ∈ a.support, (rename (Prod.mk i) q) ^ a i

private theorem topTerm_homogeneous (a : I →₀ ℕ) (r : R)
    (q : MvPolynomial J R) (e : ℕ) (hq : q.IsHomogeneous e) :
    (topTerm a r q).IsWeightedHomogeneous (blockWeight (I := I) (J := J)) (e • a) := by
  have hprod := IsWeightedHomogeneous.prod a.support
    (fun i => (rename (Prod.mk i) q) ^ a i)
    (fun i => a i • Finsupp.single i e) (by
      intro i hi
      exact (blockWeight_rename i q e hq).pow (a i))
  simpa only [topTerm, blockWeight_profile] using hprod.C_mul r

private theorem topTerm_ne_zero [NoZeroDivisors R] (a : I →₀ ℕ) (r : R)
    (q : MvPolynomial J R) (hr : r ≠ 0) (hq : q ≠ 0) : topTerm a r q ≠ 0 := by
  classical
  let : Nontrivial R := nontrivial_iff.mpr ⟨r, 0, hr⟩
  unfold topTerm
  apply mul_ne_zero (by
    intro hc
    apply hr
    exact (C_injective (I × J) R) (by simpa only [map_zero] using hc))
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  exact fun hz => hq ((rename_eq_zero_iff_of_injective q (by
    intro _ _ h
    exact (Prod.mk.inj h).2)).mp hz)

private theorem topTerms_ne_zero [NoZeroDivisors R] (p : MvPolynomial I R)
    (q : MvPolynomial J R) (e : ℕ) (he : 0 < e) (hq : q.IsHomogeneous e)
    (hq0 : q ≠ 0) (hp : p ≠ 0) :
    (∑ a ∈ p.support, topTerm a (p.coeff a) q) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero hp
  have has : a ∈ p.support := mem_support_iff.mpr ha
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero (topTerm_ne_zero a (p.coeff a) q ha hq0)
  have hwa := topTerm_homogeneous a (p.coeff a) q e hq hd
  intro hz
  have hcoeff := congrArg (fun f : MvPolynomial (I × J) R => f.coeff d) hz
  rw [coeff_sum] at hcoeff
  have hs : (∑ b ∈ p.support, (topTerm b (p.coeff b) q).coeff d) =
      (topTerm a (p.coeff a) q).coeff d := by
    apply Finset.sum_eq_single a
    · intro b hb hba
      apply (topTerm_homogeneous b (p.coeff b) q e hq).coeff_eq_zero d
      intro hwb
      apply hba
      ext i
      have hi := congrArg (fun f : I →₀ ℕ => f i) (hwa.symm.trans hwb)
      exact (Nat.eq_of_mul_eq_mul_left he (by simpa only [Finsupp.smul_apply,
        nsmul_eq_mul, Nat.cast_id] using hi)).symm
    · intro hna
      exact (hna has).elim
  rw [hs] at hcoeff
  exact hd hcoeff

private theorem homogeneousComponent_mul_top {K : Type*} (f g : MvPolynomial K R)
    (m n : ℕ) (hf : f.totalDegree ≤ m) (hg : g.totalDegree ≤ n) :
    homogeneousComponent (m + n) (f * g) =
      homogeneousComponent m f * homogeneousComponent n g := by
  classical
  ext d
  rw [coeff_homogeneousComponent]
  by_cases hd : d.degree = m + n
  · simp only [hd, ite_true, coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ hab
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases ha : f.coeff a = 0
    · simp [ha]
    by_cases hb : g.coeff b = 0
    · simp [hb]
    have ha_le : a.degree ≤ m := by
      calc
        a.degree ≤ f.totalDegree := by simpa only [Finsupp.degree_apply, Finsupp.sum] using
          (le_totalDegree (mem_support_iff.mpr ha))
        _ ≤ m := hf
    have hb_le : b.degree ≤ n := by
      calc
        b.degree ≤ g.totalDegree := by simpa only [Finsupp.degree_apply, Finsupp.sum] using
          (le_totalDegree (mem_support_iff.mpr hb))
        _ ≤ n := hg
    have hab' : a + b = d := Finset.mem_antidiagonal.mp hab
    have hadd : a.degree + b.degree = m + n := by
      rw [← hab', map_add] at hd
      exact hd
    have ham : a.degree = m := by omega
    have hbn : b.degree = n := by omega
    simp [ham, hbn]
  · simp only [hd, ite_false]
    exact (((homogeneousComponent_isHomogeneous m f).mul
      (homogeneousComponent_isHomogeneous n g)).coeff_eq_zero hd).symm

private theorem homogeneousComponent_pow_top {K : Type*} (f : MvPolynomial K R)
    (m n : ℕ) (hf : f.totalDegree ≤ m) :
    homogeneousComponent (n * m) (f ^ n) = (homogeneousComponent m f) ^ n := by
  induction n with
  | zero => simp [homogeneousComponent_zero]
  | succ n ih =>
    have hpow : (f ^ n).totalDegree ≤ n * m :=
      (totalDegree_pow f n).trans (Nat.mul_le_mul_left n hf)
    calc
      homogeneousComponent ((n + 1) * m) (f ^ (n + 1)) =
          homogeneousComponent (n * m + m) (f ^ n * f) := by
            rw [Nat.succ_mul, pow_succ]
      _ = homogeneousComponent (n * m) (f ^ n) * homogeneousComponent m f :=
        homogeneousComponent_mul_top (f ^ n) f (n * m) m hpow hf
      _ = (homogeneousComponent m f) ^ (n + 1) := by rw [ih, pow_succ]

private theorem homogeneousComponent_prod_top {K A : Type*}
    (s : Finset A) (f : A → MvPolynomial K R) (n : A → ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ n i) :
    homogeneousComponent (∑ i ∈ s, n i) (∏ i ∈ s, f i) =
      ∏ i ∈ s, homogeneousComponent (n i) (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [homogeneousComponent_zero]
  | @insert i s his ih =>
    have htail : ∀ j ∈ s, (f j).totalDegree ≤ n j := by
      intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, f j).totalDegree ≤ ∑ j ∈ s, n j :=
      (totalDegree_finsetProd s f).trans (Finset.sum_le_sum htail)
    simpa only [Finset.sum_insert his, Finset.prod_insert his,
      homogeneousComponent_mul_top (f i) (∏ j ∈ s, f j) (n i) (∑ j ∈ s, n j)
        (hf i (Finset.mem_insert_self i s)) hprod] using
      congrArg (fun x : MvPolynomial K R => homogeneousComponent (n i) (f i) * x)
        (ih htail)

private theorem homogeneousComponent_blockSubst_monomial
    (a : I →₀ ℕ) (r : R) (q : MvPolynomial J R) :
    homogeneousComponent (a.degree * q.totalDegree) (blockSubst (monomial a r) q) =
      topTerm a r (homogeneousComponent q.totalDegree q) := by
  classical
  change homogeneousComponent (a.degree * q.totalDegree)
      (bind₁ (fun i => rename (Prod.mk i) q) (monomial a r)) = _
  rw [bind₁_monomial, homogeneousComponent_C_mul]
  have hsum : a.degree * q.totalDegree = ∑ i ∈ a.support, a i * q.totalDegree := by
    rw [Finsupp.degree_apply, Finset.sum_mul]
  rw [hsum]
  rw [homogeneousComponent_prod_top a.support
    (fun i => (rename (Prod.mk i) q) ^ a i)
    (fun i => a i * q.totalDegree) (by
      intro i hi
      exact (totalDegree_pow _ _).trans (by rw [totalDegree_rename_block]))]
  change C r * (∏ i ∈ a.support,
    homogeneousComponent (a i * q.totalDegree) ((rename (Prod.mk i) q) ^ a i)) =
    C r * (∏ i ∈ a.support,
      (rename (Prod.mk i) (homogeneousComponent q.totalDegree q)) ^ a i)
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [homogeneousComponent_pow_top _ q.totalDegree (a i) (by rw [totalDegree_rename_block]),
    ← rename_homogeneousComponent]

private theorem totalDegree_blockSubst_le (p : MvPolynomial I R) (q : MvPolynomial J R) :
    (blockSubst p q).totalDegree ≤ p.totalDegree * q.totalDegree := by
  classical
  conv_lhs => rw [blockSubst, as_sum p, map_sum]
  apply totalDegree_finsetSum_le
  intro a ha
  rw [bind₁_monomial]
  calc
    (C (p.coeff a) * ∏ i ∈ a.support, (rename (Prod.mk i) q) ^ a i).totalDegree
        ≤ (∏ i ∈ a.support, (rename (Prod.mk i) q) ^ a i).totalDegree := by
          simpa only [totalDegree_C, zero_add] using
            totalDegree_mul (C (p.coeff a)) (∏ i ∈ a.support, (rename (Prod.mk i) q) ^ a i)
    _ ≤ ∑ i ∈ a.support, ((rename (Prod.mk i) q) ^ a i).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ a.support, a i * q.totalDegree := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [totalDegree_rename_block] using totalDegree_pow (rename (Prod.mk i) q) (a i)
    _ = a.degree * q.totalDegree := by rw [Finsupp.degree_apply, Finset.sum_mul]
    _ ≤ p.totalDegree * q.totalDegree := Nat.mul_le_mul_right _ (le_totalDegree ha)

private theorem homogeneousComponent_totalDegree_ne_zero {K : Type*}
    (p : MvPolynomial K R) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero hp
  have has : a ∈ p.support := mem_support_iff.mpr ha
  have hsupport : p.support.Nonempty := ⟨a, has⟩
  obtain ⟨b, hb, hmax⟩ := p.support.exists_mem_eq_sup hsupport
    (fun m : K →₀ ℕ => m.degree)
  have htotal : p.totalDegree = p.support.sup (fun m : K →₀ ℕ => m.degree) := by
    simp [totalDegree, Finsupp.degree_apply, Finsupp.sum]
  have hdegree : b.degree = p.totalDegree := by simpa only [← htotal] using hmax.symm
  have hmem : b ∈ (homogeneousComponent p.totalDegree p).support := by
    rw [support_homogeneousComponent]
    exact Finset.mem_filter.mpr ⟨hb, hdegree⟩
  intro hz
  simp [hz] at hmem

private theorem homogeneousComponent_blockSubst_top (p : MvPolynomial I R)
    (q : MvPolynomial J R) (he : 0 < q.totalDegree) :
    homogeneousComponent (p.totalDegree * q.totalDegree) (blockSubst p q) =
      ∑ a ∈ p.support with a.degree = p.totalDegree,
        topTerm a (p.coeff a) (homogeneousComponent q.totalDegree q) := by
  classical
  have hexpansion : blockSubst p q =
      ∑ a ∈ p.support, blockSubst (monomial a (p.coeff a)) q := by
    unfold blockSubst
    conv_lhs => rw [as_sum p, map_sum]
  rw [hexpansion, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases had : a.degree = p.totalDegree
  · simpa only [had, ite_true] using
      homogeneousComponent_blockSubst_monomial a (p.coeff a) q
  · have hlt : a.degree < p.totalDegree := by
      have hle : a.degree ≤ p.totalDegree := by
        simpa only [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree ha
      omega
    have hc : (blockSubst (monomial a (p.coeff a)) q).totalDegree ≤
        a.degree * q.totalDegree := by
      simpa only [totalDegree_monomial a (mem_support_iff.mp ha), Finsupp.degree_apply,
        Finsupp.sum] using totalDegree_blockSubst_le (monomial a (p.coeff a)) q
    have hdegree : (blockSubst (monomial a (p.coeff a)) q).totalDegree <
        p.totalDegree * q.totalDegree :=
      hc.trans_lt (Nat.mul_lt_mul_of_pos_right hlt he)
    simpa only [had, ite_false] using
      homogeneousComponent_eq_zero (p.totalDegree * q.totalDegree)
        (blockSubst (monomial a (p.coeff a)) q) hdegree

/-- Exact total degree under substitution into disjoint variable blocks. -/
theorem totalDegree_blockSubst [NoZeroDivisors R]
    (p : MvPolynomial I R) (q : MvPolynomial J R) :
    (blockSubst p q).totalDegree = p.totalDegree * q.totalDegree := by
  apply Nat.le_antisymm (totalDegree_blockSubst_le p q)
  by_cases he : q.totalDegree = 0
  · simp [he]
  by_cases hp : p = 0
  · simp [hp, blockSubst]
  have hepos : 0 < q.totalDegree := Nat.pos_of_ne_zero he
  have hq : q ≠ 0 := by
    intro hzero
    exact he (by simp [hzero])
  have hpTop := homogeneousComponent_totalDegree_ne_zero p hp
  have hqTop := homogeneousComponent_totalDegree_ne_zero q hq
  have hsum := topTerms_ne_zero (homogeneousComponent p.totalDegree p)
    (homogeneousComponent q.totalDegree q) q.totalDegree hepos
    (homogeneousComponent_isHomogeneous q.totalDegree q) hqTop hpTop
  have hsum' :
      (∑ a ∈ p.support with a.degree = p.totalDegree,
        topTerm a (p.coeff a) (homogeneousComponent q.totalDegree q)) ≠ 0 := by
    convert hsum using 1
    rw [support_homogeneousComponent]
    apply Finset.sum_congr rfl
    intro a ha
    rw [coeff_homogeneousComponent]
    simp [(Finset.mem_filter.mp ha).2]
  have hcomponent : homogeneousComponent (p.totalDegree * q.totalDegree)
      (blockSubst p q) ≠ 0 := by
    rwa [homogeneousComponent_blockSubst_top p q hepos]
  exact Nat.le_of_not_lt (fun h => hcomponent
    (homogeneousComponent_eq_zero _ _ h))

end MvPolynomial
