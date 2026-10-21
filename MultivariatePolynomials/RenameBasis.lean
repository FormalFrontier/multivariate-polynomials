/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameComplement
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

/-!
# A monomial basis for injective variable renaming

For an embedding `e : σ ↪ τ`, the monomials in variables outside `Set.range e`
form a basis of `MvPolynomial τ R` over `MvPolynomial σ R`. Scalars act through
renaming along `e`: the action of `a` on `p` is `rename e a * p`.

The coordinates of a target monomial separate its exponents into retained and
complementary variables. The retained exponents give a polynomial in the source
polynomial algebra, not in the target polynomial algebra.

## References

* Mathlib's `MvPolynomial.basisMonomials` (Johannes Hölzl), `Module.Basis.map`
  (Johannes Hölzl, Mario Carneiro, Alexander Bentkamp), `MvPolynomial.renameEquiv`,
  `MvPolynomial.mapAlgEquiv`, and `AlgEquiv.ofRingEquiv` (Kenny Lau,
  Yury Kudryashov) supply the monomial-basis and scalar-transport approach.
* `MvPolynomial.splitComplAlgEquiv` and its retained-variable compatibility,
  by Formal Frontier Agents, separate the complementary variables.
* Mathlib's `Finsupp.embDomain` and `Finsupp.comapDomain` describe the exponents.
-/

universe u v w

namespace MvPolynomial

private noncomputable def renameComplementEquiv
    {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R] (e : σ ↪ τ) :
    MvPolynomial τ R ≃ₐ[R]
      MvPolynomial {j : τ // j ∉ Set.range e} (MvPolynomial σ R) :=
  (splitComplAlgEquiv (R := R) (Set.range e)).trans
    (mapAlgEquiv _ (renameEquiv R (Equiv.ofInjective (e : σ → τ) e.injective)).symm)

private theorem renameComplementEquiv_rename
    {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]
    (e : σ ↪ τ) (p : MvPolynomial σ R) :
    renameComplementEquiv (R := R) e (rename (e : σ → τ) p) = C p := by
  classical
  let f := renameEquiv R (Equiv.ofInjective (e : σ → τ) e.injective)
  have h : (rename (Subtype.val : Set.range e → τ)).comp f.toAlgHom =
      rename (R := R) (e : σ → τ) := by
    apply algHom_ext
    intro i
    simp [f, renameEquiv_apply]
  have hp : rename (Subtype.val : Set.range e → τ) (f p) = rename (e : σ → τ) p :=
    DFunLike.congr_fun h p
  change map f.symm.toRingHom
    (splitComplAlgEquiv (R := R) (Set.range e) (rename (e : σ → τ) p)) = C p
  rw [← hp, splitComplAlgEquiv_rename_subtypeVal, map_C]
  exact congrArg C (f.symm_apply_apply p)

private noncomputable def renameComplementAlgebraEquiv
    {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R] (e : σ ↪ τ) :
    @AlgEquiv (MvPolynomial σ R) (MvPolynomial τ R)
      (MvPolynomial {j : τ // j ∉ Set.range e} (MvPolynomial σ R)) _ _ _
      (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra _ := by
  exact @AlgEquiv.ofRingEquiv (MvPolynomial σ R) (MvPolynomial τ R)
    (MvPolynomial {j : τ // j ∉ Set.range e} (MvPolynomial σ R)) _ _ _
    (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra _
    (renameComplementEquiv (R := R) e).toRingEquiv
    (fun p => renameComplementEquiv_rename e p)

private theorem renameComplementEquiv_symm_monomial
    {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]
    (e : σ ↪ τ) (m : {j : τ // j ∉ Set.range e} →₀ ℕ) :
    (renameComplementEquiv (R := R) e).symm (monomial m 1) =
      monomial (Finsupp.embDomain
        (Function.Embedding.subtype (fun j => j ∉ Set.range e)) m) (1 : R) := by
  classical
  have hx (j : {j : τ // j ∉ Set.range e}) :
      (renameComplementEquiv (R := R) e).symm (X j) = X (j : τ) := by
    apply (renameComplementEquiv (R := R) e).injective
    simp [renameComplementEquiv, mapAlgEquiv_apply]
  change (renameComplementEquiv (R := R) e).symm (monomial m 1) = _
  rw [Finsupp.embDomain_eq_mapDomain, ← rename_monomial]
  simp only [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, map_pow,
    hx, rename_X]
  rfl

/-- The basis of the target polynomial algebra over the source polynomial algebra,
with scalars acting through `rename e`, indexed by monomials in the variables
outside the range of `e`. -/
@[no_expose]
noncomputable def renameMonomialBasis {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (e : σ ↪ τ) :
    @Module.Basis ({j : τ // j ∉ Set.range e} →₀ ℕ)
      (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R) _ _
        (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra) := by
  exact @Module.Basis.map _ _ _ _ _ _ _ _
    (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra)
    (basisMonomials {j : τ // j ∉ Set.range e} (MvPolynomial σ R))
    (@AlgEquiv.toLinearEquiv _ _ _ _ _ _ _
      (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra
      (@AlgEquiv.symm _ _ _ _ _ _
        (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra _
        (renameComplementAlgebraEquiv (R := R) e)))

/-- A basis vector is the monomial with the given complementary exponents and
coefficient one. -/
@[simp]
theorem renameMonomialBasis_apply {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (e : σ ↪ τ) (m : {j : τ // j ∉ Set.range e} →₀ ℕ) :
    (renameMonomialBasis (R := R) e :
      @Module.Basis ({j : τ // j ∉ Set.range e} →₀ ℕ)
        (MvPolynomial σ R) (MvPolynomial τ R) _ _
        (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R) _ _
          (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra)) m =
      monomial (Finsupp.embDomain
        (Function.Embedding.subtype (fun j => j ∉ Set.range e)) m) (1 : R) := by
  change (renameComplementEquiv (R := R) e).symm (monomial m 1) = _
  exact renameComplementEquiv_symm_monomial (R := R) e m

/-- The coordinate of a target monomial is supported at its complementary
exponent, with its retained exponent and original coefficient in the source
polynomial algebra. -/
@[simp]
theorem renameMonomialBasis_repr_monomial
    {R : Type u} {σ : Type v} {τ : Type w} [CommSemiring R]
    (e : σ ↪ τ) (d : τ →₀ ℕ) (r : R) :
    (@Module.Basis.repr ({j : τ // j ∉ Set.range e} →₀ ℕ)
      (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R) _ _
        (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra)
      (renameMonomialBasis (R := R) e)) (monomial d r) =
      Finsupp.single
        (Finsupp.comapDomain
          (Function.Embedding.subtype (fun j => j ∉ Set.range e)) d
          (Function.Embedding.subtype (fun j => j ∉ Set.range e)).injective.injOn)
        (monomial (Finsupp.comapDomain e d e.injective.injOn) r) := by
  classical
  let : Module (MvPolynomial σ R) (MvPolynomial τ R) :=
    @Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra
  let c := Function.Embedding.subtype (fun j => j ∉ Set.range e)
  let ds := Finsupp.comapDomain e d e.injective.injOn
  let dc := Finsupp.comapDomain c d c.injective.injOn
  have hd : Finsupp.embDomain e ds + Finsupp.embDomain c dc = d := by
    ext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      have hc : e i ∉ Set.range c := by
        rintro ⟨k, hk⟩
        exact k.property ⟨i, hk.symm⟩
      rw [Finsupp.add_apply, Finsupp.embDomain_apply_self,
        Finsupp.embDomain_of_notMem_range c dc (e i) hc]
      simp [ds]
    · have hc : c ⟨j, hj⟩ = j := rfl
      rw [Finsupp.add_apply, Finsupp.embDomain_of_notMem_range e ds j hj,
        ← hc, Finsupp.embDomain_apply_self]
      simp [dc]
  have hp : monomial d r =
      rename (e : σ → τ) (monomial ds r) * (renameMonomialBasis (R := R) e) dc := by
    rw [renameMonomialBasis_apply, rename_monomial, monomial_mul_monomial,
      mul_one, ← Finsupp.embDomain_eq_mapDomain e]
    exact congrArg (fun s => monomial s r) hd.symm
  let ρ := @Module.Basis.repr ({j : τ // j ∉ Set.range e} →₀ ℕ)
    (MvPolynomial σ R) (MvPolynomial τ R) _ _
    (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (rename (R := R) (e : σ → τ)).toRingHom.toAlgebra)
    (renameMonomialBasis (R := R) e)
  have h := ρ.map_smul' (monomial ds r) ((renameMonomialBasis (R := R) e) dc)
  change ρ
      (rename (e : σ → τ) (monomial ds r) * (renameMonomialBasis (R := R) e) dc) =
    (monomial ds r) • ρ ((renameMonomialBasis (R := R) e) dc) at h
  dsimp only [ρ] at h
  rw [← hp, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] at h
  exact h

end MvPolynomial
