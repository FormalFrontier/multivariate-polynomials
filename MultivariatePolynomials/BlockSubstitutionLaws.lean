/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IteratedBlockSubstitution

set_option warningAsError true

/-!
# Structural laws for disjoint-block substitution

The laws compare polynomials by substitution and renaming, rather than by evaluation
at coefficient-ring points. All variable types and the coefficient commutative
semiring are arbitrary.

-/

@[expose] public section

namespace MvPolynomial

universe u v w x t

variable {I : Type u} {J : Type v} {K : Type w} {L : Type x}
  {R : Type t} [CommSemiring R]

/-- Renaming both sets of indices commutes with substitution into disjoint blocks.
Neither index map needs to be injective. -/
theorem rename_blockSubst (f : I → K) (g : J → L)
    (p : MvPolynomial I R) (q : MvPolynomial J R) :
    rename (Prod.map f g) (blockSubst p q) =
      blockSubst (rename f p) (rename g q) := by
  simp only [blockSubst, rename_bind₁, bind₁_rename, rename_rename]
  congr 1

/-- Associating three blocks transports the left-nested substitution to the
right-nested substitution. -/
theorem blockSubst_assoc (p : MvPolynomial I R) (q : MvPolynomial J R)
    (r : MvPolynomial K R) :
    rename (Equiv.prodAssoc I J K) (blockSubst (blockSubst p q) r) =
      blockSubst p (blockSubst q r) := by
  simp only [blockSubst, rename_bind₁, bind₁_bind₁, bind₁_rename, rename_rename]
  apply congrArg (fun h : I → MvPolynomial (I × (J × K)) R => bind₁ h p)
  funext i
  apply congrArg (fun h : J → MvPolynomial (I × (J × K)) R => bind₁ h q)
  funext j
  simp only [Function.comp_apply, rename_rename]
  rfl

/-- A single variable in the outer block is a left unit after erasing its tag. -/
theorem blockSubst_X_left (p : MvPolynomial I R) :
    rename (Prod.snd : PUnit × I → I) (blockSubst (X PUnit.unit) p) = p := by
  simp [blockSubst, rename_rename]

/-- A single variable in the inner block is a right unit after erasing its tag. -/
theorem blockSubst_X_right (p : MvPolynomial I R) :
    rename (Prod.fst : I × PUnit → I) (blockSubst p (X PUnit.unit)) = p := by
  simp [blockSubst, rename_bind₁, rename_X, bind₁_X_left]

private noncomputable def appendBlock {m n : ℕ} (a : MvPolynomial (Fin m → I) R)
    (b : MvPolynomial (Fin n → I) R) : MvPolynomial (Fin (m + n) → I) R :=
  rename (fun pair : (Fin m → I) × (Fin n → I) => Fin.append pair.1 pair.2)
    (blockSubst a b)

private theorem rename_word_cast {m n : ℕ} (h : m = n)
    (polys : (r : ℕ) → MvPolynomial (Fin r → I) R) :
    rename (fun t : Fin n → I => t ∘ Fin.cast h) (polys n) = polys m := by
  cases h
  exact rename_id_apply (polys m)

private theorem appendBlock_zero_left {n : ℕ} (a : MvPolynomial (Fin n → I) R) :
    appendBlock (X Fin.elim0) a =
      rename (fun t : Fin n → I => t ∘ Fin.cast (Nat.zero_add n)) a := by
  simp only [appendBlock, blockSubst, bind₁_X_right, rename_rename]
  have h : (fun t : Fin n → I => Fin.append Fin.elim0 t) =
      (fun t => t ∘ Fin.cast (Nat.zero_add n)) := by
    funext t
    exact Fin.elim0_append t
  change rename (fun t : Fin n → I => Fin.append Fin.elim0 t) a = _
  rw [h]

private theorem appendBlock_zero_right {m : ℕ} (a : MvPolynomial (Fin m → I) R) :
    appendBlock a (X Fin.elim0) = a := by
  simp only [appendBlock, blockSubst, rename_bind₁, rename_X]
  have h : (fun t : Fin m → I => (X (Fin.append t Fin.elim0) :
      MvPolynomial (Fin (m + 0) → I) R)) = X := by
    funext t
    simp only [Fin.append_elim0]
    rfl
  simp only [h, bind₁_X_left, AlgHom.id_apply]

private theorem appendBlock_assoc {m n k : ℕ}
    (a : MvPolynomial (Fin m → I) R)
    (b : MvPolynomial (Fin n → I) R)
    (c : MvPolynomial (Fin k → I) R) :
    rename (fun t : Fin ((m + n) + k) → I =>
      t ∘ Fin.cast (Nat.add_assoc m n k).symm)
        (appendBlock (appendBlock a b) c) = appendBlock a (appendBlock b c) := by
  let appMN : ((Fin m → I) × (Fin n → I)) → (Fin (m + n) → I) :=
    fun pair => Fin.append pair.1 pair.2
  let appNK : ((Fin n → I) × (Fin k → I)) → (Fin (n + k) → I) :=
    fun pair => Fin.append pair.1 pair.2
  have hleft : blockSubst (rename appMN (blockSubst a b)) c =
      rename (Prod.map appMN id) (blockSubst (blockSubst a b) c) := by
    simpa using (rename_blockSubst appMN id (blockSubst a b) c).symm
  have hright : blockSubst a (rename appNK (blockSubst b c)) =
      rename (Prod.map id appNK) (blockSubst a (blockSubst b c)) := by
    simpa using (rename_blockSubst id appNK a (blockSubst b c)).symm
  change rename (fun t : Fin ((m + n) + k) → I =>
      t ∘ Fin.cast (Nat.add_assoc m n k).symm)
      (rename (fun pair : (Fin (m+n) → I) × (Fin k → I) => Fin.append pair.1 pair.2)
        (blockSubst (rename appMN (blockSubst a b)) c)) =
    rename (fun pair : (Fin m → I) × (Fin (n+k) → I) => Fin.append pair.1 pair.2)
      (blockSubst a (rename appNK (blockSubst b c)))
  rw [hleft, hright]
  simp only [rename_rename]
  rw [← blockSubst_assoc a b c, rename_rename]
  congr 1
  congr 1
  funext ⟨⟨first, middle⟩, last⟩
  change Fin.append (Fin.append first middle) last ∘
    Fin.cast (Nat.add_assoc m n k).symm = Fin.append first (Fin.append middle last)
  rw [Fin.append_assoc]
  funext index
  exact congrArg (Fin.append first (Fin.append middle last))
    (Fin.ext rfl)

/-- A single iteration merely indexes each original variable by a one-letter word. -/
theorem iteratedBlockSubst_one (p : MvPolynomial I R) :
    iteratedBlockSubst p 1 = rename (fun i : I => Fin.cons i Fin.elim0) p := by
  rw [iteratedBlockSubst_succ]
  simp only [iteratedBlockSubst_zero, blockSubst, rename_bind₁, rename_X]
  rw [rename_eq_aeval, aeval_eq_bind₁]
  rfl

private theorem appendBlock_cons {m n : ℕ} (p : MvPolynomial I R)
    (a : MvPolynomial (Fin m → I) R) (b : MvPolynomial (Fin n → I) R) :
    appendBlock (rename (Fin.consEquiv (fun _ : Fin (m + 1) => I))
      (blockSubst p a)) b =
    rename (fun t : Fin ((m + n) + 1) → I =>
      t ∘ Fin.cast (Nat.add_right_comm m 1 n))
      (rename (Fin.consEquiv (fun _ : Fin (m + n + 1) => I))
        (blockSubst p (appendBlock a b))) := by
  let appendMN : ((Fin m → I) × (Fin n → I)) → (Fin (m + n) → I) :=
    fun pair => Fin.append pair.1 pair.2
  have hleft : blockSubst
      (rename (Fin.consEquiv (fun _ : Fin (m + 1) => I)) (blockSubst p a)) b =
      rename (Prod.map (Fin.consEquiv (fun _ : Fin (m + 1) => I)) id)
        (blockSubst (blockSubst p a) b) := by
    simpa using (rename_blockSubst (Fin.consEquiv (fun _ : Fin (m + 1) => I))
      id (blockSubst p a) b).symm
  have hright : blockSubst p (rename appendMN (blockSubst a b)) =
      rename (Prod.map id appendMN) (blockSubst p (blockSubst a b)) := by
    simpa using (rename_blockSubst id appendMN p (blockSubst a b)).symm
  change rename (fun pair : (Fin (m+1) → I) × (Fin n → I) =>
      Fin.append pair.1 pair.2)
      (blockSubst (rename (Fin.consEquiv (fun _ : Fin (m+1) => I))
        (blockSubst p a)) b) =
    rename (fun t : Fin (m+n+1) → I =>
      t ∘ Fin.cast (Nat.add_right_comm m 1 n))
      (rename (Fin.consEquiv (fun _ : Fin (m+n+1) => I))
        (blockSubst p (rename appendMN (blockSubst a b))))
  rw [hleft, hright]
  simp only [rename_rename]
  rw [← blockSubst_assoc p a b, rename_rename]
  congr 1
  congr 1
  funext ⟨⟨first, middle⟩, last⟩
  change Fin.append (Fin.cons first middle) last =
    Fin.cons first (Fin.append middle last) ∘
      Fin.cast (Nat.add_right_comm m 1 n)
  exact Fin.append_cons first middle last

/-- Additive iteration is block substitution indexed by concatenation of finite words. -/
theorem iteratedBlockSubst_add (p : MvPolynomial I R) (m n : ℕ) :
    iteratedBlockSubst p (m + n) =
      rename (fun pair : (Fin m → I) × (Fin n → I) =>
        Fin.append pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p m) (iteratedBlockSubst p n)) := by
  change iteratedBlockSubst p (m + n) =
    appendBlock (iteratedBlockSubst p m) (iteratedBlockSubst p n)
  induction m with
  | zero =>
      calc
        iteratedBlockSubst p (0 + n) =
            rename (fun t : Fin n → I => t ∘ Fin.cast (Nat.zero_add n))
              (iteratedBlockSubst p n) :=
          (rename_word_cast (Nat.zero_add n) (iteratedBlockSubst p)).symm
        _ = appendBlock (iteratedBlockSubst p 0) (iteratedBlockSubst p n) := by
          simpa only [iteratedBlockSubst_zero] using
            (appendBlock_zero_left (iteratedBlockSubst p n)).symm
  | succ m ih =>
      have h := appendBlock_cons p (iteratedBlockSubst p m) (iteratedBlockSubst p n)
      rw [← ih, ← iteratedBlockSubst_succ p (m + n),
        ← iteratedBlockSubst_succ p m] at h
      rw [h]
      exact (rename_word_cast (Nat.add_right_comm m 1 n)
        (iteratedBlockSubst p)).symm

/-- The opposite successor substitutes the original polynomial at the end of
each word, preserving the order of its preceding letters. -/
theorem iteratedBlockSubst_snoc (p : MvPolynomial I R) (m : ℕ) :
    iteratedBlockSubst p (m + 1) =
      rename (fun pair : (Fin m → I) × I => Fin.snoc pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p m) p) := by
  rw [iteratedBlockSubst_add, iteratedBlockSubst_one]
  let single : I → (Fin 1 → I) := fun i => Fin.cons i Fin.elim0
  have h : blockSubst (iteratedBlockSubst p m)
      (rename single p) =
      rename (Prod.map id single)
        (blockSubst (iteratedBlockSubst p m) p) := by
    simpa only [rename_id_apply] using
      (rename_blockSubst id single
        (iteratedBlockSubst p m) p).symm
  rw [h, rename_rename]
  congr 1
  congr 1
  funext ⟨word, letter⟩
  exact Fin.append_right_eq_snoc word (Fin.cons letter Fin.elim0 : Fin 1 → I)

end MvPolynomial
