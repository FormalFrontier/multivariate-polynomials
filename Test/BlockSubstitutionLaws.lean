/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.BlockSubstitutionLaws
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

/-!
# Ordinary-import structural-law clients

Eight private checks by original worker-b Hive Task
`hive-request-b3d4d6e3a78dc53efdabae39dcafd0f770d8c0c4` (UID
`12c22dfd-831c-4fa3-a82a-d6e0a88a8a5d`), transferred by worker-b Hive Task
`hive-request-dcfc7155e1b8f1e339a4db2a5f323981d29793e3` (UID
`50067b60-ca63-4a90-bbcf-6e81453fd6a1`).
-/

namespace BlockSubstitutionLawsClient

open MvPolynomial

private theorem arbitraryMaps (p : MvPolynomial (Fin 2) (ZMod 2))
    (q : MvPolynomial (Fin 3) (ZMod 2)) :
    rename (Prod.map (fun _ : Fin 2 => (0 : Fin 1))
        (fun _ : Fin 3 => (0 : Fin 1))) (blockSubst p q) =
      blockSubst (rename (fun _ : Fin 2 => (0 : Fin 1)) p)
        (rename (fun _ : Fin 3 => (0 : Fin 1)) q) :=
  rename_blockSubst _ _ p q

private theorem mixedAssociativity {R : Type*} [CommSemiring R]
    (p : MvPolynomial (Fin 2) R) (q : MvPolynomial PEmpty R)
    (r : MvPolynomial (Fin 1) R) :
    rename (Equiv.prodAssoc (Fin 2) PEmpty (Fin 1))
      (blockSubst (blockSubst p q) r) = blockSubst p (blockSubst q r) :=
  blockSubst_assoc p q r

private theorem singletonUnits {R : Type*} [CommSemiring R]
    (p : MvPolynomial (Fin 2) R) :
    rename (Prod.snd : PUnit × Fin 2 → Fin 2)
        (blockSubst (X PUnit.unit) p) = p ∧
      rename (Prod.fst : Fin 2 × PUnit → Fin 2)
        (blockSubst p (X PUnit.unit)) = p :=
  ⟨blockSubst_X_left p, blockSubst_X_right p⟩

private theorem additiveMixed {I R : Type*} [CommSemiring R]
    (p : MvPolynomial I R) (m n : ℕ) :
    iteratedBlockSubst p (m + n) =
      rename (fun pair : (Fin m → I) × (Fin n → I) =>
        Fin.append pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p m) (iteratedBlockSubst p n)) :=
  iteratedBlockSubst_add p m n

private theorem oppositeMixed {I R : Type*} [CommSemiring R]
    (p : MvPolynomial I R) (m : ℕ) :
    iteratedBlockSubst p (m + 1) =
      rename (fun pair : (Fin m → I) × I => Fin.snoc pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p m) p) :=
  iteratedBlockSubst_snoc p m

private theorem finiteFieldConstants :
    iteratedBlockSubst (X (0 : Fin 2) + C 1 : MvPolynomial (Fin 2) (ZMod 2))
        (2 + 1) =
      rename (fun pair : (Fin 2 → Fin 2) × (Fin 1 → Fin 2) =>
        Fin.append pair.1 pair.2)
        (blockSubst
          (iteratedBlockSubst (X (0 : Fin 2) + C 1 : MvPolynomial (Fin 2) (ZMod 2)) 2)
          (iteratedBlockSubst (X (0 : Fin 2) + C 1 : MvPolynomial (Fin 2) (ZMod 2)) 1)) :=
  iteratedBlockSubst_add _ 2 1

private theorem emptyAndZero {R : Type*} [CommSemiring R] :
    iteratedBlockSubst (0 : MvPolynomial PEmpty R) (0 + 2) =
      rename (fun pair : (Fin 0 → PEmpty) × (Fin 2 → PEmpty) =>
        Fin.append pair.1 pair.2)
        (blockSubst (iteratedBlockSubst (0 : MvPolynomial PEmpty R) 0)
          (iteratedBlockSubst (0 : MvPolynomial PEmpty R) 2)) :=
  iteratedBlockSubst_add _ 0 2

private theorem zeroRing (p : MvPolynomial (Fin 1) PUnit) :
    iteratedBlockSubst p (0 + 1) =
      rename (fun pair : (Fin 0 → Fin 1) × (Fin 1 → Fin 1) =>
        Fin.append pair.1 pair.2)
        (blockSubst (iteratedBlockSubst p 0) (iteratedBlockSubst p 1)) ∧
      iteratedBlockSubst p (0 + 1) =
        rename (fun pair : (Fin 0 → Fin 1) × Fin 1 => Fin.snoc pair.1 pair.2)
          (blockSubst (iteratedBlockSubst p 0) p) :=
  ⟨iteratedBlockSubst_add p 0 1, iteratedBlockSubst_snoc p 0⟩

end BlockSubstitutionLawsClient
