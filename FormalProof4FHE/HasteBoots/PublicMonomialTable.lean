module
public import FormalProof4FHE.HasteBoots.PBSMonomialBlindRotation
@[expose] public section

/-! Mathematical meaning of the signed monomial rows materialized by
`packed_monomial::Plan::table`: one signed coefficient, an NTT per active
round, zero padding and identical ciphertext halves. Rust allocation, flattened
packing and the optimized verifier evaluator remain separate refinements. -/
namespace FormalProof4FHE.HasteBoots.PublicMonomialTable
open scoped BigOperators
open NativeBlindRotation (Poly Cipher rotate)
noncomputable section

/-- The native constructor bounds rotations by 2N. -/
def coefficients {q n : ℕ} (rotation : Fin (2*n)) : Poly q n :=
  fun index => if index.val = rotation.val%n then (if rotation.val < n then 1 else -1) else 0

theorem evaluate_coefficients {q n : ℕ} (rotation : Fin (2*n)) (point : ZMod q)
    (negative : point^n = -1) :
    BlindRotationNTT.evaluate (coefficients rotation) point = point^rotation.val := by
  classical
  have positive : 0 < n := by have := rotation.isLt; omega
  let position : Fin n := ⟨rotation.val%n,Nat.mod_lt _ positive⟩
  unfold BlindRotationNTT.evaluate coefficients
  rw [Finset.sum_eq_single position]
  · simp only [position, ite_true]
    by_cases low : rotation.val < n
    · rw [ite_eq_left low, one_mul, Nat.mod_eq_of_lt low]
    · rw [ite_eq_right low, neg_one_mul]
      have small : rotation.val-n < n := by have := rotation.isLt; omega
      have modulo : rotation.val%n = rotation.val-n := by
        rw [Nat.mod_eq_sub_mod (by omega : n ≤ rotation.val), Nat.mod_eq_of_lt small]
      rw [modulo]
      calc
        _ = point^n * point^(rotation.val-n) := by rw [negative, neg_one_mul]
        _ = point^(n+(rotation.val-n)) := (pow_add _ _ _).symm
        _ = _ := congrArg (point^·) (by omega)
  · intro index _ different
    have unequal : index.val ≠ rotation.val%n := fun same => different (Fin.ext same)
    simp only [ite_eq_right unequal, zero_mul]
  · simp

variable {q : ℕ} [Fact q.Prime]

theorem transform_coefficients (log : ℕ) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (rotation : Fin (2*(2^log))) :
    BlindRotationNTT.transform log psi (coefficients rotation) =
      BlindRotationMonomial.powers log psi rotation.val := by
  funext index
  exact evaluate_coefficients rotation _ (NTTButterfly.nodes_power log psi primitive index)

theorem butterfly_coefficients (log : ℕ) (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (rotation : Fin (2*(2^log))) :
    NTTButterfly.flatTransform log psi (psi^2) (coefficients rotation) =
      BlindRotationMonomial.powers log psi rotation.val := by
  rw [NTTButterfly.negacyclic_evaluation log psi primitive]
  exact transform_coefficients log psi primitive rotation

/-- Padding is explicit; rotations are indexed only by active rounds. -/
def row {log rounds padded : ℕ} (rotations : Fin rounds → Fin (2*(2^log)))
    (position : Fin padded) : Poly q (2^log) :=
  if active : position.val < rounds then coefficients (rotations ⟨position.val,active⟩) else 0

/-- The two ciphertext halves use the same transformed row, as in Plan::table. -/
def table {log rounds padded : ℕ} (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^log)))
    (_half : Bool) (position : Fin padded) : Poly q (2^log) :=
  NTTButterfly.flatTransform log psi (psi^2) (row rotations position)

theorem table_active {log rounds padded : ℕ} (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (rotations : Fin rounds → Fin (2*(2^log)))
    (half : Bool) (position : Fin padded) (active : position.val < rounds) :
    table psi rotations half position = BlindRotationMonomial.powers log psi (rotations ⟨position.val,active⟩).val := by
  unfold table row
  rw [dite_eq_left active]
  exact butterfly_coefficients log psi primitive _

/-- Every original round is retained in its original row when padding fits. -/
theorem table_round {log rounds padded : ℕ} (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (rotations : Fin rounds → Fin (2*(2^log)))
    (fits : rounds ≤ padded) (half : Bool) (round : Fin rounds) :
    table psi rotations half ⟨round.val,lt_of_lt_of_le round.isLt fits⟩ =
      BlindRotationMonomial.powers log psi (rotations round).val :=
  table_active psi primitive rotations half _ round.isLt

theorem table_inactive {log rounds padded : ℕ} (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (rotations : Fin rounds → Fin (2*(2^log)))
    (half : Bool) (position : Fin padded) (inactive : ¬position.val < rounds) :
    table psi rotations half position = 0 := by
  unfold table row
  rw [dite_eq_right inactive, NTTButterfly.negacyclic_evaluation log psi primitive]
  exact map_zero (BlindRotationNTT.transform log psi)

theorem table_halves {log rounds padded : ℕ} (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^log))) (position : Fin padded) :
    table psi rotations false position = table psi rotations true position := rfl

/-- With a public factor bound to the materialized active row, the separate
node-power premise of the rotation bridge is discharged. The binding itself
is still an explicit table-layout/commitment obligation. -/
theorem rotate_of_table {log rounds padded cells width : ℕ} (psi : ZMod q)
    (primitive : IsPrimitiveRoot psi (2^(log+1))) (rotations : Fin rounds → Fin (2*(2^log)))
    (position : Fin padded) (active : position.val < rounds) (input output : Cipher q (2^log))
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) cells width)
    (address : Bool → Fin (2^log) → MatrixFold.Cube cells × Fin width) (relation : PBSHadamard.Relation tables)
    (source : ∀ half, BlindRotationNTT.transform log psi (input half) =
      PBSMonomialBlindRotation.project tables (address half) (.inl (0,false)))
    (publicRow : ∀ half, PBSMonomialBlindRotation.project tables (address half) (.inl (0,true)) =
      table psi rotations half position)
    (result : ∀ half, BlindRotationNTT.transform log psi (output half) =
      PBSMonomialBlindRotation.project tables (address half) (.inr ())) :
    output = fun half => rotate (rotations ⟨position.val,active⟩).val (input half) := by
  apply PBSMonomialBlindRotation.rotate_of_relations psi primitive _ input output tables address relation source
  · intro half
    rw [publicRow half, table_active psi primitive rotations half position active]
  · exact result

end
end FormalProof4FHE.HasteBoots.PublicMonomialTable
