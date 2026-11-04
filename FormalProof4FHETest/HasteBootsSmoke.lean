module

import all FormalProof4FHE.HasteBoots
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.LinearAlgebra.Basis.Basic
import all Mathlib.LinearAlgebra.StdBasis
import all VCVio.OracleComp.Constructions.SampleableType.Basic

open Matrix
open FormalProof4FHE.HasteBoots

namespace HasteBootsSmoke

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def left : Matrix (Fin 2) (Fin 2) (ZMod 17) := !![0, 0; 1, 0]
private def right : Matrix (Fin 2) (Fin 2) (ZMod 17) := !![0, 1; 0, 0]
private def vector : Fin 2 → ZMod 17 := ![1, 0]

/-- Reversing matrix order really changes the result; this is not a scalar identity. -/
example : (right * left) *ᵥ vector ≠ (left * right) *ᵥ vector := by decide

example : MatrixFold.weight [fun _ => left, fun _ => right] (false, (true, ())) =
    right * left := by simp [MatrixFold.weight]

example (v : MatrixFold.Cube 0 → Fin 2 → ZMod 17) :
    MatrixFold.foldAll [] v = v () := rfl

/-- Unequal left/right splits are allowed by the aggregation theorem. -/
example (l : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 17))
    (r : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod 17))
    (t : Fin 2 → Fin 3 → Fin 2 → ZMod 17) :
    foldedOpening l r t = matrixEvaluation l r t :=
  foldedOpening_eq_matrixEvaluation l r t

example : Code.minDist ((BlockCode.code (Function.Embedding.refl (ZMod 17)) 4 2 :
    Submodule (ZMod 17) (ZMod 17 → Fin 2 → ZMod 17)) :
    Set (ZMod 17 → Fin 2 → ZMod 17)) = 14 := by
  simpa using BlockCode.minDist (Function.Embedding.refl (ZMod 17)) 4 2 (by decide)

/-- Repeated draws are charged before transport deduplication. -/
example (bad : Set (Fin 4)) :
    (∀ p ∈ ([0, 0, 1] : List (Fin 4)).dedup, p ∉ bad) ↔
      (∀ p ∈ ([0, 0, 1] : List (Fin 4)), p ∉ bad) :=
  ColumnSampling.misses_dedup_iff _ _

example : Fintype.card {draw : Fin 3 → Fin 4 //
    ∀ i, draw i ∈ ({0, 1} : Finset (Fin 4))} = 8 := by
  simpa using ColumnSampling.card_goodDraws ({0, 1} : Finset (Fin 4)) 3

/-- A two-coordinate, two-coefficient message evaluates in coordinate order. -/
example : BlockEncoder.encode (fun _ : Unit => (3 : ZMod 17))
    (fun j : Fin 2 => if j = 0 then ![1, 2] else ![4, 5]) () = ![13, 0] := by
  decide

example (domain : Fin 4 ↪ ZMod 17) (input other : Fin 2 → Fin 2 → ZMod 17)
    (h : BlockEncoder.encode domain input = BlockEncoder.encode domain other) :
    input = other :=
  BlockEncoder.encode_injective domain (by decide) h

/-- A partially filled final block is zero-padded in the missing lane. -/
example : RowLayout.padded (m := 2) (b := 2) (![1, 2, 4] : Fin 3 → ZMod 17) 1 1 = 0 := by
  decide

example : RowLayout.flatOutput (m := 2) (b := 2)
    (fun _ : Fin 1 => (3 : ZMod 17)) (![1, 2, 4] : Fin 3 → ZMod 17) = ![13, 2] := by
  decide

example (input : Fin 3 → ZMod 17) :
    RowLayout.recover (m := 2) (b := 2) (by decide) (RowLayout.padded input) = input :=
  RowLayout.recover_padded _ _

/-- Half ties round up, including wraparound to zero. -/
example : NativePublic.roundModulus 4 2 1 = 1 ∧
    NativePublic.roundModulus 4 2 3 = 0 := by decide

example : NativePublic.roundModulus 18446744069414584321 2048
    ((18446744069414584321 - 1) / 4096) = 0 := by decide

example : NativePublic.roundModulus 18446744069414584321 2048
    ((18446744069414584321 - 1) / 4096 + 1) = 1 := by decide

/-- The upper stride starts at the split point 6, not at a multiple of 5. -/
example : NativePublic.nandLut (q := 17) (n := 8) 5 =
    (![2, 0, 0, 0, 0, 2, 15, 0] : Fin 8 → ZMod 17) := by decide

example : (18446744069414584321 - 1) * 2048 + 18446744069414584321 / 2 <
    (2 : ℕ) ^ 128 :=
  NativePublic.native_round_numerator_fits _ _ (by decide) (by decide)

/-- Negacyclic wraparound: X * X = -1 modulo X^2+1. -/
example : NativeBlindRotation.mul (![0, 1] : Fin 2 → ZMod 17) ![0, 1] = ![16, 0] := by
  decide

example : NativeBlindRotation.rotate 2 (![3, 5] : Fin 2 → ZMod 17) = ![14, 12] := by
  decide

/-- Both nonce/body source families contribute; key rows already include their signs. -/
example : NativeBlindRotation.externalProduct (q := 17) (n := 1) (levels := 1) 5
    (fun source _ half _ => if source then (if half then 4 else 3) else
      (if half then 2 else 1))
    (fun half _ => if half then 7 else 5) =
      (fun half _ => if half then 4 else 9) := by decide

/-- Sample extraction reverses and negates the tail before truncating to dimension 3. -/
example : (NativeKeySwitch.extract (q := 17) (n := 4) (dimension := 3) (by decide)
    (fun half => if half then ![13, 0, 0, 0] else ![3, 5, 7, 11])).mask = ![3, 6, 10] := by
  decide

private def ksKey : NativeKeySwitch.Key 17 1 1 :=
  fun _ half _ => if half then 3 else 2
private def ksInput : NativeBlindRotation.Cipher 17 1 :=
  fun half _ => if half then 9 else 4

/-- KSK multiplication is subtracted from (0,b0), not added. -/
example :
    (NativeKeySwitch.extract (dimension := 1) (by decide)
      (NativeKeySwitch.switch 5 ksKey ksInput)).mask 0 = 9 ∧
    (NativeKeySwitch.extract (dimension := 1) (by decide)
      (NativeKeySwitch.switch 5 ksKey ksInput)).body = 14 := by decide

/-- Whole-column distance sees a change in any row, not just row zero. -/
example : hammingDist
    (fun _ : Fin 3 => (![0, 0] : Fin 2 → ZMod 17))
    (fun p : Fin 3 => if p = 1 then ![0, 1] else ![0, 0]) = 1 := by decide

example : 2 * ((17 - 4) / 3) < 17 - 4 + 1 := by decide

/-- info: 'FormalProof4FHE.HasteBoots.foldedOpening_eq_matrixEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms foldedOpening_eq_matrixEvaluation
/-- info: 'FormalProof4FHE.HasteBoots.MatrixFold.foldAll_eq_weightedEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixFold.foldAll_eq_weightedEvaluation
/-- info: 'FormalProof4FHE.HasteBoots.BlockCode.minDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockCode.minDist
/-- info: 'FormalProof4FHE.HasteBoots.BlockCode.dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockCode.dimension
/-- info: 'FormalProof4FHE.HasteBoots.ApplicationKnowledge.failure_measure_eq_falseOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ApplicationKnowledge.failure_measure_eq_falseOutput
/-- info: 'FormalProof4FHE.HasteBoots.ColumnSampling.card_goodDraws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnSampling.card_goodDraws

/-- info: 'FormalProof4FHE.HasteBoots.BlockEncoder.encode_mem_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockEncoder.encode_mem_code

/-- info: 'FormalProof4FHE.HasteBoots.BlockEncoder.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockEncoder.encode_injective

/-- info: 'FormalProof4FHE.HasteBoots.BlockEncoder.encode_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockEncoder.encode_add

/-- info: 'FormalProof4FHE.HasteBoots.BlockEncoder.encode_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockEncoder.encode_smul

/-- info: 'FormalProof4FHE.HasteBoots.RowLayout.recover_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowLayout.recover_padded

/-- info: 'FormalProof4FHE.HasteBoots.RowLayout.padded_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowLayout.padded_injective

/-- info: 'FormalProof4FHE.HasteBoots.RowLayout.encode_mem_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowLayout.encode_mem_code

/-- info: 'FormalProof4FHE.HasteBoots.RowLayout.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowLayout.encode_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativePublic.initialAccumulator_mask_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePublic.initialAccumulator_mask_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativePublic.frontend_rotation_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePublic.frontend_rotation_lt

/-- info: 'FormalProof4FHE.HasteBoots.NativePublic.native_round_numerator_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePublic.native_round_numerator_fits

/-- info: 'FormalProof4FHE.HasteBoots.NativeBlindRotation.rotate_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBlindRotation.rotate_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeBlindRotation.externalProduct_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBlindRotation.externalProduct_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeBlindRotation.step_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBlindRotation.step_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeBlindRotation.validTrace_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBlindRotation.validTrace_output

/-- info: 'FormalProof4FHE.HasteBoots.NativeBlindRotation.makeTrace_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBlindRotation.makeTrace_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeKeySwitch.makeTrace_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeKeySwitch.makeTrace_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeKeySwitch.valid_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeKeySwitch.valid_output

/-- info: 'FormalProof4FHE.HasteBoots.NativePBS.relation_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePBS.relation_output

/-- info: 'FormalProof4FHE.HasteBoots.NativePBS.makeTrace_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePBS.makeTrace_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativePBS.exists_trace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePBS.exists_trace_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativePBS.extraction_succeeds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePBS.extraction_succeeds_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativePBS.extractionFailure_measure_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePBS.extractionFailure_measure_eq

/-- info: 'FormalProof4FHE.HasteBoots.CommonSource.nearby_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSource.nearby_unique

/-- info: 'FormalProof4FHE.HasteBoots.CommonSource.decode_eq_of_nearby' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSource.decode_eq_of_nearby

/-- info: 'FormalProof4FHE.HasteBoots.CommonSource.decode_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSource.decode_fallback

/-- info: 'FormalProof4FHE.HasteBoots.CommonSource.decode_rowsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSource.decode_rowsIn

/-- info: 'FormalProof4FHE.HasteBoots.CommonSource.block_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSource.block_margin

/-- info: 'FormalProof4FHE.HasteBoots.RowSpanProximity.fixedWord_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowSpanProximity.fixedWord_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommonSource.falseResponse_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSource.falseResponse_distance

/-- info: 'FormalProof4FHE.HasteBoots.SymbolLift.distance_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymbolLift.distance_eq

/-- info: 'FormalProof4FHE.HasteBoots.SymbolLift.pack_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymbolLift.pack_encode

/-- info: 'FormalProof4FHE.HasteBoots.SymbolLift.encode_mem_scalarCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymbolLift.encode_mem_scalarCode

/-- info: 'FormalProof4FHE.HasteBoots.SymbolLift.combine_tests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymbolLift.combine_tests

/-- info: 'FormalProof4FHE.HasteBoots.SymbolLift.cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymbolLift.cardinality

/-- info: 'FormalProof4FHE.HasteBoots.SymbolLift.uniform_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymbolLift.uniform_coefficients

/-- info: 'FormalProof4FHE.HasteBoots.UniformImage.uniform_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UniformImage.uniform_event

/-- info: 'FormalProof4FHE.HasteBoots.RowSpanSampling.toSpan_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowSpanSampling.toSpan_surjective

/-- info: 'FormalProof4FHE.HasteBoots.RowSpanSampling.coefficient_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowSpanSampling.coefficient_event

/-- info: 'FormalProof4FHE.HasteBoots.RowSpanSampling.coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowSpanSampling.coefficient_bound

/-- info: 'FormalProof4FHE.HasteBoots.RowSpanSampling.matrix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RowSpanSampling.matrix_bound

/-- info: 'FormalProof4FHE.HasteBoots.CodeCorrespondence.scalarRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeCorrespondence.scalarRepresentation

/-- info: 'FormalProof4FHE.HasteBoots.CodeCorrespondence.baseRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeCorrespondence.baseRepresentation

/-- info: 'FormalProof4FHE.HasteBoots.CodeCorrespondence.scalarRepresentation_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeCorrespondence.scalarRepresentation_base

/-- info: 'FormalProof4FHE.HasteBoots.CodeCorrespondence.mem_code_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeCorrespondence.mem_code_iff

/-- info: 'FormalProof4FHE.HasteBoots.CodeCorrespondence.matrix_distance_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeCorrespondence.matrix_distance_eq

/-- info: 'FormalProof4FHE.HasteBoots.CodeCorrespondence.nearby_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeCorrespondence.nearby_iff

/-- info: 'FormalProof4FHE.HasteBoots.BaseMatrixProximity.far_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BaseMatrixProximity.far_lift

/-- info: 'FormalProof4FHE.HasteBoots.BaseMatrixProximity.matrix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BaseMatrixProximity.matrix_bound

/-- One bad column out of four, tested with three ordered draws. -/
example : ColumnOpening.missBound (Fin 4) 3 1 = (27 : ENNReal) / 64 := by
  norm_num [ColumnOpening.missBound, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]

/-- Transport may omit duplicates without changing acceptance at the sampled columns. -/
example (raw claimed : Fin 4 → ZMod 17) :
    (∀ pos ∈ (List.ofFn ![0, 0, 1]).dedup, raw pos = claimed pos) ↔
      ColumnOpening.Agrees raw claimed ![0, 0, 1] :=
  ColumnOpening.agrees_dedup_iff raw claimed ![0, 0, 1]

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.agrees_dedup_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.agrees_dedup_iff

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.probability_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.probability_eq

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.probability_le

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.falseResponse_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.falseResponse_bound

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.shared_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.shared_bound

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.adaptive_shared_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.adaptive_shared_bound

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.farResponse_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.farResponse_distance

/-- info: 'FormalProof4FHE.HasteBoots.ColumnOpening.adaptive_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ColumnOpening.adaptive_far_bound

/-- info: 'FormalProof4FHE.HasteBoots.ProximityOpening.far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProximityOpening.far_bound

/-- info: 'FormalProof4FHE.HasteBoots.ProximityOpening.encoded_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProximityOpening.encoded_far_bound

/-- info: 'FormalProof4FHE.HasteBoots.StructuredOpening.combine_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructuredOpening.combine_mem

/-- info: 'FormalProof4FHE.HasteBoots.StructuredOpening.combine_distance_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructuredOpening.combine_distance_le

/-- info: 'FormalProof4FHE.HasteBoots.StructuredOpening.near_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructuredOpening.near_bound

/-- info: 'FormalProof4FHE.HasteBoots.StructuredOpening.near_falseValue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructuredOpening.near_falseValue_bound

/-- info: 'FormalProof4FHE.HasteBoots.StructuredOpening.adaptive_near_falseValue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructuredOpening.adaptive_near_falseValue_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommonSourceOpening.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSourceOpening.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.ResponseAssembly.pack_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseAssembly.pack_combine

/-- info: 'FormalProof4FHE.HasteBoots.ResponseAssembly.randomWord_eq_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseAssembly.randomWord_eq_assemble

/-- info: 'FormalProof4FHE.HasteBoots.ResponseAssembly.assemble_encoded_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseAssembly.assemble_encoded_mem

/-- info: 'FormalProof4FHE.HasteBoots.ResponseAssembly.agrees_of_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseAssembly.agrees_of_lanes

/-- info: 'FormalProof4FHE.HasteBoots.ResponseCoefficients.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseCoefficients.decode_encode

/-- info: 'FormalProof4FHE.HasteBoots.ResponseCoefficients.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseCoefficients.encode_decode

/-- info: 'FormalProof4FHE.HasteBoots.ResponseCoefficients.encode_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseCoefficients.encode_aggregate

/-- info: 'FormalProof4FHE.HasteBoots.ResponseCoefficients.decode_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseCoefficients.decode_combine

/-- info: 'FormalProof4FHE.HasteBoots.ResponseCoefficients.recover_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseCoefficients.recover_aggregate

/-- info: 'FormalProof4FHE.HasteBoots.MatrixResponse.finishEncoded_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixResponse.finishEncoded_padded

/-- info: 'FormalProof4FHE.HasteBoots.MatrixResponse.recover_structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixResponse.recover_structured

/-- info: 'FormalProof4FHE.HasteBoots.MatrixResponse.finish_structured_eq_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixResponse.finish_structured_eq_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.MatrixResponse.extractTable_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixResponse.extractTable_encoded

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningSecurity.fixedWord_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningSecurity.fixedWord_bound

/-- info: 'FormalProof4FHE.HasteBoots.ResponseCoefficients.padded_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ResponseCoefficients.padded_aggregate

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness.encoded_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningCompleteness.encoded_response

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness.checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningCompleteness.checks

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness.structured_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningCompleteness.structured_response

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningCompleteness.finish

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness.extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningCompleteness.extract

/-- The first cube bit is low: (1,0,1) is native cell 5. -/
example : (FlatMatrixFold.index 3 (true, (false, (true, ())))).val = 5 := by decide

private def flatQuery : List (MatrixFold.Pair (F := ZMod 17) (Lane := Fin 2)) :=
  [fun bit => if bit then 1 else left, fun bit => if bit then right else 1]

/-- Cell 2 selects the first variable's zero matrix and the second's one matrix. -/
example : FlatMatrixFold.weights flatQuery (2 : Fin 4) = right * left := by decide

/-- The adjacent-cell loop preserves both bit order and noncommuting matrix order. -/
example : FlatMatrixFold.foldAll flatQuery
    (fun cell => if cell = 2 then vector else 0) = (right * left) *ᵥ vector := by decide

example : FlatMatrixFold.foldAll [] (fun _ => vector) = vector := rfl

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.index_succ_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.index_succ_val

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.index_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.index_succ

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.foldFirst_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.foldFirst_constant

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.foldFirst_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.foldFirst_index

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.foldAll_eq_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.foldAll_eq_cube

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.foldAll_eq_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.foldAll_eq_weighted

/-- info: 'FormalProof4FHE.HasteBoots.FlatMatrixFold.finishMessage_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatMatrixFold.finishMessage_eq_fold

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.weight_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.weight_append

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.join_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.join_val

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.index_append_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.index_append_val

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.index_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.index_append

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.weights_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.weights_join

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.weights_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.weights_snoc

/-- info: 'FormalProof4FHE.HasteBoots.MatrixQuerySplit.foldAll_eq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixQuerySplit.foldAll_eq_split

/-- info: 'FormalProof4FHE.HasteBoots.FlatOpeningSecurity.evaluation_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatOpeningSecurity.evaluation_extract

/-- info: 'FormalProof4FHE.HasteBoots.FlatOpeningSecurity.fixedWord_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatOpeningSecurity.fixedWord_bound

/-- info: 'FormalProof4FHE.HasteBoots.FlatOpeningCompleteness.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatOpeningCompleteness.finish

/-- info: 'FormalProof4FHE.HasteBoots.FlatOpeningCompleteness.extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FlatOpeningCompleteness.extract

/-- Leaf and node input images deliberately coincide: no hidden role separator. -/
private def overlappingMerkleEncoding : MerkleOracle.Encoding (Fin 4) (Fin 2) (Fin 4) where
  leaf _ payload := payload
  node _ children := finProdFinEquiv children
  leaf_injective _ := Function.injective_id
  node_injective _ := finProdFinEquiv.injective

example : (MerkleOracle.model overlappingMerkleEncoding 0).view.input
    (overlappingMerkleEncoding.leaf () 2) = ((1 : Fin 2), 0) :=
  (MerkleOracle.model overlappingMerkleEncoding 0).input_mkQuery () (1, 0)

/-- The prefix resolver recovers the whole supported payload even in that common domain. -/
private theorem overlappingMerkle_resolves : MerklePayload.resolve overlappingMerkleEncoding [⟨2, 0⟩] 0 = some 2 := by
  apply MerklePayload.resolve_of_mem
  · intro first firstMember second secondMember _
    simp only [List.mem_singleton] at firstMember secondMember
    subst first
    subst second
    rfl
  · exact List.mem_singleton_self _

/-- A depth-zero root still contributes one target for the later leaf-payload hash. -/
example {Input Digest Payload : Type} [DecidableEq Digest]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy root : Digest)
    (log : MerkleTreeExtractor.QueryLog Input Digest) :
    (MerkleAvailability.targets enc dummy (BinaryTree.Skeleton.perfect 0) log root).length = 1 := rfl

/-- info: 'FormalProof4FHE.HasteBoots.MerkleOracle.same_cell' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleOracle.same_cell

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayload.mem_candidates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayload.mem_candidates_iff

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayload.resolve_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayload.resolve_spec

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayload.resolve_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayload.resolve_of_mem

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.leaf_mem_present' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.leaf_mem_present

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.leaf_mem_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.leaf_mem_targets

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.targets_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.targets_length_le

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.perfect_targets_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.perfect_targets_length_le

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.resolve_cache_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.resolve_cache_iff

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.resolve_eq_of_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.resolve_eq_of_represented

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.payloadAt_eq_of_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.payloadAt_eq_of_represented

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.word_eq_of_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.word_eq_of_represented

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.payload_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.payload_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.word_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.word_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailability.word_eq_of_no_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailability.word_eq_of_no_exception

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailabilityProbability.adds_target_after_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailabilityProbability.adds_target_after_update

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailabilityProbability.uniform_target_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailabilityProbability.uniform_target_bound

/-- info: 'FormalProof4FHE.HasteBoots.MerkleAvailabilityProbability.fresh_update_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleAvailabilityProbability.fresh_update_bound

/-- Native low-bit order: column 2 hashes left at the leaf and right at the root. -/
example : NativeMerklePath.root (fun left right : ℕ => 100 * left + right) 2 7 [11, 13] = 2011 := by
  decide

private def tracedMerkleHash (left right : ℕ) : StateM (List (ℕ × ℕ)) ℕ := do
  modify (fun log => log ++ [(left, right)])
  pure (100 * left + right)

/-- The effectful native loop emits the ordered pairs in the same bottom-up order. -/
example : (NativeMerklePathM.loopFrom tracedMerkleHash 2 0 7 [11, 13]).run [] =
    (2011, [(7, 11), (13, 711)]) := by rfl

example : MerkleBytes.nodeInput ((![1, 2] : Fin 2 → UInt8), ![3, 4]) = [1, 2, 3, 4] := by
  decide

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.direction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.direction

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.root_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.root_append

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.root_snoc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.root_snoc

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.loopFrom_root' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.loopFrom_root

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.loop_eq_root' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.loop_eq_root

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.root_eq_typed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.root_eq_typed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePath.root_native_eq_typed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePath.root_native_eq_typed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePathM.loopFrom_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePathM.loopFrom_root

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePathM.loop_eq_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePathM.loop_eq_root

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePathM.root_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePathM.root_append

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePathM.root_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePathM.root_snoc

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePathM.root_eq_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePathM.root_eq_typed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerklePathM.root_native_eq_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerklePathM.root_native_eq_typed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleVerifier.verifyNodes_eq_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleVerifier.verifyNodes_eq_typed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleVerifier.chain_of_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleVerifier.chain_of_accepted

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleVerifier.payload_of_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleVerifier.payload_of_accepted

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleVerifier.frozen_word_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleVerifier.frozen_word_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleVerifier.nodes_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleVerifier.nodes_query_bound

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleVerifier.payload_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleVerifier.payload_query_bound

/-- info: 'FormalProof4FHE.HasteBoots.MerkleBytes.nodeInput_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleBytes.nodeInput_length

/-- info: 'FormalProof4FHE.HasteBoots.MerkleBytes.nodeInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleBytes.nodeInput_injective

/-- info: 'FormalProof4FHE.HasteBoots.MerkleBytes.leafInput_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleBytes.leafInput_injective

/-- Digest-tree stability alone is insufficient: a later leaf query fills a payload. -/
example : MerkleAvailability.payloadAt overlappingMerkleEncoding 0 [] 0
    BinaryTree.SkeletonLeafIndex.ofLeaf = none := rfl

example : MerkleAvailability.payloadAt overlappingMerkleEncoding 0 [⟨2, 0⟩] 0
    BinaryTree.SkeletonLeafIndex.ofLeaf = some 2 := overlappingMerkle_resolves

example : MerkleAvailability.tree overlappingMerkleEncoding 0 BinaryTree.Skeleton.leaf [] 0 =
    MerkleAvailability.tree overlappingMerkleEncoding 0 BinaryTree.Skeleton.leaf [⟨2, 0⟩] 0 := rfl

private def repeatedRootState : MerklePayloadCheckpoints.State (Input := Fin 4) (Digest := Fin 2)
    (fun _ : Unit => BinaryTree.Skeleton.perfect 0) :=
  ((MerkleTreeMultiExtractability.ExtractorState.empty).recordCumulative () [] 0).recordCumulative () [] 0

/-- Shared labels are deduplicated across separately recorded roots. -/
example : (repeatedRootState.targetSet (MerkleOracle.model overlappingMerkleEncoding 0).view).card = 1 := by
  decide

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.candidates_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.candidates_append

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.resolve_append_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.resolve_append_of_ne

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.resolve_append_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.resolve_append_of_mem

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.payloadAt_append_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.payloadAt_append_cached

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.tree_append_outside_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.tree_append_outside_targets

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.payloadAt_append_outside_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.payloadAt_append_outside_targets

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.word_append_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.word_append_cached

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadEvolution.word_append_outside_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadEvolution.word_append_outside_targets

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.stable_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.stable_empty

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.stable_append_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.stable_append_cached

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.stable_append_outside_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.stable_append_outside_live

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.live_targets_eq_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.live_targets_eq_frozen

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.stable_append_outside_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.stable_append_outside_frozen

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.stable_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.stable_record

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.same_root_payloads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.same_root_payloads

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.stable_append_no_fresh_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.stable_append_no_fresh_target

/-- info: 'FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints.fresh_target_of_not_stable_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerklePayloadCheckpoints.fresh_target_of_not_stable_append

/-- info: 'FormalProof4FHE.HasteBoots.MerkleCheckpointProbability.live_target_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleCheckpointProbability.live_target_bound

/-- info: 'FormalProof4FHE.HasteBoots.MerkleCheckpointProbability.destabilization_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MerkleCheckpointProbability.destabilization_bound

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.charge_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.charge_pure

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.charge_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.charge_query_bind

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.terminal_risk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.terminal_risk_le

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.terminal_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.terminal_event_le

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.charge_const_eq_expected_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.charge_const_eq_expected_count

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.terminal_event_le_mul_expected_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.terminal_event_le_mul_expected_count


/-- A repeated hash remains in the ordered transcript without duplicating its key. -/
private noncomputable def firstHashState : CachedHashHandler.State (Fin 4) (Fin 2) :=
  CachedHashHandler.observe CachedHashHandler.empty 2 0
    (CachedHashHandler.empty.cache.cacheQuery 2 0)

private theorem firstHashState_coherent : CachedHashHandler.Coherent firstHashState :=
  CachedHashHandler.coherent_fresh CachedHashHandler.empty CachedHashHandler.coherent_empty
    2 0 rfl

example : firstHashState.cache 2 = some 0 := by rfl

example : (CachedHashHandler.observe firstHashState 2 0 firstHashState.cache).log.length = 2 := by
  rfl

example : (CachedHashHandler.observe firstHashState 2 0 firstHashState.cache).keys =
    firstHashState.keys :=
  CachedHashHandler.cached_keys firstHashState firstHashState_coherent 2 0 rfl

example : (CachedHashHandler.observe firstHashState 3 1
    (firstHashState.cache.cacheQuery 3 1)).keys.card = 2 := by
  decide

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.coherent_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.coherent_empty

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.coherent_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.coherent_cached

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.coherent_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.coherent_fresh

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.cached_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.cached_keys

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.fresh_key_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.fresh_key_count

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.represents_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.represents_cache

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.run_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.run_cached

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.run_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.run_fresh

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.coherent_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.coherent_step

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.coherent_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.coherent_run

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.project_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.project_step

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashHandler.project_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashHandler.project_run

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.failure_risk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.failure_risk_eq

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedHazard.terminal_failure_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedHazard.terminal_failure_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCheckpoint.cached_loss_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCheckpoint.cached_loss_zero

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCheckpoint.fresh_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCheckpoint.fresh_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCheckpoint.step_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCheckpoint.step_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCheckpoint.suffix_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCheckpoint.suffix_loss_bound


private def executionShape (_ : Unit) : BinaryTree.Skeleton := .leaf

private noncomputable def recordedExecution :
    CheckpointExecution.State (Input := Fin 4) (Digest := Fin 2) executionShape :=
  CheckpointExecution.record executionShape (CheckpointExecution.empty executionShape) () 0

/-- A later leaf hash changes payload availability even though the digest tree
is unchanged. The runtime must remember this failure across later recordings. -/
private theorem recordedExecution_changed :
    ¬MerklePayloadCheckpoints.StableAt overlappingMerkleEncoding 0 executionShape
      recordedExecution.checkpoints firstHashState.log := by
  intro stable
  have frozen := stable.payloads () ⟨0, []⟩ (by exact List.mem_singleton_self _)
    BinaryTree.SkeletonLeafIndex.ofLeaf
  change (none : Option (Fin 4)) = MerklePayload.resolve overlappingMerkleEncoding [⟨2, 0⟩] 0 at frozen
  rw [overlappingMerkle_resolves] at frozen
  cases frozen

private theorem recordedExecution_fired :
    (CheckpointExecution.afterHash overlappingMerkleEncoding 0 executionShape recordedExecution
      firstHashState).failed = true :=
  (CheckpointExecution.afterHash_failed_iff overlappingMerkleEncoding 0 executionShape
    recordedExecution firstHashState).mpr (Or.inr recordedExecution_changed)

example : (CheckpointExecution.record executionShape
    (CheckpointExecution.afterHash overlappingMerkleEncoding 0 executionShape recordedExecution
      firstHashState) () 1).failed = true := recordedExecution_fired

/-- Snapshots retain the actual whole log, including repeated cached calls. -/
example : (CheckpointExecution.record executionShape
    (CheckpointExecution.afterHash overlappingMerkleEncoding 0 executionShape recordedExecution
      firstHashState) () 1).checkpoints.cumulativeLog = [⟨2, 0⟩] := rfl

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.good_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.good_empty

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.afterHash_failed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.afterHash_failed_iff

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.afterHash_clear_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.afterHash_clear_stable

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.afterHash_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.afterHash_good

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.record_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.record_good

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.project_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.project_step

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.project_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.project_run

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.audited_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.audited_step

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.audited_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.audited_run

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.failed_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.failed_step

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.failed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.failed_run

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.step_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.step_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.failure_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.failure_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointExecution.failure_from_empty_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointExecution.failure_from_empty_le_charge


private noncomputable def collisionHashState : CachedHashHandler.State (Fin 4) (Fin 2) :=
  CachedHashHandler.observe firstHashState 3 0 (firstHashState.cache.cacheQuery 3 0)

private theorem collisionHashState_collision : OracleComp.CacheHasCollision collisionHashState.cache := by
  exact ⟨2, 3, 0, 0, by decide, by rfl, by rfl, HEq.rfl⟩

/-- A later fresh query cannot erase the collision between the earlier keys. -/
example : OracleComp.CacheHasCollision (collisionHashState.cache.cacheQuery 0 1) :=
  CachedHashCollision.collision_mono _ _ (OracleSpec.QueryCache.le_cacheQuery _ (by rfl))
    collisionHashState_collision

/-- Collision loss is zero for a repeated input, even in a populated cache. -/
example : CachedHashCollision.loss 2 firstHashState = 0 := rfl

/-- The root-wide event detects a late authenticated payload missing from the
immutable source snapshot, without relying on a changed digest tree. -/
example : CheckpointAvailability.Disagreement overlappingMerkleEncoding 0 executionShape
    (CheckpointExecution.afterHash overlappingMerkleEncoding 0 executionShape recordedExecution
      firstHashState) := by
  refine ⟨(), ⟨0, []⟩, List.mem_singleton_self _, BinaryTree.SkeletonLeafIndex.ofLeaf,
    ⟨[], rfl⟩, 0, 2, rfl, ?_, ?_⟩
  · rfl
  · change (none : Option (Fin 4)) ≠ some 2
    decide

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.collision_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.collision_mono

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.no_collision_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.no_collision_empty

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.cache_monotone_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.cache_monotone_step

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.cache_monotone_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.cache_monotone_run

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.cached_loss_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.cached_loss_zero

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.fresh_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.fresh_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.CachedHashCollision.step_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedHashCollision.step_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.safe_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.safe_empty

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.cache_monotone_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.cache_monotone_step

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.cache_monotone_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.cache_monotone_run

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.bad_persistent_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.bad_persistent_run

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.collision_step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.collision_step_bound

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.step_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.step_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.failure_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.failure_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.failure_from_empty_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.failure_from_empty_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointAvailability.current_payload_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointAvailability.current_payload_eq

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointAvailability.frozen_payload_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointAvailability.frozen_payload_eq

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointAvailability.no_disagreement_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointAvailability.no_disagreement_of_safe

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointAvailability.disagreement_implies_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointAvailability.disagreement_implies_bad

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointAvailability.disagreement_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointAvailability.disagreement_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointAvailability.disagreement_from_empty_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointAvailability.disagreement_from_empty_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointCollision.hash_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointCollision.hash_loss


section NativeOpeningExecutionSmoke

open OracleSpec OracleComp

private inductive OpeningEvent where
  | snapshot : Fin 2 → OpeningEvent
  | hash : Fin 4 → OpeningEvent
  deriving DecidableEq

private abbrev OpeningSpec := CheckpointExecution.Spec (Unit →ₒ Unit) Unit (Fin 4) (Fin 2)

private def tracedOpeningHandler : QueryImpl OpeningSpec (StateM (List OpeningEvent)) :=
  fun query => match query with
  | .inl _ => pure ()
  | .inr (.inl input) => do
      modify (fun events => events ++ [.hash input])
      pure (0 : Fin 2)
  | .inr (.inr (_, root)) => do
      modify (fun events => events ++ [.snapshot root])
      pure ()

private def nativeOpeningRequest : NativeOpeningAvailability.Request (Digest := Fin 2)
    (Payload := Fin 4) (fun _ : Unit => 1) :=
  ⟨(), 0, 0, 2, 0, ⟨[1], rfl⟩⟩

private def nativeOpeningFront : OracleComp OpeningSpec
    (NativeOpeningAvailability.Request (Digest := Fin 2) (Payload := Fin 4) (fun _ : Unit => 1)) := do
  let _ ← liftM (OpeningSpec.query (.inr (.inr ((), 0))))
  pure nativeOpeningRequest

/-- The checkpoint is recorded before checking; leaf and node calls use the
same routed hash. The node preimage is the raw ordered pair (0,1). -/
example : (simulateQ tracedOpeningHandler (NativeOpeningAvailability.checked (Unit →ₒ Unit)
    overlappingMerkleEncoding (fun _ : Unit => 1) nativeOpeningFront)).run [] =
      ((nativeOpeningRequest, true), [.snapshot 0, .hash 2, .hash 1]) := rfl

private def wrongLeafRequest : NativeOpeningAvailability.Request (Digest := Fin 2)
    (Payload := Fin 4) (fun _ : Unit => 1) := { nativeOpeningRequest with leaf := 1 }

/-- A wrong supplied leaf digest rejects after the whole-payload hash and
performs no sibling hash. -/
example : (simulateQ tracedOpeningHandler (NativeOpeningAvailability.checked (Unit →ₒ Unit)
    overlappingMerkleEncoding (fun _ : Unit => 1) (pure wrongLeafRequest))).run [] =
      ((wrongLeafRequest, false), [.hash 2]) := rfl

end NativeOpeningExecutionSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleExecution.random_step_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleExecution.random_step_support

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleExecution.random_run_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleExecution.random_run_support

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleExecution.simulate_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleExecution.simulate_embed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleExecution.project_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleExecution.project_embed

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleExecution.payload_of_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleExecution.payload_of_accepted

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleExecution.payload_after_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMerkleExecution.payload_after_continuation

/-- info: 'FormalProof4FHE.HasteBoots.NativeOpeningAvailability.false_acceptance_of_word_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeOpeningAvailability.false_acceptance_of_word_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.NativeOpeningAvailability.disagreement_of_false_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeOpeningAvailability.disagreement_of_false_acceptance

/-- info: 'FormalProof4FHE.HasteBoots.NativeOpeningAvailability.false_acceptance_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeOpeningAvailability.false_acceptance_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.NativeOpeningAvailability.false_acceptance_from_empty_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeOpeningAvailability.false_acceptance_from_empty_le_charge


section InterleavedWorkerSmoke

open OracleSpec OracleComp

private def workerShape (_ : Unit) : BinaryTree.Skeleton := .perfect 1
private abbrev WorkerState := CheckpointExecution.State (Input := Fin 4) (Digest := Fin 2) workerShape
private def workerBase : QueryImpl (Unit →ₒ Unit) ProbComp := fun _ => pure ()

private noncomputable def workerStart : WorkerState :=
  let node := CachedHashHandler.observe firstHashState 1 0 (firstHashState.cache.cacheQuery 1 0)
  let other := CachedHashHandler.observe node 3 1 (node.cache.cacheQuery 3 1)
  ⟨other, MerkleTreeMultiExtractability.ExtractorState.empty, false⟩

private noncomputable def workerStep (state : WorkerState) (query : Fin 4) (answer : Fin 2) : WorkerState :=
  CheckpointExecution.afterHash overlappingMerkleEncoding 0 workerShape state
    (CachedHashHandler.observe state.hash query answer state.hash.cache)

private theorem workerStep_supported (state : WorkerState) (query : Fin 4) (answer : Fin 2)
    (known : state.hash.cache query = some answer) :
    (answer, workerStep state query answer) ∈ support
      ((CheckpointExecution.handler workerBase overlappingMerkleEncoding 0 workerShape
        (.inr (.inl query))).run state) := by
  change (answer, workerStep state query answer) ∈ support
    ((fun result => (result.1, CheckpointExecution.afterHash overlappingMerkleEncoding 0 workerShape state result.2)) <$>
      (CachedHashHandler.handler query).run state.hash)
  rw [CachedHashHandler.run_cached state.hash query answer known, map_pure, mem_support_pure_iff]
  rfl

private noncomputable def workerLeafState := workerStep workerStart 2 0
private noncomputable def workerPauseState := workerStep workerLeafState 3 1
private noncomputable def workerFinalState := workerStep workerPauseState 1 0

private def otherWorkerQuery : OracleComp
    (CheckpointExecution.Spec (Unit →ₒ Unit) Unit (Fin 4) (Fin 2)) Unit := do
  let _ ← liftM ((CheckpointExecution.Spec (Unit →ₒ Unit) Unit (Fin 4) (Fin 2)).query (.inr (.inl 3)))
  pure ()

private theorem otherWorkerQuery_supported :
    ((), workerPauseState) ∈ support ((simulateQ
      (CheckpointExecution.handler workerBase overlappingMerkleEncoding 0 workerShape)
        otherWorkerQuery).run workerLeafState) := by
  rw [otherWorkerQuery, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
  refine ⟨((1 : Fin 2), workerPauseState), workerStep_supported _ _ _ rfl, ?_⟩
  rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff]

/-- Worker A's leaf and node calls have a real shared hash call from worker B
between them. Both workers use the same actual canonical cached handler. -/
private theorem interleaved_native_worker : InterleavedMerkleWorker.Run workerBase
    overlappingMerkleEncoding 0 workerShape
      (NativeMerkleVerifier.verifyPayload overlappingMerkleEncoding 1 0 2 0 0 ⟨[1], rfl⟩)
        workerStart true workerFinalState := by
  refine InterleavedMerkleWorker.Run.query _ (middle := workerLeafState) (answer := (0 : Fin 2))
    (workerStep_supported _ _ _ rfl) ?_
  change InterleavedMerkleWorker.Run workerBase overlappingMerkleEncoding 0 workerShape
    (NativeMerkleVerifier.verifyNodes overlappingMerkleEncoding 1 0 0 0 ⟨[1], rfl⟩)
      workerLeafState true workerFinalState
  refine InterleavedMerkleWorker.Run.pause otherWorkerQuery (middle := workerPauseState) (value := ())
    otherWorkerQuery_supported ?_
  change InterleavedMerkleWorker.Run workerBase overlappingMerkleEncoding 0 workerShape
    (liftM ((Fin 4 →ₒ Fin 2).query 1) >>= fun value => pure (value == (0 : Fin 2)))
      workerPauseState true workerFinalState
  refine InterleavedMerkleWorker.Run.query _ (middle := workerFinalState) (answer := (0 : Fin 2))
    (workerStep_supported _ _ _ rfl) ?_
  exact InterleavedMerkleWorker.Run.done true workerFinalState

example : workerFinalState.hash.log = [⟨2, 0⟩, ⟨1, 0⟩, ⟨3, 1⟩, ⟨2, 0⟩, ⟨3, 1⟩, ⟨1, 0⟩] := rfl

example : simulateQ workerFinalState.hash.cache.toPartialImpl
    (NativeMerkleVerifier.verifyPayload overlappingMerkleEncoding 1 0 2 0 0 ⟨[1], rfl⟩) = some true :=
  InterleavedMerkleWorker.replay workerBase overlappingMerkleEncoding 0 workerShape interleaved_native_worker

end InterleavedWorkerSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CachedVerifierReplay.run_caching_of_partial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedVerifierReplay.run_caching_of_partial

/-- info: 'FormalProof4FHE.HasteBoots.CachedVerifierReplay.payload_of_partial_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CachedVerifierReplay.payload_of_partial_acceptance

/-- info: 'FormalProof4FHE.HasteBoots.InterleavedMerkleWorker.hash_query_caches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InterleavedMerkleWorker.hash_query_caches

/-- info: 'FormalProof4FHE.HasteBoots.InterleavedMerkleWorker.cache_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InterleavedMerkleWorker.cache_monotone

/-- info: 'FormalProof4FHE.HasteBoots.InterleavedMerkleWorker.replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InterleavedMerkleWorker.replay

/-- info: 'FormalProof4FHE.HasteBoots.InterleavedMerkleWorker.payload_of_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InterleavedMerkleWorker.payload_of_accepted

/-- info: 'FormalProof4FHE.HasteBoots.ParallelColumnAvailability.failure_of_word_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParallelColumnAvailability.failure_of_word_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.ParallelColumnAvailability.failure_implies_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParallelColumnAvailability.failure_implies_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.ParallelColumnAvailability.no_failure_of_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParallelColumnAvailability.no_failure_of_safe

/-- info: 'FormalProof4FHE.HasteBoots.ParallelColumnAvailability.replays_of_worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParallelColumnAvailability.replays_of_worker

/-- info: 'FormalProof4FHE.HasteBoots.ParallelColumnAvailability.failure_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParallelColumnAvailability.failure_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.ParallelColumnAvailability.failure_from_empty_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParallelColumnAvailability.failure_from_empty_le_charge


section NativeCoordinateSmoke

/-- Packing width two and code-symbol width three use different strides. -/
example : (NativeColumnLayout.responseAddress (1 : Fin 2) (2 : Fin 4) (2 : Fin 3)).val = 20 := by decide
example : (NativeColumnLayout.payloadAddress (1 : Fin 2) (2 : Fin 3)).val = 5 := by decide
example : (NativeColumnLayout.weightAddress (1 : Fin 2) (1 : Fin 2)).val = 3 := by decide

private def coordinateWeights : Fin 4 → ZMod 17 := ![1, 2, 3, 4]

private def coordinateColumn : NativeColumnLayout.Column (ZMod 17) (Fin 2) 2 2 3 where
  position := 2
  values := ![5, 6, 7, 8, 9, 10]
  leaf := 0
  siblings := ⟨[0, 0], rfl⟩

example : NativeColumnLayout.dot coordinateWeights coordinateColumn.values (0 : Fin 2) (2 : Fin 3) = 10 := by decide
example : NativeColumnLayout.dot coordinateWeights coordinateColumn.values (1 : Fin 2) (1 : Fin 3) = 3 := by decide

private def coordinateResponse : Fin (2 * (4 * 3)) → ZMod 17 :=
  NativeColumnLayout.flattenResponse (fun (lane : Fin 2) (position : Fin 4) (coordinate : Fin 3) =>
    if position = 2 then (if lane = 0 then ![4, 7, 10] else ![13, 3, 10]) coordinate else 0)

example : NativeColumnLayout.allCoordinates [coordinateColumn] coordinateWeights coordinateWeights
    coordinateResponse coordinateResponse = true := by decide

/-- Passing the random response does not hide a wrong structured response. -/
example : NativeColumnLayout.allCoordinates [coordinateColumn] coordinateWeights coordinateWeights
    coordinateResponse (fun _ => 0) = false := by decide

private def repeatedColumnDraws : Fin 4 → Fin 4 := ![3, 1, 3, 2]

/-- Three distinct transported columns cover all four original ordered draws. -/
example : NativeColumnLayout.Covers
    (NativeColumnLayout.attach ([1, 2, 3] : List (Fin 4))
      (List.replicate 3 coordinateColumn.toData)) repeatedColumnDraws := by
  apply NativeColumnLayout.covers_attach _ _ _ rfl
  intro i
  fin_cases i <;> decide

example : NativeColumnLayout.unpackPayload 4 ([3, 5] : List (ZMod 17)) 3 = 0 := by decide

end NativeCoordinateSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.weight_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.weight_address

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.payload_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.payload_address

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.response_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.response_address

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.positions_attach' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.positions_attach

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.mem_distinctIndices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.mem_distinctIndices

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.covers_attach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.covers_attach

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.covers_distinct_attach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.covers_distinct_attach

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.dot_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.dot_eq_sum

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.unpack_packPayload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.unpack_packPayload

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.expanded_flattenWeights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.expanded_flattenWeights

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.expanded_flattenResponse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.expanded_flattenResponse

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.dot_eq_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.dot_eq_combine

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.allCoordinates_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.allCoordinates_eq_true_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnLayout.agrees_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnLayout.agrees_of_checks

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.values_of_no_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.values_of_no_failure

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.agrees_of_authentication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.agrees_of_authentication

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.matrix_checks_of_authentication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.matrix_checks_of_authentication

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.matrix_pair_checks_of_authentication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.matrix_pair_checks_of_authentication

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.failure_implies_availability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.failure_implies_availability

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.failure_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.failure_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks.failure_from_empty_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedColumnChecks.failure_from_empty_le_charge


section AdaptiveResponseSmoke

open OracleComp

/-- Response coins may be correlated with the earlier challenge. -/
private def probabilisticBitResponse (challenge : Fin 2) : ProbComp (Fin 2) := do
  let coin ← $ᵗ (Fin 2)
  pure (if coin = 0 then challenge else 0)

/-- Keeping a challenge-dependent randomized response does not inflate the
unconditional probability of an event on that earlier challenge. -/
example : Pr{let pair ← AdaptiveResponse.choose ($ᵗ (Fin 2)) probabilisticBitResponse}[pair.1 = 0] ≤
    (1 : ENNReal) / 2 := by
  have bound := AdaptiveResponse.event_le ($ᵗ (Fin 2)) probabilisticBitResponse (fun challenge => challenge = 0)
  rw [SampleableType.prEvent_uniformSample_eq_singleton] at bound
  simpa only [Fintype.card_fin, Nat.cast_ofNat, one_div] using bound

private def drawAfterResponse : ProbComp ((Fin 2 × Fin 2) × Fin 2) := do
  let pair ← AdaptiveResponse.choose ($ᵗ (Fin 2)) probabilisticBitResponse
  let draw ← $ᵗ (Fin 2)
  pure (pair, draw)

/-- Choosing the response first leaves a genuinely later uniform draw with
its exact singleton probability, irrespective of response/challenge correlation. -/
example : Pr{let result ← drawAfterResponse}[result.2 = result.1.2] ≤ (1 : ENNReal) / 2 := by
  have bound := prEvent_bind_le_of_forall_le
    (AdaptiveResponse.choose ($ᵗ (Fin 2)) probabilisticBitResponse)
    (fun pair => do let draw ← $ᵗ (Fin 2); pure (pair, draw))
    (fun result => result.2 = result.1.2)
    (ε := (1 : ENNReal) / 2) (fun pair => by
      simpa only [prEvent_norm, SampleableType.prEvent_uniformSample_eq_singleton,
        Fintype.card_fin, Nat.cast_ofNat, one_div] using (le_rfl : (2 : ENNReal)⁻¹ ≤ 2⁻¹))
  exact bound

end AdaptiveResponseSmoke

/-- info: 'FormalProof4FHE.HasteBoots.AdaptiveResponse.event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveResponse.event_le

/-- info: 'FormalProof4FHE.HasteBoots.AdaptiveResponse.event_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveResponse.event_le_add

/-- info: 'FormalProof4FHE.HasteBoots.CommonSourceOpeningKernel.far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSourceOpeningKernel.far_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommonSourceOpeningKernel.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommonSourceOpeningKernel.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.MatrixOpeningKernel.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixOpeningKernel.soundness_bound


section SharedSamplingSmoke

open OracleSpec OracleComp

private def sharedSamplingResponse (_challenge : Fin 2) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (Fin 2) :=
  liftM ((CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)).query (.inr (.inl 2)))

private theorem sharedSamplingResponse_run (challenge : Fin 2) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape) (sharedSamplingResponse challenge)).run workerStart =
        pure ((0 : Fin 2), workerStep workerStart 2 0) := by
  rw [sharedSamplingResponse, simulateQ_spec_query]
  change (fun result => (result.1,
    CheckpointExecution.afterHash overlappingMerkleEncoding 0 workerShape workerStart result.2)) <$>
      (CachedHashHandler.handler 2).run workerStart.hash = _
  rw [CachedHashHandler.run_cached workerStart.hash 2 0 rfl, map_pure]
  rfl

/-- Two real private uniform draws surround a cached hash response. The full
state returned by that hash survives the later draw exactly. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
      (InteractiveSampling.program ($ᵗ (Fin 2)) sharedSamplingResponse ($ᵗ (Fin 2)))).run workerStart =
    (do
      let challenge ← $ᵗ (Fin 2)
      let draw ← $ᵗ (Fin 2)
      pure (((challenge, (0 : Fin 2)), draw), workerStep workerStart 2 0)) := by
  rw [InteractiveSampling.run_program]
  simp only [InteractiveSampling.experiment, AdaptiveResponse.choose, sharedSamplingResponse_run,
    pure_bind, map_bind, map_pure]
  rfl

/-- The commitment really hashes before the frozen source and private draw.
The analysis records the actual post-hash log, without resetting the cache. -/
example : CommitmentPrefix.witness (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape () (sharedSamplingResponse 1)
      (fun _ => PrivateSampling.embed (Cfg := Unit) (Input := Fin 4) (Digest := Fin 2) ($ᵗ (Fin 2))) workerStart =
    (do
      let draw ← $ᵗ (Fin 2)
      pure (((0 : Fin 2), workerStep workerStart 2 0),
        (draw, CheckpointExecution.record workerShape (workerStep workerStart 2 0) () 0))) := by
  simp only [CommitmentPrefix.witness, sharedSamplingResponse_run, pure_bind, PrivateSampling.run_probComp]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

end SharedSamplingSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PrivateSampling.run_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateSampling.run_embed

/-- info: 'FormalProof4FHE.HasteBoots.PrivateSampling.run_probComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateSampling.run_probComp

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistory.recorded_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointHistory.recorded_step

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistory.recorded_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckpointHistory.recorded_run

/-- info: 'FormalProof4FHE.HasteBoots.InteractiveSampling.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractiveSampling.run_program

/-- info: 'FormalProof4FHE.HasteBoots.InteractiveSampling.retain_run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractiveSampling.retain_run_program

/-- info: 'FormalProof4FHE.HasteBoots.InteractiveSampling.earlier_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractiveSampling.earlier_event_le

/-- info: 'FormalProof4FHE.HasteBoots.SharedMatrixSampling.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedMatrixSampling.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.SharedMatrixSampling.arithmetic_after_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedMatrixSampling.arithmetic_after_bound

/-- info: 'FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening.accepted_wrong_implies_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractiveAuthenticatedOpening.accepted_wrong_implies_failure

/-- info: 'FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractiveAuthenticatedOpening.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommitmentPrefix.snapshot_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommitmentPrefix.snapshot_recorded

/-- info: 'FormalProof4FHE.HasteBoots.CommitmentPrefix.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommitmentPrefix.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.CommitmentPrefix.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommitmentPrefix.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommittedMatrixOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommittedMatrixOpening.soundness_from_empty

section PackedSumcheckSmoke

private noncomputable def packedNodes : PackedSumcheckRound.Node 2 ↪ ZMod 17 :=
  NativePackedInterpolation.nodes 17 (by decide)

private def packedLaneValues (bit : Bool) (lane : Fin 2) : ZMod 17 :=
  ((2 * lane.val + (if bit then 1 else 0) + 1 : ℕ) : ZMod 17)

private def packedChallenges (lane : Fin 2) : ZMod 17 := if lane.val = 0 then 2 else 1

/-- A row challenge selects a different original lane and Boolean branch. -/
example : (∑ bit : Bool, PackedSumcheckRound.challengePair packedNodes packedChallenges bit *ᵥ
    packedLaneValues bit) 0 = (3 : ZMod 17) := by
  rw [PackedSumcheckRound.challengePair_fold]
  change (PackedSumcheckRound.factorPolynomial packedNodes packedLaneValues).eval (packedNodes (false, 1)) = 3
  rw [PackedSumcheckRound.factorPolynomial_node]
  rfl

example : (∑ bit : Bool, PackedSumcheckRound.challengePair packedNodes packedChallenges bit *ᵥ
    packedLaneValues bit) 1 = (2 : ZMod 17) := by
  rw [PackedSumcheckRound.challengePair_fold]
  change (PackedSumcheckRound.factorPolynomial packedNodes packedLaneValues).eval (packedNodes (true, 0)) = 2
  rw [PackedSumcheckRound.factorPolynomial_node]
  rfl

/-- Repeated factor indices represent a square, rather than a squarefree product. -/
example : PackedSumcheckRound.claim (fun _ : Unit => 2) (fun _ => (1 : ZMod 17))
    (fun _ _ => ()) (fun _ bit (_ : Unit) lane => packedLaneValues bit lane) = ![5, 8] := by
  funext lane
  fin_cases lane <;> norm_num [PackedSumcheckRound.claim, PackedSumcheckRound.expression,
    packedLaneValues, Fin.prod_univ_two]
  decide

/-- Exactly two independently sampled zeroes heal X versus zero. -/
example [SampleableType (Fin 2 → ZMod 17)] :
    Pr{let challenge ← $ᵗ (Fin 2 → ZMod 17)}[
      ∀ lane, (Polynomial.X : Polynomial (ZMod 17)).eval (challenge lane) =
        (0 : Polynomial (ZMod 17)).eval (challenge lane)] = (1 / 17 : ENNReal) ^ 2 := by
  rw [PackedSumcheckProbability.all_agree_probability]
  norm_num [Polynomial.eval_X, Polynomial.eval_zero, Finset.filter_eq', ZMod.card]

/-- The native 7-entry degree-six message reads adjacent entries for lane one. -/
example : NativePackedInterpolation.Checks (k := 2) (degree := 6) (by decide)
    (fun lane : Fin 2 => if lane.val = 0 then (3 : ZMod 17) else 7)
    (fun index : Fin 7 => (index.val + 1 : ℕ)) := by
  intro lane
  fin_cases lane <;> decide

end PackedSumcheckSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckRound.factorPolynomial_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckRound.factorPolynomial_node

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckRound.factorPolynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckRound.factorPolynomial_degree

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckRound.challengePair_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckRound.challengePair_fold

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckRound.polynomial_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckRound.polynomial_check

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckRound.polynomial_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckRound.polynomial_fold

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckRound.polynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckRound.polynomial_degree

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckProbability.agreement_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckProbability.agreement_card

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckProbability.all_agree_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckProbability.all_agree_probability

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckProbability.all_agree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckProbability.all_agree_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckProbability.checked_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckProbability.checked_distinct

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckProbability.false_claim_healing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckProbability.false_claim_healing_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckProbability.round_healing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckProbability.round_healing_bound

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.interpolation_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.interpolation_capacity

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.nodeIndex_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.nodeIndex_val

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.nodeIndex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.nodeIndex_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.basis_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.basis_eval

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.messagePolynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.messagePolynomial_degree

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.messagePolynomial_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.messagePolynomial_node

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.checks_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.checks_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedInterpolation.round_healing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedInterpolation.round_healing_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckExecution.roundPolynomial_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckExecution.roundPolynomial_check

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckExecution.sum_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckExecution.sum_fold

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckExecution.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckExecution.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckExecution.native_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckExecution.native_soundness_bound

section PackedZeroFirstSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

/-- The low Boolean coordinate selects the low equality-point coordinate. -/
example : PackedZeroEquality.equality (![2, 3] : Fin 2 → ZMod 17) (![1, 0] : Fin 2 → Fin 2) = 13 := by
  rw [PackedZeroEquality.equality_prod]
  decide

/-- Row-major mixing combines different equality tables with different columns. -/
example : PackedZeroFirst.mixedEquality (F := ZMod 17) !![1, 2; 3, 4]
    (fun point (_ : Unit) => if point.val = 0 then 2 else 5) () = ![12, 9] := by
  funext lane
  fin_cases lane <;> decide

/-- Regrouping coins keeps each matrix row with that row's own challenge. -/
example : PackedZeroMixing.rowCoins (F := ZMod 17) (k := 2)
    (!![1, 2; 3, 4], ![5, 6]) 1 = (![3, 4], 6) := rfl

/-- A nonzero vector has a uniform dot product even though one entry is zero. -/
example : Pr{let row ← $ᵗ (Fin 2 → ZMod 17)}[
    ∑ point : Fin 2, row point * (![1, 0] : Fin 2 → ZMod 17) point = 0] = (1 / 17 : ENNReal) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using PackedZeroMixing.dot_zero_probability
    (![1, 0] : Fin 2 → ZMod 17) ⟨0, by decide⟩

private def zeroFirstMessage (point : Fin 2) (index : Fin 7) : ZMod 17 :=
  if index.val < 4 then 0 else (point.val + index.val + 1 : ℕ)

/-- Nonzero trailing entries are allowed; all first 2*k entries are checked. -/
example : NativePackedZeroFirst.checkFirst (k := 2) (degree := 6) (by decide) zeroFirstMessage = true := by decide

private def badZeroFirstMessage (point : Fin 2) (index : Fin 7) : ZMod 17 :=
  if point.val = 1 ∧ index.val = 3 then 1 else zeroFirstMessage point index

/-- The last boundary entry in the last row cannot be skipped. -/
example : NativePackedZeroFirst.checkFirst (k := 2) (degree := 6) (by decide) badZeroFirstMessage = false := by decide

end PackedZeroFirstSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroFirst.polynomial_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroFirst.polynomial_node

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroFirst.boundary_of_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroFirst.boundary_of_vanishes

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroFirst.polynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroFirst.polynomial_degree

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroFirst.reduced_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroFirst.reduced_expression

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroFirst.reduce_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroFirst.reduce_honest

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroFirst.boundary_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroFirst.boundary_distinct

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroMixing.dot_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroMixing.dot_surjective

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroMixing.dot_zero_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroMixing.dot_zero_probability

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroMixing.all_rows_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroMixing.all_rows_probability

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroMixing.row_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroMixing.row_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroMixing.rows_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroMixing.rows_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroMixing.mixing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroMixing.mixing_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroEquality.equality_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroEquality.equality_prod

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroEquality.weighted_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroEquality.weighted_sum

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroEquality.mle_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroEquality.mle_degree

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroEquality.point_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroEquality.point_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroEquality.points_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroEquality.points_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroEquality.boundary_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroEquality.boundary_miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroReduction.healing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroReduction.healing_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroReduction.native_healing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroReduction.native_healing_bound

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedZeroFirst.nodeIndex_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedZeroFirst.nodeIndex_surjective

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedZeroFirst.checkFirst_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedZeroFirst.checkFirst_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativePackedZeroFirst.checkFirst_boundary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePackedZeroFirst.checkFirst_boundary_iff

section PublicEqualitySmoke

/-- Coordinates zero and two are respectively native address bits zero and two. -/
example : PackedEqualityCube.bits 3 (true, (false, (true, ()))) = ![1, 0, 1] := by
  funext index
  fin_cases index <;> rfl

example : (FlatMatrixFold.index 3 (true, (false, (true, ())))).val = 5 := by decide

/-- The native two-block builder keeps the first coordinate at the low bit. -/
example : NativeEqualityTable.table 2 (![2, 3] : Fin 2 → ZMod 17) = ![2, 13, 14, 6] := by
  funext index
  fin_cases index <;> decide

private def publicFirstPair (bit : Bool) : Matrix (Fin 2) (Fin 2) (ZMod 17) :=
  if bit then right else left

private def publicSecondPair (bit : Bool) : Matrix (Fin 2) (Fin 2) (ZMod 17) :=
  if bit then left else right

/-- Later matrices act on the left; noncommuting query reversal changes the value. -/
example : PackedPublicEquality.evaluateSingle [publicFirstPair, publicSecondPair]
    (![2, 3] : Fin 2 → ZMod 17) vector = ![2, 0] := by decide

example : PackedPublicEquality.evaluateSingle [publicSecondPair, publicFirstPair]
    (![2, 3] : Fin 2 → ZMod 17) vector = ![6, 0] := by decide

/-- The public terminal needs no oracle-supplied EQ vector. -/
example : PackedZeroTerminal.check (fun _ : Unit => 2) (fun _ => (1 : ZMod 17))
    (fun _ _ => ()) (fun (_ : Unit) (_ : Fin 2) => 3) ![2, 4] ![1, 2] = true := by decide

/-- A wrong endpoint in the final lane is rejected by the terminal identity. -/
example : PackedZeroTerminal.check (fun _ : Unit => 2) (fun _ => (1 : ZMod 17))
    (fun _ _ => ()) (fun (_ : Unit) (_ : Fin 2) => 3) ![2, 4] ![1, 3] = false := by decide

end PublicEqualitySmoke

/-- info: 'FormalProof4FHE.HasteBoots.PackedEqualityCube.bits_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedEqualityCube.bits_zero

/-- info: 'FormalProof4FHE.HasteBoots.PackedEqualityCube.bits_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedEqualityCube.bits_succ

/-- info: 'FormalProof4FHE.HasteBoots.PackedEqualityCube.index_eq_sum_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedEqualityCube.index_eq_sum_bits

/-- info: 'FormalProof4FHE.HasteBoots.PackedEqualityCube.weight_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedEqualityCube.weight_zero

/-- info: 'FormalProof4FHE.HasteBoots.PackedEqualityCube.weight_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedEqualityCube.weight_succ

/-- info: 'FormalProof4FHE.HasteBoots.PackedEqualityCube.weighted_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedEqualityCube.weighted_sum

/-- info: 'FormalProof4FHE.HasteBoots.NativeEqualityTable.address_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeEqualityTable.address_val

/-- info: 'FormalProof4FHE.HasteBoots.NativeEqualityTable.address_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeEqualityTable.address_succ

/-- info: 'FormalProof4FHE.HasteBoots.NativeEqualityTable.equality_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeEqualityTable.equality_succ

/-- info: 'FormalProof4FHE.HasteBoots.NativeEqualityTable.table_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeEqualityTable.table_address

/-- info: 'FormalProof4FHE.HasteBoots.NativeEqualityTable.table_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeEqualityTable.table_index

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.foldFirst_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.foldFirst_weight

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.evaluateSingle_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.evaluateSingle_eq_fold

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.foldAll_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.foldAll_sum

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.fold_eq_evaluatePublic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.fold_eq_evaluatePublic

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.flat_fold_eq_evaluatePublic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.flat_fold_eq_evaluatePublic

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.nativeMixedTable_eq_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.nativeMixedTable_eq_flat

/-- info: 'FormalProof4FHE.HasteBoots.PackedPublicEquality.native_fold_eq_evaluatePublic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedPublicEquality.native_fold_eq_evaluatePublic

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCube.firstPolynomials_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCube.firstPolynomials_eq

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCube.vanishes_onCells_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCube.vanishes_onCells_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCube.reducedSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCube.reducedSum_eq

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCube.healing_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCube.healing_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroTerminal.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroTerminal.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroTerminal.augmented_folds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroTerminal.augmented_folds

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroTerminal.check_folds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroTerminal.check_folds_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroExecution.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroExecution.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroExecution.native_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroExecution.native_soundness_bound

section HonestPackedSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private noncomputable def honestRoundPoints : Fin 7 ↪ ZMod 17 :=
  NativePackedInterpolation.consecutive 17 (by decide)

private noncomputable def honestFirstPoints : Fin 4 ↪ ZMod 17 :=
  NativePackedInterpolation.consecutive 17 (by decide)

/-- Interpolation recovers a polynomial at the maximum permitted round degree. -/
example : NativePackedInterpolation.messagePolynomial honestRoundPoints
    (PackedHonestMessages.encode honestRoundPoints ((Polynomial.X : Polynomial (ZMod 17)) ^ 6)) =
      Polynomial.X ^ 6 := PackedHonestMessages.decode_encode _ _ (by simp)

/-- The codec also covers the zero polynomial without a nonzero premise. -/
example : NativePackedInterpolation.messagePolynomial honestRoundPoints
    (PackedHonestMessages.encode honestRoundPoints 0) = 0 :=
  PackedHonestMessages.decode_encode _ _ (by simp)

private def honestSquareTables : PackedSumcheckExecution.Tables (ZMod 17) Unit 1 2 :=
  fun _ cell lane => packedLaneValues cell.1 lane

/-- Completeness applies to the actual soundness verifier on a nonzero source
with a repeated factor and a nonzero claimed sum. -/
example : Pr{let accepted ← (PackedSumcheckExecution.run packedNodes
    (fun _ : Unit => 2) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
    (NativePackedInterpolation.messagePolynomial honestRoundPoints)
    (PackedSumcheckCompleteness.send packedNodes (fun _ : Unit => 2) (fun _ => (1 : ZMod 17))
      (fun _ _ => ()) (PackedHonestMessages.encode honestRoundPoints))
    (PackedSumcheckCompleteness.afterChallenge packedNodes) 1 honestSquareTables ![5, 8] ⟨1, honestSquareTables⟩)}[
      accepted = true] = 1 := by
  apply PackedSumcheckCompleteness.native_probability_one 17 2 (by decide) (by decide)
    (fun _ : Unit => 2) (fun _ => (1 : ZMod 17)) (fun _ _ => ()) (fun _ => le_rfl)
  decide

private def cancellationArity (_ : Fin 2) : ℕ := 1
private def cancellationCoefficients : Fin 2 → ZMod 17 := ![1, -1]
private def cancellationIndices (_ : Fin 2) (_ : Fin 1) : Unit := ()

private def cancellationTables (n : ℕ) : PackedSumcheckExecution.Tables (ZMod 17) Unit (n + 1) 2 :=
  fun _ cell lane => packedLaneValues cell.1 lane

private noncomputable def honestZeroRun (n : ℕ) : ProbComp Bool :=
  PackedZeroExecution.run packedNodes cancellationArity cancellationCoefficients cancellationIndices
    (cancellationTables n)
    (fun message point => NativePackedInterpolation.messagePolynomial honestFirstPoints (message point))
    (NativePackedInterpolation.messagePolynomial honestRoundPoints)
    (PackedZeroCompleteness.firstRespond packedNodes cancellationArity cancellationCoefficients cancellationIndices
      (cancellationTables n) (PackedHonestMessages.encode honestFirstPoints))
    (PackedZeroCompleteness.afterFirst packedNodes (cancellationTables n))
    (PackedSumcheckCompleteness.send packedNodes (fun term => cancellationArity term + 1) cancellationCoefficients
      (PackedZeroFirst.reducedIndices cancellationArity cancellationIndices) (PackedHonestMessages.encode honestRoundPoints))
    (PackedSumcheckCompleteness.afterChallenge packedNodes)

/-- Nonzero factors satisfy X-X=0. The same verifier accepts with probability
one at any suffix dimension, including no remaining sumcheck rounds. -/
example (n : ℕ) : Pr{let accepted ← honestZeroRun n}[accepted = true] = 1 := by
  apply PackedZeroCompleteness.native_probability_one 17 1 (by decide) (by decide) (by decide)
    cancellationArity cancellationCoefficients cancellationIndices (cancellationTables n) (fun _ => le_rfl)
  intro cell lane
  have product (term : Fin 2) :
      (∏ index : Fin (cancellationArity term), cancellationTables n (cancellationIndices term index) cell lane) =
        cancellationTables n () cell lane := by
    change (∏ _index : Fin 1, cancellationTables n () cell lane) = _
    simp
  simp only [PackedSumcheckRound.expression, product, Fin.sum_univ_two]
  change (1 : ZMod 17) * cancellationTables n () cell lane + (-1) * cancellationTables n () cell lane = 0
  ring

end HonestPackedSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PackedHonestMessages.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedHonestMessages.decode_encode

/-- info: 'FormalProof4FHE.HasteBoots.PackedHonestMessages.native_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedHonestMessages.native_decode_encode

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness.native_round_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckCompleteness.native_round_checks

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness.supported_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckCompleteness.supported_accepts

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness.probability_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckCompleteness.probability_one

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckCompleteness.native_probability_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckCompleteness.native_probability_one

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCompleteness.first_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCompleteness.first_decoded

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCompleteness.native_first_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCompleteness.native_first_check

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCompleteness.supported_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCompleteness.supported_accepts

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCompleteness.probability_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCompleteness.probability_one

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroCompleteness.native_probability_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroCompleteness.native_probability_one

section SharedSubclaimSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private noncomputable def oraclePackedNodes : PackedSumcheckRound.Node 1 ↪ ZMod 17 :=
  NativePackedInterpolation.nodes 17 (by decide)

private noncomputable def oraclePackedSend (_round : ℕ) (_state : Unit) (_claimed : Fin 1 → ZMod 17) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (Polynomial (ZMod 17) × Unit) :=
  (fun _ => ((0 : Polynomial (ZMod 17)), ())) <$> sharedSamplingResponse 0

private def oraclePackedAfter (_state : Unit) (_challenge : Fin 1 → ZMod 17) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) Unit := do
  let _ ← liftM ((CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)).query (.inr (.inl 3)))
  pure ()

private theorem oraclePackedSend_run (round : ℕ) (state : Unit) (claimed : Fin 1 → ZMod 17) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape) (oraclePackedSend round state claimed)).run workerStart =
        pure (((0 : Polynomial (ZMod 17)), ()), workerStep workerStart 2 0) := by
  simp only [oraclePackedSend, simulateQ_map, StateT.run_map, sharedSamplingResponse_run, map_pure]

private theorem oraclePackedAfter_run (challenge : Fin 1 → ZMod 17) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape) (oraclePackedAfter () challenge)).run (workerStep workerStart 2 0) =
        pure ((), workerStep (workerStep workerStart 2 0) 3 1) := by
  have hit : ((CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape (.inr (.inl (3 : Fin 4)))).run (workerStep workerStart 2 0)) =
        pure ((1 : Fin 2), workerStep (workerStep workerStart 2 0) 3 1) := by
    change (fun result => (result.1, CheckpointExecution.afterHash overlappingMerkleEncoding 0 workerShape
      (workerStep workerStart 2 0) result.2)) <$>
        (CachedHashHandler.handler 3).run (workerStep workerStart 2 0).hash = _
    rw [CachedHashHandler.run_cached (workerStep workerStart 2 0).hash 3 1 rfl, map_pure]
    rfl
  rw [oraclePackedAfter, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hit]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure]

/-- A rejected message retains its actual hash call and skips the challenge
and callback. It cannot roll the cache/log back to the initial state. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
      (PackedSumcheckOracle.program oraclePackedNodes id oraclePackedSend oraclePackedAfter
        1 (fun _ => (1 : ZMod 17)) ())).run workerStart =
      pure (none, workerStep workerStart 2 0) := by
  rw [PackedSumcheckOracle.run_succ, oraclePackedSend_run, pure_bind]
  have rejected : ¬PackedSumcheckProbability.Checks oraclePackedNodes (fun _ => (1 : ZMod 17)) 0 := by
    intro checked
    have impossible := checked 0
    norm_num at impossible
  simp only [id_eq, rejected, ite_false]

/-- The fresh private draw lies between the actual message and callback hashes;
the returned matrix pair and final log belong to that same execution. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
      (PackedSumcheckOracle.program oraclePackedNodes id oraclePackedSend oraclePackedAfter
        1 (fun _ => (0 : ZMod 17)) ())).run workerStart =
    (do
      let challenge ← $ᵗ (Fin 1 → ZMod 17)
      pure (some (⟨.cons (PackedSumcheckRound.challengePair oraclePackedNodes challenge) .nil, fun _ => 0⟩, ()),
        workerStep (workerStep workerStart 2 0) 3 1)) := by
  rw [PackedSumcheckOracle.run_succ, oraclePackedSend_run, pure_bind]
  have checked : PackedSumcheckProbability.Checks oraclePackedNodes (fun _ => (0 : ZMod 17)) 0 := by
    intro lane
    simp
  simp only [id_eq, checked, reduceIte, oraclePackedAfter_run, pure_bind, PackedSumcheckOracle.program,
    simulateQ_pure, StateT.run_pure, PackedSumcheckOracle.prependResult, Option.map_some, Polynomial.eval_zero,
    PackedSumcheckSubclaim.Subclaim.prepend]

/-- The error term cannot be discarded: a terminal check can accept an
incorrect supplied factor, even when its expected value is satisfied. -/
example : PackedSumcheckTerminalOracle.accepted (fun _ : Unit => 1) (fun _ => (1 : ZMod 17))
    (fun _ _ => ())
    ((some (⟨PackedSumcheckSubclaim.Query.nil, fun _ : Fin 1 => (0 : ZMod 17)⟩, ())),
      some (fun (_ : Unit) (_ : Fin 1) => (0 : ZMod 17))) = true := by decide

example : PackedSumcheckTerminalOracle.WrongFactor (fun (_ : Unit) (_ : MatrixFold.Cube 0) (_ : Fin 1) => (1 : ZMod 17))
    ((some (⟨PackedSumcheckSubclaim.Query.nil, fun _ : Fin 1 => (0 : ZMod 17)⟩, ())),
      some (fun (_ : Unit) (_ : Fin 1) => (0 : ZMod 17))) := by
  refine ⟨_, _, rfl, (), ?_⟩
  intro equal
  have impossible := congrFun equal 0
  norm_num [PackedSumcheckSubclaim.Query.fold] at impossible

end SharedSubclaimSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim.Query.length_toList' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSubclaim.Query.length_toList

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim.Query.index_cubeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSubclaim.Query.index_cubeEquiv

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim.Query.fold_eq_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSubclaim.Query.fold_eq_list

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim.Subclaim.truthful_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSubclaim.Subclaim.truthful_zero_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim.Subclaim.truthful_prepend_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSubclaim.Subclaim.truthful_prepend_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckOracle.truthful_prepend_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckOracle.truthful_prepend_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckOracle.run_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckOracle.run_succ

/-- info: 'FormalProof4FHE.HasteBoots.SharedContinuation.earlier_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedContinuation.earlier_event_le

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSharedSoundness.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness.native_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSharedSoundness.native_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness.continued_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckSharedSoundness.continued_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckTerminalOracle.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle.accepted_implies_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckTerminalOracle.accepted_implies_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle.false_sum_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckTerminalOracle.false_sum_acceptance_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedSumcheckTerminalOracle.native_false_sum_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedSumcheckTerminalOracle.native_false_sum_acceptance_bound

namespace SubclaimLayoutSmoke

private def query : PackedSumcheckSubclaim.Query (ZMod 17) 2 2 :=
  .cons (fun _ => left) (.cons (fun _ => right) .nil)

private def table (low high : Fin 2) : Fin 2 → ZMod 17 :=
  if low = 0 ∧ high = 1 then vector else 0

/-- The front is the low bit, including across the PCS split boundary. -/
example : SubclaimSourceLayout.source (front := 1) (suffix := 1) table (false, (true, ())) = vector := by decide
example : SubclaimSourceLayout.source (front := 1) (suffix := 1) table (true, (false, ())) = 0 := by decide

/-- The later half acts on the left, even for noncommuting matrices. -/
example : query.fold (SubclaimSourceLayout.source (front := 1) (suffix := 1) table) = (right * left) *ᵥ vector := by decide

example : SubclaimSourceLayout.leftWeights (front := 1) (suffix := 1) query 0 = left := by decide
example : SubclaimSourceLayout.rightWeights (front := 1) (suffix := 1) query 1 = right := by decide

/-- Both empty halves keep the unique source cell. -/
example (t : Fin 1 → Fin 1 → Fin 2 → ZMod 17) :
    (PackedSumcheckSubclaim.Query.nil : PackedSumcheckSubclaim.Query (ZMod 17) 2 0).fold
      (SubclaimSourceLayout.source (front := 0) (suffix := 0) t) = t 0 0 := by
  change SubclaimSourceLayout.lookup (front := 0) (suffix := 0) t 0 = t 0 0
  exact SubclaimSourceLayout.lookup_join (front := 0) (suffix := 0) t 0 0

/-- A zero front or suffix dimension also uses the same fixed source. -/
example (q : PackedSumcheckSubclaim.Query (ZMod 17) 2 2)
    (t : Fin 1 → Fin 4 → Fin 2 → ZMod 17) :
    q.fold (SubclaimSourceLayout.source (front := 0) (suffix := 2) t) =
      matrixEvaluation (SubclaimSourceLayout.leftWeights (front := 0) (suffix := 2) q)
        (SubclaimSourceLayout.rightWeights (front := 0) (suffix := 2) q) t :=
  SubclaimSourceLayout.fold_source (front := 0) (suffix := 2) q t

example (q : PackedSumcheckSubclaim.Query (ZMod 17) 2 2)
    (t : Fin 4 → Fin 1 → Fin 2 → ZMod 17) :
    q.fold (SubclaimSourceLayout.source (front := 2) (suffix := 0) t) =
      matrixEvaluation (SubclaimSourceLayout.leftWeights (front := 2) (suffix := 0) q)
        (SubclaimSourceLayout.rightWeights (front := 2) (suffix := 0) q) t :=
  SubclaimSourceLayout.fold_source (front := 2) (suffix := 0) q t

end SubclaimLayoutSmoke

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.lookup_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.lookup_join

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.fold_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.fold_lookup

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.front_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.front_length

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.suffix_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.suffix_length

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.fold_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.fold_source

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.fold_decodedSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.fold_decodedSource

/-- info: 'FormalProof4FHE.HasteBoots.SubclaimSourceLayout.wrong_finish_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubclaimSourceLayout.wrong_finish_iff

/-- info: 'FormalProof4FHE.HasteBoots.SharedContinuation.later_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedContinuation.later_event_le

/-- info: 'FormalProof4FHE.HasteBoots.SharedContinuation.support_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedContinuation.support_program

/-- info: 'FormalProof4FHE.HasteBoots.AdaptiveMatrixOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveMatrixOpening.soundness_from_empty

section StatefulPrefixSmoke

open OracleSpec OracleComp

/-- Equal public roots can carry different private commitment coins. The
continuation receives the same sampled memory; the recorded root stays zero. -/
example : StatefulCommitmentPrefix.witness (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape ()
      (PrivateSampling.embed (Cfg := Unit) (Input := Fin 4) (Digest := Fin 2)
        ((fun memory : Fin 2 => ((0 : Fin 2), memory)) <$> ($ᵗ (Fin 2))))
      (fun emission => pure emission.2) workerStart =
    (do
      let memory ← $ᵗ (Fin 2)
      pure ((((0 : Fin 2), memory), workerStart),
        (memory, CheckpointExecution.record workerShape workerStart () 0))) := by
  simp only [StatefulCommitmentPrefix.witness, PrivateSampling.run_probComp,
    simulateQ_pure, StateT.run_pure, bind_map_left, pure_bind]

end StatefulPrefixSmoke

/-- info: 'FormalProof4FHE.HasteBoots.StatefulCommitmentPrefix.snapshot_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StatefulCommitmentPrefix.snapshot_recorded

/-- info: 'FormalProof4FHE.HasteBoots.StatefulCommitmentPrefix.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StatefulCommitmentPrefix.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.StatefulCommitmentPrefix.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StatefulCommitmentPrefix.event_bound

section JointOpeningSmoke

open OracleSpec OracleComp

private def orderedQuery (memory : Fin 2) : Fin 4 := if memory = 0 then 2 else 3

private def orderedStep (_index : Unit) (memory : Fin 2) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (Fin 2 × Fin 2) := do
  let answer ← liftM ((CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)).query (.inr (.inl (orderedQuery memory))))
  pure (answer, 1 - memory)

private theorem orderedStep_run (memory : Fin 2) (initial : WorkerState) (answer : Fin 2)
    (known : initial.hash.cache (orderedQuery memory) = some answer) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape) (orderedStep () memory)).run initial =
      pure ((answer, 1 - memory), workerStep initial (orderedQuery memory) answer) := by
  have hit : ((CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape (.inr (.inl (orderedQuery memory)))).run initial) =
        pure (answer, workerStep initial (orderedQuery memory) answer) := by
    change (fun result => (result.1, CheckpointExecution.afterHash overlappingMerkleEncoding 0 workerShape
      initial result.2)) <$> (CachedHashHandler.handler (orderedQuery memory)).run initial.hash = _
    rw [CachedHashHandler.run_cached initial.hash (orderedQuery memory) answer known, map_pure]
    rfl
  rw [orderedStep, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hit]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure]

/-- The second hash is chosen by the private memory returned by the first
step. Resetting either memory or the shared log changes this result. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape) (SharedSequence.program orderedStep [(), ()] 0)).run workerStart =
      pure (([((), (0 : Fin 2)), ((), 1)], (0 : Fin 2)),
        workerStep (workerStep workerStart 2 0) 3 1) := by
  simp only [SharedSequence.program, simulateQ_bind, StateT.run_bind]
  rw [orderedStep_run 0 workerStart 0 rfl, pure_bind]
  have memoryZero : 1 - (0 : Fin 2) = 1 := by decide
  have firstQuery : orderedQuery 0 = 2 := rfl
  simp only [memoryZero, firstQuery]
  rw [orderedStep_run 1 (workerStep workerStart 2 0) 1 rfl, pure_bind]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rfl

/-- Root recording is passive even for repeated roots in one context. -/
example : (RecordRoots.state workerShape [((), (0 : Fin 2)), ((), 1), ((), 0)] workerStart).hash =
    workerStart.hash := RecordRoots.hash_eq _ _ _

example : ⟨(), ⟨(1 : Fin 2), workerStart.hash.log⟩⟩ ∈
    (RecordRoots.state workerShape [((), (0 : Fin 2)), ((), 1), ((), 0)] workerStart).checkpoints.checkpoints :=
  RecordRoots.recorded _ _ _ ((), 1) (by decide)

/-- A real commitment hash precedes freezing both roots. Later private coins
retain the entire recorded family and the post-commitment shared cache. -/
example : MultiCommitmentPrefix.witness overlappingMerkleEncoding 0 workerShape
    (fun root : Fin 2 => [((), root), ((), 1)]) (sharedSamplingResponse 1)
    (fun _ => PrivateSampling.embed (Cfg := Unit) (Input := Fin 4) (Digest := Fin 2) ($ᵗ (Fin 2))) workerStart =
    (do
      let coin ← $ᵗ (Fin 2)
      pure (((0 : Fin 2), workerStep workerStart 2 0),
        (coin, RecordRoots.state workerShape [((), (0 : Fin 2)), ((), 1)] (workerStep workerStart 2 0)))) := by
  simp only [MultiCommitmentPrefix.witness, sharedSamplingResponse_run, pure_bind, PrivateSampling.run_probComp]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

end JointOpeningSmoke

/-- info: 'FormalProof4FHE.HasteBoots.SharedSequence.anyBad_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedSequence.anyBad_cons

/-- info: 'FormalProof4FHE.HasteBoots.SharedSequence.program_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedSequence.program_cons

/-- info: 'FormalProof4FHE.HasteBoots.SharedSequence.arithmetic_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedSequence.arithmetic_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.RecordRoots.hash_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecordRoots.hash_eq

/-- info: 'FormalProof4FHE.HasteBoots.RecordRoots.retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecordRoots.retains

/-- info: 'FormalProof4FHE.HasteBoots.RecordRoots.recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecordRoots.recorded

/-- info: 'FormalProof4FHE.HasteBoots.RecordRoots.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecordRoots.run_program

/-- info: 'FormalProof4FHE.HasteBoots.MultiCommitmentPrefix.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MultiCommitmentPrefix.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.MultiCommitmentPrefix.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MultiCommitmentPrefix.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.JointMatrixOpening.step_arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JointMatrixOpening.step_arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.JointMatrixOpening.arithmetic_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JointMatrixOpening.arithmetic_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.JointMatrixOpening.joint_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JointMatrixOpening.joint_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening.snapshots_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommittedJointMatrixOpening.snapshots_recorded

/-- info: 'FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommittedJointMatrixOpening.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening.final_checks_imply_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractiveAuthenticatedOpening.final_checks_imply_failure

section GuardedTerminalSmoke

open OracleSpec OracleComp

private def stoppedStep (index : Unit) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (ShortCircuitSequence.StepResult (Fin 2) (Fin 2)) :=
  (fun first => ⟨first.1, first.2, false⟩) <$> orderedStep index memory

/-- The first failure keeps its changed private memory and issued hash, while
skipping the second step's memory-dependent hash and all later private draws. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape) (ShortCircuitSequence.program stoppedStep [(), ()] 0)).run workerStart =
      pure ((⟨[((), (0 : Fin 2))], (1 : Fin 2), false⟩ : ShortCircuitSequence.Outcome Unit (Fin 2) (Fin 2)),
        workerStep workerStart 2 0) := by
  simp only [ShortCircuitSequence.program, stoppedStep, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]
  rw [orderedStep_run 0 workerStart 0 rfl]
  simp only [map_pure, pure_bind, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure]
  rfl

private def allowedStep (index : Unit) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (ShortCircuitSequence.StepResult (Fin 2) (Fin 2)) :=
  (fun first => ⟨first.1, first.2, true⟩) <$> orderedStep index memory

/-- A literal result check can reject an otherwise accepted step, without
adding queries or running the next factor. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (ShortCircuitSequence.program (ShortCircuitSequence.enforce (fun (_ : Unit) (value : Fin 2) => value == 1) allowedStep)
      [(), ()] 0)).run workerStart =
      pure ((⟨[((), (0 : Fin 2))], (1 : Fin 2), false⟩ : ShortCircuitSequence.Outcome Unit (Fin 2) (Fin 2)),
        workerStep workerStart 2 0) := by
  simp only [ShortCircuitSequence.program, ShortCircuitSequence.enforce, allowedStep,
    simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]
  rw [orderedStep_run 0 workerStart 0 rfl]
  simp only [map_pure, pure_bind]
  rfl

private def terminalHash (query : Fin 4) : OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (Fin 2) :=
  liftM ((SharedSequence.Shared Unit (Fin 4) (Fin 2)).query (.inr (.inl query)))

private theorem terminalHash_run (query : Fin 4) (initial : WorkerState) (answer : Fin 2)
    (known : initial.hash.cache query = some answer) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape) (terminalHash query)).run initial =
      pure (answer, workerStep initial query answer) := by
  rw [terminalHash, simulateQ_spec_query]
  change (fun result => (result.1, CheckpointExecution.afterHash overlappingMerkleEncoding 0 workerShape
    initial result.2)) <$> (CachedHashHandler.handler query).run initial.hash = _
  rw [CachedHashHandler.run_cached initial.hash query answer known, map_pure]
  rfl

private def terminalClaim : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 0 :=
  ⟨.nil, fun _ => 0⟩

private def receiveTerminal (value : ZMod 17) (_claim : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 0)
    (memory : Fin 2) : OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2))
      ((Unit → Fin 1 → ZMod 17) × Fin 2) :=
  (fun _ => ((fun _ _ => value), 1 - memory)) <$> terminalHash 2

private def bindTerminal (_claim : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 0)
    (_values : Unit → Fin 1 → ZMod 17) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (Fin 2) :=
  (fun _ => memory) <$> terminalHash 3

private def openTerminal (_claim : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 0)
    (_values : Unit → Fin 1 → ZMod 17) (_factor : Unit) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (ShortCircuitSequence.StepResult (Fin 2) (Fin 2)) :=
  (fun answer => ⟨answer, 1 - memory, false⟩) <$> terminalHash 1

/-- A bad terminal value retains receive-work and private memory, and invokes
neither the binding hash nor either of the two factor openings. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (GuardedSumcheckTerminal.finish (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
      (receiveTerminal 1) bindTerminal openTerminal [(), ()] (some (terminalClaim, 0)))).run workerStart =
      pure (some (((fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 17)), (1 : Fin 2)), none),
        workerStep workerStart 2 0) := by
  simp only [GuardedSumcheckTerminal.finish, receiveTerminal, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, terminalHash_run 2 workerStart 0 rfl, map_pure, pure_bind]
  have rejected : PackedSumcheckTerminalOracle.check (fun _ : Unit => 1) (fun _ => (1 : ZMod 17))
      (fun _ _ => ()) (fun _ _ => (1 : ZMod 17)) terminalClaim.expected = false := by decide
  simp only [rejected, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure]
  rfl

/-- A valid terminal identity binds first, opens one factor, and stops on its
failure. The second factor's hash is absent from the final shared log. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (GuardedSumcheckTerminal.finish (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
      (receiveTerminal 0) bindTerminal openTerminal [(), ()] (some (terminalClaim, 0)))).run workerStart =
      pure (some (((fun (_ : Unit) (_ : Fin 1) => (0 : ZMod 17)), (0 : Fin 2)),
        some (⟨[((), (0 : Fin 2))], (0 : Fin 2), false⟩ : ShortCircuitSequence.Outcome Unit (Fin 2) (Fin 2))),
        workerStep (workerStep (workerStep workerStart 2 0) 3 1) 1 0) := by
  simp only [GuardedSumcheckTerminal.finish, receiveTerminal, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, terminalHash_run 2 workerStart 0 rfl, map_pure, pure_bind]
  have checked : PackedSumcheckTerminalOracle.check (fun _ : Unit => 1) (fun _ => (1 : ZMod 17))
      (fun _ _ => ()) (fun _ _ => (0 : ZMod 17)) terminalClaim.expected = true := by decide
  simp only [checked, reduceIte, bindTerminal, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    terminalHash_run 3 (workerStep workerStart 2 0) 1 rfl, map_pure, pure_bind]
  simp only [ShortCircuitSequence.program, openTerminal, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    terminalHash_run 1 (workerStep (workerStep workerStart 2 0) 3 1) 0 rfl, map_pure, pure_bind,
    Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure]
  rfl

/-- Incorrect proposals rejected before opening do not count as accepted PCS
failures, even though the supplied factor differs from the fixed source. -/
example : ¬GuardedSumcheckTerminal.WrongAcceptedFactor (fun _ : Unit => 1) (fun _ => (1 : ZMod 17))
    (fun _ _ => ()) (fun (_ : Unit) (_ : MatrixFold.Cube 0) (_ : Fin 1) => (0 : ZMod 17))
    ((some (terminalClaim, (0 : Fin 2))), some (((fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 17)), (1 : Fin 2)),
      (none : Option (ShortCircuitSequence.Outcome Unit (Fin 2) (Fin 2))))) := by
  rintro ⟨passed, _⟩
  exact Bool.false_ne_true passed

private def checkedColumn : NativeColumnLayout.Column (ZMod 17) (Fin 2) 1 1 1 :=
  { values := fun _ => 0, leaf := 0, siblings := ⟨[0], rfl⟩, position := 0 }

private noncomputable def checkedDomain : Fin 2 ↪ ZMod 17 := NativePackedInterpolation.consecutive 17 (by decide)
private def checkedData : JointMatrixOpening.Data (ZMod 17) (Fin 2) Unit 1 1 1 1 :=
  (((fun _ _ => 0, ()), fun _ => 0), [checkedColumn])

/-- Literal coordinate checks also enforce the claimed terminal factor value. -/
example : NativeFactorChecks.check (m := 1) (size := 1) checkedDomain (fun _ => 1) (fun _ => 1)
    (fun _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) checkedData = true := by decide
example : NativeFactorChecks.check (m := 1) (size := 1) checkedDomain (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) checkedData = false := by decide
example : NativeFactorChecks.coversCheck (leftCount := 1) (b := 1) (height := 1) [checkedColumn] (fun _ : Fin 1 => (1 : Fin 2)) = false := by decide

end GuardedTerminalSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.program_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.program_cons

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.reject_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.reject_cons

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.enforce_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.enforce_accepts

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.accepted_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.accepted_indices

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.accepted_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.accepted_results

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.enforced_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.enforced_results

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.arithmetic_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.arithmetic_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal.accepted_terminalView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedSumcheckTerminal.accepted_terminalView

/-- info: 'FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal.accepted_implies_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedSumcheckTerminal.accepted_implies_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal.false_sum_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedSumcheckTerminal.false_sum_acceptance_bound

/-- info: 'FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal.native_false_sum_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedSumcheckTerminal.native_false_sum_acceptance_bound

/-- info: 'FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening.checked_step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StoppingJointMatrixOpening.checked_step_eq

/-- info: 'FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening.step_arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StoppingJointMatrixOpening.step_arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening.arithmetic_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StoppingJointMatrixOpening.arithmetic_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommittedStoppingMatrixOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommittedStoppingMatrixOpening.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeFactorChecks.coversCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFactorChecks.coversCheck_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeFactorChecks.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFactorChecks.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeFactorChecks.wrong_values_imply_bad_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFactorChecks.wrong_values_imply_bad_opening

/-- info: 'FormalProof4FHE.HasteBoots.NativeFactorChecks.successful_wrong_values_imply_bad_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFactorChecks.successful_wrong_values_imply_bad_opening

section NativeWorkerPoolSmoke

open OracleSpec OracleComp

private def poolChoose (_workers : HashWorkerPool.Workers (Fin 4) (Fin 2) 2) (plan : List (Fin 2)) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (Option (Fin 2) × List (Fin 2)) :=
  pure (plan.head?, plan.drop 1)

private def nativePoolWorkers : HashWorkerPool.Workers (Fin 4) (Fin 2) 2 := fun index =>
  if index = 0 then
    NativeMerkleVerifier.verifyPayload overlappingMerkleEncoding 1 0 2 0 0 ⟨[1], rfl⟩
  else (fun answer => answer == (1 : Fin 2)) <$> liftM ((Fin 4 →ₒ Fin 2).query 3)

/-- A leaf, another worker's hash and the first worker's node are actual
interleaved calls. Acceptance is computed only after both workers return true. -/
example : (fun outcome => (HashWorkerPool.allAccepted outcome.1.workers, outcome.1.memory, outcome.2.hash.log)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (HashWorkerPool.program poolChoose 3 nativePoolWorkers [0, 1, 0])).run workerStart =
      pure (true, ([] : List (Fin 2)), (workerStep (workerStep (workerStep workerStart 2 0) 3 1) 1 0).hash.log) := by
  rfl

/-- A pending node cannot be accepted merely because its answer happens to be
cached already. The native worker must actually issue that hash call. -/
example : (fun outcome => (HashWorkerPool.allAccepted outcome.1.workers, outcome.1.memory, outcome.2.hash.log)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (HashWorkerPool.program poolChoose 2 nativePoolWorkers [0, 1, 0])).run workerStart =
      pure (false, ([0] : List (Fin 2)), (workerStep (workerStep workerStart 2 0) 3 1).hash.log) := by
  rfl

/-- Cancellation leaves completed prefix work in the shared log and does not
run the pending node or the other worker. -/
example : (fun outcome => (HashWorkerPool.allAccepted outcome.1.workers, outcome.2.hash.log)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (HashWorkerPool.program poolChoose 3 nativePoolWorkers [0])).run workerStart =
      pure (false, (workerStep workerStart 2 0).hash.log) := by
  rfl

private def poolCancel (_workers : HashWorkerPool.Workers (Fin 4) (Fin 2) 2) (memory : Unit) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (Option (Fin 2) × Unit) := do
  let _ ← terminalHash 3
  pure (none, memory)

/-- Background scheduling work survives cancellation even when no worker is
advanced. It cannot supply a true acceptance flag for an unfinished pool. -/
example : (fun outcome => (HashWorkerPool.allAccepted outcome.1.workers, outcome.2.hash.log)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (HashWorkerPool.program poolCancel 1 nativePoolWorkers ())).run workerStart =
      pure (false, (workerStep workerStart 3 1).hash.log) := by
  rfl

private abbrev ColumnInput := Sum (List (ZMod 17)) (Fin 2 × Fin 2)
private def columnEncoding : MerkleOracle.Encoding ColumnInput (Fin 2) (List (ZMod 17)) where
  leaf _ := Sum.inl
  node _ := Sum.inr
  leaf_injective _ := Sum.inl_injective
  node_injective _ := Sum.inr_injective

private noncomputable def columnStart :
    CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) workerShape :=
  let empty := CachedHashHandler.empty (Input := ColumnInput) (Digest := Fin 2)
  let zeroLeaf := CachedHashHandler.observe empty (.inl [0]) 0 (empty.cache.cacheQuery (.inl [0]) 0)
  let oneLeaf := CachedHashHandler.observe zeroLeaf (.inl [1]) 1 (zeroLeaf.cache.cacheQuery (.inl [1]) 1)
  let node := CachedHashHandler.observe oneLeaf (.inr (0, 1)) 0 (oneLeaf.cache.cacheQuery (.inr (0, 1)) 0)
  ⟨node, MerkleTreeMultiExtractability.ExtractorState.empty, false⟩

private def poolColumn (bit : Fin 2) : NativeColumnLayout.Column (ZMod 17) (Fin 2) 1 1 1 :=
  { values := fun _ => bit.val, leaf := bit,
    siblings := ⟨[1 - bit], rfl⟩, position := bit }

private def poolColumns := [poolColumn 0, poolColumn 1]
private def poolWeights : Fin (1 * (1 * 1)) → ZMod 17 := fun _ => 1
private def poolResponse : Fin (1 * ((2 ^ 1) * 1)) → ZMod 17 := fun index => index.val
private def columnChoose (_workers : HashWorkerPool.Workers ColumnInput (Fin 2) poolColumns.length)
    (plan : List (Fin 2)) : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2))
      (Option (Fin poolColumns.length) × List (Fin 2)) := pure (plan.head?, plan.drop 1)

/-- Both native column workers authenticate and check coordinates, with their
leaf hashes interleaved before the common root-node calls. -/
example : (fun outcome => (outcome.1.2, outcome.1.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeColumnWorkerPool.program columnEncoding 0 poolWeights poolWeights poolResponse poolResponse
        poolColumns columnChoose 4 [0, 1, 0, 1])).run columnStart =
      pure (true, ([] : List (Fin 2)), 7) := by
  rfl

/-- A real native authentication can pass while a coordinate fails. The
worker pool's computed flag must still reject. -/
example : (fun outcome => outcome.1.2) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeColumnWorkerPool.program columnEncoding 0 poolWeights poolWeights poolResponse (fun _ => 0)
        poolColumns columnChoose 4 [0, 1, 0, 1])).run columnStart =
      pure false := by
  rfl

end NativeWorkerPoolSmoke

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.done_sound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.done_sound

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.allAccepted_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.allAccepted_sound

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.tick_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.tick_pure

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.tick_query' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.tick_query

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.refines_refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.refines_refl

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.refines_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.refines_mono

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.tick_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.tick_refines

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.update_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.update_refines

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.run_refines

/-- info: 'FormalProof4FHE.HasteBoots.HashWorkerPool.accepted_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HashWorkerPool.accepted_replays

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnWorkerPool.worker_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnWorkerPool.worker_accepts

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnWorkerPool.accepted_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnWorkerPool.accepted_columns

/-- info: 'FormalProof4FHE.HasteBoots.NativeColumnWorkerPool.accepted_columns_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeColumnWorkerPool.accepted_columns_later

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitSequence.accepted_cache_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitSequence.accepted_cache_results

/-- info: 'FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening.step_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StoppingJointMatrixOpening.step_supported

/-- info: 'FormalProof4FHE.HasteBoots.NativeMatrixVerifier.next_accepts_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMatrixVerifier.next_accepts_later

/-- info: 'FormalProof4FHE.HasteBoots.NativeMatrixVerifier.step_accepts_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMatrixVerifier.step_accepts_later

/-- info: 'FormalProof4FHE.HasteBoots.NativeMatrixVerifier.successful_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMatrixVerifier.successful_results

/-- info: 'FormalProof4FHE.HasteBoots.NativeMatrixVerifier.successful_wrong_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeMatrixVerifier.successful_wrong_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.NativeCommittedOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeCommittedOpening.soundness_from_empty

section AuthenticatedSumcheckSmoke

open OracleSpec OracleComp

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

/-- Preparation is an equality of oracle programs, not merely an acceptance
probability comparison; this includes binding and failed-opening work. -/
example : PreparedTerminal.finish (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
    (receiveTerminal 0) bindTerminal openTerminal [(), ()] 0 (some (terminalClaim, 0)) =
    GuardedSumcheckTerminal.finish (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
      (receiveTerminal 0) bindTerminal openTerminal [(), ()] (some (terminalClaim, 0)) :=
  PreparedTerminal.finish_eq _ _ _ _ _ _ _ _ _

/-- A rejected preparation retains the actual earlier subclaim and received
private memory, and never invokes the binding callback. -/
example : (fun outcome => (outcome.1.earlier, outcome.1.data.values, outcome.1.data.memory,
    outcome.1.data.enabled, outcome.2.hash.log)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (PreparedTerminal.select (pure (some (terminalClaim, (0 : Fin 2))))
        (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
        (receiveTerminal 1) bindTerminal 0)).run workerStart =
      pure (some (terminalClaim, (0 : Fin 2)), (fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 17)),
        (1 : Fin 2), false, (workerStep workerStart 2 0).hash.log) := by
  rfl

private def schemeHash (input : ColumnInput) :
    OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) (Fin 2) :=
  liftM ((SharedSequence.Shared Unit ColumnInput (Fin 2)).query (.inr (.inl input)))

private noncomputable def rejectedScheme : AuthenticatedSumcheck.Scheme (ZMod 17) Unit Unit (Fin 2 → ZMod 17)
    ColumnInput (Fin 2) Unit Unit Unit Unit 1 0 0 1 1 1 where
  encoding := columnEncoding
  domain := checkedDomain
  tag := fun _ => ()
  factors := [(), ()]
  nodes := NativePackedInterpolation.nodes 17 (by decide)
  arity := fun _ => 1
  coefficient := fun _ => 1
  indices := fun _ _ => ()
  interpret := NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive 17 (by decide))
  claimed := fun _ => 0
  commit := (fun _ => ((fun _ : Unit => (0 : Fin 2)), ())) <$> schemeHash (.inl [0])
  initial := fun _ => ()
  send := fun _ _ _ _ => do
    let _ ← schemeHash (.inr (1, 1))
    pure ((fun _ => 0), ())
  afterChallenge := fun _ _ _ => do
    let _ ← schemeHash (.inr (1, 1))
    pure ()
  receiveValues := fun _ _ _ => (fun _ => ((fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 17)), ())) <$>
    schemeHash (.inl [1])
  bindValues := fun _ _ _ _ => (fun _ => ()) <$> schemeHash (.inr (0, 1))
  build := fun _ _ =>
    { encoding := columnEncoding
      domain := checkedDomain
      root := fun _ => 1
      left := fun _ _ => 0
      right := fun _ _ => 0
      value := fun _ _ => 0
      testResponse := fun _ _ _ _ _ => 0
      structuredResponse := fun _ _ _ _ _ => 0
      respond := fun _ _ _ => pure ()
      receiveColumns := fun _ _ _ => pure ([checkedColumn], ())
      choose := fun _ _ _ _ _ _ => pure (none, ())
      fuel := fun _ _ _ _ => 2 }

/-- The complete committed program performs the commitment hash and the
received-value hash, rejects the bad terminal identity and skips binding,
sumcheck callbacks (zero rounds), opening coins and every native worker. -/
example : (fun outcome => (AuthenticatedSumcheck.accepted outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (AuthenticatedSumcheck.program rejectedScheme)).run columnStart = pure (false, 5) := by
  rfl

end AuthenticatedSumcheckSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PreparedTerminal.finish_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedTerminal.finish_eq

/-- info: 'FormalProof4FHE.HasteBoots.PreparedTerminal.checked_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedTerminal.checked_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.PreparedTerminal.prepare_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedTerminal.prepare_sound

/-- info: 'FormalProof4FHE.HasteBoots.PreparedTerminal.earlier_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedTerminal.earlier_event_le

/-- info: 'FormalProof4FHE.HasteBoots.PreparedTerminal.select_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedTerminal.select_sound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedSumcheck.opening_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedSumcheck.opening_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedSumcheck.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedSumcheck.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedSumcheck.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedSumcheck.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedSumcheck.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedSumcheck.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedSumcheck.native_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedSumcheck.native_soundness_from_empty

section SharedZeroSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def indexedPairQuery : PackedSumcheckSubclaim.Query (ZMod 17) 2 2 :=
  .cons (fun _ => left) (.cons (fun _ => right) .nil)

/-- The indexed public EQ recurrence preserves the same noncommuting order as
native folding: the first variable acts first, then the second. -/
example : IndexedPublicEquality.evaluateSingle indexedPairQuery (fun _ => 0) vector = vector := by decide

example : IndexedPublicEquality.evaluateSingle
    (.cons (fun _ => right) (.cons (fun _ => left) .nil)) (fun _ => 0) vector ≠ vector := by decide

private noncomputable def zeroFirstResponse (_points : PackedZeroReduction.Points (ZMod 17) 0 1) (_memory : Unit) :
    OracleComp (PackedSumcheckOracle.Shared Unit (Fin 4) (Fin 2)) ((Fin 1 → Polynomial (ZMod 17)) × Unit) :=
  (fun _ => ((fun _ => (1 : Polynomial (ZMod 17))), ())) <$> terminalHash 2

private def zeroFirstAfter (_points : PackedZeroReduction.Points (ZMod 17) 0 1)
    (_message : (Fin 1 → Polynomial (ZMod 17)) × Unit) (_coins : PackedZeroReduction.Coins (ZMod 17) 1) :
    OracleComp (PackedSumcheckOracle.Shared Unit (Fin 4) (Fin 2)) Unit :=
  (fun _ => ()) <$> terminalHash 3

/-- Boundary rejection retains the actual first-message hash. Mixing, the
first callback, all later rounds and their callbacks are skipped. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (PackedZeroOracle.program oraclePackedNodes id id zeroFirstResponse zeroFirstAfter
      oraclePackedSend oraclePackedAfter ())).run workerStart =
      (fun _ : PackedZeroReduction.Points (ZMod 17) 0 1 => (none, workerStep workerStart 2 0)) <$>
        ($ᵗ (PackedZeroReduction.Points (ZMod 17) 0 1)) := by
  rw [PackedZeroOracle.run_program]
  have rejected : ¬PackedZeroFirst.Boundary oraclePackedNodes (fun _ : Fin 1 => (1 : Polynomial (ZMod 17))) := by
    intro checked
    have impossible := checked 0 false 0
    norm_num at impossible
  simp only [zeroFirstResponse, simulateQ_map, StateT.run_map, terminalHash_run 2 workerStart 0 rfl,
    map_pure, pure_bind, id_eq, rejected, reduceIte]
  rw [map_eq_pure_bind]

private def zeroTerminalClaim : PackedZeroOracle.Subclaim (ZMod 17) 1 0 :=
  ⟨fun _ => Fin.elim0, (fun _ _ => 1, fun _ => 0), ⟨.nil, fun _ => 0⟩⟩

private def receiveZeroTerminal (_claim : PackedZeroOracle.Subclaim (ZMod 17) 1 0)
    (memory : Fin 2) : OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2))
      ((Unit → Fin 1 → ZMod 17) × Fin 2) :=
  (fun _ => ((fun _ _ => 1), 1 - memory)) <$> terminalHash 2

private def bindZeroTerminal (_claim : PackedZeroOracle.Subclaim (ZMod 17) 1 0)
    (_values : Unit → Fin 1 → ZMod 17) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) (Fin 2) :=
  (fun _ => memory) <$> terminalHash 3

/-- The zero-suffix public EQ terminal is the mixing column sum. It is not a
supplied value or a newly committed factor. -/
example : zeroTerminalClaim.equality = fun _ => 1 := by decide

/-- A wrong original-factor terminal value rejects before binding, retaining
received memory and the shared log. EQ is computed from the earlier subclaim. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (PreparedZeroTerminal.prepare (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
      receiveZeroTerminal bindZeroTerminal 0 (some (zeroTerminalClaim, 0)))).run workerStart =
      pure (⟨fun _ _ => 1, (1 : Fin 2), false⟩, workerStep workerStart 2 0) := by
  simp only [PreparedZeroTerminal.prepare, receiveZeroTerminal, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, terminalHash_run 2 workerStart 0 rfl, map_pure, pure_bind]
  have rejected : PackedZeroOracle.Subclaim.check (fun _ : Unit => 1) (fun _ => (1 : ZMod 17))
      (fun _ _ => ()) (fun _ _ => 1) zeroTerminalClaim = false := by decide
  simp only [rejected, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure]
  rfl

/-- Passing the same computed-EQ terminal check runs binding on the received
state. Its hash must remain after the receive hash in the actual final log. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (PreparedZeroTerminal.prepare (fun _ : Unit => 1) (fun _ => (1 : ZMod 17)) (fun _ _ => ())
      (fun _ memory => (fun _ => ((fun (_ : Unit) (_ : Fin 1) => (0 : ZMod 17)), 1 - memory)) <$> terminalHash 2)
      bindZeroTerminal 0 (some (zeroTerminalClaim, 0)))).run workerStart =
      pure (⟨fun _ _ => 0, (1 : Fin 2), true⟩, workerStep (workerStep workerStart 2 0) 3 1) := by
  simp only [PreparedZeroTerminal.prepare, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, terminalHash_run 2 workerStart 0 rfl, map_pure, pure_bind]
  have checked : PackedZeroOracle.Subclaim.check (fun _ : Unit => 1) (fun _ => (1 : ZMod 17))
      (fun _ _ => ()) (fun _ _ => 0) zeroTerminalClaim = true := by decide
  simp only [checked, reduceIte, bindZeroTerminal]
  rfl

end SharedZeroSmoke

/-- info: 'FormalProof4FHE.HasteBoots.IndexedPublicEquality.evaluateSingle_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexedPublicEquality.evaluateSingle_eq_fold

/-- info: 'FormalProof4FHE.HasteBoots.IndexedPublicEquality.fold_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexedPublicEquality.fold_sum

/-- info: 'FormalProof4FHE.HasteBoots.IndexedPublicEquality.fold_eq_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexedPublicEquality.fold_eq_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.IndexedPublicEquality.evaluateSingle_eq_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexedPublicEquality.evaluateSingle_eq_list

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroOracle.Subclaim.reduced_folds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroOracle.Subclaim.reduced_folds

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroOracle.Subclaim.check_folds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroOracle.Subclaim.check_folds_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroOracle.Subclaim.checked_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroOracle.Subclaim.checked_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroOracle.truthful_wrap_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroOracle.truthful_wrap_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroOracle.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroOracle.run_program

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroSharedSoundness.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness.native_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroSharedSoundness.native_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness.continued_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedZeroSharedSoundness.continued_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.PreparedZeroTerminal.checked_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedZeroTerminal.checked_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.PreparedZeroTerminal.prepare_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedZeroTerminal.prepare_sound

/-- info: 'FormalProof4FHE.HasteBoots.PreparedZeroTerminal.earlier_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedZeroTerminal.earlier_event_le

/-- info: 'FormalProof4FHE.HasteBoots.PreparedZeroTerminal.select_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedZeroTerminal.select_sound

section AuthenticatedZeroSmoke

open OracleSpec OracleComp

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private noncomputable def zeroColumnStep
    (state : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) workerShape)
    (input : ColumnInput) (answer : Fin 2) :=
  CheckpointExecution.afterHash columnEncoding 0 workerShape state (CachedHashHandler.observe state.hash input answer state.hash.cache)

private theorem schemeHash_run (input : ColumnInput)
    (state : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) workerShape)
    (answer : Fin 2) (known : state.hash.cache input = some answer) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) (schemeHash input)).run state =
      pure (answer, zeroColumnStep state input answer) := by
  rw [schemeHash, simulateQ_spec_query]
  change (fun result => (result.1, CheckpointExecution.afterHash columnEncoding 0 workerShape state result.2)) <$>
    (CachedHashHandler.handler input).run state.hash = _
  rw [CachedHashHandler.run_cached state.hash input answer known, map_pure]
  rfl

private noncomputable def rejectedZeroScheme : AuthenticatedZeroCheck.Scheme (ZMod 17) Unit Unit Unit
    (Fin 3 → ZMod 17) ColumnInput (Fin 2) Unit Unit Unit Unit 1 0 1 0 1 1 1 where
  dimensions := rfl
  encoding := columnEncoding
  domain := checkedDomain
  tag := fun _ => ()
  factors := [(), ()]
  nodes := NativePackedInterpolation.nodes 17 (by decide)
  arity := fun _ => 1
  coefficient := fun _ => 1
  indices := fun _ _ => ()
  interpretFirst := fun _ _ => 1
  interpret := NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive 17 (by decide))
  commit := (fun _ => ((fun _ : Unit => (0 : Fin 2)), ())) <$> schemeHash (.inl [0])
  initial := fun _ => ()
  firstRespond := fun _ _ _ => (fun _ => ((), ())) <$> schemeHash (.inl [1])
  afterFirst := fun _ _ _ _ => (fun _ => ()) <$> schemeHash (.inr (1, 1))
  send := fun _ _ _ _ => do
    let _ ← schemeHash (.inr (1, 1))
    pure ((fun _ => 0), ())
  afterChallenge := fun _ _ _ => (fun _ => ()) <$> schemeHash (.inr (1, 1))
  receiveValues := fun _ _ _ => (fun _ => ((fun (_ : Unit) (_ : Fin 1) => (1 : ZMod 17)), ())) <$>
    schemeHash (.inr (1, 1))
  bindValues := fun _ _ _ _ => (fun _ => ()) <$> schemeHash (.inr (1, 1))
  build := fun _ _ =>
    { encoding := columnEncoding
      domain := checkedDomain
      root := fun _ => 1
      left := fun _ _ => 0
      right := fun _ _ => 0
      value := fun _ _ => 0
      testResponse := fun _ _ _ _ _ => 0
      structuredResponse := fun _ _ _ _ _ => 0
      respond := fun _ _ _ => pure ()
      receiveColumns := fun _ _ _ => pure ([], ())
      choose := fun _ _ _ _ _ _ => pure (none, ())
      fuel := fun _ _ _ _ => 2 }

private def zeroPacket : PreparedZeroTerminal.Packet (ZMod 17) Unit Unit 1 0 :=
  ⟨some (zeroTerminalClaim, ()), ⟨fun _ _ => 1, (), true⟩⟩

/-- The value checked with public EQ overrides a conflicting opening factory
value. There is no public-EQ factor in the committed family. -/
example : (AuthenticatedZeroCheck.build rejectedZeroScheme ((fun _ => 0), ()) zeroPacket).value () 0 = 1 := by
  rfl

/-- The one special variable may occupy the entire front half, with an empty
suffix. Reindexing still preserves the actual ordered query. -/
example : (AuthenticatedZeroCheck.query rejectedZeroScheme zeroPacket).toList =
    (PreparedZeroTerminal.query rejectedZeroScheme.nodes zeroPacket).toList :=
  QueryReindex.toList _ _

/-- The complete committed program keeps both commit/first-message hashes,
rejects the boundary, and skips all mixing callbacks, terminal work and PCS
workers. The initial equality-point draw remains in the exact oracle program. -/
example : (fun outcome => (AuthenticatedZeroCheck.accepted outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (AuthenticatedZeroCheck.program rejectedZeroScheme)).run columnStart =
      (fun _ : PackedZeroReduction.Points (ZMod 17) 0 1 => (false, 5)) <$>
        ($ᵗ (PackedZeroReduction.Points (ZMod 17) 0 1)) := by
  have rejected : ¬PackedZeroFirst.Boundary rejectedZeroScheme.nodes (fun _ : Fin 1 => (1 : Polynomial (ZMod 17))) := by
    intro checked
    have impossible := checked 0 false 0
    norm_num at impossible
  simp only [AuthenticatedZeroCheck.program, MultiCommitmentPrefix.program,
    AuthenticatedZeroCheck.continuation, NativeCommittedOpening.continuation,
    AuthenticatedZeroCheck.select, PreparedZeroTerminal.select, SharedContinuation.program,
    simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, pure_bind, bind_assoc]
  dsimp only [rejectedZeroScheme]
  simp only [PackedZeroOracle.run_program, simulateQ_map, StateT.run_map, schemeHash_run (.inl [0]) columnStart 0 rfl,
    map_pure, pure_bind, RecordRoots.run_program]
  change ¬PackedZeroFirst.Boundary (NativePackedInterpolation.nodes 17 (by decide))
    (fun _ : Fin 1 => (1 : Polynomial (ZMod 17))) at rejected
  simp only [rejected, reduceIte]
  rw [schemeHash_run (.inl [1]) (RecordRoots.state workerShape
    (CommittedJointMatrixOpening.requests (fun _ : Unit => ()) [(), ()] ((fun _ => (0 : Fin 2)), ()))
      (zeroColumnStep columnStart (.inl [0]) 0)) 1 rfl]
  simp only [map_pure, pure_bind, bind_assoc, PreparedZeroTerminal.prepare,
    simulateQ_pure, StateT.run_pure, Bool.false_eq_true, reduceIte]
  rw [map_eq_pure_bind]
  rfl

end AuthenticatedZeroSmoke

/-- info: 'FormalProof4FHE.HasteBoots.QueryReindex.fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QueryReindex.fold

/-- info: 'FormalProof4FHE.HasteBoots.QueryReindex.toList' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms QueryReindex.toList

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedZeroCheck.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedZeroCheck.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck.opening_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedZeroCheck.opening_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedZeroCheck.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck.native_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedZeroCheck.native_soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedZeroCheck.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedZeroCheck.project_witness

section PBSHadamardSmoke

/-- Native canonical registry order is evaluation0,key0,evaluation1,key1,...,
then output; no source slot aliases another one. -/
example : ((PBSHadamard.factors 3).map (fun factor => (PBSHadamard.address factor).val)) = List.range 7 := by decide

private def hadamardValues : PBSHadamard.Factor 2 → ZMod 17
  | .inl (index, bit) => if index = 0 then (if bit then 3 else 2) else (if bit then 7 else 5)
  | .inr _ => 7

/-- Both products contribute: 2*3+5*7=7 in F17. The output term has coefficient
-1, and every product term has degree two and coefficient +1. -/
example : PackedSumcheckRound.expression PBSHadamard.arity PBSHadamard.coefficient
    PBSHadamard.indices hadamardValues = 0 := by decide

example : PBSHadamard.Relation (fun factor (_ : MatrixFold.Cube 1) (_ : Fin 1) => hadamardValues factor) := by unfold PBSHadamard.Relation; decide

/-- Swapping key rows across pairs changes the checked relation. -/
private def swappedHadamard : PBSHadamard.Factor 2 → ZMod 17
  | .inl (index, true) => if index = 0 then 7 else 3
  | factor => hadamardValues factor

example : ¬PBSHadamard.Relation (fun factor (_ : MatrixFold.Cube 1) (_ : Fin 1) => swappedHadamard factor) := by unfold PBSHadamard.Relation; decide

/-- The terminal output slot cannot be replaced by a different value. -/
example : ¬PBSHadamard.Relation (fun factor (_ : MatrixFold.Cube 1) (_ : Fin 1) =>
    match factor with | .inr _ => 8 | _ => hadamardValues factor) := by unfold PBSHadamard.Relation; decide

/-- The native relation checks the total product sum. Opposite nonzero products
may cancel, so it must not require every individual product to vanish. -/
private def cancellingHadamard : PBSHadamard.Factor 2 → ZMod 17
  | .inl (index, true) => if index = 0 then 1 else -1
  | .inl (_, false) => 1
  | .inr _ => 0

example : PBSHadamard.Relation (fun factor (_ : MatrixFold.Cube 1) (_ : Fin 1) => cancellingHadamard factor) := by unfold PBSHadamard.Relation; decide

example : cancellingHadamard (.inl (0, false)) * cancellingHadamard (.inl (0, true)) ≠ 0 := by decide

/-- Even the zero-product-count edge retains the final negative-output term. -/
example : ¬PBSHadamard.Relation (count := 0)
    (fun _ (_ : MatrixFold.Cube 1) (_ : Fin 1) => (1 : ZMod 17)) := by unfold PBSHadamard.Relation; decide

end PBSHadamardSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.address_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.address_injective

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.factors_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.factors_complete

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.degree_bound

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.expression

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.vanishes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.vanishes_iff

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.native_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.native_soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.PBSHadamard.address_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PBSHadamard.address_bijective

section NTTStageSmoke

open OracleSpec OracleComp

private def nttNodes : Fin 2 → ZMod 17 := ![4, 13]

/-- Negacyclic size-two evaluation at the two roots of X^2+1. Output order
is fixed by the supplied public node order, not an unordered polynomial set. -/
example : (4 : ZMod 17) ^ 2 = -1 ∧ (13 : ZMod 17) ^ 2 = -1 := by decide

example : NTTRowCheck.evaluation nttNodes ![2, 3] = ![14, 7] := by decide

example : NTTRowCheck.check (NTTRowCheck.evaluation nttNodes)
    (fun _ : Fin 2 => ![2, 3]) (fun _ => ![14, 7]) = true := by decide

example : NTTRowCheck.check (NTTRowCheck.evaluation nttNodes)
    (fun _ : Fin 2 => ![2, 3]) (fun _ => ![7, 14]) = false := by decide

/-- Coefficient coordinates are low and polynomial-row coordinates are high. -/
example : (FlatMatrixFold.index 3 (NTTSourceQuery.join 2 1 (true, (false, ())) (true, ()))).val = 5 := by decide

private def nttFullSource (cell : MatrixFold.Cube 3) : Fin 2 → ZMod 17 :=
  if cell.2.2.1 then 2 • vector else vector

/-- Arbitrary noncommuting compression matrices precede scalar row matrices. -/
example : (NTTSourceQuery.append indexedPairQuery (NTTSourceQuery.rowQuery (![3] : Fin 1 → ZMod 17))).fold
    nttFullSource = ![16, 0] := by decide

/-- Swapping the row/compression query order changes the source obligation. -/
example : (NTTSourceQuery.append (NTTSourceQuery.rowQuery (![3] : Fin 1 → ZMod 17)) indexedPairQuery).fold
    nttFullSource = ![6, 0] := by decide

private def receiveBadNTTRows (_points : Fin 1 → Fin 0 → ZMod 17) (memory : Fin 2) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2))
      (NTTRowOracle.Proposal (ZMod 17) (Fin 1) (Fin 2) 1) :=
  (fun _ => ⟨fun _ _ => 0, fun _ _ => 1, 1 - memory⟩) <$> terminalHash 2

private def bindBadNTTRows (_points : Fin 1 → Fin 0 → ZMod 17)
    (proposal : NTTRowOracle.Proposal (ZMod 17) (Fin 1) (Fin 2) 1) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (Fin 2) :=
  (fun _ => proposal.memory) <$> terminalHash 3

private theorem badNTTRows_run (points : Fin 1 → Fin 0 → ZMod 17) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (NTTRowOracle.next (LinearMap.id : (Fin 1 → ZMod 17) →ₗ[ZMod 17] (Fin 1 → ZMod 17))
        receiveBadNTTRows bindBadNTTRows 0 points)).run workerStart =
      pure (⟨⟨fun _ _ => 0, fun _ _ => 1, 1⟩, false⟩, workerStep (workerStep workerStart 2 0) 3 1) := by
  rfl

/-- A failed local transform check still retains received memory and both
receive/binding hashes. Native NTT binding occurs before local rejection. -/
example : (fun outcome => (outcome.1.2.accepted, outcome.1.2.proposal.memory, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (NTTRowOracle.program (LinearMap.id : (Fin 1 → ZMod 17) →ₗ[ZMod 17] (Fin 1 → ZMod 17))
        receiveBadNTTRows bindBadNTTRows 0)).run workerStart =
      (fun _ : Fin 1 → Fin 0 → ZMod 17 => (false, (1 : Fin 2), 5)) <$>
        ($ᵗ (Fin 1 → Fin 0 → ZMod 17)) := by
  simp only [NTTRowOracle.program, SharedContinuation.program, simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, bind_map_left, badNTTRows_run, pure_bind, simulateQ_pure,
    StateT.run_pure, map_bind, map_pure]
  rw [map_eq_pure_bind]
  rfl

end NTTStageSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.fold_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.fold_sub

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.map_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.map_fold

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.fold_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.fold_native

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.honest_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.honest_rows

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowCheck.checked_miss_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowCheck.checked_miss_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowOracle.next_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowOracle.next_checked

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowOracle.miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowOracle.miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowOracle.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowOracle.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowOracle.soundness_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowOracle.soundness_reduction

/-- info: 'FormalProof4FHE.HasteBoots.NTTSourceQuery.append_list' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTSourceQuery.append_list

/-- info: 'FormalProof4FHE.HasteBoots.NTTSourceQuery.join_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTSourceQuery.join_index

/-- info: 'FormalProof4FHE.HasteBoots.NTTSourceQuery.append_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTSourceQuery.append_fold

/-- info: 'FormalProof4FHE.HasteBoots.NTTSourceQuery.rowQuery_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTSourceQuery.rowQuery_fold

/-- info: 'FormalProof4FHE.HasteBoots.NTTSourceQuery.fold_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTSourceQuery.fold_smul

/-- info: 'FormalProof4FHE.HasteBoots.NTTSourceQuery.source_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTSourceQuery.source_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.NTTRowOracle.continued_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRowOracle.continued_miss_bound

section NTTCompressionSmoke

open OracleSpec OracleComp

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private abbrev CompressionPosition := NTTCompression.Position 1 1

private def compressionSource (cell : MatrixFold.Cube 1) (_lane : Fin 1) : ZMod 17 :=
  if cell.1 then 1 else 0

private def compressionEvaluation (cell : MatrixFold.Cube 1) (lane : Fin 1) : ZMod 17 :=
  2 * compressionSource cell lane

private def receiveCompressionRows (bad : Bool) (_points : Fin 1 → Fin 0 → ZMod 17) (memory : Fin 2) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2))
      (NTTRowOracle.Proposal (ZMod 17) CompressionPosition (Fin 2) 1) :=
  (fun _ => ⟨fun _ _ => 0, fun _ _ => if bad then 1 else 0, 1 - memory⟩) <$> terminalHash 2

private def bindCompressionRows (_points : Fin 1 → Fin 0 → ZMod 17)
    (proposal : NTTRowOracle.Proposal (ZMod 17) CompressionPosition (Fin 2) 1) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (Fin 2) :=
  (fun _ => proposal.memory) <$> terminalHash 3

private def afterCompression (entry : NTTCompression.Prefix (ZMod 17) (Fin 2) 1 1 0 1)
    (_query : PackedSumcheckSubclaim.Query (ZMod 17) 1 1) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (Fin 2) :=
  (fun _ => entry.2.proposal.memory) <$> terminalHash 1

private def zeroCompression : PackedSumcheckSubclaim.Query (ZMod 17) 1 1 :=
  .cons (fun bit => if bit then 0 else 1) .nil

private theorem badCompressionRows_run (points : Fin 1 → Fin 0 → ZMod 17) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (NTTRowOracle.next (LinearMap.id : (CompressionPosition → ZMod 17) →ₗ[ZMod 17] (CompressionPosition → ZMod 17))
        (receiveCompressionRows true) bindCompressionRows 0 points)).run workerStart =
      pure (⟨⟨fun _ _ => 0, fun _ _ => 1, 1⟩, false⟩, workerStep (workerStep workerStart 2 0) 3 1) := by
  rfl

/-- The root-hitting compression used below is a real native Lagrange query,
obtained when the fresh field challenge is zero. -/
example : PackedSumcheckRound.challengePair oraclePackedNodes (fun _ => 0) =
    (fun bit => if bit then (0 : Matrix (Fin 1) (Fin 1) (ZMod 17)) else 1) := by
  have zeroNode : oraclePackedNodes (false, 0) = 0 := by rfl
  funext bit outLane inLane
  fin_cases outLane
  fin_cases inLane
  cases bit with
  | false =>
    change (Lagrange.basis Finset.univ oraclePackedNodes (false, 0)).eval 0 = 1
    simpa only [zeroNode] using Lagrange.eval_basis_self oraclePackedNodes.injective.injOn
      (Finset.mem_univ (false, (0 : Fin 1)))
  | true =>
    change (Lagrange.basis Finset.univ oraclePackedNodes (true, 0)).eval 0 = 0
    simpa only [zeroNode] using Lagrange.eval_basis_of_ne
      (s := Finset.univ) (v := oraclePackedNodes) (by decide : (true, (0 : Fin 1)) ≠ (false, 0))
      (Finset.mem_univ (false, (0 : Fin 1)))

/-- A wrong polynomial can compress to the same value at a root. The bound is
probabilistic; it must not claim deterministic detection of every false row. -/
example : zeroCompression.fold compressionSource = 0 ∧ zeroCompression.fold compressionEvaluation = 0 := by decide

/-- The fixed original coefficient and evaluation polynomials violate the
identity transform, even though their zero-row proposals pass its local check. -/
private theorem compressionRelation_false : ¬NTTRowCheck.Relation
    (LinearMap.id : (CompressionPosition → ZMod 17) →ₗ[ZMod 17] (CompressionPosition → ZMod 17))
    (NTTCompression.sourceRows 1 0 compressionSource) (NTTCompression.sourceRows 1 0 compressionEvaluation) := by
  intro valid
  have impossible := congrFun (valid ()) ((true, ()), 0)
  norm_num [NTTCompression.sourceRows, NTTSourceQuery.join, compressionSource, compressionEvaluation] at impossible
  exact (by decide : (1 : ZMod 17) ≠ 2) impossible

/-- One coefficient variable and one independent output lane yield the
nontrivial 1/17 bound on this actual shared prefix/compression execution. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (NTTCompression.program oraclePackedNodes
      (LinearMap.id : (CompressionPosition → ZMod 17) →ₗ[ZMod 17] (CompressionPosition → ZMod 17))
      (receiveCompressionRows false) bindCompressionRows 0 afterCompression)).run workerStart}[
        NTTCompression.TruthfulTerminals compressionSource compressionEvaluation outcome.1] ≤ (1 / 17 : ENNReal) := by
  have bound := NTTCompression.truthful_bound overlappingMerkleEncoding 0 workerShape oraclePackedNodes
    (LinearMap.id : (CompressionPosition → ZMod 17) →ₗ[ZMod 17] (CompressionPosition → ZMod 17))
    compressionSource compressionEvaluation (receiveCompressionRows false) bindCompressionRows 0 afterCompression
    workerStart compressionRelation_false
  norm_num at bound ⊢
  exact bound

/-- A rejected local check disables all coefficient-compression coins and
callbacks. It still retains the earlier received and binding hashes. -/
example : (fun outcome => (outcome.1.1.2.accepted, outcome.1.2.isSome, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      overlappingMerkleEncoding 0 workerShape)
      (NTTCompression.program oraclePackedNodes
        (LinearMap.id : (CompressionPosition → ZMod 17) →ₗ[ZMod 17] (CompressionPosition → ZMod 17))
        (receiveCompressionRows true) bindCompressionRows 0 afterCompression)).run workerStart =
      (fun _ : Fin 1 → Fin 0 → ZMod 17 => (false, false, 5)) <$>
        ($ᵗ (Fin 1 → Fin 0 → ZMod 17)) := by
  simp only [NTTCompression.program, GuardedCompression.program, SharedContinuation.program,
    NTTRowOracle.program, PrivateSampling.run_probComp, simulateQ_bind, StateT.run_bind,
    bind_map_left, simulateQ_pure, StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind,
    badCompressionRows_run]
  simp only [GuardedCompression.finish, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure, pure_bind]
  rw [map_eq_pure_bind]
  rfl

/-- Disabled compression issues no callback even when its query dimension is
positive and the callback itself would query the shared hash. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    overlappingMerkleEncoding 0 workerShape)
    (GuardedCompression.finish oraclePackedNodes false
      (fun (_ : PackedSumcheckSubclaim.Query (ZMod 17) 1 2) => terminalHash 3))).run workerStart =
      pure (none, workerStart) := by rfl

end NTTCompressionSmoke

/-- info: 'FormalProof4FHE.HasteBoots.MatrixCompression.factor_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixCompression.factor_nonzero

/-- info: 'FormalProof4FHE.HasteBoots.MatrixCompression.first_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixCompression.first_zero_bound

/-- info: 'FormalProof4FHE.HasteBoots.MatrixCompression.zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixCompression.zero_bound

/-- info: 'FormalProof4FHE.HasteBoots.MatrixCompression.fold_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixCompression.fold_sub

/-- info: 'FormalProof4FHE.HasteBoots.MatrixCompression.agreement_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixCompression.agreement_bound

/-- info: 'FormalProof4FHE.HasteBoots.MatrixCompression.family_agreement_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MatrixCompression.family_agreement_bound

/-- info: 'FormalProof4FHE.HasteBoots.GuardedCompression.finish_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedCompression.finish_bound

/-- info: 'FormalProof4FHE.HasteBoots.GuardedCompression.wrong_agreement_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedCompression.wrong_agreement_bound

/-- info: 'FormalProof4FHE.HasteBoots.GuardedCompression.finish_enabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GuardedCompression.finish_enabled

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.pack_injective' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.pack_injective

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.pack_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.pack_fold

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.correct_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.correct_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.wrong_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.wrong_family

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.truthful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.truthful_iff

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.truthful_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.truthful_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.NTTCompression.truthful_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTCompression.truthful_bound

section NativeBatchOpeningSmoke

open OracleSpec OracleComp

/-- Native insertion order keeps first representatives, not the last duplicate. -/
example : BatchGrouping.compute ([2, 1, 2, 3, 1] : List ℕ) = ([2, 1, 3], [0, 1, 0, 2, 1]) := by rfl

example : (BatchGrouping.representative ([2, 1, 2, 3, 1] : List ℕ) ⟨2, by decide⟩).val = 3 := by rfl

private def batchQueryA : PackedSumcheckSubclaim.Query (ZMod 17) 1 2 :=
  .cons (fun _ => 1) (.cons (fun _ => 1) .nil)
private def batchQueryB : PackedSumcheckSubclaim.Query (ZMod 17) 1 2 :=
  .cons (fun _ => 1) (.cons (fun _ => 2) .nil)
private def batchQueryC : PackedSumcheckSubclaim.Query (ZMod 17) 1 2 :=
  .cons (fun _ => 2) (.cons (fun _ => 1) .nil)
private def batchQueries : Fin 3 → PackedSumcheckSubclaim.Query (ZMod 17) 1 2 :=
  ![batchQueryA, batchQueryB, batchQueryC]

/-- A different suffix may share a structured response; a different prefix
gets its own group. The front/suffix split is explicitly trusted. -/
example : BatchQueryLayout.groupCount (front := 1) (suffix := 1) batchQueries = 2 := by decide

example : BatchQueryLayout.groupOf (front := 1) (suffix := 1) batchQueries 0 =
    BatchQueryLayout.groupOf (front := 1) (suffix := 1) batchQueries 1 := by decide

example : BatchQueryLayout.groupOf (front := 1) (suffix := 1) batchQueries 0 ≠
    BatchQueryLayout.groupOf (front := 1) (suffix := 1) batchQueries 2 := by decide

/-- Equal semantic left weights do not merge distinct native prefix arrays. -/
example : SubclaimSourceLayout.leftWeights (front := 2) (suffix := 0) batchQueryB =
    SubclaimSourceLayout.leftWeights (front := 2) (suffix := 0) batchQueryC := by decide

example : BatchQueryLayout.groupCount (front := 2) (suffix := 0)
    (![batchQueryB, batchQueryC] : Fin 2 → PackedSumcheckSubclaim.Query (ZMod 17) 1 2) = 2 := by decide

/-- Two grouped responses share each actual native column authentication. The
log has the same four worker hashes as the one-group case, not eight. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeBatchColumnWorkerPool.program columnEncoding 0 poolWeights (fun _ : Fin 2 => poolWeights)
        poolResponse (fun _ : Fin 2 => poolResponse) poolColumns columnChoose 4 [0, 1, 0, 1])).run columnStart =
      pure (true, 7) := by rfl

/-- A bad response in the second group rejects despite the first group and
random test passing; previously issued authentication hashes stay in the log. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeBatchColumnWorkerPool.program columnEncoding 0 poolWeights (fun _ : Fin 2 => poolWeights)
        poolResponse (fun group : Fin 2 => if group = 0 then poolResponse else fun _ => 0)
        poolColumns columnChoose 4 [0, 1, 0, 1])).run columnStart =
      pure (false, 7) := by rfl

/-- Empty structured groups must not erase a failing random-test check. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeBatchColumnWorkerPool.program columnEncoding 0 poolWeights (fun group : Fin 0 => Fin.elim0 group)
        (fun _ => 0) (fun group : Fin 0 => Fin.elim0 group) poolColumns columnChoose 4 [0, 1, 0, 1])).run columnStart =
      pure (false, 7) := by rfl

end NativeBatchOpeningSmoke

/-- info: 'FormalProof4FHE.HasteBoots.BatchMatrixSampling.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchMatrixSampling.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.BatchMatrixSampling.arithmetic_after_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchMatrixSampling.arithmetic_after_bound

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.step_prefix' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.step_prefix

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.step_lookup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.step_lookup

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.preserve_lookup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.preserve_lookup

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.run_prefix' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.run_prefix

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.run_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.run_valid

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.step_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.step_nodup

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.run_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.run_nodup

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.representatives_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.representatives_nodup

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.groups_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.groups_length

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.group_lookup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.group_lookup

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.group_key' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.group_key

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.groupOf_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.groupOf_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.step_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.step_mem

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.run_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.run_mem

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.representatives_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.representatives_mem

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.representative_key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.representative_key

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.representative_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.representative_first

/-- info: 'FormalProof4FHE.HasteBoots.BatchGrouping.representative_group_key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchGrouping.representative_group_key

/-- info: 'FormalProof4FHE.HasteBoots.BatchQueryLayout.key_position' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchQueryLayout.key_position

/-- info: 'FormalProof4FHE.HasteBoots.BatchQueryLayout.key_representative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchQueryLayout.key_representative

/-- info: 'FormalProof4FHE.HasteBoots.BatchQueryLayout.groupOf_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchQueryLayout.groupOf_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.BatchQueryLayout.representative_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchQueryLayout.representative_prefix

/-- info: 'FormalProof4FHE.HasteBoots.BatchQueryLayout.left_eq_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchQueryLayout.left_eq_of_prefix

/-- info: 'FormalProof4FHE.HasteBoots.BatchQueryLayout.representative_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchQueryLayout.representative_left

/-- info: 'FormalProof4FHE.HasteBoots.BatchColumnChecks.allCoordinates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchColumnChecks.allCoordinates_iff

/-- info: 'FormalProof4FHE.HasteBoots.BatchColumnChecks.pair_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BatchColumnChecks.pair_coordinates

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchColumnWorkerPool.worker_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchColumnWorkerPool.worker_accepts

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchColumnWorkerPool.accepted_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchColumnWorkerPool.accepted_columns

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchColumnWorkerPool.accepted_columns_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchColumnWorkerPool.accepted_columns_later

section CommittedNativeBatchSmoke

open OracleSpec OracleComp

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def selectedBatchQuery (claim : Fin 2) : PackedSumcheckSubclaim.Query (ZMod 17) 1 1 :=
  .cons (fun bit => if bit then (if claim = 0 then 0 else 1) else (if claim = 0 then 1 else 0)) .nil

private def selectedBatchValues (claim : Fin 2) (_ : Fin 1) : ZMod 17 := if claim = 0 then 0 else 1
private def wrongAliasValues (claim : Fin 2) (_ : Fin 1) : ZMod 17 := if claim = 0 then 0 else 2

private def batchTestMessage (matrix : InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) 1 1)
    (_ : Unit) (_ : Fin 1) (index : Fin 2) : ZMod 17 := matrix 0 (0, 0) * index.val
private def batchGroupMessage (_ : ℕ) (_matrix : InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) 1 1)
    (_ : Unit) (_ : Fin 1) (index : Fin 2) : ZMod 17 := index.val

private def selectedBatchData : JointMatrixOpening.Data (ZMod 17) (Fin 2) Unit 1 1 1 2 :=
  ((((fun _ _ => 1), ()), fun index => index), poolColumns)

private theorem selectedBatchIndices : NativeColumnLayout.distinctIndices selectedBatchData.1.2 = [0, 1] := by
  unfold NativeColumnLayout.distinctIndices
  change (([0, 1] : List (Fin 2)).mergeSort (fun a b => decide (a ≤ b))).dedup = [0, 1]
  rw [List.mergeSort_eq_self (r := fun a b : Fin 2 => a ≤ b) (by decide)]
  simp

private theorem selectedColumnsCheck : NativeBatchChecks.columnsCheck poolColumns selectedBatchData.1.2 = true := by
  simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
  decide

/-- Both queries share the one empty left prefix but finish different suffixes. -/
example : BatchQueryLayout.groupCount (front := 0) (suffix := 1) selectedBatchQuery = 1 := by decide

example : NativeBatchChecks.coordinates (front := 0) (suffix := 1) (m := 2) checkedDomain selectedBatchQuery
    batchTestMessage batchGroupMessage selectedBatchData = true := by decide

example : NativeBatchChecks.check (front := 0) (suffix := 1) (m := 2) checkedDomain selectedBatchQuery selectedBatchValues
    batchTestMessage batchGroupMessage selectedBatchData = true := by decide

/-- The nonrepresentative query must check its own value. Checking only group
representatives would miss this changed second value despite valid columns. -/
example : NativeBatchChecks.check (front := 0) (suffix := 1) (m := 2) checkedDomain selectedBatchQuery wrongAliasValues
    batchTestMessage batchGroupMessage selectedBatchData = false := by decide

/-- Coverage alone is insufficient for the native position attachment: extra
columns and changed order must fail before workers start. -/
example : NativeBatchChecks.columnsCheck poolColumns selectedBatchData.1.2 = true := selectedColumnsCheck
example : NativeBatchChecks.columnsCheck poolColumns.reverse selectedBatchData.1.2 = false := by
  simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
  decide
example : NativeBatchChecks.columnsCheck (poolColumns ++ [poolColumn 0]) selectedBatchData.1.2 = false := by
  simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
  decide

private noncomputable def selectedBatchProtocol
    (columns : List (NativeColumnLayout.Column (ZMod 17) (Fin 2) 1 1 1)) :
    NativeBatchVerifier.Protocol (ZMod 17) ColumnInput (Fin 2) Unit Unit (Fin 2) 1 0 1 2 2 2 1 where
  encoding := columnEncoding
  domain := checkedDomain
  root := 0
  query := selectedBatchQuery
  values := selectedBatchValues
  testResponse := batchTestMessage
  groupResponse := batchGroupMessage
  prepare := fun memory => (fun _ => 1 - memory) <$> schemeHash (.inl [0])
  respond := fun _ _ => (fun _ => ()) <$> schemeHash (.inr (0, 1))
  receiveColumns := fun _ _ => (fun _ => (columns, 1)) <$> schemeHash (.inl [0])
  choose := fun _ _ columns _ memory =>
    if bound : memory.val < columns.length then pure (some ⟨memory.val, bound⟩, 1 - memory)
    else pure (none, memory)
  fuel := fun _ _ _ => 4

/-- Correct grouped columns run exactly one native authentication pool. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeBatchVerifier.next (selectedBatchProtocol poolColumns) 0 selectedBatchData.1)).run columnStart =
      pure (true, 8)  := by
  simp only [NativeBatchVerifier.next, selectedBatchProtocol, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, schemeHash_run (.inl [0]) columnStart 0 rfl, map_pure, pure_bind]
  simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
  rfl

/-- A missing selected column keeps provider work but starts neither workers
nor scheduler callbacks, so only the received-data hash is added. -/
example : (fun outcome => (outcome.1.2, outcome.1.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeBatchVerifier.next (selectedBatchProtocol [poolColumn 0]) 0 selectedBatchData.1)).run columnStart =
      pure (false, (1 : Fin 2), 4)  := by
  simp only [NativeBatchVerifier.next, selectedBatchProtocol, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, schemeHash_run (.inl [0]) columnStart 0 rfl, map_pure, pure_bind]
  simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
  rfl

example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (NativeBatchVerifier.next (selectedBatchProtocol poolColumns.reverse) 0 selectedBatchData.1)).run columnStart =
      pure (false, 4)  := by
  simp only [NativeBatchVerifier.next, selectedBatchProtocol, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, schemeHash_run (.inl [0]) columnStart 0 rfl, map_pure, pure_bind]
  simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
  rfl

/-- A failed first batch skips the second root's prelude as well as all its
coins and hashes. The first root retains prepare/response/provider work. -/
example : (fun outcome => (outcome.1.accepted, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (ShortCircuitSequence.program (fun _ : Unit => NativeBatchVerifier.step (selectedBatchProtocol [])) [(), ()] 0)).run columnStart =
      (do
        let _ ← $ᵗ (InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) 1 1)
        let _ ← $ᵗ (Fin 2 → Fin 2)
        pure (false, 6)) := by
  simp only [ShortCircuitSequence.program, NativeBatchVerifier.step, NativeBatchVerifier.sampledStep,
    StoppingJointMatrixOpening.step, StoppingJointMatrixOpening.checkedNext, InteractiveSampling.complete,
    InteractiveSampling.program, NativeBatchVerifier.next, selectedBatchProtocol,
    simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp,
    bind_map_left, simulateQ_pure, StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind,
    schemeHash_run (.inl [0]) columnStart 0 rfl,
    schemeHash_run (.inr (0, 1)) (zeroColumnStep columnStart (.inl [0]) 0) 0 rfl,
    schemeHash_run (.inl [0]) (zeroColumnStep (zeroColumnStep columnStart (.inl [0]) 0) (.inr (0, 1)) 0) 0 rfl,
    NativeBatchChecks.columnsCheck, List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.false_eq_true, reduceIte]
  rfl

private def batchCommit : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) ((Unit → Fin 2) × Unit) :=
  (fun _ => ((fun _ => 0), ())) <$> schemeHash (.inl [0])
private def batchSelect (_emission : (Unit → Fin 2) × Unit) :
    OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) Unit :=
  (fun _ => ()) <$> schemeHash (.inl [1])

/-- A disabled committed terminal retains commit/selection work but skips all
root preludes, random tests, response calls, column draws and worker hashes. -/
example : (fun outcome => (outcome.1.2.2.accepted, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (MultiCommitmentPrefix.program (CommittedJointMatrixOpening.requests (fun _ : Unit => ()) [(), ()]) batchCommit
        (CommittedBatchOpening.continuation columnEncoding checkedDomain
          (fun (_ : (Unit → Fin 2) × Unit) (_ : Unit) (_ : Unit) => selectedBatchProtocol poolColumns)
          batchSelect (fun _ _ => false) (fun _ _ => (0 : Fin 2)) [(), ()]))).run columnStart = pure (false, 5) := by
  rfl

private def authenticatedNTTPacket : AuthenticatedNTT.Packet (ZMod 17) (Fin 2) 1 1 0 2 :=
  ((fun _ => Fin.elim0,
    ⟨⟨fun repetition position => repetition.val + if position.1.1 then 10 else 3,
      fun repetition position => 2 * (repetition.val + if position.1.1 then 10 else 3), 1⟩, true⟩),
    some (selectedBatchQuery 0, 0))

private noncomputable def authenticatedNTTScheme (bad : Bool) :
    AuthenticatedNTT.Scheme (ZMod 17) ColumnInput (Fin 2) Unit Unit (Fin 2) Unit 1 1 0 2 0 1 2 2 1 where
  dimensions := rfl
  encoding := columnEncoding
  domain := checkedDomain
  tag := fun _ => ()
  nodes := oraclePackedNodes
  transform := 2 • LinearMap.id
  commit := (fun _ => ((fun side => if side then 1 else 0), ())) <$> schemeHash (.inl [0])
  initial := fun _ => 0
  receive := fun _ _ memory =>
    (fun _ => ⟨fun _ _ => 0, fun _ _ => if bad then 1 else 0, 1 - memory⟩) <$> schemeHash (.inl [0])
  bindRows := fun _ _ proposal => (fun _ => proposal.memory) <$> schemeHash (.inl [1])
  afterQuery := fun _ packet _ => (fun _ => packet.2.proposal.memory) <$> schemeHash (.inr (0, 1))
  build := fun _ _ _ => selectedBatchProtocol poolColumns

/-- The factory attempts different repetition queries and values. Both are
replaced by the one computed compression query and proposed row evaluations. -/
example : (AuthenticatedNTT.build (authenticatedNTTScheme false) ((fun _ => 0), ())
    authenticatedNTTPacket false).values 0 0 = 3 := by decide
example : (AuthenticatedNTT.build (authenticatedNTTScheme false) ((fun _ => 0), ())
    authenticatedNTTPacket false).values 1 0 = 4 := by decide
example : (AuthenticatedNTT.build (authenticatedNTTScheme false) ((fun _ => 0), ())
    authenticatedNTTPacket true).values 1 0 = 8 := by decide
example : (AuthenticatedNTT.build (authenticatedNTTScheme false) ((fun _ => 0), ())
    authenticatedNTTPacket true).query 1 = selectedBatchQuery 0 := rfl

/-- Root protection occurs after factory replacement of the computed claims. -/
example : (CommittedBatchOpening.protocol columnEncoding checkedDomain
    (AuthenticatedNTT.build (authenticatedNTTScheme false)) ((fun side => if side then 1 else 0), ())
    authenticatedNTTPacket true).root = 1 := rfl

example : AuthenticatedNTT.enabled
    (authenticatedNTTPacket.1, (none : Option (PackedSumcheckSubclaim.Query (ZMod 17) 1 1 × Fin 2))) = false := rfl
example : AuthenticatedNTT.memory
    (authenticatedNTTPacket.1, (none : Option (PackedSumcheckSubclaim.Query (ZMod 17) 1 1 × Fin 2))) = 1 := rfl
example : AuthenticatedNTT.memory authenticatedNTTPacket = 0 := rfl

/-- A failed transform identity still binds the received rows, then skips
positive-dimensional compression and both roots' bindings, coins and hashes. -/
example : (fun outcome => (AuthenticatedNTT.accepted outcome.1, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (AuthenticatedNTT.continuation (authenticatedNTTScheme true) ((fun _ => 0), ()))).run columnStart =
      (fun _ : Fin 2 → Fin 0 → ZMod 17 => (false, 5)) <$> ($ᵗ (Fin 2 → Fin 0 → ZMod 17)) := by
  simp only [AuthenticatedNTT.continuation, CommittedBatchOpening.continuation,
    AuthenticatedNTT.select, NTTCompression.program, GuardedCompression.program,
    SharedContinuation.program, NTTRowOracle.program, PrivateSampling.run_probComp,
    simulateQ_bind, StateT.run_bind, bind_map_left, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, bind_assoc, pure_bind]
  simp only [GuardedCompression.finish, AuthenticatedNTT.enabled]
  rw [map_eq_pure_bind]
  rfl

end CommittedNativeBatchSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchChecks.columnsCheck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchChecks.columnsCheck_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchChecks.columnsCheck_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchChecks.columnsCheck_covers

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchChecks.group_left_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchChecks.group_left_eq

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchChecks.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchChecks.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchChecks.coordinates_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchChecks.coordinates_claim

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchChecks.wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchChecks.wrong_implies_arithmetic_or_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchVerifier.next_accepts_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchVerifier.next_accepts_later

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchVerifier.sampled_accepts_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchVerifier.sampled_accepts_later

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchVerifier.step_accepts_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchVerifier.step_accepts_later

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchVerifier.wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchVerifier.wrong_implies_arithmetic_or_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchVerifier.sampled_arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchVerifier.sampled_arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.NativeBatchVerifier.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeBatchVerifier.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommittedBatchOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommittedBatchOpening.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.CommittedBatchOpening.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommittedBatchOpening.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedNTT.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedNTT.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedNTT.source_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedNTT.source_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedNTT.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedNTT.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedNTT.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedNTT.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedNTT.opening_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedNTT.opening_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedNTT.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedNTT.soundness_from_empty

section NTTButterflySmoke

private theorem primitiveEight : IsPrimitiveRoot (2 : ZMod 17) 8 := by
  apply (IsPrimitiveRoot.iff (by decide)).mpr
  refine ⟨by decide, ?_⟩
  intro exponent positive less
  have checked : ∀ exponent : Fin 8, exponent.val ≠ 0 → (2 : ZMod 17) ^ exponent.val ≠ 1 := by decide
  exact checked ⟨exponent, less⟩ (Nat.ne_of_gt positive)

private theorem primitiveFour : IsPrimitiveRoot (4 : ZMod 17) 4 := by
  exact primitiveEight.pow (by decide) (by decide : 8 = 2 * 4)

example : (fun index => (NTTButterfly.reverseIndex 3 index).val) = ![0, 4, 2, 6, 1, 5, 3, 7] := by decide

/-- Output order is the native odd-root bit reversal, rather than sorted
odd exponents. This fixture changes if the middle two outputs are swapped. -/
example : NTTButterfly.nodes 2 (2 : ZMod 17) = ![2, 15, 8, 9] := by decide
example : NTTButterfly.flatTransform 2 (2 : ZMod 17) 4 ![1, 2, 3, 4] = ![15, 11, 13, 16] := by decide
example : NTTButterfly.flatTransform 2 (2 : ZMod 17) 4 ![1, 2, 3, 4] ≠ ![15, 13, 11, 16] := by decide
example : NTTButterfly.flatTransform 0 (-1 : ZMod 17) 1 (fun _ => 7) 0 = 7 := rfl

example (index : Fin 4) : NTTButterfly.nodes 2 (2 : ZMod 17) index ^ 4 = -1 :=
  NTTButterfly.nodes_power 2 2 primitiveEight index

private def packedFour : NTTCompression.Position 1 2 → ZMod 17 :=
  fun position => if position.1.1 then (if position.2 = 0 then 3 else 4) else (if position.2 = 0 then 1 else 2)

/-- The lane stays low within each coefficient block, independently of the
bit-reversed output ordering. -/
example : (PackedNTT.address (by decide : 2 ^ 1 * 2 = 2 ^ 2) ((true, ()), 0)).val = 2 := rfl
example : PackedNTT.flatten (by decide : 2 ^ 1 * 2 = 2 ^ 2) packedFour = ![1, 2, 3, 4] := by decide
example : PackedNTT.flatten (by decide : 2 ^ 1 * 2 = 2 ^ 2)
    (PackedNTT.butterfly (by decide : 2 ^ 1 * 2 = 2 ^ 2) (2 : ZMod 17) packedFour) = ![15, 11, 13, 16] := by decide

example : PackedNTT.check (by decide : 2 ^ 1 * 2 = 2 ^ 2) (2 : ZMod 17)
    (fun _ : Fin 1 => packedFour)
    (fun _ => PackedNTT.unflatten (by decide : 2 ^ 1 * 2 = 2 ^ 2) ![15, 11, 13, 16]) = true := by decide
example : PackedNTT.check (by decide : 2 ^ 1 * 2 = 2 ^ 2) (2 : ZMod 17)
    (fun _ : Fin 1 => packedFour)
    (fun _ => PackedNTT.unflatten (by decide : 2 ^ 1 * 2 = 2 ^ 2) ![15, 13, 11, 16]) = false := by decide

/-- The concrete scheme replaces a factory's unrelated transform (2*id) with
the actual butterflies; the first output is 1+psi, not 2. -/
example : (PackedNTT.scheme (by decide : 2 ^ 1 * 1 = 2 ^ 1) (4 : ZMod 17) primitiveFour
    (authenticatedNTTScheme false)).transform (fun _ => 1) ((false, ()), 0) = 5 := by decide

/-- Each coordinate gets its own zero-padded N-element buffer, then outputs
are interleaved. The second lane is just X; the first has three coefficients. -/
example : NTTBlockEncoder.encode (n := 2) (2 : ZMod 17) ![![1, 0], ![2, 1], ![3, 0]] =
    ![![0, 2], ![9, 15], ![5, 8], ![7, 9]] := by decide

example : NTTBlockEncoder.encode (n := 2) (2 : ZMod 17) (0 : Fin 3 → Fin 2 → ZMod 17) = 0 := by decide

end NTTButterflySmoke

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.outputIndex_succ_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.outputIndex_succ_val

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.reverseIndex_outputIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.reverseIndex_outputIndex

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.halves_left_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.halves_left_val

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.halves_right_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.halves_right_val

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.evaluate_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.evaluate_halves

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.point_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.point_succ

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.half_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.half_power

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.square_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.square_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.point_half_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.point_half_power

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.transform_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.transform_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.nodes_eq_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.nodes_eq_point

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.negacyclic_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.negacyclic_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.nodes_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.nodes_power

/-- info: 'FormalProof4FHE.HasteBoots.NTTButterfly.nodes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTButterfly.nodes_injective

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.address_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.address_val

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.unflatten_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.unflatten_flatten

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.flatten_unflatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.flatten_unflatten

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.butterfly_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.butterfly_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.check_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.check_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.relation_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.relation_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.sources_scheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.sources_scheme

/-- info: 'FormalProof4FHE.HasteBoots.PackedNTT.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedNTT.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.NTTBlockEncoder.evaluate_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTBlockEncoder.evaluate_padded

/-- info: 'FormalProof4FHE.HasteBoots.NTTBlockEncoder.encode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTBlockEncoder.encode_eq

/-- info: 'FormalProof4FHE.HasteBoots.NTTBlockEncoder.encode_mem_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTBlockEncoder.encode_mem_code

section NativeNTTRootSmoke

example : NTTRootCheck.check 2 (0 : ZMod 17) = false := by decide
example : NTTRootCheck.check 2 (1 : ZMod 17) = false := by decide
example : NTTRootCheck.check 2 (2 : ZMod 17) = true := by decide
example : NTTRootCheck.check 2 (4 : ZMod 17) = false := by decide
example : NTTRootCheck.check 3 (2 : ZMod 17) = false := by decide

/-- Odd characteristic is essential: the literal half-power test alone can
accept one in characteristic two, although it has no order four. -/
example : NTTRootCheck.check 1 (1 : ZMod 2) = true := by decide
example : ¬IsPrimitiveRoot (1 : ZMod 2) 4 := by
  intro primitive
  exact primitive.ne_one (by decide) rfl

example : Field NativeFields.Goldilocks := inferInstance
example : Field NativeFields.BabyBear := inferInstance
example : (NativeNTTRoots.goldilocksMain).val = 455906449640507599 := rfl
example : (NativeNTTRoots.babyBearMain).val = 812423803 := rfl

example : NativeNTTRoots.goldilocksMain ^ 1024 = -1 :=
  NTTButterfly.half_power (n := 10) NativeNTTRoots.goldilocksMain_primitive
example : NativeNTTRoots.babyBearMain ^ 1024 = -1 :=
  NTTButterfly.half_power (n := 10) NativeNTTRoots.babyBearMain_primitive
example : NTTRootCheck.check 10 NativeNTTRoots.goldilocksMain = true := NativeNTTRoots.goldilocksMain_check
example : NTTRootCheck.check 10 NativeNTTRoots.babyBearMain = true := NativeNTTRoots.babyBearMain_check

/-- Both endpoints of each full two-adic tower are covered, without a query
budget or an empirically chosen transform-height cutoff. -/
example : IsPrimitiveRoot (NativeNTTRoots.goldilocksRoot 0) 2 := NativeNTTRoots.goldilocksRoot_primitive 0 (by decide)
example : IsPrimitiveRoot (NativeNTTRoots.goldilocksRoot 31) (2 ^ 32) := NativeNTTRoots.goldilocksRoot_primitive 31 (by decide)
example : IsPrimitiveRoot (NativeNTTRoots.babyBearRoot 0) 2 := NativeNTTRoots.babyBearRoot_primitive 0 (by decide)
example : IsPrimitiveRoot (NativeNTTRoots.babyBearRoot 26) (2 ^ 27) := NativeNTTRoots.babyBearRoot_primitive 26 (by decide)

/-- The public field-adicity condition cannot be dropped: subtraction saturates
but does not create a root of a larger order. -/
example : ¬IsPrimitiveRoot (NativeNTTRoots.goldilocksRoot 32) (2 ^ 33) := by
  intro impossible
  have smaller : IsPrimitiveRoot (NativeNTTRoots.goldilocksRoot 32) (2 ^ 32) := by
    simpa only [NativeNTTRoots.goldilocksRoot, Nat.reduceSub, pow_zero, pow_one] using NativeNTTRoots.goldilocksTop_primitive
  have different := smaller.unique impossible
  norm_num at different

end NativeNTTRootSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NTTRootCheck.primitive_of_half_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRootCheck.primitive_of_half_power

/-- info: 'FormalProof4FHE.HasteBoots.NTTRootCheck.half_power_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRootCheck.half_power_iff

/-- info: 'FormalProof4FHE.HasteBoots.NTTRootCheck.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NTTRootCheck.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.goldilocks_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.goldilocks_prime

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.babyBear_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.babyBear_prime

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.goldilocks_top_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.goldilocks_top_arithmetic

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.babyBear_top_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.babyBear_top_arithmetic

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.goldilocks_main_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.goldilocks_main_arithmetic

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.babyBear_main_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.babyBear_main_arithmetic

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.goldilocks_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.goldilocks_card

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.babyBear_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.babyBear_card

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.goldilocks_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.goldilocks_odd

/-- info: 'FormalProof4FHE.HasteBoots.NativeFields.babyBear_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeFields.babyBear_odd

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocksTop_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocksTop_half

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBearTop_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBearTop_half

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocksTop_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocksTop_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBearTop_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBearTop_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocksRoot_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocksRoot_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBearRoot_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBearRoot_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocksMain_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocksMain_tower

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBearMain_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBearMain_tower

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocksMain_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocksMain_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBearMain_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBearMain_primitive

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocksMain_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocksMain_check

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBearMain_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBearMain_check

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.goldilocks_packing' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.goldilocks_packing

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTRoots.babyBear_packing' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTRoots.babyBear_packing

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTSecurity.goldilocks_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTSecurity.goldilocks_soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeNTTSecurity.babyBear_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeNTTSecurity.babyBear_soundness_from_empty

section PCSAnalysisAlphabetSmoke

noncomputable section

example : Field (PCSAnalysisField.Alphabet 17 2) := inferInstance
example : SampleableType (Fin 3 → PCSAnalysisField.Alphabet 17 2) := inferInstance
example : Module.finrank (ZMod 17) (PCSAnalysisField.Alphabet 17 2) = 2 := PCSAnalysisField.dimension 17 2
example : Fintype.card (PCSAnalysisField.Alphabet 17 2) = 289 := PCSAnalysisField.cardinality 17 2
example : Fintype.card PCSAnalysisField.GoldilocksAlphabet = NativeFields.goldilocksModulus ^ 4 := PCSAnalysisField.goldilocks_card
example : Fintype.card PCSAnalysisField.BabyBearAlphabet = NativeFields.babyBearModulus ^ 8 := PCSAnalysisField.babyBear_card

/-- The PCS alphabets cannot silently be replaced by the lookup degrees 3/6. -/
example : Fintype.card PCSAnalysisField.GoldilocksAlphabet ≠ NativeFields.goldilocksModulus ^ 3 := by
  rw [PCSAnalysisField.goldilocks_card]
  intro equal
  have impossible := Nat.pow_right_injective NativeFields.goldilocks_prime.one_lt equal
  omega
example : Fintype.card PCSAnalysisField.BabyBearAlphabet ≠ NativeFields.babyBearModulus ^ 6 := by
  rw [PCSAnalysisField.babyBear_card]
  intro equal
  have impossible := Nat.pow_right_injective NativeFields.babyBear_prime.one_lt equal
  omega

/-- A zero extension exponent does not produce a one-element field. The
positive-degree condition on the basis/cardinality theorem is essential. -/
example : 1 < Fintype.card (PCSAnalysisField.Alphabet 17 0) := Fintype.one_lt_card

/-- A genuine two-coordinate symbol alphabet instantiates the full exact PCS
error, including the proximity term and the larger column miss term. -/
example : JointMatrixOpening.error (F := ZMod 17) (K := PCSAnalysisField.Alphabet 17 2) (m := 2) (b := 2) (queries := 2) (height := 3)
    (NativePackedInterpolation.consecutive 17 (by decide : 8 ≤ 17)) 1 = (2713 / 4624 : ENNReal) := by
  rw [PCSParameters.error_eq]
  norm_num [PCSParameters.error, PCSParameters.distance, PCSParameters.miss, ZMod.card]
  have numeric : (7 / 289 + max ((2 / 8) ^ 2) ((6 / 8) ^ 2) : NNReal) = 2713 / 4624 := by
    have comparison : (1 / 16 : NNReal) ≤ 9 / 16 :=
      div_le_div_of_nonneg_right (by norm_num) (by norm_num)
    rw [show (2 / 8 : NNReal) ^ 2 = 1 / 16 by norm_num,
      show (6 / 8 : NNReal) ^ 2 = 9 / 16 by norm_num, max_eq_right comparison]
    norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_max, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (289 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0), ENNReal.coe_div (by norm_num : (4624 : NNReal) ≠ 0),
    ENNReal.coe_ofNat] using congrArg (fun value : NNReal => (value : ENNReal)) numeric

/-- An empty column quota has no detection power; its miss terms stay one. -/
example : PCSParameters.error 17 2 3 2 0 1 = (296 / 289 : ENNReal) := by
  norm_num [PCSParameters.error, PCSParameters.distance, PCSParameters.miss]
  have numeric : (7 / 289 + 1 : NNReal) = 296 / 289 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (289 : NNReal) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one] using congrArg (fun value : NNReal => (value : ENNReal)) numeric

/-- Saturation truncates the Nat subtraction, retaining distance one. -/
example : PCSParameters.distance 3 10 = 1 := rfl

/-- Zero message degree instead gives the zero code, so distance L-m+1 must
not be applied after dropping the positive-degree premise. -/
example : Code.minDist (ReedSolomon.code checkedDomain 0 : Set (Fin 2 → ZMod 17)) = 0 := ReedSolomon.minDist_n_0
example : PCSParameters.distance 1 0 = 3 := rfl

/-- Division by zero is genuinely different in ENNReal, so the finite-error
bridge must retain its nonzero-alphabet premise. -/
example : PCSParameters.error 0 1 0 1 1 0 = ⊤ := by
  norm_num [PCSParameters.error, PCSParameters.distance, PCSParameters.miss]
example : PCSParameters.finiteError 0 1 0 1 1 0 = 0 := by
  norm_num [PCSParameters.finiteError, PCSParameters.distance]
example (height m queries radius : ℕ) :
    PCSParameters.error NativeFields.goldilocksModulus 4 height m queries radius ≠ ⊤ :=
  PCSParameters.error_ne_top _ _ _ _ _ _ NativeFields.goldilocks_prime.ne_zero

end

end PCSAnalysisAlphabetSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PCSAnalysisField.dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSAnalysisField.dimension

/-- info: 'FormalProof4FHE.HasteBoots.PCSAnalysisField.cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSAnalysisField.cardinality

/-- info: 'FormalProof4FHE.HasteBoots.PCSAnalysisField.goldilocks_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSAnalysisField.goldilocks_card

/-- info: 'FormalProof4FHE.HasteBoots.PCSAnalysisField.babyBear_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSAnalysisField.babyBear_card

/-- info: 'FormalProof4FHE.HasteBoots.PCSParameters.lifted_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSParameters.lifted_distance

/-- info: 'FormalProof4FHE.HasteBoots.PCSParameters.block_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSParameters.block_distance

/-- info: 'FormalProof4FHE.HasteBoots.PCSParameters.miss_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSParameters.miss_eq

/-- info: 'FormalProof4FHE.HasteBoots.PCSParameters.error_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSParameters.error_eq

/-- info: 'FormalProof4FHE.HasteBoots.ConcreteNTTSecurity.goldilocks_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConcreteNTTSecurity.goldilocks_soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.ConcreteNTTSecurity.babyBear_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConcreteNTTSecurity.babyBear_soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.PCSParameters.finiteError_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSParameters.finiteError_coe

/-- info: 'FormalProof4FHE.HasteBoots.PCSParameters.error_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PCSParameters.error_ne_top

section CanonicalLinearSmoke

open OracleSpec OracleComp

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

/-- Repeated source indices and zero coefficients retain literal native sum
semantics; a violation only in the second lane still rejects. -/
example : PackedLinear.check [[((3 : ZMod 17), false), (-1, false), (-2, false), (0, true)]]
    (fun _ => ![1, 2]) = true := by decide
example : PackedLinear.check [[((1 : ZMod 17), false), (-1, true)]]
    (fun side => if side then ![1, 3] else ![1, 2]) = false := by decide

private def linearRelations : List (PackedLinear.Relation (ZMod 17) Bool) :=
  [[(1, false), (-1, true)], [(2, false), (-2, true)]]
private def linearSources (side : Bool) (cell : MatrixFold.Cube 1) (_lane : Fin 1) : ZMod 17 :=
  if side && cell.1 then 1 else 0

private theorem linearFalse : ¬PackedLinear.Holds linearRelations linearSources := by
  intro valid
  have equal := valid [(1, false), (-1, true)] (by simp [linearRelations])
  have entry := congrFun (congrFun equal (true, ())) 0
  norm_num [PackedLinear.residual, PackedLinear.evaluate, linearSources] at entry
  exact (by decide : (-1 : ZMod 17) ≠ 0) entry

/-- Both false relations share the one real native zero-challenge query,
which hides the nonzero second cell. Detection has a nonzero arithmetic loss. -/
example : ∀ relation ∈ linearRelations,
    (selectedBatchQuery 0).fold (PackedLinear.residual relation linearSources) = 0 := by decide

example : Pr{let query ← MatrixCompression.sample oraclePackedNodes 1}[
    ∀ relation ∈ linearRelations, query.fold (PackedLinear.residual relation linearSources) = 0] ≤ (1 / 17 : ENNReal) := by
  simpa using PackedLinear.agreement_bound oraclePackedNodes linearRelations linearSources linearFalse

private noncomputable def linearOpening : SingletonOpening.Protocol
    (ZMod 17) ColumnInput (Fin 2) Unit Unit (Fin 2) 1 0 1 2 2 1 :=
  let p := selectedBatchProtocol poolColumns
  { encoding := p.encoding, domain := p.domain, root := p.root,
    query := selectedBatchQuery 1, value := fun _ => 9,
    testResponse := p.testResponse, structuredResponse := p.groupResponse 0,
    prepare := p.prepare, respond := p.respond, receiveColumns := p.receiveColumns,
    choose := p.choose, fuel := p.fuel }

private noncomputable def linearScheme : AuthenticatedLinear.Scheme
    (ZMod 17) ColumnInput (Fin 2) Unit Unit (Fin 2) Unit 2 1 0 1 2 2 1 where
  encoding := columnEncoding
  domain := checkedDomain
  tag := fun _ => ()
  relations := [[(1, 0), (-1, 1)]]
  nodes := oraclePackedNodes
  commit := (fun _ => ((fun factor => factor), ())) <$> schemeHash (.inl [0])
  initial := fun _ => 0
  bindRelations := fun _ memory => (fun _ => 1 - memory) <$> schemeHash (.inl [0])
  receive := fun _ memory _ => (fun _ => ((fun factor _ => if factor = 0 then 0 else 1), memory)) <$> schemeHash (.inl [1])
  build := fun _ _ _ => linearOpening

private theorem linearPreflight : AuthenticatedLinear.preflight linearScheme = true := by decide
example : AuthenticatedLinear.preflight { linearScheme with relations := [] } = false := by decide
example : AuthenticatedLinear.preflight { linearScheme with relations := [[]] } = false := by decide

private def linearPacket : PackedLinearOracle.Packet (ZMod 17) (Fin 2) (Fin 2) 1 1 :=
  PackedLinearOracle.packet [[(1, 0), (-1, 1)]] (selectedBatchQuery 0, (fun _ _ => 3), 0)

/-- The factory's query/value/root fields cannot replace the checked claims. -/
example : linearPacket.accepted = true := by decide
example : (AuthenticatedLinear.single linearScheme ((fun factor => factor), ()) linearPacket 1).value 0 = 3 := rfl
example : (AuthenticatedLinear.single linearScheme ((fun factor => factor), ()) linearPacket 1).query = selectedBatchQuery 0 := rfl
example : (AuthenticatedLinear.single linearScheme ((fun factor => factor), ()) linearPacket 1).root = 1 := rfl

/-- A false supplied linear identity retains commitment, relation-binding and
receive hashes, then skips every root's prelude, test, column draw and workers. -/
example : (fun outcome => (AuthenticatedLinear.accepted outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (AuthenticatedLinear.program linearScheme)).run columnStart =
      (fun _ : Fin 1 → ZMod 17 => (false, 6)) <$> ($ᵗ (Fin 1 → ZMod 17)) := by
  simp only [AuthenticatedLinear.program, MultiCommitmentPrefix.program, AuthenticatedLinear.continuation,
    CommittedBatchOpening.continuation, AuthenticatedLinear.select, PackedLinearOracle.program,
    linearPreflight, reduceIte]
  simp only [linearScheme, SharedContinuation.program, MatrixCompression.sample, PrivateSampling.run_probComp,
    simulateQ_bind, StateT.run_bind, bind_map_left, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, bind_assoc, pure_bind]
  conv_rhs => rw [map_eq_pure_bind]
  rfl

/-- Invalid trusted relations reject before binding or sampling; only the
already issued commitment hash remains. -/
example : (fun outcome => (AuthenticatedLinear.accepted outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (AuthenticatedLinear.program { linearScheme with relations := [] })).run columnStart = pure (false, 4) := by rfl

end CanonicalLinearSmoke

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.groupCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.groupCount

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.coordinates

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.worker

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.pool

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.next_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.next_eq

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.checks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.checks_eq

/-- info: 'FormalProof4FHE.HasteBoots.SingletonOpening.step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SingletonOpening.step_eq

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.foldl_evaluate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.foldl_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.fold_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.fold_zero

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.fold_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.fold_add

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.fold_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.fold_residual

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.truthful_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.truthful_agreement

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.agreement_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.agreement_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinearOracle.truthful_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinearOracle.truthful_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.factors_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.factors_complete

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.continuation_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.continuation_single

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.opening_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.opening_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.AuthenticatedLinear.native_soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AuthenticatedLinear.native_soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.ConcreteLinearSecurity.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConcreteLinearSecurity.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.PackedLinear.honest_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedLinear.honest_check

section DecompositionLinearSmoke

/-- Input, two digits, and three borrows occupy the exact native slots. -/
example : DecompositionLinear.relations (d := 2) (4 : ZMod 17) =
    [[(-1, 0), (1, 1), (4, 2)], [(1, 3)], [(1, 5)]] := by decide

private def decompositionValues : Fin 6 → Fin 1 → ZMod 17 := fun factor _ => ![9, 1, 2, 0, 3, 0] factor

example : PackedLinear.check (DecompositionLinear.relations (d := 2) (4 : ZMod 17))
    decompositionValues = true := by decide

example : PackedLinear.check (DecompositionLinear.relations (d := 2) (4 : ZMod 17))
    (Function.update decompositionValues 3 (fun _ => 1)) = false := by decide
example : PackedLinear.check (DecompositionLinear.relations (d := 2) (4 : ZMod 17))
    (Function.update decompositionValues 5 (fun _ => 1)) = false := by decide
example : PackedLinear.check (DecompositionLinear.relations (d := 2) (4 : ZMod 17))
    (Function.update decompositionValues 2 (fun _ => 3)) = false := by decide

/-- Field reconstruction alone accepts 17=0 mod 17 and an out-of-range
digit; the separate lookup constraints are essential for canonicity. -/
example : PackedLinear.check (DecompositionLinear.relations (d := 2) (4 : ZMod 17))
    (fun factor (_ : Fin 1) => ![0, 1, 4, 0, 0, 0] factor) = true := by decide

private theorem decompositionValid : DecompositionLinear.Relation (d := 2) (4 : ZMod 17)
    (fun factor (_cell : MatrixFold.Cube 1) => decompositionValues factor) := by
  unfold DecompositionLinear.Relation
  decide

example : PackedLinear.check (DecompositionLinear.relations (d := 2) (4 : ZMod 17))
    (fun factor => (selectedBatchQuery 0).fold (fun _ => decompositionValues factor)) = true :=
  DecompositionLinear.honest_check _ _ decompositionValid _

/-- The empty digit boundary still has two borrow/input roles and the two
endpoint relations coincide; no positive digit count is silently assumed. -/
example : DecompositionLinear.relations (d := 0) (4 : ZMod 17) =
    [[(-1, 0)], [(1, 1)], [(1, 1)]] := by decide
example : PackedLinear.check (DecompositionLinear.relations (d := 0) (4 : ZMod 17))
    (fun (_ : Fin 2) (_ : Fin 1) => 0) = true := by decide

end DecompositionLinearSmoke

/-- info: 'FormalProof4FHE.HasteBoots.DecompositionLinear.registry_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecompositionLinear.registry_complete

/-- info: 'FormalProof4FHE.HasteBoots.DecompositionLinear.reconstruction_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecompositionLinear.reconstruction_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.DecompositionLinear.holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecompositionLinear.holds_iff

/-- info: 'FormalProof4FHE.HasteBoots.DecompositionLinear.honest_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecompositionLinear.honest_check

/-- info: 'FormalProof4FHE.HasteBoots.DecompositionLinear.preflight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecompositionLinear.preflight

/-- info: 'FormalProof4FHE.HasteBoots.DecompositionLinear.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecompositionLinear.soundness_from_empty

section RadixCanonicitySmoke

example : RadixCanonicity.digitCount 17 4 = 3 := by decide
example : List.ofFn (fun i : Fin 3 => RadixCanonicity.modulusDigit 17 4 i.val) = [0, 0, 1] := by decide
example : RadixCanonicity.table 17 4 0 =
    [![0, 0, 0], ![0, 1, 1], ![1, 0, 1], ![1, 1, 1],
     ![2, 0, 1], ![2, 1, 1], ![3, 0, 1], ![3, 1, 1]] := by decide

private def radixTables (factor : Fin 8) (_cell : MatrixFold.Cube 1) (_lane : Fin 1) : ZMod 17 :=
  ![9, 1, 2, 0, 0, 1, 1, 0] factor

private theorem radixLinear : DecompositionLinear.Relation (d := 3) (n := 1) (b := 1) (4 : ZMod 17) radixTables := by
  unfold DecompositionLinear.Relation
  decide

private theorem radixLookup : RadixCanonicity.LookupAt 17 4 (d := 3) (n := 1) (b := 1) radixTables (true, ()) 0 := by
  unfold RadixCanonicity.LookupAt
  decide

example : RadixCanonicity.CanonicalAt 17 4 (d := 3) (n := 1) (b := 1) radixTables (true, ()) 0 :=
  RadixCanonicity.canonical_of_constraints (p := 17) (radix := 4) (d := 3) (n := 1) (b := 1) (by decide) (by decide) (by decide)
    radixTables radixLinear _ _ radixLookup

example (i : Fin 3) : (radixTables (DecompositionLinear.digit i) (true, ()) 0).val =
    9 / 4 ^ i.val % 4 :=
  RadixCanonicity.digits_of_constraints (p := 17) (radix := 4) (d := 3) (n := 1) (b := 1) (by decide) (by decide) (by decide)
    radixTables radixLinear _ _ radixLookup i

/-- Bounded digits can still reconstruct 17 instead of 0. Forcing zero
borrow endpoints preserves the field relation but breaks the last lookup. -/
private def wrappedTables (factor : Fin 8) (_cell : MatrixFold.Cube 1) (_lane : Fin 1) : ZMod 17 :=
  ![0, 1, 0, 1, 0, 1, 1, 0] factor

private theorem wrappedLinear : DecompositionLinear.Relation (d := 3) (n := 1) (b := 1) (4 : ZMod 17) wrappedTables := by
  unfold DecompositionLinear.Relation
  decide

private theorem wrappedNoncanonical : ¬RadixCanonicity.CanonicalAt 17 4 (d := 3) (n := 1) (b := 1) wrappedTables (true, ()) 0 := by
  unfold RadixCanonicity.CanonicalAt
  decide

example : ∃ i : Fin 3,
    ![wrappedTables (DecompositionLinear.digit i) (true, ()) 0,
      wrappedTables (DecompositionLinear.borrow i.castSucc) (true, ()) 0,
      wrappedTables (DecompositionLinear.borrow i.succ) (true, ()) 0] ∉
        RadixCanonicity.table 17 4 (RadixCanonicity.modulusDigit 17 4 i.val) := by
  rcases RadixCanonicity.failure_dichotomy (p := 17) (radix := 4) (d := 3) (n := 1) (b := 1) (by decide) (by decide) (by decide)
    wrappedTables (true, ()) 0 wrappedNoncanonical with wrong | missing
  · exact (wrong wrappedLinear).elim
  · exact missing

example : ![(1 : ZMod 17), 1, 0] ∉ RadixCanonicity.table 17 4 1 := by decide

/-- Keeping the true overflowing borrow satisfies every lookup; the linear
endpoint constraint rejects this version of the same noncanonical value. -/
private def overflowingTables (factor : Fin 8) (_cell : MatrixFold.Cube 1) (_lane : Fin 1) : ZMod 17 :=
  ![0, 1, 0, 1, 0, 1, 1, 1] factor

example : RadixCanonicity.LookupAt 17 4 (d := 3) (n := 1) (b := 1) overflowingTables (true, ()) 0 := by
  unfold RadixCanonicity.LookupAt
  decide
example : ¬DecompositionLinear.Relation (d := 3) (n := 1) (b := 1) (4 : ZMod 17) overflowingTables := by
  unfold DecompositionLinear.Relation
  decide

example : ![(4 : ZMod 17), 0, 1] ∉ RadixCanonicity.table 17 4 0 := by decide

/-- If radix exceeds p, table casts alias and no longer imply the natural
transition rule. The strict radix<p premise cannot be removed. -/
example : ![(0 : ZMod 3), 0, 1] ∈ RadixCanonicity.table 3 4 2 := by decide
example : (1 : ℕ) ≠ (if 2 < (0 : ℕ) + 0 then 1 else 0) := by decide

example : RadixCanonicity.value 0 (fun _ : Fin 3 => 7) = 7 := by decide
example : RadixCanonicity.value 1 (fun _ : Fin 3 => 7) = 21 := by decide

end RadixCanonicitySmoke

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.value_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.value_succ

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.value_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.value_last

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.value_eq_ofDigits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.value_eq_ofDigits

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.digits_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.digits_unique

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.value_lt_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.value_lt_pow

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.weighted_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.weighted_bound

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.value_mod_digits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.value_mod_digits

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.digits_eq_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.digits_eq_mod

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.modulus_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.modulus_value

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.digitCount_enough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.digitCount_enough

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.transition_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.transition_bound

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.mem_table_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.mem_table_iff

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.table_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.table_values

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.integer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.integer_bound

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.canonical_of_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.canonical_of_constraints

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.canonical_of_digitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.canonical_of_digitCount

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.digits_of_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.digits_of_constraints

/-- info: 'FormalProof4FHE.HasteBoots.RadixCanonicity.failure_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixCanonicity.failure_dichotomy

section RadixWitnessSmoke

example : List.ofFn (RadixWitness.borrows 17 4 3 9) = [0, 1, 1, 0] := by decide
example : List.ofFn (RadixWitness.borrows 17 4 3 16) = [0, 0, 0, 0] := by decide
example : RadixWitness.borrows 17 4 3 17 (Fin.last 3) = 1 := by decide

/-- The incoming bit matters at the exact public upper bound. -/
example : RadixWitness.sequence ![0, 0, 1] ![0, 0, 1] 1 (Fin.last 3) ≠ 0 := by
  intro zero
  have wrong := (RadixWitness.last_zero_iff (radix := 4) (d := 3) ![0, 0, 1] ![0, 0, 1]
    (by decide) (by decide) 1 (by decide)).mp zero
  exact (by decide : ¬ (RadixCanonicity.value 4 ![0, 0, 1] + 1 ≤ RadixCanonicity.value 4 ![0, 0, 1])) wrong

example : RadixWitness.sequence (fun _ : Fin 0 => 0) (fun _ => 0) 1 0 = 1 := rfl

private def witnessSource (cell : MatrixFold.Cube 1) (lane : Fin 2) : ZMod 17 :=
  if cell.1 then (if lane = 0 then 9 else 16) else 0

/-- Literal registry order includes the input, three digits, four borrows. -/
example : List.ofFn (fun factor : Fin 8 => RadixWitness.tables 17 4 3 witnessSource factor (true, ()) 0) =
    [9, 1, 2, 0, 0, 1, 1, 0] := by decide
example : List.ofFn (fun factor : Fin 8 => RadixWitness.tables 17 4 3 witnessSource factor (true, ()) 1) =
    [16, 0, 0, 1, 0, 0, 0, 0] := by decide

example (factor : Fin 8) (lane : Fin 2) :
    RadixWitness.tables 17 4 3 witnessSource factor (false, ()) lane = 0 :=
  RadixWitness.tables_zero (p := 17) (radix := 4) (d := 3)
    witnessSource (false, ()) lane (by simp [witnessSource]) factor

example : DecompositionLinear.Relation (d := 3) (b := 2) (n := 1) (4 : ZMod 17)
    (RadixWitness.tables 17 4 3 witnessSource) :=
  RadixWitness.tables_valid (by decide) (by decide) witnessSource

example (cell : MatrixFold.Cube 1) (lane : Fin 2) :
    RadixCanonicity.LookupAt 17 4 (d := 3) (b := 2) (n := 1)
      (RadixWitness.tables 17 4 3 witnessSource) cell lane :=
  RadixWitness.tables_lookup (by decide) witnessSource cell lane

example : PackedLinear.check (DecompositionLinear.relations (d := 3) (4 : ZMod 17))
    (fun factor => (selectedBatchQuery 1).fold
      (RadixWitness.tables 17 4 3 (fun cell (_ : Fin 1) => witnessSource cell 0) factor)) = true :=
  RadixWitness.honest_check (p := 17) (radix := 4) (d := 3) (b := 1) (n := 1)
    (by decide) (by decide) _ _

example : ∃ witness : Fin (2 * RadixCanonicity.digitCount 17 4 + 2) → MatrixFold.Cube 1 → Fin 2 → ZMod 17,
    (∀ cell lane, witness DecompositionLinear.input cell lane = witnessSource cell lane) ∧
    DecompositionLinear.Relation (4 : ZMod 17) witness ∧
    ∀ cell lane, RadixCanonicity.LookupAt 17 4 witness cell lane :=
  RadixWitness.exists_witness_digitCount (p := 17) (radix := 4) (b := 2) (n := 1) (by decide) witnessSource

end RadixWitnessSmoke

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.next_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.next_bit

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.sequence_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.sequence_zero

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.sequence_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.sequence_succ

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.sequence_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.sequence_bit

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.sequence_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.sequence_step

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.comparison_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.comparison_step

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.last_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.last_zero_iff

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.sequence_zero_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.sequence_zero_digits

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.sequence_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.sequence_table

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.digits_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.digits_small

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.digits_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.digits_value

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.borrows_first' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.borrows_first

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.borrows_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.borrows_bit

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.borrows_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.borrows_last

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.borrows_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.borrows_zero

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.columns_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.columns_input

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.columns_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.columns_digit

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.columns_borrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.columns_borrow

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.columns_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.columns_zero

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.tables_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.tables_zero

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.tables_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.tables_input

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.tables_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.tables_valid

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.tables_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.tables_lookup

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.honest_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.honest_check

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.exists_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.exists_witness

/-- info: 'FormalProof4FHE.HasteBoots.RadixWitness.exists_witness_digitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixWitness.exists_witness_digitCount

section TupleHashSmoke

open OracleSpec OracleComp
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def hashBadRow : Fin 3 → ZMod 17 := ![0, -1, 1]
private def hashZeroRow : Fin 3 → ZMod 17 := fun _ => 0

example : TupleHash.powers (3 : ZMod 17) 1 4 = [1, 3, 9, 10] := by decide
example : TupleHash.powers (3 : ZMod 17) 5 4 = [5, 15, 11, 16] := by decide

/-- One shared scalar gives the exact two-root probability 2/17. Coordinates
are not independent repetitions that would give a squared error. -/
example : Pr{let y ← $ᵗ (ZMod 17)}[TupleHash.hash y hashBadRow = TupleHash.hash y hashZeroRow] =
    (2 / 17 : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun y : ZMod 17 =>
      TupleHash.hash y hashBadRow = TupleHash.hash y hashZeroRow)).card = 2 := by decide
  rw [count, ZMod.card]
  norm_num

example : Pr{let y ← $ᵗ (ZMod 17)}[∀ _ : Bool, ∃ entry ∈ [hashZeroRow],
    TupleHash.hash y hashBadRow = TupleHash.hash y entry] ≤ (2 / 17 : ENNReal) := by
  simpa only [List.length_singleton, Nat.reduceSub, Nat.cast_one, one_mul, Nat.cast_ofNat, ZMod.card] using
    TupleHash.list_family_miss_bound (K := ZMod 17) (fun _ : Bool => hashBadRow)
      [hashZeroRow] ⟨false, by decide⟩

/-- The denominator is the hash field's full cardinality. This abstract
degree-two field illustrates the generic extension theorem, not a claim of
native Goldilocks/BabyBear lookup-field implementation refinement. -/
example : Pr{let y ← $ᵗ (PCSAnalysisField.Alphabet 17 2)}[
    TupleHash.hash y hashBadRow = TupleHash.hash y hashZeroRow] ≤ (2 / 289 : ENNReal) := by
  simpa only [PCSAnalysisField.cardinality, Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat] using
    TupleHash.collision_bound (K := PCSAnalysisField.Alphabet 17 2) hashBadRow hashZeroRow (by decide)

/-- Choosing the tuple after seeing y defeats the fixed-source bound. -/
example (y : ZMod 17) : (![-y, 1] : Fin 2 → ZMod 17) ≠ (fun _ => 0) ∧
    TupleHash.hash y ![-y, 1] = TupleHash.hash y (fun _ : Fin 2 => (0 : ZMod 17)) := by
  constructor
  · intro equal
    have entry := congrFun equal 1
    norm_num at entry
  · simp [TupleHash.hash_eq_sum, Fin.sum_univ_two]

example : TupleHash.hash (7 : ZMod 17) (fun _ : Fin 0 => (3 : ZMod 17)) = 0 := by decide
example (y : ZMod 17) : TupleHash.hash y ![(1 : ZMod 17)] ≠ TupleHash.hash y ![(0 : ZMod 17)] := by
  simp [TupleHash.hash_eq_sum]

example : (RadixCanonicity.table 17 4 0).Nodup := RadixTupleHash.table_nodup 0 (by decide)
example : (RadixCanonicity.table 17 4 0).length = 8 := RadixTupleHash.table_length _ _ _
example : ¬(RadixCanonicity.table 3 4 0).Nodup := by decide

example : Pr{let y ← $ᵗ (ZMod 17)}[∃ entry ∈ RadixCanonicity.table 17 4 0,
    TupleHash.hash y ![(4 : ZMod 17), 0, 1] = TupleHash.hash y entry] ≤
      (8 : ENNReal) * (2 / 17) := by
  simpa only [ZMod.card, Nat.reduceMul, Nat.cast_ofNat] using
    RadixTupleHash.collision_bound (p := 17) (radix := 4) (K := ZMod 17)
      0 ![4, 0, 1] (by decide)

/-- Both preparation and a rejecting continuation keep their actual shared
hash calls around the one private scalar sample. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (TupleHashOracle.program (schemeHash (.inl [0]))
        (fun _ (_ : ZMod 17) => (fun _ => false) <$> schemeHash (.inl [1])))).run columnStart =
      (fun _ : ZMod 17 => (false, 5)) <$> ($ᵗ (ZMod 17)) := by
  simp only [TupleHashOracle.program, SharedContinuation.program, simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, simulateQ_pure, StateT.run_pure,
    schemeHash_run (.inl [0]) columnStart 0 rfl,
    schemeHash_run (.inl [1]) (zeroColumnStep columnStart (.inl [0]) 0) 1 rfl,
    map_bind, map_pure, bind_map_left, pure_bind]
  conv_rhs => rw [map_eq_pure_bind]
  rfl

example : Pr{let outcome ←
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (TupleHashOracle.program (schemeHash (.inl [0]))
        (fun _ (_ : ZMod 17) => (fun _ => false) <$> schemeHash (.inl [1])))).run columnStart}[
      ∀ _ : Bool, ∃ entry ∈ [hashZeroRow],
        TupleHash.hash outcome.1.1 hashBadRow = TupleHash.hash outcome.1.1 entry] ≤ (2 / 17 : ENNReal) := by
  simpa only [List.length_singleton, Nat.reduceSub, Nat.cast_one, one_mul, Nat.cast_ofNat, ZMod.card] using
    TupleHashOracle.prepared_miss_bound columnEncoding 0 workerShape
      (fun _ : Bool => hashBadRow) [hashZeroRow] ⟨false, by decide⟩
      (schemeHash (.inl [0])) (fun _ (_ : ZMod 17) => (fun _ => false) <$> schemeHash (.inl [1])) columnStart

end TupleHashSmoke

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.powers_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.powers_eq

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.hash_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.hash_eq_sum

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.hash_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.hash_add

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.hash_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.hash_smul

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.polynomial_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.polynomial_injective

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.polynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.polynomial_degree

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.polynomial_eval

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.collision_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.collision_card

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.collision_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.collision_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.table_collision_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.table_collision_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.family_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.family_miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.list_collision_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.list_collision_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleHash.list_family_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHash.list_family_miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.RadixTupleHash.table_as_product' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixTupleHash.table_as_product

/-- info: 'FormalProof4FHE.HasteBoots.RadixTupleHash.table_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixTupleHash.table_length

/-- info: 'FormalProof4FHE.HasteBoots.RadixTupleHash.row_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixTupleHash.row_injective

/-- info: 'FormalProof4FHE.HasteBoots.RadixTupleHash.table_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixTupleHash.table_nodup

/-- info: 'FormalProof4FHE.HasteBoots.RadixTupleHash.collision_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixTupleHash.collision_bound

/-- info: 'FormalProof4FHE.HasteBoots.RadixTupleHash.family_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RadixTupleHash.family_miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleHashOracle.retained_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHashOracle.retained_miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleHashOracle.prepared_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleHashOracle.prepared_miss_bound

section ReciprocalDetectionSmoke

open OracleSpec OracleComp
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def reciprocalSources : Fin 2 → ZMod 17 := fun _ => 0
private def reciprocalTable : Fin 1 → ZMod 17 := fun _ => 1
private def reciprocalMultiplicities : Fin 1 → ZMod 17 := fun _ => 1

private theorem reciprocalInv16 : ((15 : ZMod 17) + 1)⁻¹ = 16 :=
  (ReciprocalPolynomial.reciprocal_forced 15 1 16 (by decide)).2.symm
private theorem reciprocalInv2 : ((2 : ZMod 17) + 0)⁻¹ = 9 :=
  (ReciprocalPolynomial.reciprocal_forced 2 0 9 (by decide)).2.symm
private theorem reciprocalInv3 : ((2 : ZMod 17) + 1)⁻¹ = 6 :=
  (ReciprocalPolynomial.reciprocal_forced 2 1 6 (by decide)).2.symm

private theorem reciprocalMissing : ∃ i, ∀ j, reciprocalSources i ≠ reciprocalTable j :=
  ⟨0, by intro j; change (0 : ZMod 17) ≠ 1; decide⟩

example : ReciprocalPolynomial.numerator reciprocalSources reciprocalTable reciprocalMultiplicities ≠ 0 :=
  ReciprocalPolynomial.numerator_ne_zero (p := 17) _ _ _ reciprocalMissing (by decide)

example : (ReciprocalPolynomial.numerator reciprocalSources reciprocalTable reciprocalMultiplicities).natDegree ≤ 2 :=
  ReciprocalPolynomial.numerator_degree _ _ _ (by decide)

/-- A genuine false-pass point remains in the allowed domain; the arithmetic
error is nonzero even though the numerator is proved nonzero. -/
example : ReciprocalDetection.Passes reciprocalSources reciprocalTable reciprocalMultiplicities 15 := by
  refine ⟨fun _ => 8, ?_, ?_⟩
  · intro i
    change (8 : ZMod 17) * (15 + 0) = 1
    decide
  · simp only [Fin.sum_univ_two, Fin.sum_univ_one, reciprocalMultiplicities, reciprocalTable]
    rw [reciprocalInv16]
    decide

example : ¬ReciprocalDetection.Passes reciprocalSources reciprocalTable reciprocalMultiplicities 2 := by
  intro valid
  have equal := ((ReciprocalDetection.passes_iff _ _ _ _).mp valid).2
  exact (by
    simp only [Fin.sum_univ_two, Fin.sum_univ_one, reciprocalSources, reciprocalMultiplicities, reciprocalTable]
    simp only [reciprocalInv2, reciprocalInv3]
    decide : (∑ i, ((2 : ZMod 17) + reciprocalSources i)⁻¹) ≠
    ∑ i, reciprocalMultiplicities i * (2 + reciprocalTable i)⁻¹) equal

example : (15 : ZMod 17) ∈ ReciprocalDetection.allowed reciprocalTable := by decide
example : (0 : ZMod 17) ∉ ReciprocalDetection.allowed reciprocalTable := by decide
example : (16 : ZMod 17) ∉ ReciprocalDetection.allowed reciprocalTable := by decide
example : (ReciprocalDetection.allowed reciprocalTable).card = 15 := by decide

example : Pr{let r ← ReciprocalDetection.sample reciprocalTable}[r = (15 : ZMod 17)] = (1 / 15 : ENNReal) := by
  rw [ReciprocalDetection.sample, ProbComp.prEvent_uniformSelectFinset]
  have good : ((ReciprocalDetection.allowed reciprocalTable).filter (fun r => r = (15 : ZMod 17))).card = 1 := by decide
  have total : (ReciprocalDetection.allowed reciprocalTable).card = 15 := by decide
  rw [good, total]
  norm_num

example : Pr{let r ← ReciprocalDetection.sample reciprocalTable}[
    ReciprocalDetection.Passes reciprocalSources reciprocalTable reciprocalMultiplicities r] ≤ (2 / 15 : ENNReal) := by
  simpa only [ZMod.card, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat] using
    ReciprocalDetection.detection_bound (p := 17) reciprocalSources reciprocalTable reciprocalMultiplicities reciprocalMissing (by decide)

example : Pr{let _ ← ReciprocalDetection.sample reciprocalTable}[True] = 1 :=
  ReciprocalDetection.sample_total reciprocalTable (by norm_num [ZMod.card])

/-- Repeated public hashes exclude the pole once, and zero may coincide with
a public pole. The lower bound must remain valid in both cases. -/
example : (ReciprocalDetection.allowed (fun _ : Fin 3 => (1 : ZMod 17))).card = 15 := by decide
example : (ReciprocalDetection.allowed (fun _ : Fin 1 => (0 : ZMod 17))).card = 16 := by decide
example : (ReciprocalDetection.allowed (![(1 : ZMod 3), 2])).card = 0 := by decide

/-- At count=characteristic, repeated missing source rows cancel: the strict
active-count characteristic condition cannot be replaced by mere finiteness. -/
example : ReciprocalPolynomial.numerator (fun _ : Fin 3 => (0 : ZMod 3))
    (fun _ : Fin 1 => 1) (fun _ => 0) = 0 := by
  norm_num [ReciprocalPolynomial.numerator, ReciprocalPolynomial.denominator,
    ReciprocalPolynomial.factor, ReciprocalPolynomial.tableNumerator]
  exact Or.inl (CharP.cast_eq_zero _ 3)

example (r : ZMod 3) (nonzero : r ≠ 0) :
    ReciprocalDetection.Passes (fun _ : Fin 3 => (0 : ZMod 3))
      (fun _ : Fin 1 => 1) (fun _ => 0) r := by
  refine ⟨fun _ => r⁻¹, ?_, ?_⟩
  · intro i
    simpa only [add_zero] using inv_mul_cancel₀ nonzero
  · simp
    exact Or.inl (CharP.cast_eq_zero _ 3)

/-- The exact masked identity forces zero padding even when r+g=0 there. -/
example : ReciprocalMask.residual (2 : ZMod 17) (-2) 1 false ≠ 0 := by decide
example : (1 : ZMod 17) * (2 + -2) = 0 := by decide
example : ReciprocalMask.residual (0 : ZMod 17) 7 1 false = 0 := by decide
example (helper : ZMod 17) : ReciprocalMask.residual 2 (-2) helper true ≠ 0 := by
  intro valid
  exact (ReciprocalMask.active_forced _ _ _ valid).1 (by decide)

example : (∑ i : Fin 4, (![8, 8, 0, 0] : Fin 4 → ZMod 17) i) =
    ∑ i : Fin 2, ((15 : ZMod 17) + (![0, 0, 2, 7] : Fin 4 → ZMod 17) (i.castAdd 2))⁻¹ :=
  ReciprocalMask.prefix_sum (count := 2) (padding := 2) 15 ![0, 0, 2, 7] ![8, 8, 0, 0]
    (by decide) (by intro i; fin_cases i <;> decide)

example : (ReciprocalPolynomial.numerator
    (fun i : Fin 2 => (![0, 0, 2, 7] : Fin 4 → ZMod 17) (i.castAdd 2))
    reciprocalTable reciprocalMultiplicities).eval 15 = 0 :=
  ReciprocalMask.prefix_identity_implies_root (count := 2) (padding := 2) 15 ![0, 0, 2, 7] ![8, 8, 0, 0]
    reciprocalTable reciprocalMultiplicities (by decide)
    (by intro i; fin_cases i <;> decide)
    (by intro i; change (15 : ZMod 17) + 1 ≠ 0; decide)
    (by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, reciprocalMultiplicities, reciprocalTable]
      rw [reciprocalInv16]
      decide)

end ReciprocalDetectionSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_monic

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_ne_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_degree

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.cofactor_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.cofactor_degree

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_split

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.factor_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.factor_eval

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_eval

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.cofactor_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.cofactor_eval

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.derivative_denominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.derivative_denominator

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.derivative_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.derivative_eval

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.tableNumerator_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.tableNumerator_eval

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.identity_implies_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.identity_implies_root

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.reciprocal_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.reciprocal_forced

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.helper_identity_implies_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.helper_identity_implies_root

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.tableNumerator_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.tableNumerator_degree

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.numerator_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.numerator_degree

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_eval_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_eval_ne_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.denominator_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.denominator_root

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.multiplicity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.multiplicity_bound

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.natCast_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.natCast_ne_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.derivative_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.derivative_ne_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalPolynomial.numerator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalPolynomial.numerator_ne_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalMask.active_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalMask.active_forced

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalMask.inactive_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalMask.inactive_forced

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalMask.honest_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalMask.honest_active

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalMask.honest_inactive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalMask.honest_inactive

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalMask.prefix_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalMask.prefix_sum

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalMask.prefix_identity_implies_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalMask.prefix_identity_implies_root

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.mem_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.mem_allowed

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.allowed_card_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.allowed_card_lower

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.allowed_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.allowed_nonempty

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.sample_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.sample_total

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.passes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.passes_iff

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.passing_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.passing_card

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalDetection.detection_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalDetection.detection_bound

section TupleLookupPairSmoke

open OracleSpec OracleComp
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def pairSources : Fin 2 → Fin 1 → ZMod 17 := fun _ _ => 0
private def pairTable : Fin 1 → Fin 1 → ZMod 17 := fun _ _ => 1
private def pairMultiplicities : Fin 1 → ZMod 17 := fun _ => 1

private theorem pairMissing : ∃ i, ∀ j, pairSources i ≠ pairTable j := by
  refine ⟨0, ?_⟩
  intro j equal
  have wrong := congrFun equal 0
  exact (by decide : (0 : ZMod 17) ≠ 1) wrong

private theorem pairError : TupleLookupPair.error 17 1 2 1 = (2 / 15 : ENNReal) := by
  norm_num [TupleLookupPair.error]

/-- Width one has no hash-collision term, but retains reciprocal detection. -/
example : Pr{let pair ← TupleLookupPair.sample (K := ZMod 17) pairTable}[
    TupleLookupPair.Passes pairSources pairTable pairMultiplicities pair] ≤ (2 / 15 : ENNReal) := by
  simpa only [ZMod.card, pairError] using
    TupleLookupPair.single_bound (p := 17) pairSources pairTable pairMultiplicities pairMissing (by decide)

example : Pr{let pairs ← TupleLookupPair.repeats (K := ZMod 17) pairTable 2}[
    TupleLookupPair.AllPass pairSources pairTable pairMultiplicities pairs] ≤ (2 / 15 : ENNReal) ^ 2 := by
  simpa only [ZMod.card, pairError] using
    TupleLookupPair.repeated_bound (p := 17) pairSources pairTable pairMultiplicities pairMissing (by decide) 2

/-- The exact fresh-pair law is a square; reuse of one pair retains only the
single-pair probability. These are distinct sampling programs. -/
example : Pr{let pairs ← TupleLookupPair.repeats (K := ZMod 17) pairTable 2}[
    TupleLookupPair.AllPass pairSources pairTable pairMultiplicities pairs] =
    Pr{let pair ← TupleLookupPair.sample (K := ZMod 17) pairTable}[
      TupleLookupPair.Passes pairSources pairTable pairMultiplicities pair] ^ 2 :=
  TupleLookupPair.repeated_probability pairSources pairTable pairMultiplicities 2

example : Pr{let pair ← TupleLookupPair.sample (K := ZMod 17) pairTable}[
    TupleLookupPair.AllPass pairSources pairTable pairMultiplicities [pair, pair]] =
    Pr{let pair ← TupleLookupPair.sample (K := ZMod 17) pairTable}[
      TupleLookupPair.Passes pairSources pairTable pairMultiplicities pair] := by
  simp [TupleLookupPair.AllPass]

/-- Zero repetitions give no soundness: the empty conjunction passes surely. -/
example : Pr{let pairs ← TupleLookupPair.repeats (K := ZMod 17) pairTable 0}[
    TupleLookupPair.AllPass pairSources pairTable pairMultiplicities pairs] = 1 := by
  simp [TupleLookupPair.repeats, TupleLookupPair.AllPass, prEvent_norm]

example : Pr{let _ ← TupleLookupPair.sample (K := ZMod 17) pairTable}[True] = 1 :=
  TupleLookupPair.sample_total pairTable (by norm_num [ZMod.card])
example : Pr{let _ ← TupleLookupPair.repeats (K := ZMod 17) pairTable 2}[True] = 1 :=
  TupleLookupPair.repeats_total pairTable (by norm_num [ZMod.card]) 2

/-- Both loss terms remain for width three, and the accepted-domain loss
cannot be replaced by division by the whole field cardinality. -/
example : TupleLookupPair.error 17 3 2 1 = (2 / 17 : ENNReal) + 2 / 15 := by
  norm_num [TupleLookupPair.error]
example : TupleLookupPair.error 17 1 2 1 ≠ (2 / 17 : ENNReal) := by
  rw [pairError]
  intro equal
  have original := congrArg ENNReal.toNNReal equal
  norm_num [ENNReal.toNNReal_div, ENNReal.toNNReal_ofNat] at original

/-- Ideal pair sampling leaves the cached hash state unchanged; preparation
and the rejecting continuation retain their two actual issued hash calls. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (TupleLookupPairOracle.program pairTable 2 (schemeHash (.inl [0]))
        (fun _ (_ : Option (List (ZMod 17 × ZMod 17))) => (fun _ => false) <$> schemeHash (.inl [1])))).run columnStart =
      (fun _ : Option (List (ZMod 17 × ZMod 17)) => (false, 5)) <$>
        (TupleLookupPair.repeats (K := ZMod 17) pairTable 2).run := by
  simp only [TupleLookupPairOracle.program, SharedContinuation.program, simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, simulateQ_pure, StateT.run_pure,
    schemeHash_run (.inl [0]) columnStart 0 rfl,
    schemeHash_run (.inl [1]) (zeroColumnStep columnStart (.inl [0]) 0) 1 rfl,
    map_bind, map_pure, bind_map_left, pure_bind]
  conv_rhs => rw [map_eq_pure_bind]
  rfl

example : Pr{let outcome ←
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (TupleLookupPairOracle.program pairTable 2 (schemeHash (.inl [0]))
        (fun _ (_ : Option (List (ZMod 17 × ZMod 17))) => (fun _ => false) <$> schemeHash (.inl [1])))).run columnStart}[
      outcome.1.1.elim False (TupleLookupPair.AllPass pairSources pairTable pairMultiplicities)] ≤ (2 / 15 : ENNReal) ^ 2 := by
  simpa only [ZMod.card, pairError] using
    TupleLookupPairOracle.prepared_bound columnEncoding 0 workerShape pairSources pairTable pairMultiplicities
      pairMissing (by decide) 2 (schemeHash (.inl [0]))
      (fun _ (_ : Option (List (ZMod 17 × ZMod 17))) => (fun _ => false) <$> schemeHash (.inl [1])) columnStart

/-- Support attachment erases to the exact old oracle program, including
its private draws, rather than merely assuming an equal event probability. -/
example : (fun pair => some (LookupPairVector.forget pair)) <$>
    LookupPairVector.sample (K := ZMod 17) pairTable (by norm_num [ZMod.card]) =
      (TupleLookupPair.sample (K := ZMod 17) pairTable).run :=
  LookupPairVector.sample_forget _ _

example : Pr{let pairs ← LookupPairVector.vector (K := ZMod 17) pairTable (by norm_num [ZMod.card]) 2}[
    LookupPairVector.AllPass pairSources pairTable pairMultiplicities pairs] ≤ (2 / 15 : ENNReal) ^ 2 := by
  simpa only [ZMod.card, pairError] using LookupPairVector.vector_bound (p := 17)
    pairSources pairTable pairMultiplicities (by norm_num [ZMod.card]) pairMissing (by decide) 2

example : Pr{let pairs ← LookupPairVector.vector (K := ZMod 17) pairTable (by norm_num [ZMod.card]) 0}[
    LookupPairVector.AllPass pairSources pairTable pairMultiplicities pairs] = 1 := by
  simp [LookupPairVector.vector, LookupPairVector.AllPass, prEvent_norm]

private def forgedPairs : Fin 2 → StagedRepeatedLookup.Pair (ZMod 17) := fun _ => (0, ⟨1, by decide⟩)

private noncomputable def pairHelper (_actual : Fin 2 → StagedRepeatedLookup.Pair (ZMod 17)) :=
  (fun _ : Fin 2 => ((fun _ : Fin 2 => (0 : Fin 2)), (forgedPairs, false))) <$> schemeHash (.inl [1])

/-- A helper builder puts a forged vector and a rejecting flag in its opaque
memory and makes a hash call. The wrapper still retains the original fresh
vector, the entire returned memory and the additional issued hash call. -/
example : (fun outcome => (LookupPairVectorMiddle.pairs outcome.1, outcome.1.2.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (LookupPairVectorMiddle.program pairTable (by norm_num [ZMod.card]) pairHelper)).run columnStart =
      (fun actual => (actual, (forgedPairs, false), 4)) <$>
        LookupPairVector.vector (K := ZMod 17) pairTable (by norm_num [ZMod.card]) 2 := by
  simp only [LookupPairVectorMiddle.program, SharedContinuation.program, pairHelper,
    simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, simulateQ_pure, StateT.run_pure,
    schemeHash_run (.inl [1]) columnStart 1 rfl,
    map_bind, map_pure, bind_map_left, pure_bind, LookupPairVectorMiddle.pairs]
  conv_rhs => rw [map_eq_pure_bind]
  rfl

example : Pr{let outcome ←
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (LookupPairVectorMiddle.program pairTable (by norm_num [ZMod.card]) pairHelper)).run columnStart}[
      LookupPairVector.AllPass pairSources pairTable pairMultiplicities (LookupPairVectorMiddle.pairs outcome.1)] ≤
        (2 / 15 : ENNReal) ^ 2 := by
  simpa only [ZMod.card, pairError] using LookupPairVectorMiddle.retained_bound columnEncoding 0 workerShape
    pairSources pairTable pairMultiplicities (by norm_num [ZMod.card]) pairMissing (by decide) pairHelper columnStart

end TupleLookupPairSmoke

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPair.sample_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPair.sample_total

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPair.allPass_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPair.allPass_cons

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPair.repeats_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPair.repeats_total

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPair.repeated_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPair.repeated_probability

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPair.single_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPair.single_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPair.repeated_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPair.repeated_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPairOracle.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPairOracle.retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.TupleLookupPairOracle.prepared_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TupleLookupPairOracle.prepared_bound

namespace ExtensionQuerySmoke

private noncomputable def basis : Module.Basis (Fin 1) (ZMod 17) (ZMod 17) :=
  Module.Basis.singleton _ _

private theorem encode_eq (x : ZMod 17) : PaddedExtension.encode (padding := 1) basis x = ![x, 0] := by
  funext lane
  fin_cases lane
  · change PaddedExtension.encode basis x ((0 : Fin 1).castAdd 1) = x
    rw [PaddedExtension.encode_left]
    simp [basis, Module.Basis.equivFun_apply]
  · exact PaddedExtension.encode_right basis x (0 : Fin 1)

private theorem decode_eq (v : Fin 2 → ZMod 17) : PaddedExtension.decode (padding := 1) basis v = v 0 := by
  rw [PaddedExtension.decode_sum]
  simp [basis]

/-- The raw helper has nonzero padding. It is rejected as an encoded element,
but the coefficient query correctly ignores that padding after opening it. -/
example : PaddedExtension.element (padding := 1) basis (![3, 7] : Fin 2 → ZMod 17) = none := by
  rw [PaddedExtension.element, ite_eq_right]
  intro padded
  have entry := padded 0
  exact (by decide : (7 : ZMod 17) ≠ 0) entry

example : (ExtensionQuery.coefficientsQuery (padding := 1) basis (Fin.elim0 : Fin 0 → ZMod 17)).query.fold
    (fun _ => ![3, 7]) = ![3, 7] := rfl

example : (ExtensionQuery.coefficientsQuery (padding := 1) basis (Fin.elim0 : Fin 0 → ZMod 17)).evaluate
    (fun _ => ![3, 7]) = ![3, 0] := by
  rw [ExtensionQuery.coefficients_evaluate]
  simp only [ExtensionQuery.evaluate, decode_eq, encode_eq]
  rfl

example : (ExtensionQuery.coefficientsQuery (padding := 1) basis (![2] : Fin 1 → ZMod 17)).evaluate
    (fun cell => if cell.1 then ![5, 9] else ![3, 7]) = ![7, 0] := by
  rw [ExtensionQuery.coefficients_evaluate]
  simp only [ExtensionQuery.evaluate, decode_eq, encode_eq]
  decide

/-- Selecting the second scalar lane must retain the original unused helper
lane. Pre-projecting it would change the authenticated scalar polynomial. -/
example : (ExtensionQuery.scalarQuery (padding := 1) basis (![0, 1] : Fin 2 → ZMod 17) 0 Fin.elim0).evaluate
    (fun _ => ![0, 1]) = ![1, 0] := by
  rw [ExtensionQuery.scalar_evaluate]
  simp only [ExtensionQuery.evaluate, ExtensionQuery.laneValue, encode_eq, smul_eq_mul]
  decide

example : ((PaddedExtension.multiplication (padding := 1) basis 1) * ExtensionQuery.laneMatrix basis ![0, 1]) *ᵥ
    (![0, 1] : Fin 2 → ZMod 17) = ![1, 0] := by
  rw [← Matrix.mulVec_mulVec, ExtensionQuery.laneMatrix_mulVec, PaddedExtension.multiplication_encode]
  simp only [ExtensionQuery.laneValue, encode_eq, smul_eq_mul]
  decide

example : (ExtensionQuery.laneMatrix (padding := 1) basis ![0, 1] * PaddedExtension.multiplication basis 1) *ᵥ
    (![0, 1] : Fin 2 → ZMod 17) = ![0, 0] := by
  rw [← Matrix.mulVec_mulVec, PaddedExtension.projection_mulVec, decode_eq, encode_eq,
    ExtensionQuery.laneMatrix_mulVec]
  simp only [ExtensionQuery.laneValue, encode_eq, smul_eq_mul]
  decide

example : (ExtensionQuery.scalarQuery (padding := 1) basis (![0, 1] : Fin 2 → ZMod 17) 1 ![2]).evaluate
    (fun cell => if cell.1 then ![5, 9] else ![3, 7]) = ![11, 0] := by
  rw [ExtensionQuery.scalar_evaluate]
  simp only [ExtensionQuery.evaluate, ExtensionQuery.laneValue, encode_eq, smul_eq_mul]
  decide

/-- Accepted decoding of a wrong constant EF value implies the original
constant-vector opening is false, although its committed padding is nonzero. -/
example : (![4, 8] : Fin 2 → ZMod 17) ≠
    (ExtensionQuery.coefficientsQuery (padding := 1) basis (Fin.elim0 : Fin 0 → ZMod 17)).query.fold
      (fun _ => ![3, 7]) := by
  apply ExtensionQuery.coefficients_false_claim (padding := 1) basis Fin.elim0 (fun _ => ![3, 7]) 4 ![4, 8]
  · change PaddedExtension.element basis (PaddedExtension.multiplication (padding := 1) basis 1 *ᵥ (![4, 8] : Fin 2 → ZMod 17)) = some 4
    rw [PaddedExtension.element_multiplication, decode_eq]
    decide
  · change (4 : ZMod 17) ≠ PaddedExtension.decode (padding := 1) basis (![3, 7] : Fin 2 → ZMod 17)
    rw [decode_eq]
    decide

/-- Lane address one is the true low bit, not a basis index. -/
private theorem laneWeights_one : ExtensionQuery.laneWeights (d := 1) (padding := 1) (FlatMatrixFold.index 1).symm
    (![1] : Fin 1 → ZMod 17) = ![0, 1] := by
  have address (bit : Bool) : (FlatMatrixFold.index 1).symm (if bit then 1 else 0) = (bit, ()) := by
    apply (FlatMatrixFold.index 1).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    erw [FlatMatrixFold.index_succ_val]
    have bound := (FlatMatrixFold.index 0 ()).isLt
    cases bit <;> simp_all
  funext lane
  fin_cases lane
  · change PackedEqualityCube.weight (![1] : Fin 1 → ZMod 17) ((FlatMatrixFold.index 1).symm 0) = 0
    erw [address false, PackedEqualityCube.weight_succ, PackedEqualityCube.weight_zero]
    decide
  · change PackedEqualityCube.weight (![1] : Fin 1 → ZMod 17) ((FlatMatrixFold.index 1).symm 1) = 1
    erw [address true, PackedEqualityCube.weight_succ, PackedEqualityCube.weight_zero]
    decide

example : ExtensionQuery.evaluate 2 (![2, 3] : Fin 2 → ZMod 17)
    (fun cell => if cell.1 then (if cell.2.1 then 8 else 4) else (if cell.2.1 then 2 else 1)) = 11 := by
  decide

example : (![0, 2] : Fin 2 → ZMod 17) ≠
    (ExtensionQuery.scalarQuery (padding := 1) basis (![0, 1] : Fin 2 → ZMod 17) 0 Fin.elim0).query.fold
      (fun _ => ![0, 1]) := by
  apply ExtensionQuery.scalar_false_claim (padding := 1) basis ![0, 1] Fin.elim0 (fun _ => ![0, 1]) 2 ![0, 2]
  · change PaddedExtension.element basis
      (ExtensionQuery.laneMatrix (padding := 1) basis (![0, 1] : Fin 2 → ZMod 17) *ᵥ (![0, 2] : Fin 2 → ZMod 17)) = some 2
    rw [ExtensionQuery.laneMatrix_mulVec, PaddedExtension.element_encode]
    decide
  · change (2 : ZMod 17) ≠ ExtensionQuery.laneValue (d := 1) (padding := 1) (![0, 1] : Fin 2 → ZMod 17) (![0, 1] : Fin 2 → ZMod 17)
    decide

end ExtensionQuerySmoke

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.encode_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.encode_left

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.encode_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.encode_right

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.decode_encode

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.decode_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.decode_sum

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.encode_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.encode_padded

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.encode_decode_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.encode_decode_left

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.encode_decode_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.encode_decode_iff

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.element_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.element_encode

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.element_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.element_some_iff

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.multiplication_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.multiplication_left

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.multiplication_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.multiplication_right

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.multiplication_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.multiplication_mulVec

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.multiplication_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.multiplication_encode

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.multiplication_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.multiplication_mul

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.projection_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.projection_mulVec

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.projection_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.projection_idempotent

/-- info: 'FormalProof4FHE.HasteBoots.PaddedExtension.element_multiplication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaddedExtension.element_multiplication

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.evaluate_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.evaluate_eq_sum

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.foldFirst_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.foldFirst_coefficients

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.coefficients_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.coefficients_encoded

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.coefficients_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.coefficients_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.laneValue_algebraMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.laneValue_algebraMap

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.laneMatrix_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.laneMatrix_mulVec

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.foldFirst_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.foldFirst_scalar

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.scalar_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.scalar_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.scalar_evaluate_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.scalar_evaluate_tensor

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.false_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.false_claim

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.coefficients_false_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.coefficients_false_claim

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.scalar_false_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.scalar_false_claim


/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.nativeLanes_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.nativeLanes_index

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionQuery.nativeLanes_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionQuery.nativeLanes_bits


/-- info: 'FormalProof4FHE.HasteBoots.ExtensionSourceOpening.false_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionSourceOpening.false_finish

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionSourceOpening.coefficients_false_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionSourceOpening.coefficients_false_finish

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionSourceOpening.scalar_false_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionSourceOpening.scalar_false_finish

namespace LookupIdentitySmoke

/-- Every boundary of a four-cell active prefix, evaluated off the cube. -/
example : NativePrefixMask.evaluatePrefix (![2, 3] : Fin 2 → ZMod 17) 0 (by decide) = 0 :=
  NativePrefixMask.prefix_zero _
example : NativePrefixMask.evaluatePrefix (![2, 3] : Fin 2 → ZMod 17) 1 (by decide) = 2 := by
  rw [NativePrefixMask.prefix_eq_evaluate]
  decide
example : NativePrefixMask.evaluatePrefix (![2, 3] : Fin 2 → ZMod 17) 2 (by decide) = 15 := by
  rw [NativePrefixMask.prefix_eq_evaluate]
  decide
example : NativePrefixMask.evaluatePrefix (![2, 3] : Fin 2 → ZMod 17) 3 (by decide) = 12 := by
  rw [NativePrefixMask.prefix_eq_evaluate]
  decide
example : NativePrefixMask.evaluatePrefix (![2, 3] : Fin 2 → ZMod 17) 4 (by decide) = 1 :=
  NativePrefixMask.prefix_full _

/-- Coordinate order matters: the high-to-low loop preserves native addresses. -/
example : NativePrefixMask.evaluatePrefix (![2, 3, 4] : Fin 3 → ZMod 17) 5 (by decide) = 5 := by
  rw [NativePrefixMask.prefix_eq_evaluate]
  decide
example : NativePrefixMask.evaluatePrefix (![4, 3, 2] : Fin 3 → ZMod 17) 5 (by decide) = 11 := by
  rw [NativePrefixMask.prefix_eq_evaluate]
  decide

/-- The loop carries both accumulators; the full-table shortcut is necessary. -/
example : NativePrefixMask.loop 2 (![1, 1] : Fin 2 → Fin 2) (![2, 3] : Fin 2 → ZMod 17) 3 7 = 9 := by decide
example : NativePrefixMask.loop 2 (![0, 0] : Fin 2 → Fin 2) (![2, 3] : Fin 2 → ZMod 17) 1 0 = 0 := by decide
example : NativePrefixMask.evaluatePrefix (Fin.elim0 : Fin 0 → ZMod 17) 0 (by decide) = 0 :=
  NativePrefixMask.prefix_zero _
example : NativePrefixMask.evaluatePrefix (Fin.elim0 : Fin 0 → ZMod 17) 1 (by decide) = 1 :=
  NativePrefixMask.prefix_full _

example : ExtensionLookupIdentity.equality (![2, 3] : Fin 2 → ZMod 17) ![4, 5] = 15 := by decide
example : ExtensionQuery.evaluate 2 (![4, 5] : Fin 2 → ZMod 17)
    (PackedEqualityCube.weight ![2, 3]) = 15 := by
  rw [ExtensionLookupIdentity.evaluate_equality]
  decide

example : ExtensionQuery.evaluate 1 (![2] : Fin 1 → ZMod 17)
    (ExtensionLookupIdentity.hashTable (F := ZMod 17) 2
      (fun i : Fin 2 => fun cell => if i = 0 then (if cell.1 then 5 else 3) else (if cell.1 then 9 else 7))) = 12 := by
  rw [ExtensionLookupIdentity.evaluate_hash]
  decide

/-- Products of separately evaluated MLEs cannot be replaced by the MLE of
the pointwise residual. This distinction matters at a non-Boolean point. -/
example : ExtensionQuery.evaluate 1 (![2] : Fin 1 → ZMod 17)
    (fun cell => ReciprocalMask.residual 1 (if cell.1 then 1 else 0) (if cell.1 then 1 else 0) true) = 3 := by decide
example : let v := ExtensionQuery.evaluate 1 (![2] : Fin 1 → ZMod 17) (fun cell => if cell.1 then 1 else 0)
    1 * v + v * v - 1 = 5 := by decide

private def zeroSources : Fin 1 → MatrixFold.Cube 1 → ZMod 17 := fun _ _ => 0
private def wrongHelpers : MatrixFold.Cube 1 → ZMod 17 := fun cell => if cell.1 then 0 else 2
private def zeroTable : Fin 1 → ZMod 17 := fun _ => 0
private def twice : Fin 1 → ZMod 17 := fun _ => 2

private theorem notPasses : ¬ReciprocalDetection.Passes
    (LookupReciprocalEnforcement.activeSource (count := 1) (padding := 1) (n := 1) rfl
      (ExtensionLookupIdentity.hashTable 0 zeroSources)) zeroTable twice 1 := by
  rw [ReciprocalDetection.passes_iff]
  simp [LookupReciprocalEnforcement.activeSource, ExtensionLookupIdentity.hashTable, zeroSources,
    TupleHash.hash_eq_sum, zeroTable, twice]
  decide

/-- A truthful helper sum for a nonpassing pair forces a false identity. The
helper has sum two, while the actual active source has only one reciprocal. -/
example : Pr{let eqPoint ← $ᵗ (Fin 1 → ZMod 17)}[
    (∑ cell, PackedSumcheckRound.expression ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient 1) ExtensionLookupIdentity.partialIndices
      (fun factor => ExtensionLookupIdentity.factors eqPoint 0 zeroSources wrongHelpers 1 factor cell)) = 0] ≤
      (1 / 17 : ENNReal) := by
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat] using
    LookupReciprocalEnforcement.equality_bound (count := 1) (padding := 1) (n := 1) rfl
      1 0 zeroSources wrongHelpers zeroTable twice (by decide) notPasses (by
        change (∑ cell : Bool × Unit, wrongHelpers cell) = _
        simp [Fintype.sum_prod_type, wrongHelpers, zeroTable, twice])

end LookupIdentitySmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.mle_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.mle_snoc

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.mle_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.mle_one

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.mle_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.mle_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.loop_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.loop_affine

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.loop_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.loop_result

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.address_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.address_snoc

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.core_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.core_eq_mle

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.prefix_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.prefix_eq_mle

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.prefix_eq_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.prefix_eq_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.prefix_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.prefix_boolean

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.prefix_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.prefix_full

/-- info: 'FormalProof4FHE.HasteBoots.NativePrefixMask.prefix_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativePrefixMask.prefix_zero

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_mul

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_add

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_sum

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_equality

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_hash

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.partial_degree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.partial_degree

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.partial_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.partial_expression

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.full_degree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.full_degree

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.full_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.full_expression

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.partial_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.partial_terminal

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.partial_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.partial_boolean

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.partial_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.partial_sum

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.terminal_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.terminal_full

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.partial_round_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.partial_round_degree

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.full_round_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.full_round_degree

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.equality_miss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.equality_miss_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement.cells_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupReciprocalEnforcement.cells_address

/-- info: 'FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement.passes_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupReciprocalEnforcement.passes_of_checks

/-- info: 'FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement.not_passes_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupReciprocalEnforcement.not_passes_obstruction

/-- info: 'FormalProof4FHE.HasteBoots.LookupReciprocalEnforcement.equality_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupReciprocalEnforcement.equality_bound

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupTerminal.source_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupTerminal.source_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupTerminal.source_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupTerminal.source_tensor

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupTerminal.checked_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupTerminal.checked_truthful_or_wrong


/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_const

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.evaluate_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.evaluate_translate

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionLookupIdentity.full_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionLookupIdentity.full_terminal

namespace LookupFlatteningSmoke

private def packed : MatrixFold.Cube 1 → Fin 2 → ZMod 17 :=
  fun cell => if cell.1 then ![2, 8] else ![1, 4]

/-- Low lane bits precede the row bits: the flat values are [1,4,2,8]. -/
example : LookupSourceFlattening.flatten (d := 1) (padding := 1) (c := 1) rfl packed (false, (false, ())) = 1 := by decide
example : LookupSourceFlattening.flatten (d := 1) (padding := 1) (c := 1) rfl packed (true, (false, ())) = 4 := by decide
example : LookupSourceFlattening.flatten (d := 1) (padding := 1) (c := 1) rfl packed (false, (true, ())) = 2 := by decide
example : LookupSourceFlattening.flatten (d := 1) (padding := 1) (c := 1) rfl packed (true, (true, ())) = 8 := by decide

example : ExtensionLookupTerminal.sourceTruth (F := ZMod 17) (d := 1) (padding := 1) (c := 1) rfl
    (![2, 3] : Fin 2 → ZMod 17) packed = 11 := by
  rw [LookupSourceFlattening.sourceTruth_eq_evaluate]
  decide

/-- Swapping coordinates changes the polynomial value for this source. -/
example : ExtensionLookupTerminal.sourceTruth (F := ZMod 17) (d := 1) (padding := 1) (c := 1) rfl
    (![3, 2] : Fin 2 → ZMod 17) packed = 13 := by
  rw [LookupSourceFlattening.sourceTruth_eq_evaluate]
  decide

/-- A scalar table with no row variables still authenticates both original lanes. -/
example : ExtensionLookupTerminal.sourceTruth (F := ZMod 17) (d := 1) (padding := 1) (c := 1) (row := 0) rfl
    (![2] : Fin 1 → ZMod 17) (fun _ => ![3, 7]) = 11 := by
  rw [LookupSourceFlattening.sourceTruth_eq_evaluate]
  decide

/-- Width one has no lane coordinates; both-zero dimensions return the entry. -/
example : ExtensionLookupTerminal.sourceTruth (F := ZMod 17) (d := 1) (padding := 0) (c := 0) (row := 1) rfl
    (![2] : Fin 1 → ZMod 17) (fun cell => if cell.1 then ![7] else ![3]) = 11 := by
  rw [LookupSourceFlattening.sourceTruth_eq_evaluate]
  decide
example : ExtensionLookupTerminal.sourceTruth (F := ZMod 17) (d := 1) (padding := 0) (c := 0) (row := 0) rfl
    (Fin.elim0 : Fin 0 → ZMod 17) (fun _ => ![9]) = 9 := by
  rw [LookupSourceFlattening.sourceTruth_eq_evaluate]
  decide

/-- Packing width four, basis degree three, two lane bits and one row bit
remain separate dimensions. Flattening retains the fourth scalar lane. -/
example : LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) (row := 1) rfl
    (fun cell => if cell.1 then (![5, 6, 7, 8] : Fin 4 → ZMod 17) else ![1, 2, 3, 4]) (true, (true, (true, ()))) = 8 := by decide

end LookupFlatteningSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.low_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.low_bits

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.high_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.high_bits

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.split_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.split_address

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.split_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.split_weight

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.evaluate_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.evaluate_split

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.flatten_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.flatten_address

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.flatten_recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.flatten_recover

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.flatten_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.flatten_injective

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.sourceTruth_eq_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.sourceTruth_eq_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.source_query_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.source_query_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.hash_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.hash_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.terminal_eq_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.terminal_eq_identity

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceFlattening.terminal_eq_full_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupSourceFlattening.terminal_eq_full_identity

namespace ScalarSumcheckSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

example : PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes (F := ZMod 17) 17 (by decide))
    (fun _ : Fin 1 => 2) false 0 0 = 16 := by
  rw [ScalarSumcheckQuery.native_pair]
  decide
example : PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes (F := ZMod 17) 17 (by decide))
    (fun _ : Fin 1 => 2) true 0 0 = 2 := by
  rw [ScalarSumcheckQuery.native_pair]
  rfl

example : ScalarSumcheckQuery.point (ScalarSumcheckQuery.query 2 (![2, 3] : Fin 2 → ZMod 17)) = ![2, 3] :=
  ScalarSumcheckQuery.point_query _

/-- The original coordinate order is preserved by scalar query folding. -/
example : (ScalarSumcheckQuery.query 2 (![2, 3] : Fin 2 → ZMod 17)).fold
    (fun cell (_ : Fin 1) => if cell.1 then (if cell.2.1 then 8 else 4) else (if cell.2.1 then 2 else 1)) =
      fun _ => 11 := by
  rw [ScalarSumcheckQuery.fold_query]
  decide

/-- Arbitrary 1×1 queries need not be scalar interpolation queries. -/
example : ¬ScalarSumcheckQuery.Scalar
    (.cons (fun _ _ _ => (0 : ZMod 17)) .nil : PackedSumcheckSubclaim.Query (ZMod 17) 1 1) := by
  intro valid
  have entry := congrArg (fun q : PackedSumcheckSubclaim.Query (ZMod 17) 1 1 =>
    (q.toList.headD (fun _ _ _ => 0)) false 0 0) valid
  change (0 : ZMod 17) = 1 - 0 at entry
  exact (by decide : (0 : ZMod 17) ≠ 1) (by simpa only [sub_zero] using entry)

example (table : MatrixFold.Cube 0 → ZMod 17) :
    (ScalarSumcheckQuery.query 0 Fin.elim0).fold (fun cell (_ : Fin 1) => table cell) = fun _ => table () := rfl

/-- Native false boundary claim: [1,-1] passes its sum-zero check, and the
shared callback still runs. The MLE arithmetic event has the checked 1/17 bound. -/
private noncomputable def sendVector (_round : ℕ) (_state : Unit) (_claimed : Fin 1 → ZMod 17) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) ((Fin 2 → ZMod 17) × Unit) :=
  (fun _ => ((![1, 16] : Fin 2 → ZMod 17), ())) <$> sharedSamplingResponse 0

example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (PackedSumcheckOracle.program (NativePackedInterpolation.nodes (F := ZMod 17) 17 (by decide))
      (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive 17 (by decide)))
      sendVector oraclePackedAfter 1 (fun _ => 0) ())).run workerStart}[
      ScalarSumcheckOracle.MLETruthful LookupScalarSubclaim.sumArity (LookupScalarSubclaim.sumCoefficient (K := ZMod 17))
        LookupScalarSubclaim.sumIndices (fun (_ : Unit) (_ : MatrixFold.Cube 1) => 1) outcome.1] ≤ (1 / 17 : ENNReal) := by
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat, one_mul] using
    ScalarSumcheckOracle.native_soundness_bound overlappingMerkleEncoding 0 workerShape 17 1 (by decide) (by decide)
      LookupScalarSubclaim.sumArity (LookupScalarSubclaim.sumCoefficient (K := ZMod 17)) LookupScalarSubclaim.sumIndices
      (fun _ => le_rfl) sendVector oraclePackedAfter 1 (fun (_ : Unit) (_ : MatrixFold.Cube 1) => 1) 0 () workerStart (by
        change (0 : ZMod 17) ≠ ∑ _cell : Bool × Unit, 1
        simp
        decide)

example : PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes (F := ZMod 17) 17 (by decide))
    (fun _ : Fin 1 => 0) false 0 0 = 1 := by
  rw [ScalarSumcheckQuery.native_pair]
  decide
example : PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes (F := ZMod 17) 17 (by decide))
    (fun _ : Fin 1 => 1) true 0 0 = 1 := by
  rw [ScalarSumcheckQuery.native_pair]
  rfl

/-- With no rounds, a false scalar claim is still a false MLE terminal. -/
example : ¬ScalarSumcheckOracle.MLETruthful LookupScalarSubclaim.sumArity
    (LookupScalarSubclaim.sumCoefficient (K := ZMod 17)) LookupScalarSubclaim.sumIndices
    (fun (_ : Unit) (_ : MatrixFold.Cube 0) => 1)
    (some ((⟨.nil, fun _ => 0⟩ : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 0), ())) := by
  rw [LookupScalarSubclaim.sum_truthful_iff]
  decide

end ScalarSumcheckSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.native_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.native_pair

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.point_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.point_query

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.scalar_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.scalar_query

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.scalar_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.scalar_nil

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.scalar_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.scalar_prepend

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.fold_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.fold_query

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.fold_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.fold_scalar

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckQuery.truthful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckQuery.truthful_iff

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckOracle.valid_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckOracle.valid_prepend

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckOracle.valid_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckOracle.valid_result

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckOracle.truthful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckOracle.truthful_iff

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckOracle.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckOracle.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckOracle.native_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckOracle.native_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.ScalarSumcheckOracle.continued_soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScalarSumcheckOracle.continued_soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarSubclaim.sum_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupScalarSubclaim.sum_expression

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarSubclaim.sum_truthful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupScalarSubclaim.sum_truthful_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarSubclaim.partial_truthful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupScalarSubclaim.partial_truthful_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarSubclaim.full_truthful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupScalarSubclaim.full_truthful_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarSubclaim.checked_partial_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupScalarSubclaim.checked_partial_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.LookupScalarSubclaim.checked_full_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupScalarSubclaim.checked_full_or_wrong

namespace LookupPairSequenceSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private noncomputable def sumSend (_round : ℕ) (_memory : Unit) (_claimed : Fin 1 → ZMod 17) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) ((Fin 2 → ZMod 17) × Unit) :=
  (fun _ => ((fun _ : Fin 2 => 0), ())) <$> sharedSamplingResponse 0

private noncomputable def schedule : LookupPairSequence.Schedule (ZMod 17) Unit Unit (Fin 4) (Fin 2) 1 4 where
  sumSend := sumSend
  sumAfter := oraclePackedAfter
  zeroSend := fun _ _ _ _ _ => (fun _ => ((fun _ : Fin 5 => 0), ())) <$> sharedSamplingResponse 0
  zeroAfter := fun _ _ => oraclePackedAfter

private theorem send_run (round : ℕ) (memory : Unit) (claimed : Fin 1 → ZMod 17) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (sumSend round memory claimed)).run workerStart = pure (((fun _ : Fin 2 => (0 : ZMod 17)), ()), workerStep workerStart 2 0) := by
  simp only [sumSend, simulateQ_map, StateT.run_map, sharedSamplingResponse_run, map_pure]

private theorem interpolate_zero : NativePackedInterpolation.messagePolynomial
    (NativePackedInterpolation.consecutive (F := ZMod 17) 17 (show 2 ≤ 17 by decide)) (fun _ : Fin 2 => 0) = 0 := by
  simp [NativePackedInterpolation.messagePolynomial, Lagrange.interpolate_apply]

/-- A wrong public-table sum claim issues no stage hashes or verifier coins. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (LookupPairSequence.program 17 (by decide) (by decide) schedule 0 1 ())).run workerStart =
      pure ((none, none), workerStart) := by
  simp only [LookupPairSequence.program, show ¬(1 : ZMod 17) = 0 from by decide, ite_false, simulateQ_pure, StateT.run_pure]

/-- A bad sumcheck message keeps its actual issued hash and skips the
sum callback, EQ point and all identity work. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (LookupPairSequence.program 17 (by decide) (by decide) schedule 1 1 ())).run workerStart =
      pure ((none, none), workerStep workerStart 2 0) := by
  have sumFailed : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (LookupPairSequence.sumProgram 17 (by decide) schedule 1 ())).run workerStart =
        pure (none, workerStep workerStart 2 0) := by
    rw [LookupPairSequence.sumProgram, PackedSumcheckOracle.run_succ]
    change (do
      let packet ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
        (sumSend 1 () (fun _ => 1))).run workerStart
      _) = _
    rw [send_run, pure_bind, interpolate_zero]
    have rejected : ¬PackedSumcheckProbability.Checks
        (NativePackedInterpolation.nodes (F := ZMod 17) 17 (by decide)) (fun _ : Fin 1 => 1) 0 := by
      intro checked
      have bad := checked 0
      norm_num at bad
    simp only [rejected, ite_false]
  rw [LookupPairSequence.program, ite_eq_left rfl, SharedContinuation.program, simulateQ_bind, StateT.run_bind, sumFailed, pure_bind]
  simp only [LookupPairSequence.afterSum, simulateQ_pure, StateT.run_pure, pure_bind]

private def sources : Fin 1 → MatrixFold.Cube 1 → ZMod 17 := fun _ _ => 0
private def helpers : MatrixFold.Cube 1 → ZMod 17 := fun cell => if cell.1 then 0 else 2
private def table : Fin 1 → Fin 1 → ZMod 17 := fun _ _ => 0
private def multiplicities : Fin 1 → ZMod 17 := fun _ => 2

private theorem nonpassing : ¬TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples (active := 1) (inactive := 1) (n := 1) rfl sources) table
    (fun i => algebraMap (ZMod 17) (ZMod 17) (multiplicities i)) (0, 1) := by
  rw [TupleLookupPair.Passes, ReciprocalDetection.passes_iff]
  simp [LookupPairArithmetic.activeTuples, sources, table, multiplicities,
    TupleHash.hash_eq_sum]
  decide

/-- The concrete partial bound uses both stages of this actual shared program
and computes the EQ obstruction from a nonpassing pair with truthful helper sum. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (LookupPairSequence.program 17 (by decide) (by decide) schedule
      (LookupPairArithmetic.tableSum 1 0 table multiplicities) 2 ())).run workerStart}[
      LookupPairSequence.JointTruthful ExtensionLookupIdentity.partialArity
        (ExtensionLookupIdentity.partialCoefficient 1) ExtensionLookupIdentity.partialIndices
        (fun eqPoint => ExtensionLookupIdentity.factors eqPoint 0 sources helpers 1) helpers outcome.1] ≤
      (1 / 17 : ENNReal) + 4 / 17 := by
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat, one_mul] using
    LookupPairArithmetic.partial_bound overlappingMerkleEncoding 0 workerShape 17 (by decide) schedule
      (active := 1) (inactive := 1) rfl 1 0 table multiplicities sources helpers (by decide) nonpassing 2 () workerStart

private noncomputable def fullSchedule : LookupPairSequence.Schedule (ZMod 17) Unit Unit (Fin 4) (Fin 2) 1 3 where
  sumSend := fun _ _ _ => (fun _ => ((![2, 1] : Fin 2 → ZMod 17), ())) <$> sharedSamplingResponse 0
  sumAfter := oraclePackedAfter
  zeroSend := fun _ _ _ _ _ => (fun _ => ((fun _ : Fin 4 => 0), ())) <$> sharedSamplingResponse 0
  zeroAfter := fun _ _ => oraclePackedAfter

private def fullHelpers : MatrixFold.Cube 1 → ZMod 17 := fun cell => if cell.1 then 1 else 2
private def fullMultiplicities : Fin 1 → ZMod 17 := fun _ => 3

private theorem fullNonpassing : ¬TupleLookupPair.Passes
    (LookupPairArithmetic.activeTuples (active := 2 ^ 1) (inactive := 0) (n := 1) (by decide) sources) table
    (fun i => algebraMap (ZMod 17) (ZMod 17) (fullMultiplicities i)) (0, 1) := by
  rw [TupleLookupPair.Passes, ReciprocalDetection.passes_iff]
  simp [LookupPairArithmetic.activeTuples, sources, table, fullMultiplicities, TupleHash.hash_eq_sum]
  decide

/-- The full-table branch uses degree three and its own actual native message
shape; it retains the fresh EQ term and truthful helper sum. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (LookupPairSequence.program 17 (by decide) (by decide) fullSchedule
      (LookupPairArithmetic.tableSum 1 0 table fullMultiplicities) 3 ())).run workerStart}[
      LookupPairSequence.JointTruthful ExtensionLookupIdentity.fullArity
        (ExtensionLookupIdentity.fullCoefficient (K := ZMod 17)) ExtensionLookupIdentity.fullIndices
        (fun eqPoint => LookupPairArithmetic.fullTables eqPoint 1 0 sources fullHelpers) fullHelpers outcome.1] ≤
      (1 / 17 : ENNReal) + 3 / 17 := by
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat, one_mul] using
    LookupPairArithmetic.full_bound overlappingMerkleEncoding 0 workerShape 17 (by decide) fullSchedule
      1 0 table fullMultiplicities sources fullHelpers (by decide) fullNonpassing 3 () workerStart

end LookupPairSequenceSmoke

namespace LookupPairTerminalSmoke

private noncomputable def basis : Module.Basis (Fin 1) (ZMod 17) (ZMod 17) := Module.Basis.singleton _ _

private theorem encoded (value : ZMod 17) : PaddedExtension.encode (padding := 1) basis value = ![value, 0] := by
  funext i
  fin_cases i
  · change PaddedExtension.encode basis value ((0 : Fin 1).castAdd 1) = value
    rw [PaddedExtension.encode_left]
    simp [basis, Module.Basis.equivFun_apply]
  · exact PaddedExtension.encode_right basis value (0 : Fin 1)

private theorem decoded : LookupPairTerminal.decodeSources basis (c := 1) (row := 1) rfl
    (![0, 0] : Fin 2 → ZMod 17) 1 (fun _ => ![3, 0]) = some ![3] := by
  have canonical : PaddedExtension.element (padding := 1) basis (![3, 0] : Fin 2 → ZMod 17) = some 3 := by
    rw [← encoded, PaddedExtension.element_encode]
  change (PaddedExtension.element (padding := 1) basis (![3, 0] : Fin 2 → ZMod 17)).bind
    (fun first => some (Fin.cons first (Fin.elim0 : Fin 0 → ZMod 17))) = some ![3]
  rw [canonical]
  congr 1

private theorem maskValue : NativePrefixMask.evaluatePrefix (![0, 0] : Fin 2 → ZMod 17) 1 (by decide) = 1 := by
  rw [NativePrefixMask.prefix_eq_evaluate]
  decide

private theorem localValue : ExtensionLookupIdentity.terminal (![0, 0] : Fin 2 → ZMod 17) ![0, 0] 1 3 1 1 (by decide) = 3 := by
  rw [ExtensionLookupIdentity.terminal, maskValue]
  decide

private theorem check_accepts : LookupPairTerminal.check basis (c := 1) (row := 1) rfl ![0, 0] ![0, 0] 1 0 1 (by decide)
    (fun _ : Fin 1 => ![3, 0]) 1 3 = true := by
  rw [LookupPairTerminal.check, decoded]
  simp only [decide_eq_true_eq]
  change (ExtensionLookupIdentity.terminal (![0, 0] : Fin 2 → ZMod 17) ![0, 0] 1
    (∑ i : Fin 1, (0 : ZMod 17) ^ i.val * (![3] : Fin 1 → ZMod 17) i) 1 1 (by decide) = 3)
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.cons_val_zero]
  rw [localValue]
private theorem check_rejects : LookupPairTerminal.check basis (c := 1) (row := 1) rfl ![0, 0] ![0, 0] 1 0 1 (by decide)
    (fun _ : Fin 1 => ![3, 0]) 1 4 = false := by
  rw [LookupPairTerminal.check, decoded]
  simp only [decide_eq_false_iff_not]
  change ¬(ExtensionLookupIdentity.terminal (![0, 0] : Fin 2 → ZMod 17) ![0, 0] 1
    (∑ i : Fin 1, (0 : ZMod 17) ^ i.val * (![3] : Fin 1 → ZMod 17) i) 1 1 (by decide) = 4)
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.cons_val_zero]
  rw [localValue]
  decide

/-- Malformed supplied terminal padding is rejected by the computed decoder. -/
example : LookupPairTerminal.check basis (c := 1) (row := 1) rfl ![0, 0] ![0, 0] 1 0 1 (by decide)
    (fun _ : Fin 1 => ![3, 7]) 1 3 = false := by
  have malformed : PaddedExtension.element (padding := 1) basis (![3, 7] : Fin 2 → ZMod 17) = none := by
    rw [PaddedExtension.element, ite_eq_right]
    intro padded
    exact (by decide : (7 : ZMod 17) ≠ 0) (padded 0)
  have failed : LookupPairTerminal.decodeSources basis (c := 1) (row := 1) rfl
      (![0, 0] : Fin 2 → ZMod 17) 1 (fun _ => ![3, 7]) = none := by
    change (PaddedExtension.element (padding := 1) basis (![3, 7] : Fin 2 → ZMod 17)).bind _ = none
    rw [malformed]
    rfl
  rw [LookupPairTerminal.check, failed]

private def claim (expected : ZMod 17) : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 2 :=
  ⟨ScalarSumcheckQuery.query 2 ![0, 0], fun _ => expected⟩
private def values : PreparedLookupPair.Values (ZMod 17) (ZMod 17) 2 1 := ⟨fun _ => ![3, 0], 1⟩
private noncomputable def receive (_ : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 2) (_ : Fin 2 → ZMod 17)
    (_ : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 2) (_ : Unit) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) (PreparedLookupPair.Values (ZMod 17) (ZMod 17) 2 1 × Unit) :=
  (fun _ => (values, ())) <$> sharedSamplingResponse 0
private def bindValues (_ : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 2) (_ : Fin 2 → ZMod 17)
    (_ : PackedSumcheckSubclaim.Subclaim (ZMod 17) 1 2) (_ : PreparedLookupPair.Values (ZMod 17) (ZMod 17) 2 1) (_ : Unit) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) Unit := oraclePackedAfter () (fun _ => 0)

/-- Rejected terminals keep reception's real hash and skip value binding. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (PreparedLookupPair.prepare basis (c := 1) (row := 1) rfl 1 0 1 (by decide) receive bindValues
      (some (claim 0, ()), some ((![0, 0] : Fin 2 → ZMod 17), some (claim 4, ()))))).run workerStart =
      pure (none, workerStep workerStart 2 0) := by
  rw [PreparedLookupPair.prepare, simulateQ_bind, StateT.run_bind]
  have receiveRun : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (receive (claim 0) ![0, 0] (claim 4) ())).run workerStart = pure ((values, ()), workerStep workerStart 2 0) := by
    simp only [receive, simulateQ_map, StateT.run_map, sharedSamplingResponse_run, map_pure]
  rw [receiveRun, pure_bind]
  have rejected : LookupPairTerminal.check basis (c := 1) (row := 1) rfl ![0, 0]
      (ScalarSumcheckQuery.point (claim 4).query) 1 0 1 (by decide) values.sources values.helper ((claim 4).expected 0) = false := by
    simpa only [claim, ScalarSumcheckQuery.point_query, values] using check_rejects
  simp only [rejected, Bool.false_eq_true, ite_false, simulateQ_pure, StateT.run_pure]

/-- A successful computed terminal binds after reception on the same state. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (PreparedLookupPair.prepare basis (c := 1) (row := 1) rfl 1 0 1 (by decide) receive bindValues
      (some (claim 0, ()), some ((![0, 0] : Fin 2 → ZMod 17), some (claim 3, ()))))).run workerStart =
      pure (some ((⟨claim 0, ![0, 0], claim 3, values⟩ : PreparedLookupPair.Packet (ZMod 17) (ZMod 17) 2 1 2), ()),
        workerStep (workerStep workerStart 2 0) 3 1) := by
  rw [PreparedLookupPair.prepare, simulateQ_bind, StateT.run_bind]
  have receiveRun : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (receive (claim 0) ![0, 0] (claim 3) ())).run workerStart = pure ((values, ()), workerStep workerStart 2 0) := by
    simp only [receive, simulateQ_map, StateT.run_map, sharedSamplingResponse_run, map_pure]
  rw [receiveRun, pure_bind]
  have accepted : LookupPairTerminal.check basis (c := 1) (row := 1) rfl ![0, 0]
      (ScalarSumcheckQuery.point (claim 3).query) 1 0 1 (by decide) values.sources values.helper ((claim 3).expected 0) = true := by
    simpa only [claim, ScalarSumcheckQuery.point_query, values] using check_accepts
  simp only [accepted, ite_true, simulateQ_bind, StateT.run_bind, bindValues, oraclePackedAfter_run, pure_bind,
    simulateQ_pure, StateT.run_pure]

end LookupPairTerminalSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairSequence.afterSum_run_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairSequence.afterSum_run_some

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairSequence.false_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairSequence.false_sum_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairSequence.identity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairSequence.identity_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairSequence.soundness_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairSequence.soundness_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairArithmetic.full_sum_eq_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairArithmetic.full_sum_eq_partial

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairArithmetic.partial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairArithmetic.partial_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairArithmetic.full_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairArithmetic.full_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.decodeSources_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.decodeSources_sound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.check_sound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.coefficients_finish_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.coefficients_finish_encode

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.sum_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.sum_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.partial_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.partial_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.full_truthful_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.full_truthful_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.partial_joint_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.partial_joint_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairTerminal.full_joint_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairTerminal.full_joint_or_wrong


/-- info: 'FormalProof4FHE.HasteBoots.PreparedLookupPair.prepare_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedLookupPair.prepare_sound

namespace LookupCompletionSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def emptyPacket : PreparedLookupPair.Packet (ZMod 17) (ZMod 17) 1 0 0 :=
  ⟨⟨.nil, fun _ => 0⟩, Fin.elim0, ⟨.nil, fun _ => 0⟩, ⟨Fin.elim0, 0⟩⟩
private def propose : OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2))
    (PreparedLookupSoundness.Output (ZMod 17) (ZMod 17) Unit 1 0 0) :=
  pure ((none, none), some (emptyPacket, ()))
private noncomputable def rejectLater (_ : PreparedLookupPair.Packet (ZMod 17) (ZMod 17) 1 0 0) (_ : Unit) :
    OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2)) Bool :=
  (fun _ => false) <$> sharedSamplingResponse 0

/-- Disabled preparation cannot invoke even a callback that would return true. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (CompletedLookupPair.program
      (pure ((none, none), none) : OracleComp (CheckpointExecution.Spec unifSpec Unit (Fin 4) (Fin 2))
        (PreparedLookupSoundness.Output (ZMod 17) (ZMod 17) Unit 1 0 0))
      (fun _ _ => (fun _ => true) <$> sharedSamplingResponse 0))).run workerStart =
      pure ((((none, none), none), false), workerStart) := by
  simp [CompletedLookupPair.program, CompletedLookupPair.finish, SharedContinuation.program,
    simulateQ_pure, StateT.run_pure]

/-- Rejecting later work retains its real hash and final state. -/
example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (CompletedLookupPair.program propose rejectLater)).run workerStart =
      pure ((((none, none), some (emptyPacket, ())), false), workerStep workerStart 2 0) := by
  simp only [CompletedLookupPair.program, SharedContinuation.program, propose, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, pure_bind, CompletedLookupPair.finish, rejectLater,
    simulateQ_map, StateT.run_map, sharedSamplingResponse_run, map_pure]

/-- All proposals could be wrong, yet rejected final executions have zero
accepted-wrong-opening probability. Removing the acceptance gate gives one. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (CompletedLookupPair.program propose rejectLater)).run workerStart}[
      outcome.1.2 = true ∧ (fun _ : PreparedLookupSoundness.Prepared (ZMod 17) (ZMod 17) Unit 1 0 0 => True) outcome.1.1.2] = 0 := by
  simp [CompletedLookupPair.program, SharedContinuation.program, propose, CompletedLookupPair.finish, rejectLater,
    simulateQ_map, StateT.run_map, prEvent_norm]

private noncomputable def basis : Module.Basis (Fin 1) (ZMod 17) (ZMod 17) := Module.Basis.singleton _ _
private def zeroClaims : Fin 1 → Fin 1 → ZMod 17 := fun _ _ => 0
private noncomputable def schedule : LookupPairSequence.Schedule (ZMod 17) Unit Unit (Fin 4) (Fin 2) 0 3 where
  sumSend := fun _ _ _ => pure (fun _ => 0, ())
  sumAfter := fun _ _ => pure ()
  zeroSend := fun _ _ _ _ _ => pure (fun _ => 0, ())
  zeroAfter := fun _ _ _ _ => pure ()
private def io : PreparedLookupSoundness.Interface (ZMod 17) (ZMod 17) Unit Unit (Fin 4) (Fin 2) 1 1 0 where
  receive := fun _ _ _ _ => pure (⟨zeroClaims, 1⟩, ())
  bindValues := fun _ _ _ _ _ => pure ()

private theorem zeroCheck (eqPoint : Fin 0 → ZMod 17) :
    LookupPairTerminal.check basis (d := 1) (padding := 0) (c := 0) (row := 0) rfl eqPoint Fin.elim0
      1 0 1 (by decide) zeroClaims 1 0 = true := by
  have parsed : PaddedExtension.element (padding := 0) basis (0 : Fin 1 → ZMod 17) = some 0 := by
    simpa only [map_zero] using PaddedExtension.element_encode (padding := 0) basis (0 : ZMod 17)
  have projected : (ExtensionLookupTerminal.sourceQuery basis (padding := 0) (c := 0) (row := 0) rfl (Fin.elim0 : Fin 0 → ZMod 17)).finish
      (0 : Fin 1 → ZMod 17) = 0 := Matrix.mulVec_zero _
  have decoded : LookupPairTerminal.decodeSources basis (padding := 0) (c := 0) (row := 0) rfl (Fin.elim0 : Fin 0 → ZMod 17) 1 zeroClaims =
      some (fun _ : Fin 1 => 0) := by
    change (PaddedExtension.element (padding := 0) basis ((ExtensionLookupTerminal.sourceQuery basis (padding := 0) (c := 0) (row := 0) rfl Fin.elim0).finish
      (0 : Fin 1 → ZMod 17))).bind (fun first : ZMod 17 => some (Fin.cons first (Fin.elim0 : Fin 0 → ZMod 17))) = some (fun _ : Fin 1 => (0 : ZMod 17))
    rw [projected, parsed]
    simp only [Option.bind_some]
    congr 1
    funext i
    fin_cases i
    rfl
  rw [LookupPairTerminal.check, decoded]
  simp only [decide_eq_true_eq]
  simp [ExtensionLookupIdentity.terminal, NativePrefixMask.evaluatePrefix, ExtensionLookupIdentity.equality]

private noncomputable def uncheckedPreparation := PreparedLookupSoundness.program 17 (by decide) (by decide) schedule
  basis (padding := 0) (c := 0) (row := 0) rfl 1 0 1 (by decide) 2 2 () io

/-- A callback that simply returns true is deliberately not a PCS verifier.
With zero rounds, wrong helper values can pass the local field check, so the
remaining accepted-wrong-opening term cannot be discarded. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (CompletedLookupPair.program uncheckedPreparation (fun _ _ => pure true))).run workerStart}[outcome.1.2 = true] = 1 := by
  simp [uncheckedPreparation, PreparedLookupSoundness.program, PreparedLookupPair.program,
    LookupPairSequence.program, LookupPairSequence.sumProgram, LookupPairSequence.afterSum, LookupPairSequence.zeroProgram,
    PackedSumcheckOracle.program, PreparedLookupPair.prepare, io, zeroCheck, CompletedLookupPair.program,
    CompletedLookupPair.finish, SharedContinuation.program, ScalarSumcheckQuery.point,
    prEvent_norm]

end LookupCompletionSmoke

namespace VariableHeightBatchSmoke

private def heights : Bool → ℕ | false => 1 | true => 2
private def shape (cfg : Bool) := BinaryTree.Skeleton.perfect (heights cfg)
private noncomputable def start : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) shape :=
  ⟨columnStart.hash, MerkleTreeMultiExtractability.ExtractorState.empty, false⟩
private def hashCall (input : ColumnInput) : OracleComp (SharedSequence.Shared Bool ColumnInput (Fin 2)) (Fin 2) :=
  liftM ((SharedSequence.Shared Bool ColumnInput (Fin 2)).query (.inr (.inl input)))
private theorem hashCall_run (input : ColumnInput)
    (state : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) shape)
    (answer : Fin 2) (known : state.hash.cache input = some answer) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 shape)
      (hashCall input)).run state = pure (answer, CheckpointExecution.afterHash columnEncoding 0 shape state
        (CachedHashHandler.observe state.hash input answer state.hash.cache)) := by
  rw [hashCall, simulateQ_spec_query]
  change (fun result => (result.1, CheckpointExecution.afterHash columnEncoding 0 shape state result.2)) <$>
    (CachedHashHandler.handler input).run state.hash = _
  rw [CachedHashHandler.run_cached state.hash input answer known, map_pure]
private noncomputable def protocol : NativeBatchVerifier.Protocol (ZMod 17) ColumnInput (Fin 2) Bool Unit (Fin 2) 1 0 1 2 2 2 (heights false) where
  encoding := columnEncoding
  domain := checkedDomain
  root := 0
  query := selectedBatchQuery
  values := selectedBatchValues
  testResponse := batchTestMessage
  groupResponse := batchGroupMessage
  prepare := fun memory => (fun _ => 1 - memory) <$> hashCall (.inl [0])
  respond := fun _ _ => (fun _ => ()) <$> hashCall (.inr (0, 1))
  receiveColumns := fun _ _ => (fun _ => (poolColumns, 1)) <$> hashCall (.inl [0])
  choose := fun _ _ columns _ memory =>
    if bound : memory.val < columns.length then pure (some ⟨memory.val, bound⟩, 1 - memory)
    else pure (none, memory)
  fuel := fun _ _ _ => 4

example : heights false ≠ heights true := by decide

/-- A native height-one worker pool runs on the same state signature as a
height-two context; final acceptance and all five issued hashes are retained. -/
example : (fun outcome => (outcome.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 shape)
      (NativeBatchVerifier.next protocol 0 selectedBatchData.1)).run start = pure (true, 8) := by
  simp only [NativeBatchVerifier.next, protocol, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    hashCall_run (.inl [0]) start 0 rfl, map_pure, pure_bind]
  have checked : NativeBatchChecks.columnsCheck poolColumns selectedBatchData.1.2 = true := by
    simp only [NativeBatchChecks.columnsCheck, selectedBatchIndices]
    rfl
  erw [checked]
  rfl

end VariableHeightBatchSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PreparedLookupSoundness.partial_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedLookupSoundness.partial_supported

/-- info: 'FormalProof4FHE.HasteBoots.PreparedLookupSoundness.full_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedLookupSoundness.full_supported

/-- info: 'FormalProof4FHE.HasteBoots.PreparedLookupSoundness.partial_retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedLookupSoundness.partial_retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.PreparedLookupSoundness.full_retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PreparedLookupSoundness.full_retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.CompletedLookupPair.support_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedLookupPair.support_accepts

/-- info: 'FormalProof4FHE.HasteBoots.CompletedLookupPair.probability_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedLookupPair.probability_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompletionSoundness.partial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupCompletionSoundness.partial_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompletionSoundness.full_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupCompletionSoundness.full_bound

/-- info: 'FormalProof4FHE.HasteBoots.VariableHeightBatchVerifier.checks_wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VariableHeightBatchVerifier.checks_wrong_implies_arithmetic_or_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.VariableHeightBatchVerifier.step_wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VariableHeightBatchVerifier.step_wrong_implies_arithmetic_or_disagreement

namespace DependentRootSmoke

private def height : Bool → ℕ | false => 1 | true => 2
private noncomputable def run (index : Bool) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2))
      (ShortCircuitSequence.StepResult (Fin (height index)) (Fin 2)) :=
  match index with
  | false => (fun _ => ⟨⟨0, by decide⟩, 1 - memory, true⟩) <$> sharedSamplingResponse 0
  | true => (fun _ => ⟨⟨1, by decide⟩, 1 - memory, false⟩) <$> oraclePackedAfter () 0

/-- The root's result type and trusted tag vary together. Rejection of the
second step keeps both real calls and skips the third step. -/
example : (fun outcome => (outcome.1.results.map (fun entry => (entry.1, entry.2.1, entry.2.2.val)),
    outcome.1.memory, outcome.1.accepted, outcome.2)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (DependentShortCircuitSequence.program run [false, true, false] 0)).run workerStart =
      pure ([(false, false, 0), (true, true, 1)], 0, false, workerStep (workerStep workerStart 2 0) 3 1) := by
  simp only [DependentShortCircuitSequence.program, ShortCircuitSequence.program,
    DependentShortCircuitSequence.step, DependentShortCircuitSequence.pack, run,
    simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    sharedSamplingResponse_run, oraclePackedAfter_run, map_pure, pure_bind,
    Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure, List.map_cons, List.map_nil]
  rfl

end DependentRootSmoke

namespace HeterogeneousRootSmoke

private def heights : Bool → ℕ | false => 1 | true => 2
private def tag : Bool → Bool := id
private def layout : Bool → HeterogeneousBatchOpening.Layout
  | false => ⟨0, 1, 2, 2, 2⟩
  | true => ⟨1, 0, 1, 1, 3⟩
private def shape (cfg : Bool) := BinaryTree.Skeleton.perfect (heights cfg)
private noncomputable def start : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) shape :=
  ⟨columnStart.hash, MerkleTreeMultiExtractability.ExtractorState.empty, false⟩
private theorem hashCall_run (input : ColumnInput)
    (state : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) shape)
    (answer : Fin 2) (known : state.hash.cache input = some answer) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 shape)
      (VariableHeightBatchSmoke.hashCall input)).run state = pure (answer, CheckpointExecution.afterHash columnEncoding 0 shape state
        (CachedHashHandler.observe state.hash input answer state.hash.cache)) :=
  VariableHeightBatchSmoke.hashCall_run input state answer known
private noncomputable def domain (factor : Bool) : Fin (2 ^ heights (tag factor)) ↪ ZMod 17 :=
  NativePackedInterpolation.consecutive 17 (by cases factor <;> decide)
private noncomputable instance (factor : Bool) :
    SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) (2 ^ (layout factor).front) 1) :=
  SampleableType.ofFintype _
private noncomputable instance (factor : Bool) :
    SampleableType (Fin (layout factor).queries → Fin (2 ^ heights (tag factor))) := SampleableType.ofFintype _

private noncomputable def tallProtocol : NativeBatchVerifier.Protocol (ZMod 17) ColumnInput (Fin 2) Bool Unit (Fin 2) 1 1 0 1 1 3 2 where
  encoding := columnEncoding
  domain := domain true
  root := 1
  query := fun _ => .cons (fun _ _ _ => 1) .nil
  values := fun _ _ => 0
  testResponse := fun _ _ _ _ => 0
  groupResponse := fun _ _ _ _ _ => 0
  prepare := pure
  respond := fun _ _ => pure ()
  receiveColumns := fun _ _ => (fun _ => ([], 1)) <$> VariableHeightBatchSmoke.hashCall (.inr (0, 1))
  choose := fun _ _ _ _ memory => pure (none, memory)
  fuel := fun _ _ _ => 5

private noncomputable def build (_ : (Bool → Fin 2) × Unit) (_ : Unit) (factor : Bool) :
    HeterogeneousBatchOpening.Protocol (ZMod 17) ColumnInput (Fin 2) Bool Unit (Fin 2) 1 heights tag layout factor :=
  match factor with
  | false => VariableHeightBatchSmoke.protocol
  | true => tallProtocol

private def emission : (Bool → Fin 2) × Unit := (fun _ => 0, ())

/-- The trusted emitted root overrides a behavior factory's different root. -/
example : (HeterogeneousBatchOpening.protocol columnEncoding heights tag layout domain build emission () true).root = 0 := rfl

/-- Layouts really differ in front/suffix, claims, m, query count and height. -/
example : (layout false).front ≠ (layout true).front ∧ (layout false).suffix ≠ (layout true).suffix ∧
    (layout false).claims ≠ (layout true).claims ∧ (layout false).m ≠ (layout true).m ∧
    (layout false).queries ≠ (layout true).queries ∧ heights false ≠ heights true := by decide

/-- A disabled actual heterogeneous opening phase retains query-selection work
and invokes neither root factory nor any fresh native batch draws. -/
example : (fun outcome => (outcome.1.1, outcome.1.2.results.length, outcome.1.2.memory,
    outcome.1.2.accepted, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 shape)
      (HeterogeneousBatchOpening.continuation columnEncoding domain build
        (fun _ => (fun _ => ()) <$> VariableHeightBatchSmoke.hashCall (.inr (0, 1)))
        (fun _ _ => false) (fun _ _ => 0) [false, true] emission)).run start =
      pure ((), 0, 0, false, 4) := by
  simp only [HeterogeneousBatchOpening.continuation, SharedContinuation.program,
    simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    hashCall_run (.inr (0, 1)) start 0 rfl, map_pure, pure_bind,
    Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure]
  rfl

private def tallSample : InteractiveAuthenticatedOpening.SampleData (ZMod 17) Unit 2 1 2 3 :=
  ((fun _ _ => 0, ()), fun _ => 0)

/-- The second layout uses the actual height-two native verifier. Missing
columns reject before workers, retaining the provider's real hash. -/
example : (fun outcome => (outcome.1.2, outcome.1.1.2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 shape)
      (NativeBatchVerifier.next tallProtocol 0 tallSample)).run start = pure (false, 1, 4) := by
  simp only [NativeBatchVerifier.next, tallProtocol, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map,
    hashCall_run (.inr (0, 1)) start 0 rfl, map_pure, pure_bind,
    NativeBatchChecks.columnsCheck, List.isEmpty_nil, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure]
  rfl

/-- A real fresh-sampled height-two batch rejects and prevents the height-one
batch's prepare, samples and hashes. The trusted sigma tag is the attempted
root, even though its behavior factory proposed a different root digest. -/
example : (fun outcome => (outcome.1.results.map Prod.fst,
    outcome.1.results.map (fun entry => entry.2.1), outcome.1.accepted,
    outcome.1.memory, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 shape)
      (DependentShortCircuitSequence.program
        (fun factor => NativeBatchVerifier.step
          (HeterogeneousBatchOpening.protocol columnEncoding heights tag layout domain build emission () factor))
        [true, false] 0)).run start =
      (do
        let _ ← $ᵗ (InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) (2 ^ (layout true).front) 1)
        let _ ← $ᵗ (Fin (layout true).queries → Fin (2 ^ heights (tag true)))
        pure ([true], [true], false, 1, 4)) := by
  dsimp only [layout, heights, tag]
  simp only [layout, heights, DependentShortCircuitSequence.program, DependentShortCircuitSequence.step,
    DependentShortCircuitSequence.pack, ShortCircuitSequence.program,
    HeterogeneousBatchOpening.protocol, build, tallProtocol, NativeBatchVerifier.step, NativeBatchVerifier.sampledStep,
    StoppingJointMatrixOpening.step, StoppingJointMatrixOpening.checkedNext,
    InteractiveSampling.complete, InteractiveSampling.program, NativeBatchVerifier.next,
    simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp,
    bind_map_left, simulateQ_pure, StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind,
    hashCall_run (.inr (0, 1)) start 0 rfl,
    NativeBatchChecks.columnsCheck, List.isEmpty_nil, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, reduceIte]
  rfl

end HeterogeneousRootSmoke

/-- info: 'FormalProof4FHE.HasteBoots.DependentShortCircuitSequence.support_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DependentShortCircuitSequence.support_step

/-- info: 'FormalProof4FHE.HasteBoots.DependentShortCircuitSequence.accepted_cache_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DependentShortCircuitSequence.accepted_cache_results

/-- info: 'FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening.snapshots_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HeterogeneousBatchOpening.snapshots_recorded

/-- info: 'FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HeterogeneousBatchOpening.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HeterogeneousBatchOpening.soundness_from_empty

namespace StagedRootSmoke

private def tag (_ : Unit ⊕ Unit) : Unit := ()
private def heights (_ : Unit) : ℕ := 1
private def first : StagedHeterogeneousBatchOpening.SourceEmission Unit (Fin 2) (Fin 2) := (fun _ => 0, 0)
private def second (coin : Fin 2) : StagedHeterogeneousBatchOpening.HelperEmission Unit (Fin 2) (Fin 2 × Fin 2) :=
  (fun _ => 1, coin, 0)
private noncomputable def sourceCommit : OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2))
    (StagedHeterogeneousBatchOpening.SourceEmission Unit (Fin 2) (Fin 2)) :=
  (fun answer => (fun _ => 0, answer)) <$> terminalHash 2
private noncomputable def helperCommit (source : StagedHeterogeneousBatchOpening.SourceEmission Unit (Fin 2) (Fin 2)) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2))
      (StagedHeterogeneousBatchOpening.HelperEmission Unit (Fin 2) (Fin 2 × Fin 2)) := do
  let coin ← PrivateSampling.embed Unit (Fin 4) (Fin 2) ($ᵗ (Fin 2))
  let answer ← terminalHash (if source.2 = 0 then 3 else 1)
  pure (fun _ => answer, coin, source.2)
private noncomputable def rejectLater (_ : StagedHeterogeneousBatchOpening.SourceEmission Unit (Fin 2) (Fin 2))
    (_ : StagedHeterogeneousBatchOpening.HelperEmission Unit (Fin 2) (Fin 2 × Fin 2)) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) Bool :=
  (fun _ => false) <$> terminalHash 1
private noncomputable def firstState := workerStep workerStart 2 0
private noncomputable def beforeMiddle := RecordRoots.state workerShape [((), 0)] firstState
private noncomputable def secondState := workerStep beforeMiddle 3 1
private noncomputable def beforeLater := RecordRoots.state workerShape [((), 1)] secondState
private noncomputable def finalState := workerStep beforeLater 1 0

/-- Actual pair coins are drawn between the two recordings. Both private
memories, all issued hashes and the rejecting suffix's final state survive. -/
private theorem witness_run :
    StagedCommitmentPrefix.witness overlappingMerkleEncoding 0 workerShape
      (StagedHeterogeneousBatchOpening.sourceRequests tag [()])
      (StagedHeterogeneousBatchOpening.helperRequests tag [()])
      sourceCommit helperCommit rejectLater workerStart =
      (do
        let coin ← $ᵗ (Fin 2)
        pure ((first, firstState), (second coin, secondState), (false, finalState))) := by
  simp only [StagedCommitmentPrefix.witness, sourceCommit, helperCommit, rejectLater,
    simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    terminalHash_run 2 workerStart 0 rfl, map_pure, pure_bind,
    PrivateSampling.run_probComp, bind_map_left, ite_true,
    StagedHeterogeneousBatchOpening.sourceRequests, StagedHeterogeneousBatchOpening.helperRequests,
    List.map_cons, List.map_nil, tag]
  erw [terminalHash_run 3 beforeMiddle 1 rfl]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, bind_assoc]
  erw [terminalHash_run 1 beforeLater 0 rfl]
  simp only [pure_bind]
  rfl

/-- Source checkpoints really keep the pre-pair log, while helpers keep the
later log; even rejection retains the subsequent issued work and private coin. -/
example : (fun outcome =>
    ((StagedHeterogeneousBatchOpening.snapshots heights tag outcome.1 outcome.2.1 (.inl ())).cumulativeLog.length,
     (StagedHeterogeneousBatchOpening.snapshots heights tag outcome.1 outcome.2.1 (.inr ())).cumulativeLog.length,
     outcome.2.2.2.hash.log.length, outcome.2.2.1, outcome.2.1.1.2)) <$>
    StagedCommitmentPrefix.witness overlappingMerkleEncoding 0 workerShape
      (StagedHeterogeneousBatchOpening.sourceRequests tag [()])
      (StagedHeterogeneousBatchOpening.helperRequests tag [()])
      sourceCommit helperCommit rejectLater workerStart =
      (do let coin ← $ᵗ (Fin 2); pure (4, 5, 6, false, coin, 0)) := by
  rw [witness_run]
  simp only [map_bind, map_pure]
  rfl

/-- Replacing the source checkpoint by the helper-stage log is detectably
wrong even when both roots use the same context tag. -/
example : (StagedHeterogeneousBatchOpening.snapshots heights tag (first, firstState)
    (second 0, secondState) (.inl ())).cumulativeLog ≠ secondState.hash.log := by decide

/-- The proof-only snapshots erase to the actual recorded program, including
both roots and the rejecting callback's last hash call. -/
example : (fun outcome => (outcome.1.2.2, outcome.2.hash.log.length, outcome.2.checkpoints.checkpoints.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (StagedCommitmentPrefix.program
        (StagedHeterogeneousBatchOpening.sourceRequests tag [()])
        (StagedHeterogeneousBatchOpening.helperRequests tag [()]) sourceCommit helperCommit rejectLater)).run workerStart =
      (do let _ ← $ᵗ (Fin 2); pure (false, 6, 2)) := by
  rw [← StagedCommitmentPrefix.project_witness]
  simp only [Functor.map_map]
  rw [witness_run]
  simp only [map_bind, map_pure]
  rfl

example : StagedHeterogeneousBatchOpening.factors ([0, 1] : List (Fin 2)) ([0, 1, 2] : List (Fin 3)) =
    [.inr 0, .inr 1, .inr 2, .inl 0, .inl 1] := rfl

end StagedRootSmoke

/-- info: 'FormalProof4FHE.HasteBoots.StagedCommitmentPrefix.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedCommitmentPrefix.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.StagedCommitmentPrefix.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedCommitmentPrefix.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.RecordedHeterogeneousBatchOpening.reduce_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecordedHeterogeneousBatchOpening.reduce_wrong

/-- info: 'FormalProof4FHE.HasteBoots.RecordedHeterogeneousBatchOpening.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecordedHeterogeneousBatchOpening.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.StagedHeterogeneousBatchOpening.factors_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedHeterogeneousBatchOpening.factors_complete

/-- info: 'FormalProof4FHE.HasteBoots.StagedHeterogeneousBatchOpening.snapshots_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedHeterogeneousBatchOpening.snapshots_roots

/-- info: 'FormalProof4FHE.HasteBoots.StagedHeterogeneousBatchOpening.snapshots_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedHeterogeneousBatchOpening.snapshots_recorded

/-- info: 'FormalProof4FHE.HasteBoots.StagedHeterogeneousBatchOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedHeterogeneousBatchOpening.soundness_from_empty

namespace LookupOpeningFamilySmoke

private noncomputable def basis := ExtensionQuerySmoke.basis
private def geometry : LookupOpeningFamily.Geometry 1 0 1 3 where
  front := fun _ => 0
  suffix := fun root => match root with | .inl _ => 0 | .inr _ => 1
  m := fun _ => 1
  queries := fun _ => 1
  sourceArity := fun _ => rfl
  helperArity := fun _ => rfl

private noncomputable def packets : LookupOpeningFamily.Packets (ZMod 17) (ZMod 17) 2 1 1 3 := fun pair =>
  ⟨⟨ScalarSumcheckQuery.query 1 ![0], fun _ => (pair.val : ZMod 17) + 1⟩,
   ![0], ⟨ScalarSumcheckQuery.query 1 ![1], fun _ => 0⟩,
   ⟨fun _ => ![3, 5], (pair.val : ZMod 17) + 9⟩⟩
private def heights (_ : Unit) : ℕ := 2
private def tag (_ : LookupOpeningFamily.Root 1 3) : Unit := ()
private noncomputable def fakeHelper :
    NativeBatchVerifier.Protocol (ZMod 17) ColumnInput (Fin 2) Unit Unit Unit 2 0 1 2 1 1 2 where
  encoding := columnEncoding
  domain := NativePackedInterpolation.consecutive 17 (by decide)
  root := 0
  query := fun _ => .cons (fun _ => 0) .nil
  values := fun _ _ => 12
  testResponse := fun _ _ _ _ => 0
  groupResponse := fun _ _ _ _ _ => 0
  prepare := pure
  respond := fun _ _ => pure ()
  receiveColumns := fun memory _ => pure ([], memory)
  choose := fun _ _ _ _ memory => pure (none, memory)
  fuel := fun _ _ _ => 0
private def helperTable (cell : MatrixFold.Cube 1) : Fin 2 → ZMod 17 := if cell.1 then ![8, 7] else ![4, 9]

/-- Three repetitions give three raw source claims, but each helper root
still has exactly its sum/identity pair. Physical root dimensions differ. -/
example : (LookupOpeningFamily.layout geometry (.inl (0 : Fin 1))).claims = 3 ∧
    (LookupOpeningFamily.layout geometry (.inr (0 : Fin 3))).claims = 2 ∧
    geometry.suffix (.inl 0) ≠ geometry.suffix (.inr 0) := by decide

/-- The second pair's encoded claims preserve [sum, identity] order and
cannot be replaced by the behavior factory's constant claim vectors. -/
example : (LookupOpeningFamily.bind (heights := heights) (tag := tag) basis (padding := 1) rfl geometry packets
    (.inr (1 : Fin 3)) fakeHelper).values (0 : Fin 2) = ![2, 0] ∧
    (LookupOpeningFamily.bind (heights := heights) (tag := tag) basis (padding := 1) rfl geometry packets
      (.inr (1 : Fin 3)) fakeHelper).values (1 : Fin 2) = ![10, 0] := by
  constructor
  · change PaddedExtension.encode (padding := 1) basis (2 : ZMod 17) = _
    exact ExtensionQuerySmoke.encode_eq 2
  · change PaddedExtension.encode (padding := 1) basis (10 : ZMod 17) = _
    exact ExtensionQuerySmoke.encode_eq 10

private theorem sum_fold : (LookupOpeningFamily.helperQuery (padding := 1) basis geometry packets (0 : Fin 3) (0 : Fin 2)).fold helperTable = ![4, 0] := by
  change (ExtensionQuery.coefficientsQuery (padding := 1) basis (![0] : Fin 1 → ZMod 17)).evaluate helperTable = _
  rw [ExtensionQuery.coefficients_evaluate]
  simp only [ExtensionQuery.evaluate, basis, ExtensionQuerySmoke.decode_eq, ExtensionQuerySmoke.encode_eq]
  decide

/-- Trusted helper query construction actually changes the authenticated
fold from the factory's forged zero query to the original helper sum query. -/
example : ((LookupOpeningFamily.bind (heights := heights) (tag := tag) basis (padding := 1) rfl geometry packets
    (.inr (0 : Fin 3)) fakeHelper).query (0 : Fin 2)).fold helperTable ≠
    (fakeHelper.query 0).fold helperTable := by
  change (LookupOpeningFamily.helperQuery (padding := 1) basis geometry packets (0 : Fin 3) (0 : Fin 2)).fold helperTable ≠ _
  rw [sum_fold]
  decide

/-- Source roots authenticate raw original vectors, even for zero row
variables; the scalar bridge's local post-map must not replace PCS values. -/
example : LookupOpeningFamily.values (padding := 1) basis geometry packets (.inl (0 : Fin 1)) (0 : Fin 3) = ![3, 5] := rfl

private theorem finished_source :
    (ExtensionLookupTerminal.sourceQuery (padding := 1) basis (c := 1) (row := 0) rfl
      (ScalarSumcheckQuery.point (packets 0).zeroClaim.query)).finish (![3, 5] : Fin 2 → ZMod 17) = ![5, 0] := by
  change ExtensionQuery.laneMatrix (padding := 1) basis
    (ExtensionQuery.laneWeights (d := 1) (padding := 1) (FlatMatrixFold.index 1).symm (![1] : Fin 1 → ZMod 17)) *ᵥ
      (![3, 5] : Fin 2 → ZMod 17) = _
  rw [ExtensionQuerySmoke.laneWeights_one, ExtensionQuery.laneMatrix_mulVec]
  simp only [ExtensionQuery.laneValue, basis, ExtensionQuerySmoke.encode_eq, smul_eq_mul]
  decide

example : (ExtensionLookupTerminal.sourceQuery (padding := 1) basis (c := 1) (row := 0) rfl
    (ScalarSumcheckQuery.point (packets 0).zeroClaim.query)).finish
      (LookupOpeningFamily.values (padding := 1) basis geometry packets (.inl (0 : Fin 1)) (0 : Fin 3)) ≠
    LookupOpeningFamily.values (padding := 1) basis geometry packets (.inl (0 : Fin 1)) (0 : Fin 3) := by
  change (ExtensionLookupTerminal.sourceQuery (padding := 1) basis (c := 1) (row := 0) rfl _).finish ![3, 5] ≠ ![3, 5]
  rw [finished_source]
  decide

/-- Transport into an original zero-row root adds no matrices or committed
view; the three pair queries are raw constant-vector openings. -/
example : (LookupOpeningFamily.queries (padding := 1) basis (c := 1) (row := 0) rfl geometry packets
    (.inl (0 : Fin 1)) (2 : Fin 3)).toList = [] := rfl

end LookupOpeningFamilySmoke

/-- info: 'FormalProof4FHE.HasteBoots.PackedQueryArity.toList' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PackedQueryArity.toList

/-- info: 'FormalProof4FHE.HasteBoots.PackedQueryArity.fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PackedQueryArity.fold

/-- info: 'FormalProof4FHE.HasteBoots.LookupOpeningFamily.source_wrong_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupOpeningFamily.source_wrong_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupOpeningFamily.helper_wrong_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupOpeningFamily.helper_wrong_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupOpeningFamily.any_pair_wrong_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupOpeningFamily.any_pair_wrong_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupGroupedOpening.wrong_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupGroupedOpening.wrong_iff

/-- info: 'FormalProof4FHE.HasteBoots.LookupGroupedOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupGroupedOpening.soundness_from_empty

namespace RepeatedSelectorSmoke

private def packet (value : ZMod 17) : PreparedLookupPair.Packet (ZMod 17) (ZMod 17) 1 0 0 :=
  ⟨⟨.nil, fun _ => 0⟩, Fin.elim0, ⟨.nil, fun _ => 0⟩, ⟨Fin.elim0, value⟩⟩
private noncomputable def run (index : Fin 3) (memory : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2))
      (PreparedLookupSoundness.Output (ZMod 17) (ZMod 17) (Fin 2) 1 0 0) :=
  (fun _ => ((none, none), if index = 1 then none else some (packet (index.val + 3), 1 - memory))) <$>
    terminalHash (if memory = 0 then 2 else 3)
private noncomputable def next (_ : Fin 3 → PreparedLookupPair.Packet (ZMod 17) (ZMod 17) 1 0 0) (_ : Fin 2) :
    OracleComp (SharedSequence.Shared Unit (Fin 4) (Fin 2)) Bool := (fun _ => true) <$> terminalHash 1

/-- The second pair sees the first pair's actual returned memory. Rejection
keeps both issued hashes, records only indices 0/1 and skips index 2. -/
example : (fun outcome => (outcome.1.accepted, outcome.1.results.map Prod.fst, outcome.1.memory.memory,
    (RepeatedLookupSelector.packets (packet 15) outcome.1 0).values.helper,
    outcome.1.memory.packets 1, outcome.1.memory.packets 2, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (RepeatedLookupSelector.program run 0)).run workerStart = pure (false, [0, 1], 1, 3, none, none, 5) := by
  rfl

/-- A rejected actual selector cannot invoke a callback that would hash and
return true; fallback packets cannot forge whole-selector success. -/
example : (fun outcome => (outcome.1.2, outcome.1.1.results.map Prod.fst, outcome.2.hash.log.length)) <$>
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
      (RepeatedLookupCompletion.program run 0 (packet 15) next)).run workerStart = pure (false, [0, 1], 5) := by
  rfl

end RepeatedSelectorSmoke

namespace RepeatedNativeAlgebraSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _
private noncomputable def schedule : LookupPairSequence.Schedule (ZMod 17) (Fin 2) Unit (Fin 4) (Fin 2) 0 3 where
  sumSend := fun _ memory _ => pure (fun _ => 0, memory)
  sumAfter := fun memory _ => pure memory
  zeroSend := fun _ _ _ memory _ => pure (fun _ => 0, memory)
  zeroAfter := fun _ _ memory _ => pure memory
private noncomputable def io : PreparedLookupSoundness.Interface (ZMod 17) (ZMod 17) (Fin 2) Unit (Fin 4) (Fin 2) 1 1 0 where
  receive := fun _ _ _ memory => pure (⟨LookupCompletionSmoke.zeroClaims, 1⟩, memory)
  bindValues := fun _ _ _ _ memory => (fun _ => 1 - memory) <$> terminalHash (if memory = 0 then 2 else 3)
private noncomputable def verifier := RepeatedLookupAlgebra.run 17 (by decide) (by decide)
  (fun _ : Fin 3 => schedule) LookupCompletionSmoke.basis (padding := 0) (c := 0) (row := 0) rfl
  (fun _ => (0, 1)) 1 (by decide) (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17))
  (fun _ => 2) (fun _ => 2) (fun _ => io)
private def fallback : PreparedLookupPair.Packet (ZMod 17) (ZMod 17) 1 1 0 :=
  ⟨⟨.nil, fun _ => 15⟩, Fin.elim0, ⟨.nil, fun _ => 15⟩, ⟨fun _ _ => 15, 15⟩⟩

/-- Three actual native zero-round pair verifiers return their own packets,
carry private memory between bindings and retain all three real binding hashes.
The fallback 15 is never used for a successful packet slot. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) overlappingMerkleEncoding 0 workerShape)
    (RepeatedLookupSelector.program verifier 0)).run workerStart}[
      outcome.1.accepted = true ∧ outcome.1.results.map Prod.fst = [0, 1, 2] ∧
      outcome.1.memory.memory = 1 ∧ outcome.2.hash.log.length = 6 ∧
      ∀ index, (RepeatedLookupSelector.packets fallback outcome.1 index).values.helper = 1] = 1 := by
  have indices : List.finRange 3 = [(0 : Fin 3), 1, 2] := rfl
  simp [RepeatedLookupSelector.program, indices, Fin.forall_fin_succ, ShortCircuitSequence.program, RepeatedLookupSelector.step,
    RepeatedLookupSelector.advance, RepeatedLookupSelector.packets, verifier, RepeatedLookupAlgebra.run,
    PreparedLookupSoundness.program, PreparedLookupPair.program, LookupPairSequence.program,
    LookupPairSequence.sumProgram, LookupPairSequence.afterSum, LookupPairSequence.zeroProgram,
    PackedSumcheckOracle.program, PreparedLookupPair.prepare, io, LookupCompletionSmoke.zeroCheck,
    LookupPairArithmetic.tableSum, TupleHash.hash, TupleHash.powers,
    SharedContinuation.program, ScalarSumcheckQuery.point,
    simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    prEvent_norm]

  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [terminalHash_run 2 workerStart 0 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [terminalHash_run 3 (workerStep workerStart 2 0) 1 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [terminalHash_run 2 (workerStep (workerStep workerStart 2 0) 3 1) 0 rfl]
  have finalLength : (workerStep (workerStep (workerStep workerStart 2 0) 3 1) 2 0).hash.log.length = 6 := rfl
  simp [prEvent_norm, finalLength]

end RepeatedNativeAlgebraSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitAccumulator.accepted_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShortCircuitAccumulator.accepted_invariant

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupSelector.advance_provenance' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupSelector.advance_provenance

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupSelector.support_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupSelector.support_step

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupSelector.accepted_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupSelector.accepted_packet

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupSelector.selected_arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupSelector.selected_arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupCompletion.accepted_selected_or_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupCompletion.accepted_selected_or_wrong

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupCompletion.support_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupCompletion.support_accepts

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupCompletion.probability_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupCompletion.probability_bound

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupAlgebra.partial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupAlgebra.partial_bound

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupAlgebra.full_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupAlgebra.full_bound

namespace StagedRepeatedLookupSmoke

open RepeatedLookupPCSAlgebra

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _
private def geometry : LookupOpeningFamily.Geometry 0 0 1 3 where
  front := fun _ => 0
  suffix := fun _ => 0
  m := fun _ => 1
  queries := fun _ => 1
  sourceArity := fun _ => rfl
  helperArity := fun _ => rfl
private def heights (_ : Unit) : ℕ := 1
private def tag (_ : LookupOpeningFamily.Root 1 3) : Unit := ()
private noncomputable def domain (_ : LookupOpeningFamily.Root 1 3) : Fin 2 ↪ ZMod 17 := checkedDomain
private noncomputable instance (root : LookupOpeningFamily.Root 1 3) :
    SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) (2 ^ (LookupOpeningFamily.layout geometry root).front) 1) := SampleableType.ofFintype _
private noncomputable instance (root : LookupOpeningFamily.Root 1 3) :
    SampleableType (Fin (LookupOpeningFamily.layout geometry root).queries → Fin (2 ^ heights (tag root))) := SampleableType.ofFintype _
private noncomputable def io : PreparedLookupSoundness.Interface (ZMod 17) (ZMod 17) (Fin 2) Unit ColumnInput (Fin 2) 1 1 0 where
  receive := fun _ _ _ memory => pure (⟨LookupCompletionSmoke.zeroClaims, 1⟩, memory)
  bindValues := fun _ _ _ _ memory => (fun _ => 1 - memory) <$> schemeHash (if memory = 0 then .inl [0] else .inl [1])
private noncomputable def schedule : LookupPairSequence.Schedule (ZMod 17) (Fin 2) Unit ColumnInput (Fin 2) 0 3 where
  sumSend := fun _ memory _ => pure (fun _ => 0, memory)
  sumAfter := fun memory _ => pure memory
  zeroSend := fun _ _ _ memory _ => pure (fun _ => 0, memory)
  zeroAfter := fun _ _ memory _ => pure memory
private noncomputable def algebra (_ : RepeatedLookupPCS.Emission 1 3 (Fin 2) Unit Unit) :
    ScheduleData (ZMod 17) (ZMod 17) (Fin 2) Unit ColumnInput (Fin 2) 1 1 0 3 .full :=
  ⟨fun _ => schedule, fun _ => 2, fun _ => io, 0⟩
private noncomputable def behavior (_ : RepeatedLookupPCS.Emission 1 3 (Fin 2) Unit Unit)
    (_ : RepeatedLookupPCS.Selection (F := ZMod 17) (K := ZMod 17) (Memory := Fin 2)
      (d := 1) (padding := 0) (c := 0) (row := 0) (count := 1) (repetitions := 3))
    (root : LookupOpeningFamily.Root 1 3) :
    HeterogeneousBatchOpening.Protocol (ZMod 17) ColumnInput (Fin 2) Unit Unit (Fin 2) 1 heights tag
      (LookupOpeningFamily.layout geometry) root where
  encoding := columnEncoding
  domain := domain root
  root := 1
  query := fun _ => .nil
  values := fun _ _ => 15
  testResponse := fun _ _ _ _ => 0
  groupResponse := fun _ _ _ _ _ => 0
  prepare := fun memory => schemeHash (if memory = 1 then .inl [1] else .inl [0])
  respond := fun _ _ => pure ()
  receiveColumns := fun memory _ => (fun _ => ([], memory)) <$> schemeHash (.inl [0])
  choose := fun _ _ _ _ memory => pure (none, memory)
  fuel := fun _ _ _ => 0
private def pairs (_ : StagedRepeatedLookup.HelperEmission 3 (Fin 2) Unit) : Fin 3 → StagedRepeatedLookup.Pair (ZMod 17) :=
  fun _ => (0, ⟨1, by decide⟩)
private noncomputable def next := StagedRepeatedLookup.continuation (heights := heights) (tag := tag) (g := geometry)
  columnEncoding .full 17 (by decide) LookupCompletionSmoke.basis (padding := 0) (c := 0) (row := 0) rfl
  1 (by decide) (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17))
  (fun _ _ => 2) pairs algebra domain RepeatedNativeAlgebraSmoke.fallback behavior
private def sourceCommit : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) (StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit) :=
  pure (fun _ => 0, ())
private def helperCommit (_ : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit) :
    OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) (StagedRepeatedLookup.HelperEmission 3 (Fin 2) Unit) := pure (fun _ => 0, ())
private noncomputable def program := StagedCommitmentPrefix.program
  (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1))
  (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange 3)) sourceCommit helperCommit next

private noncomputable def recorded := RecordRoots.state workerShape [((), 0), ((), 0), ((), 0), ((), 0)] columnStart
private noncomputable def state1 := zeroColumnStep recorded (.inl [0]) 0
private noncomputable def state2 := zeroColumnStep state1 (.inl [1]) 1
private noncomputable def state3 := zeroColumnStep state2 (.inl [0]) 0
private noncomputable def state4 := zeroColumnStep state3 (.inl [1]) 1
private noncomputable def state5 := zeroColumnStep state4 (.inl [0]) 0

/-- The typed staged execution runs three real pair verifiers, then only the
first helper PCS batch. Its computed rejection skips later roots; successful
selector memory reaches PCS, and all five issued hashes and four roots remain. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape) program).run columnStart}[
      outcome.1.2.2.1.accepted = true ∧ outcome.1.2.2.2.accepted = false ∧
      outcome.1.2.2.2.results.map Prod.fst = [.inr (0 : Fin 3)] ∧
      outcome.1.2.2.2.memory = 1 ∧ outcome.2.hash.log.length = 8 ∧ outcome.2.checkpoints.checkpoints.length = 4] = 1 := by
  have sources : List.finRange 1 = [(0 : Fin 1)] := rfl
  have helpers : List.finRange 3 = [(0 : Fin 3), 1, 2] := rfl
  simp [program, StagedCommitmentPrefix.program, sourceCommit, helperCommit, next,
    StagedRepeatedLookup.continuation, RepeatedLookupPCS.program, HeterogeneousBatchOpening.continuation,
    RepeatedLookupPCS.select, RepeatedLookupPCS.enabled, RepeatedLookupPCS.start,
    StagedRepeatedLookup.verifier, RepeatedLookupPCSAlgebra.run, RepeatedLookupAlgebra.run, algebra,
    RepeatedLookupSelector.program, ShortCircuitSequence.program, RepeatedLookupSelector.step, RepeatedLookupSelector.advance,
    PreparedLookupSoundness.program, PreparedLookupPair.program, LookupPairSequence.program,
    LookupPairSequence.sumProgram, LookupPairSequence.afterSum, LookupPairSequence.zeroProgram,
    PackedSumcheckOracle.program, PreparedLookupPair.prepare, io, LookupCompletionSmoke.zeroCheck,
    LookupPairArithmetic.tableSum, TupleHash.hash, TupleHash.powers, pairs, StagedRepeatedLookup.pairValues,
    StagedHeterogeneousBatchOpening.factors, StagedHeterogeneousBatchOpening.emission,
    StagedHeterogeneousBatchOpening.sourceRequests, StagedHeterogeneousBatchOpening.helperRequests,
    DependentShortCircuitSequence.program, DependentShortCircuitSequence.step, DependentShortCircuitSequence.pack,
    NativeBatchVerifier.step, NativeBatchVerifier.sampledStep, StoppingJointMatrixOpening.step,
    StoppingJointMatrixOpening.checkedNext, InteractiveSampling.complete, InteractiveSampling.program,
    NativeBatchVerifier.next, HeterogeneousBatchOpening.protocol, LookupGroupedOpening.build, LookupOpeningFamily.bind,
    behavior, NativeBatchChecks.columnsCheck, geometry, LookupOpeningFamily.layout, heights, tag,
    SharedContinuation.program, ScalarSumcheckQuery.point,
    simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map,
    sources, helpers, prEvent_norm]

  erw [RecordRoots.run_program]
  simp only [pure_bind]
  erw [RecordRoots.run_program]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [0]) recorded 0 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [1]) state1 1 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [0]) state2 0 rfl]
  simp only [pure_bind]
  erw [schemeHash_run (.inl [1]) state3 1 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [0]) state4 0 rfl]
  have logLength : (zeroColumnStep state4 (.inl [0]) 0).hash.log.length = 8 := rfl
  have rootCount : (zeroColumnStep state4 (.inl [0]) 0).checkpoints.checkpoints.length = 4 := rfl
  simp [prEvent_norm, logLength, rootCount]

end StagedRepeatedLookupSmoke

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupPCS.support_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupPCS.support_accepts

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupPCS.reduce_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupPCS.reduce_acceptance

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupPCS.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupPCS.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.RepeatedLookupPCSAlgebra.facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepeatedLookupPCSAlgebra.facts

/-- info: 'FormalProof4FHE.HasteBoots.StagedRepeatedLookup.bad_prefix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedRepeatedLookup.bad_prefix_bound

/-- info: 'FormalProof4FHE.HasteBoots.StagedRepeatedLookup.acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedRepeatedLookup.acceptance_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.sample_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.sample_valid

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.sample_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.sample_supported

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.checked_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.checked_forget

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.sample_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.sample_forget

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.sample_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.sample_law

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.allPass_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.allPass_cons

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.vector_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.vector_probability

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVector.vector_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVector.vector_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVectorMiddle.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVectorMiddle.retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupPairVectorMiddle.staged_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LookupPairVectorMiddle.staged_bound

/-- info: 'FormalProof4FHE.HasteBoots.FrozenLookupSources.allPass_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrozenLookupSources.allPass_iff

/-- info: 'FormalProof4FHE.HasteBoots.StagedPrivateLookup.allPass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedPrivateLookup.allPass_bound

/-- info: 'FormalProof4FHE.HasteBoots.StagedPrivateLookup.false_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedPrivateLookup.false_acceptance_bound

section RejectionSamplingSmoke

open OracleSpec OracleComp

private def acceptedOffsets : Finset (Fin 4) := {1}

private theorem retryRate : RejectionSampling.reject acceptedOffsets = (3 / 4 : ENNReal) := by
  rw [RejectionSampling.reject, SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun candidate : Fin 4 => candidate ∉ acceptedOffsets)).card = 3 := by decide
  rw [count]
  norm_num

/-- A suspended prefix retains its full nonzero failure probability. -/
example : Pr{let result ← RejectionSampling.runPrefix acceptedOffsets 3}[result.1 = none] = (27 / 64 : ENNReal) := by
  rw [RejectionSampling.suspended_probability, retryRate]
  norm_num [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]

example : Pr{let result ← RejectionSampling.runPrefix acceptedOffsets 3}[result.1.elim False (fun x => x = 1)] =
    (37 / 64 : ENNReal) := by
  rw [RejectionSampling.success_probability, retryRate, RejectionSampling.hit_fraction]
  norm_num [acceptedOffsets, Finset.filter_singleton, Finset.sum_range_succ]
  have numeric : ((1 + 3 / 4 + (3 / 4) ^ 2) * (1 / 4) : NNReal) = 37 / 64 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (4 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (64 : NNReal) ≠ 0), ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
    ENNReal.coe_one, ENNReal.coe_ofNat, one_div] using
      congrArg (fun value : NNReal => (value : ENNReal)) numeric

/-- Work includes the rejected attempts and the last attempted candidate even
on suspension; it is not the successful-output probability or its reciprocal. -/
example : RejectionSampling.expectedAttempts acceptedOffsets 3 = (37 / 16 : ENNReal) := by
  rw [RejectionSampling.expectedAttempts_eq_sum, retryRate]
  norm_num [Finset.sum_range_succ]
  have numeric : (1 + 3 / 4 + (3 / 4) ^ 2 : NNReal) = 37 / 16 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (4 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using
      congrArg (fun value : NNReal => (value : ENNReal)) numeric

example : RejectionSampling.totalExpectedAttempts acceptedOffsets = 4 := by
  rw [RejectionSampling.totalExpectedAttempts_fraction]
  norm_num [acceptedOffsets]

example : RejectionSampling.eventProbability acceptedOffsets (fun x => x = 1) = 1 := by
  rw [RejectionSampling.eventProbability_eq_uniform, ProbComp.prEvent_uniformSelectFinset]
  norm_num [acceptedOffsets, Finset.filter_singleton]

example : RejectionSampling.expectedAttempts acceptedOffsets 0 = 0 := by
  rw [RejectionSampling.expectedAttempts_eq_sum]
  simp

/-- Empty domains never complete and have infinite unbounded expected work. -/
example : RejectionSampling.eventProbability (∅ : Finset (Fin 4)) (fun _ => True) = 0 := by
  rw [RejectionSampling.eventProbability_eq_uniform, ProbComp.prEvent_uniformSelectFinset]
  simp

example : RejectionSampling.totalExpectedAttempts (∅ : Finset (Fin 4)) = ⊤ := by
  rw [RejectionSampling.totalExpectedAttempts_fraction]
  norm_num [ENNReal.div_zero]

example : RejectionSampling.totalExpectedAttempts (Finset.univ : Finset (Fin 4)) = 1 := by
  rw [RejectionSampling.totalExpectedAttempts_fraction]
  norm_num [ENNReal.div_self]

/-- This deterministic response tape exercises actual primitive query paths.
The production theorem uses fresh uniform responses, not this test handler. -/
private def retryTape : QueryImpl unifSpec (StateT (List ℕ) Id) := fun query => do
  let tape ← get
  set tape.tail
  pure ⟨tape.headD 0 % (query + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Two rejected draws remain in order before the accepted draw. The loop
stops immediately and leaves the next response unconsumed. -/
example : (simulateQ retryTape (RejectionSampling.runPrefix ({1} : Finset (Fin 2)) 4)).run [0, 0, 1, 0] =
    ((some 1, [0, 0, 1]), [0]) := by rfl

/-- Suspending the same path earlier retains both already issued draws. -/
example : (simulateQ retryTape (RejectionSampling.runPrefix ({1} : Finset (Fin 2)) 2)).run [0, 0, 1, 0] =
    ((none, [0, 0]), [1, 0]) := by rfl

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

/-- Three repeated public poles exclude only one field element; exact work
respects distinct exclusions while the size-only upper bound remains looser. -/
example : RejectionSampling.totalExpectedAttempts
    (ReciprocalDetection.allowed (fun _ : Fin 3 => (0 : ZMod 17))) = (17 / 16 : ENNReal) := by
  rw [ReciprocalRejection.expected_candidates]
  have domain : ReciprocalDetection.allowed (fun _ : Fin 3 => (0 : ZMod 17)) = Finset.univ.erase 0 := by
    ext candidate
    simp [ReciprocalDetection.mem_allowed]
  rw [domain]
  norm_num [ZMod.card]

example : RejectionSampling.totalExpectedAttempts
    (ReciprocalDetection.allowed (fun _ : Fin 3 => (0 : ZMod 17))) ≤ (17 / 13 : ENNReal) := by
  simpa only [ZMod.card, Nat.reduceSub, Nat.cast_ofNat] using
    ReciprocalRejection.expected_candidates_bound (fun _ : Fin 3 => (0 : ZMod 17))

example : (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
    (PrivateSampling.embed Unit ColumnInput (Fin 2)
      (ReciprocalRejection.runPrefix (fun _ : Fin 3 => (0 : ZMod 17)) 3))).run columnStart =
      (fun result => (result, columnStart)) <$>
        ReciprocalRejection.runPrefix (fun _ : Fin 3 => (0 : ZMod 17)) 3 :=
  ReciprocalRejection.runPrefix_state columnEncoding 0 workerShape _ _ columnStart

end RejectionSamplingSmoke

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.success_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.success_succ

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.suspended_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.suspended_probability

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.success_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.success_probability

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.reject_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.reject_lt_one

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.suspension_tends_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.suspension_tends_to_zero

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.hit_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.hit_fraction

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.one_sub_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.one_sub_reject

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.eventProbability_eq_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.eventProbability_eq_uniform

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.expectedAttempts_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.expectedAttempts_succ

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.expectedAttempts_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.expectedAttempts_eq_sum

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.totalExpectedAttempts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.totalExpectedAttempts_eq

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.totalExpectedAttempts_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.totalExpectedAttempts_fraction

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.prefix_event_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.prefix_event_le_uniform

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.totalExpectedAttempts_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.totalExpectedAttempts_finite

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.success_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.success_monotone

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.success_tends_to_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.success_tends_to_uniform

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.expectedAttempts_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.expectedAttempts_monotone

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.expectedAttempts_tends_to_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.expectedAttempts_tends_to_fraction

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalRejection.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalRejection.law

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalRejection.expected_candidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalRejection.expected_candidates

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalRejection.expected_candidates_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalRejection.expected_candidates_bound

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalRejection.suspension_tends_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalRejection.suspension_tends_to_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalRejection.runPrefix_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalRejection.runPrefix_state

section CanonicalByteSamplerSmoke

open OracleSpec OracleComp

/-- Increasing memory addresses contribute increasing powers of 256. -/
example : CanonicalByteMask.decode (![1, 2] : CanonicalByteMask.Bytes 2) = 513 := by decide

example : CanonicalByteMask.decode (CanonicalByteMask.pad (by decide : 2 ≤ 16)
    (![1, 2] : CanonicalByteMask.Bytes 2)) = 513 := by
  rw [CanonicalByteMask.decode_pad]
  decide

/-- The low-bit mask is distinct from reduction modulo the characteristic. -/
example : CanonicalByteMask.masked 5 (![255] : CanonicalByteMask.Bytes 1) = 31 := by decide
example : CanonicalByteMask.masked 5 (![144] : CanonicalByteMask.Bytes 1) = 16 := by decide
example : (255 : ℕ) % 17 = 0 := by decide

example : CanonicalByteSampler.bits 17 = 5 ∧ CanonicalByteSampler.byteCount 17 = 1 := by decide
example : CanonicalByteSampler.bits 257 = 9 ∧ CanonicalByteSampler.byteCount 257 = 2 := by decide

example : CanonicalByteSampler.nativeCandidate 17 (by decide)
    (![144] : CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount 17)) = 16 := by
  erw [CanonicalByteSampler.nativeCandidate_eq]
  decide

/-- Full-width characteristics use the explicit u128-max mask branch. -/
example : CanonicalByteSampler.bits (2 ^ 127 + 1) = 128 ∧
    CanonicalByteSampler.byteCount (2 ^ 127 + 1) = 16 ∧
    CanonicalByteSampler.nativeMask (2 ^ 127 + 1) = 2 ^ 128 - 1 := by decide

example : CanonicalByteSampler.eventProbability 17 (fun value => value = 16) = (1 / 17 : ENNReal) := by
  rw [CanonicalByteSampler.uniform_value 17 (by decide)]
  have singleton := SampleableType.prEvent_uniformSample_eq_singleton (16 : Fin 17)
  refine (prEvent_congr _ _ (fun value => value = (16 : Fin 17)) ?_).trans ?_
  · intro value
    simp only [Fin.ext_iff]
    rfl
  · simpa only [Fintype.card_fin, Nat.cast_ofNat, one_div] using singleton

example (event : ZMod 17 → Prop) : CanonicalByteSampler.eventProbability 17 (fun value => event (value : ZMod 17)) =
    Pr{let value ← $ᵗ (ZMod 17)}[event value] :=
  CanonicalByteSampler.uniform_zmod 17 (by decide) event

example : CanonicalByteSampler.totalExpectedBytes 17 = (32 / 17 : ENNReal) := by
  rw [CanonicalByteSampler.totalExpectedBytes_eq 17 (by decide)]
  rw [show CanonicalByteSampler.byteCount 17 = 1 by decide, show CanonicalByteSampler.bits 17 = 5 by decide]
  norm_num

/-- A power-of-two range accepts every masked candidate, rather than paying
a spurious rejection penalty or selecting an extra bit. -/
example : CanonicalByteSampler.totalExpectedBytes 2 = 1 := by
  rw [CanonicalByteSampler.totalExpectedBytes_eq 2 (by decide)]
  norm_num [CanonicalByteSampler.byteCount, CanonicalByteSampler.bits, ENNReal.div_self]

/-- Both profiles retain exact byte costs before any XOF/hash-work transfer. -/
example : CanonicalByteSampler.bits 18446744069414584321 = 64 ∧
    CanonicalByteSampler.byteCount 18446744069414584321 = 8 := by decide

example : CanonicalByteSampler.bits 2013265921 = 31 ∧
    CanonicalByteSampler.byteCount 2013265921 = 4 := by decide

example : CanonicalByteSampler.totalExpectedBytes 18446744069414584321 =
    (8 : ENNReal) * (((2 ^ 64 : ℕ) : ENNReal) / 18446744069414584321) := by
  rw [CanonicalByteSampler.totalExpectedBytes_eq _ (by decide)]
  rw [show CanonicalByteSampler.byteCount 18446744069414584321 = 8 by decide,
    show CanonicalByteSampler.bits 18446744069414584321 = 64 by decide]
  norm_num

example : CanonicalByteSampler.totalExpectedBytes 2013265921 =
    (4 : ENNReal) * ((2147483648 : ENNReal) / 2013265921) := by
  rw [CanonicalByteSampler.totalExpectedBytes_eq _ (by decide)]
  rw [show CanonicalByteSampler.byteCount 2013265921 = 4 by decide,
    show CanonicalByteSampler.bits 2013265921 = 31 by decide]
  norm_num

/-- Actual byte queries reject 255 and 49 after masking to 31 and 17, then
accept 144 after masking to 16. The raw rejected chunks remain available;
the subsequent byte is not consumed. Modulo-p reduction would accept 255. -/
example : (fun outcome => ((outcome.1.1.map (CanonicalByteMask.masked (CanonicalByteSampler.bits 17)),
      outcome.1.2.map CanonicalByteMask.decode), outcome.2))
    ((simulateQ retryTape (CanonicalByteSampler.runPrefix 17 4)).run [255, 49, 144, 99]) =
      ((some 16, [255, 49, 144]), [99]) := by rfl

/-- A shorter analysis prefix suspends while preserving both rejected chunks. -/
example : (fun outcome => ((outcome.1.1.map (CanonicalByteMask.masked (CanonicalByteSampler.bits 17)),
      outcome.1.2.map CanonicalByteMask.decode), outcome.2))
    ((simulateQ retryTape (CanonicalByteSampler.runPrefix 17 2)).run [255, 49, 144, 99]) =
      ((none, [255, 49]), [144, 99]) := by rfl

/-- A two-byte read uses little-endian order and masks its unused high bits.
The next byte remains unused after the canonical value one is accepted. -/
example : (fun outcome => ((outcome.1.1.map (CanonicalByteMask.masked (CanonicalByteSampler.bits 257)),
      outcome.1.2.map CanonicalByteMask.decode, CanonicalByteSampler.consumedBytes 257 outcome.1), outcome.2))
    ((simulateQ retryTape (CanonicalByteSampler.runPrefix 257 2)).run [1, 2, 99]) =
      ((some 1, [513], 2), [99]) := by rfl

end CanonicalByteSamplerSmoke

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.eventProbability_eq_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.eventProbability_eq_ratio

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.returned_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.returned_mem

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.decode_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.decode_eq_sum

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.decode_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.decode_lt

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.masked_eq_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.masked_eq_mod

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.low_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.low_val

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.split_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.split_snd

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.uniform_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.uniform_low

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.uniform_masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.uniform_masked

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.decode_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.decode_pad

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteMask.decode_pad_lt_u128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteMask.decode_pad_lt_u128

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.bits_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.bits_positive

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.fits

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.modulus_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.modulus_le

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.range_lt_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.range_lt_twice

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.truncated_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.truncated_card

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.runPrefix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.runPrefix_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.hit_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.hit_law

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.hit_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.hit_fraction

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.eventProbability_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.eventProbability_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.uniform_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.uniform_value

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.expected_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.expected_attempts

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.byteCount_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.byteCount_positive

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.byteCount_le_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.byteCount_le_sixteen

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.nativeMask_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.nativeMask_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.expectedBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.expectedBytes_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.totalExpectedBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.totalExpectedBytes_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.expected_attempts_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.expected_attempts_lt_two

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.totalExpectedBytes_lt_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.totalExpectedBytes_lt_twice

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.accepted_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.accepted_nonempty

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.suspension_tends_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.suspension_tends_to_zero

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.expectedBytes_tends_to_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.expectedBytes_tends_to_total

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.uniform_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.uniform_zmod

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.value_tends_to_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.value_tends_to_uniform

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.nativeCandidate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.nativeCandidate_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalByteSampler.returned_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalByteSampler.returned_canonical

section CanonicalCoefficientVectorSmoke

open OracleSpec OracleComp MeasureTheory

/-- Two coefficients are filled in native order; all rejected raw chunks
remain before the first accepted coefficient, and the next byte is unused. -/
example : (fun outcome => ((outcome.1.values.map (fun values => [values 0, values 1]), outcome.1.completed,
      outcome.1.chunks.map CanonicalByteMask.decode, CanonicalCoefficientWork.consumedBytes 17 outcome.1), outcome.2))
    ((simulateQ retryTape (CanonicalCoefficientVector.program 17 3 2)).run [255, 49, 144, 5, 99]) =
      ((some [16, 5], [16, 5], [255, 49, 144, 5], 4), [99]) := by rfl

/-- Suspension while filling the second coefficient preserves the first one,
all work already issued, and skips the third coefficient. -/
example : (fun outcome => ((outcome.1.values.map (fun values => [values 0, values 1, values 2]), outcome.1.completed,
      outcome.1.chunks.map CanonicalByteMask.decode, CanonicalCoefficientWork.consumedBytes 17 outcome.1), outcome.2))
    ((simulateQ retryTape (CanonicalCoefficientVector.program 17 2 3)).run [5, 255, 49, 144, 99]) =
      ((none, [5], [5, 255, 49], 3), [144, 99]) := by rfl

/-- An empty coefficient request reads no bytes. Transcript framing is a
separate obligation and is not claimed to have zero hash cost here. -/
example : (fun outcome => ((outcome.1.values.isSome, outcome.1.completed,
      outcome.1.chunks.map CanonicalByteMask.decode, CanonicalCoefficientWork.consumedBytes 17 outcome.1), outcome.2))
    ((simulateQ retryTape (CanonicalCoefficientVector.program 17 0 0)).run [255, 99]) =
      ((true, [], [], 0), [255, 99]) := by rfl

private theorem oneCompletion : CanonicalCoefficientVector.completion 17 1 = (17 / 32 : ENNReal) := by
  unfold CanonicalCoefficientVector.completion
  rw [CanonicalByteSampler.runPrefix_eq, RejectionSampling.success_probability]
  simp only [Finset.sum_range_one, pow_zero, one_mul]
  have hit := CanonicalByteSampler.hit_fraction 17 (by decide) (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ, Fintype.card_fin] at hit
  rw [hit, show CanonicalByteSampler.bits 17 = 5 by decide]
  norm_num

private theorem oneRead : CanonicalByteSampler.expectedBytes 17 1 = 1 := by
  rw [CanonicalByteSampler.expectedBytes_eq, RejectionSampling.expectedAttempts_eq_sum]
  simp only [Finset.sum_range_one, pow_zero, mul_one]
  rw [show CanonicalByteSampler.byteCount 17 = 1 by decide]
  norm_num

/-- Finite prefixes retain their true joint completion probability, rather
than silently normalizing away either unfinished coefficient. -/
example : Pr{let result ← CanonicalCoefficientVector.program 17 1 2}[result.values.elim False (fun _ => True)] =
    (17 / 32 : ENNReal) ^ 2 := by
  rw [CanonicalCoefficientVector.probability 17 (by decide), oneCompletion]
  simp [prEvent_norm]

example : CanonicalCoefficientVector.eventProbability 17 2 (fun values => values = (![16, 5] : Fin 2 → ZMod 17)) =
    (1 / 289 : ENNReal) := by
  rw [CanonicalCoefficientVector.uniform_values 17 (by decide), SampleableType.prEvent_uniformSample_eq_singleton]
  simp [ZMod.card, one_div]

/-- The second read runs only after the first coefficient completes. -/
example : CanonicalCoefficientWork.expectedBytes 17 1 2 = (1 + 17 / 32 : ENNReal) := by
  rw [CanonicalCoefficientWork.expectedBytes_succ, CanonicalCoefficientWork.expectedBytes_succ,
    CanonicalCoefficientWork.expectedBytes_zero, oneRead, oneCompletion]
  simp

example : CanonicalCoefficientWork.totalExpectedBytes 17 2 = (2 : ENNReal) * (32 / 17) := by
  rw [CanonicalCoefficientWork.totalExpectedBytes_formula 17 (by decide)]
  rw [show CanonicalByteSampler.byteCount 17 = 1 by decide, show CanonicalByteSampler.bits 17 = 5 by decide]
  norm_num

/-- Lookup degree three/six is kept distinct from PCS packing width four/eight. -/
example : CanonicalCoefficientWork.totalExpectedBytes 18446744069414584321 3 =
    (24 : ENNReal) * (((2 ^ 64 : ℕ) : ENNReal) / 18446744069414584321) := by
  rw [CanonicalCoefficientWork.totalExpectedBytes_formula _ (by decide)]
  rw [show CanonicalByteSampler.byteCount 18446744069414584321 = 8 by decide,
    show CanonicalByteSampler.bits 18446744069414584321 = 64 by decide]
  norm_num [← mul_assoc]

example : CanonicalCoefficientWork.totalExpectedBytes 2013265921 6 =
    (24 : ENNReal) * ((2147483648 : ENNReal) / 2013265921) := by
  rw [CanonicalCoefficientWork.totalExpectedBytes_formula _ (by decide)]
  rw [show CanonicalByteSampler.byteCount 2013265921 = 4 by decide,
    show CanonicalByteSampler.bits 2013265921 = 31 by decide]
  norm_num [← mul_assoc]

/-- Coordinate-order fixture; this product module is not a concrete native
extension field implementation or a 128-bit parameter certificate. -/
private noncomputable def coordinateBasis : Module.Basis (Fin 2) (ZMod 17) (Fin 2 → ZMod 17) := Pi.basisFun _ _

example : (fun outcome => ((outcome.1.1.map (fun values => [values 0 1, values 0 0, values 0 1, values 1 0, values 1 1]),
      outcome.1.2.chunks.map CanonicalByteMask.decode, CanonicalCoefficientWork.consumedBytes 17 outcome.1.2), outcome.2))
    ((simulateQ retryTape (CanonicalExtensionSampler.program coordinateBasis 1 2)).run [3, 5, 7, 11, 99]) =
      ((some [5, 3, 5, 7, 11], [3, 5, 7, 11], 4), [99]) := by rfl

private noncomputable def oneCoordinateBasis : Module.Basis (Fin 1) (ZMod 17) (Fin 1 → ZMod 17) := Pi.basisFun _ _

private def traceNext (earlier : Option (Fin 1 → Fin 1 → ZMod 17) × CanonicalCoefficientVector.Result 17 (1 * 1)) :=
  schemeHash (if (earlier.2.chunks.head?.map CanonicalByteMask.decode).getD 0 > 31 then .inl [1] else .inl [0])

private noncomputable def traceShared :=
  SharedContinuation.program (PrivateSampling.embed Unit ColumnInput (Fin 2)
    (CanonicalExtensionSampler.program oneCoordinateBasis 1 1)) traceNext

/-- Two raw accepted chunks yield the same canonical value but expose different
raw traces to the adaptive callback. Its actual cached hash is retained. -/
example : (fun outcome => ((outcome.1.1.1.1.map (fun fields => fields 0 0),
      outcome.1.1.1.2.chunks.map CanonicalByteMask.decode, outcome.1.1.2, outcome.1.2.hash.log.length), outcome.2))
    ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) traceShared).run columnStart)).run [16, 99]) =
      ((some 16, [16], 0, 4), [99]) := by rfl

example : (fun outcome => ((outcome.1.1.1.1.map (fun fields => fields 0 0),
      outcome.1.1.1.2.chunks.map CanonicalByteMask.decode, outcome.1.1.2, outcome.1.2.hash.log.length), outcome.2))
    ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) traceShared).run columnStart)).run [144, 99]) =
      ((some 16, [144], 1, 4), [99]) := by rfl

end CanonicalCoefficientVectorSmoke

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.success_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.success_scaled

/-- info: 'FormalProof4FHE.HasteBoots.OptionalUniformSequence.uniform_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalUniformSequence.uniform_cons

/-- info: 'FormalProof4FHE.HasteBoots.OptionalUniformSequence.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalUniformSequence.probability

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.values_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.values_erasure

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.scalar_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.scalar_law

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.probability

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.completion_tends_to_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.completion_tends_to_one

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.completion_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.completion_monotone

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.completion_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.completion_le_one

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.probability_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.probability_monotone

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.values_tends_to_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.values_tends_to_uniform

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientVector.uniform_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientVector.uniform_values

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.consumed_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.consumed_cons

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.expectedBytes_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.expectedBytes_zero

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.expectedBytes_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.expectedBytes_succ

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.expectedBytes_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.expectedBytes_monotone

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.expectedBytes_tends_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.expectedBytes_tends_to

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.totalExpectedBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.totalExpectedBytes_eq

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalCoefficientWork.totalExpectedBytes_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalCoefficientWork.totalExpectedBytes_formula

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.offset

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.assemble_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.assemble_coordinate

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.raw_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.raw_erasure

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.observation

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.uniform_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.uniform_assembly

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.probability

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.uniform_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.uniform_values

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.expectedBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.expectedBytes

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.totalExpectedBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.totalExpectedBytes

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.private_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.private_state

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalExtensionSampler.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalExtensionSampler.retained_bound

section ByteReciprocalSamplerSmoke

open OracleSpec OracleComp MeasureTheory

private noncomputable def reciprocalBasis : Module.Basis (Fin 1) (ZMod 17) (ZMod 17) := Module.Basis.singleton _ _
private def bytePoleTable : Fin 1 → ZMod 17 := fun _ => 1

/-- Canonical byte rejection and completed-field pole rejection are distinct.
All six bytes remain in the four actual field trials before offset five. -/
example : (fun outcome => ((outcome.1.value, outcome.1.trials.map ByteReciprocalSampler.candidate,
      outcome.1.trials.map (fun trial => trial.2.chunks.map CanonicalByteMask.decode),
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 3 4)).run [0, 16, 255, 49, 144, 5, 99]) =
      ((some 5, [some 0, some 16, some 16, some 5], [[0], [16], [255, 49, 144], [5]], 6), [99]) := by rfl

/-- The third field trial suspends internally after two rejected canonical
chunks. It is not a completed zero candidate and cannot start a fourth trial. -/
example : (fun outcome => ((outcome.1.value, outcome.1.trials.map ByteReciprocalSampler.candidate,
      outcome.1.trials.map (fun trial => trial.2.chunks.map CanonicalByteMask.decode),
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 2 4)).run [0, 16, 255, 49, 144, 5, 99]) =
      ((none, [some 0, some 16, none], [[0], [16], [255, 49]], 4), [144, 5, 99]) := by rfl

/-- A shorter outer prefix retains completed rejected trials and suspends
before consuming another byte; it does not erase their work. -/
example : (fun outcome => ((outcome.1.value, outcome.1.trials.map ByteReciprocalSampler.candidate,
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 3 2)).run [0, 16, 5, 99]) =
      ((none, [some 0, some 16], 2), [5, 99]) := by rfl

example : (fun outcome => ((outcome.1.value, outcome.1.trials.length,
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 0 5)).run [0, 5]) =
      ((none, 1, 0), [0, 5]) := by rfl

example : (fun outcome => ((outcome.1.value, outcome.1.trials.length,
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 3 0)).run [0, 5]) =
      ((none, 0, 0), [0, 5]) := by rfl

private theorem reciprocalDomain : ReciprocalDetection.allowed bytePoleTable = Finset.univ \ {0, 16} := by
  ext value
  simp only [ReciprocalDetection.mem_allowed, bytePoleTable, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_insert, Finset.mem_singleton, true_and]
  have pole : value + (1 : ZMod 17) = 0 ↔ value = 16 := by
    constructor
    · intro zero
      have equal := eq_neg_of_add_eq_zero_left zero
      exact equal.trans (by decide : (-1 : ZMod 17) = 16)
    · intro equal
      subst value
      decide
  simp [pole, not_or]

private theorem outerRate : RejectionSampling.reject (ReciprocalDetection.allowed bytePoleTable) = (2 / 17 : ENNReal) := by
  rw [RejectionSampling.reject, SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter (fun value : ZMod 17 => value ∉ ReciprocalDetection.allowed bytePoleTable)).card = 2 := by
    rw [reciprocalDomain]
    decide
  rw [count]
  norm_num [ZMod.card]

private theorem innerCompletion : ByteReciprocalSampler.completion 17 1 1 = (17 / 32 : ENNReal) := by
  simpa only [ByteReciprocalSampler.completion, Nat.reduceMul, pow_one] using oneCompletion

private theorem nestedRetryRate : ByteReciprocalSampler.completion 17 1 1 *
    RejectionSampling.reject (ReciprocalDetection.allowed bytePoleTable) = (1 / 16 : ENNReal) := by
  rw [innerCompletion, outerRate]
  have numeric : (17 / 32 * (2 / 17) : NNReal) = 1 / 16 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (32 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (17 : NNReal) ≠ 0), ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one] using congrArg (fun value : NNReal => (value : ENNReal)) numeric

/-- The restart probability includes actual inner completion. It is 1/16,
not the full-field rejection probability 2/17 and not normalized by success. -/
example : ByteReciprocalSampler.expectedBytes reciprocalBasis bytePoleTable 1 2 = (1 + 1 / 16 : ENNReal) := by
  rw [ByteReciprocalSampler.expectedBytes_formula (by decide), nestedRetryRate]
  have oneField : CanonicalCoefficientWork.expectedBytes 17 1 (1 * 1) = 1 := by
    rw [CanonicalCoefficientWork.expectedBytes_succ, CanonicalCoefficientWork.expectedBytes_zero, oneRead]
    simp
  rw [oneField]
  norm_num [Finset.sum_range_succ]

example : ByteReciprocalLimit.eventProbability reciprocalBasis bytePoleTable (fun value => value = 5) = (1 / 15 : ENNReal) := by
  rw [ByteReciprocalLimit.law (by decide), ReciprocalDetection.sample, ProbComp.prEvent_uniformSelectFinset, reciprocalDomain]
  have filtered : ((Finset.univ \ ({0, 16} : Finset (ZMod 17))).filter (fun value => value = 5)).card = 1 := by decide
  rw [filtered]
  have domainCard : (Finset.univ \ ({0, 16} : Finset (ZMod 17))).card = 15 := by decide
  rw [domainCard]
  norm_num

example : ByteReciprocalLimit.totalExpectedBytes reciprocalBasis bytePoleTable = (32 / 15 : ENNReal) := by
  rw [ByteReciprocalLimit.totalExpectedBytes_eq (by decide), reciprocalDomain]
  have single : ByteReciprocalLimit.fieldCost 17 1 = (32 / 17 : ENNReal) := by
    rw [ByteReciprocalLimit.fieldCost, CanonicalByteSampler.totalExpectedBytes_eq 17 (by decide)]
    rw [show CanonicalByteSampler.byteCount 17 = 1 by decide, show CanonicalByteSampler.bits 17 = 5 by decide]
    norm_num
  rw [single]
  have domainCard : (Finset.univ \ ({0, 16} : Finset (ZMod 17))).card = 15 := by decide
  rw [domainCard]
  norm_num [ZMod.card]
  have numeric : (32 / 17 * (17 / 15) : NNReal) = 32 / 15 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (17 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (15 : NNReal) ≠ 0), ENNReal.coe_ofNat] using
      congrArg (fun value : NNReal => (value : ENNReal)) numeric

/-- Repeated poles keep their true distinct-domain cost, even after composing
all canonical byte and field retries. -/
example : ByteReciprocalLimit.totalExpectedBytes reciprocalBasis (fun _ : Fin 3 => (0 : ZMod 17)) = 2 := by
  rw [ByteReciprocalLimit.totalExpectedBytes_eq (by decide)]
  have domain : ReciprocalDetection.allowed (fun _ : Fin 3 => (0 : ZMod 17)) = Finset.univ.erase 0 := by
    ext value
    simp [ReciprocalDetection.mem_allowed]
  rw [domain]
  have single : ByteReciprocalLimit.fieldCost 17 1 = (32 / 17 : ENNReal) := by
    rw [ByteReciprocalLimit.fieldCost, CanonicalByteSampler.totalExpectedBytes_eq 17 (by decide)]
    rw [show CanonicalByteSampler.byteCount 17 = 1 by decide, show CanonicalByteSampler.bits 17 = 5 by decide]
    norm_num
  rw [single]
  norm_num [ZMod.card]
  have numeric : (32 / 17 * (17 / 16) : NNReal) = 2 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (17 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat] using
      congrArg (fun value : NNReal => (value : ENNReal)) numeric

private def nestedNext (earlier : OptionalRejectionLoop.Result (ZMod 17) (ByteReciprocalSampler.Trial 17 1 (ZMod 17))) :=
  schemeHash (if earlier.trials.length > 1 then .inl [1] else .inl [0])

private noncomputable def nestedShared := SharedContinuation.program
  (PrivateSampling.embed Unit ColumnInput (Fin 2) (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 3 4)) nestedNext

/-- A trace-aware continuation observes the actual rejected trial, keeps its
cached hash call, and cannot replace the previously sampled offset. -/
example : (fun outcome => ((outcome.1.1.1.value, outcome.1.1.1.trials.length,
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1.1.1, outcome.1.1.2,
      outcome.1.2.hash.log.length), outcome.2))
    ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) nestedShared).run columnStart)).run [0, 5, 99]) =
      ((some 5, 2, 2, 1, 4), [99]) := by rfl

end ByteReciprocalSamplerSmoke

/-- info: 'FormalProof4FHE.HasteBoots.OptionalUniformSequence.bind_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalUniformSequence.bind_probability

/-- info: 'FormalProof4FHE.HasteBoots.RejectionSampling.one_step_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionSampling.one_step_probability

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.value_erasure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.value_erasure

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.returned_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.returned_accept

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.value_success_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.value_success_succ

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.value_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.value_probability

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.probability

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.success_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.success_scaled

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionLoop.event_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionLoop.event_le_uniform

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionWork.consumed_cons' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionWork.consumed_cons

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionWork.expectedCost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionWork.expectedCost_zero

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionWork.expectedCost_succ_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionWork.expectedCost_succ_raw

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionWork.expectedCost_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionWork.expectedCost_succ

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionWork.expectedCost_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionWork.expectedCost_formula

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.singleton_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.singleton_uniform

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.accepted_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.accepted_eq

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.candidate_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.candidate_law

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.returned_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.returned_allowed

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.event_le_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.event_le_ideal

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.head_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.head_cost

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.expectedBytes_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.expectedBytes_formula

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.private_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.private_state

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalSampler.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalSampler.retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.geometric_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.geometric_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.geometric_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.geometric_ne_top

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.completion_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.completion_monotone

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.completion_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.completion_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.fieldCost_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.fieldCost_ne_top

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.rate_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.rate_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.probability_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.probability_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.probability_monotone_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.probability_monotone_inner

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.probability_monotone_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.probability_monotone_outer

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.probability_iSup_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.probability_iSup_inner

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.law

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.completion_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.completion_probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.work_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.work_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.work_monotone_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.work_monotone_inner

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.work_iSup_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.work_iSup_inner

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.totalExpectedBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.totalExpectedBytes_eq

/-- info: 'FormalProof4FHE.HasteBoots.ByteReciprocalLimit.totalExpectedBytes_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteReciprocalLimit.totalExpectedBytes_bound

section ByteLookupPairSmoke

open OracleSpec OracleComp MeasureTheory

private def bytePairTable : Fin 2 → Fin 2 → ZMod 17 := ![![0, 1], ![1, 0]]

/-- The actual challenge changes the domain: two coincident poles at y=1
become distinct at y=2. This is not a pair of independent uniform fields. -/
example : (ReciprocalDetection.allowed (ByteLookupPairSampler.hashes bytePairTable (1 : ZMod 17))).card = 15 := by decide
example : (ReciprocalDetection.allowed (ByteLookupPairSampler.hashes bytePairTable (2 : ZMod 17))).card = 14 := by decide

/-- Y itself rejects a byte before completing. Both stages retain their
raw traces, and all five bytes are charged before returning the pair. -/
example : (fun outcome => ((outcome.1.value,
      outcome.1.hashTrial.2.chunks.map CanonicalByteMask.decode,
      outcome.1.offsetTrials.map (fun last => last.trials.map ByteReciprocalSampler.candidate),
      ByteLookupPairWork.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairSampler.program reciprocalBasis bytePairTable 2 2 4)).run [255, 1, 0, 16, 15, 99]) =
      ((some (1, 15), [255, 1], some [some 0, some 16, some 15], 5), [99]) := by rfl

/-- Changing Y changes which offsets are rejected. The same offset fifteen
which succeeded above now fails, and its work remains charged. -/
example : (fun outcome => ((outcome.1.value,
      outcome.1.offsetTrials.map (fun last => last.trials.map ByteReciprocalSampler.candidate),
      ByteLookupPairWork.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairSampler.program reciprocalBasis bytePairTable 2 2 4)).run [2, 15, 5, 99]) =
      ((some (2, 5), some [some 15, some 5], 3), [99]) := by rfl

/-- An unfinished Y starts no reciprocal trial and retains all first bytes. -/
example : (fun outcome => ((outcome.1.value, outcome.1.offsetTrials.isNone,
      outcome.1.hashTrial.2.chunks.map CanonicalByteMask.decode,
      ByteLookupPairWork.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairSampler.program reciprocalBasis bytePairTable 2 3 4)).run [255, 49, 2, 5, 99]) =
      ((none, true, [255, 49], 2), [2, 5, 99]) := by rfl

/-- A suspended reciprocal trial keeps the completed Y and both raw bytes
from that unfinished trial, without starting another field trial. -/
example : (fun outcome => ((outcome.1.value, ByteReciprocalSampler.candidate outcome.1.hashTrial,
      outcome.1.offsetTrials.map (fun last => last.trials.map (fun trial => trial.2.chunks.map CanonicalByteMask.decode)),
      ByteLookupPairWork.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairSampler.program reciprocalBasis bytePairTable 2 2 4)).run [2, 255, 49, 5, 99]) =
      ((none, some 2, some [[255, 49]], 3), [5, 99]) := by rfl

example : (fun outcome => ((outcome.1.value, outcome.1.offsetTrials.isNone,
      ByteLookupPairWork.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairSampler.program reciprocalBasis bytePairTable 0 3 4)).run [2, 5]) =
      ((none, true, 0), [2, 5]) := by rfl

example : (fun outcome => ((outcome.1.value, outcome.1.offsetTrials.map (fun last => last.trials.length),
      ByteLookupPairWork.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairSampler.program reciprocalBasis bytePairTable 2 3 0)).run [2, 5]) =
      ((none, some 0, 1), [5]) := by rfl

example : ByteLookupPairLimit.eventProbability reciprocalBasis bytePairTable (fun _ => True) = 1 :=
  ByteLookupPairLimit.completion_probability (by decide) reciprocalBasis bytePairTable (by decide)

example : ByteLookupPairWork.expectedBytes reciprocalBasis bytePairTable 0 2 4 = 0 := by
  rw [ByteLookupPairWork.expectedBytes_formula (by decide)]
  simp [ByteReciprocalSampler.completion, CanonicalCoefficientVector.completion,
    CanonicalCoefficientWork.expectedBytes, CanonicalCoefficientVector.program,
    CanonicalByteSampler.runPrefix, CanonicalCoefficientWork.consumedBytes, evalDist_pure]

/-- Finite reciprocal completion really depends on Y. No global successful
completion scalar is silently inserted when composing the pair. -/
private theorem conditionalOne (y : ZMod 17) (domainSize : ℕ)
    (cardinality : (ReciprocalDetection.allowed (ByteLookupPairSampler.hashes bytePairTable y)).card = domainSize) :
    ByteLookupPairSampler.conditional reciprocalBasis bytePairTable 1 1 (fun _ => True) y =
      (17 / 32 : ENNReal) * ((domainSize : ENNReal) / 17) := by
  rw [ByteLookupPairSampler.conditional, ByteReciprocalSampler.probability (by decide), innerCompletion]
  simp only [Finset.sum_range_one, pow_zero, one_mul]
  congr 1
  rw [RejectionSampling.hit, SampleableType.prEvent_uniformSample]
  have filtered : (Finset.univ.filter (fun r : ZMod 17 =>
      r ∈ ReciprocalDetection.allowed (ByteLookupPairSampler.hashes bytePairTable y) ∧ True)) =
        ReciprocalDetection.allowed (ByteLookupPairSampler.hashes bytePairTable y) := by ext r; simp
  rw [filtered, cardinality]
  norm_num [ZMod.card]

example : ByteLookupPairSampler.conditional reciprocalBasis bytePairTable 1 1 (fun _ => True) (1 : ZMod 17) =
    (17 / 32 : ENNReal) * (15 / 17) := conditionalOne 1 15 (by decide)

example : ByteLookupPairSampler.conditional reciprocalBasis bytePairTable 1 1 (fun _ => True) (2 : ZMod 17) =
    (17 / 32 : ENNReal) * (14 / 17) := conditionalOne 2 14 (by decide)

/-- Starting no reciprocal trial still incurs the first-challenge bytes,
including first-challenge suspension outcomes in the unconditional mean. -/
example : ByteLookupPairWork.expectedBytes reciprocalBasis bytePairTable 1 2 0 = 1 := by
  rw [ByteLookupPairWork.expectedBytes_formula (by decide)]
  simp only [ByteReciprocalSampler.expectedBytes_formula (p := 17) (by decide) reciprocalBasis, Finset.range_zero, Finset.sum_empty, mul_zero]
  rw [CanonicalCoefficientWork.expectedBytes_succ, CanonicalCoefficientWork.expectedBytes_zero, oneRead]
  simp

end ByteLookupPairSmoke

/-- info: 'FormalProof4FHE.HasteBoots.OptionalUniformSequence.successful_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalUniformSequence.successful_expectation

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.value_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.value_erasure

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.ideal_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.ideal_probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.event_le_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.event_le_ideal

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.single_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.single_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.returned_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.returned_allowed

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairSampler.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairSampler.retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairLimit.sum_iSup_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairLimit.sum_iSup_nat

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairLimit.iSup_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairLimit.iSup_hash

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairLimit.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairLimit.law

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairLimit.single_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairLimit.single_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairLimit.completion_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairLimit.completion_probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairWork.expectedBytes_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairWork.expectedBytes_formula

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairWork.work_iSup_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairWork.work_iSup_hash

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairWork.totalExpectedBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairWork.totalExpectedBytes_eq

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairWork.totalExpectedBytes_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairWork.totalExpectedBytes_bound


section ByteLookupVectorSmoke

open OracleSpec OracleComp MeasureTheory

/-- Three fresh calls read different Y values and use their corresponding
reciprocal domains. Both earlier rejected offsets remain charged. -/
example : (fun outcome => ((outcome.1.values.map List.ofFn, outcome.1.completed,
      outcome.1.trials.map ByteLookupPairSampler.Result.value,
      ByteLookupPairVector.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 4 3)).run [2, 15, 5, 1, 15, 0, 16, 1, 99]) =
      ((some [(2, 5), (1, 15), (0, 1)], [(2, 5), (1, 15), (0, 1)],
        [some (2, 5), some (1, 15), some (0, 1)], 8), [99]) := by rfl

/-- Suspension during Y in the second repetition preserves the first pair
and all bytes from the second draw. The third repetition never starts. -/
example : (fun outcome => ((outcome.1.values.isNone, outcome.1.completed,
      outcome.1.trials.map (fun trial => trial.hashTrial.2.chunks.map CanonicalByteMask.decode),
      ByteLookupPairVector.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 4 3)).run [2, 5, 255, 49, 1, 15, 99]) =
      ((true, [(2, 5)], [[2], [255, 49]], 4), [1, 15, 99]) := by rfl

/-- A partial reciprocal draw in repetition two retains its completed Y,
its rejected offset, and both incomplete raw chunks, after repetition one. -/
example : (fun outcome => ((outcome.1.values.isNone, outcome.1.completed,
      outcome.1.trials.map (fun trial => trial.offsetTrials.map (fun last => last.trials.map
        (fun field => field.2.chunks.map CanonicalByteMask.decode))),
      ByteLookupPairVector.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 4 3)).run [1, 15, 2, 15, 255, 49, 5, 99]) =
      ((true, [(1, 15)], [some [[15]], some [[15], [255, 49]]], 6), [5, 99]) := by rfl

/-- Zero repetitions succeeds with an empty vector and consumes no byte. -/
example : (fun outcome => ((outcome.1.values.map List.ofFn, outcome.1.completed, outcome.1.trials.length,
      ByteLookupPairVector.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 4 0)).run [2, 5, 99]) =
      ((some [], [], 0, 0), [2, 5, 99]) := by rfl

/-- A completed Y with no started reciprocal trial suspends the first pair;
no later repetition or fallback pair is supplied. -/
example : (fun outcome => ((outcome.1.values.isNone, outcome.1.completed, outcome.1.trials.length,
      ByteLookupPairVector.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 0 3)).run [2, 5, 99]) =
      ((true, [], 1, 1), [5, 99]) := by rfl

example : ByteLookupPairVector.allEventProbability reciprocalBasis bytePairTable 3 (fun _ => True) = 1 :=
  ByteLookupPairVector.completion_probability (by decide) reciprocalBasis bytePairTable (by decide) 3

example : ByteLookupPairVector.totalExpectedBytes reciprocalBasis bytePairTable 3 =
    ByteLookupPairWork.totalExpectedBytes reciprocalBasis bytePairTable * 3 :=
  ByteLookupPairVector.totalExpectedBytes_eq (by decide) reciprocalBasis bytePairTable (by decide) 3

private def byteVectorBadSource : Fin 1 → Fin 2 → ZMod 17 := fun _ => ![1, 1]

/-- A bad original source remains fixed before all three genuine repetitions. -/
example : Pr{let result ← ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 4 3}[
      result.values.elim False (ObservedOptionalVector.All
        (TupleLookupPair.Passes byteVectorBadSource bytePairTable (fun _ => 1)))] ≤
      TupleLookupPair.error 17 2 1 2 ^ 3 := by
  exact ByteLookupPairVector.finite_bound (char := 17) (by decide) reciprocalBasis byteVectorBadSource bytePairTable
    (fun _ => 1) (by decide) (by decide) (by decide) 2 2 4 3

end ByteLookupVectorSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.values_erasure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.values_erasure

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.all_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.all_cons

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.view_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.view_probability

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.probability

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.returned_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.returned_property

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.consumed_cons' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.consumed_cons

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.expectedCost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.expectedCost_zero

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.expectedCost_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.expectedCost_succ

/-- info: 'FormalProof4FHE.HasteBoots.ObservedOptionalVector.expectedCost_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedOptionalVector.expectedCost_formula

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.iSup_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.iSup_diagonal

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.iSup_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.iSup_power

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.probability_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.probability_mono

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.law

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.probability_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.probability_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.work_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.work_mono

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.work_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.work_law

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairDiagonal.work_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairDiagonal.work_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.finite_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.finite_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.law

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.completion_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.completion_probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.lookup_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.lookup_law

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.expectedBytes_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.expectedBytes_formula

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.work_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.work_monotone

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.totalExpectedBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.totalExpectedBytes_eq

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.totalExpectedBytes_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.totalExpectedBytes_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.returned_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.returned_nonzero

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairVector.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairVector.retained_bound


section ByteLookupTypedMiddleSmoke

open OracleSpec OracleComp MeasureTheory

/-- Proof-only typing retains both the actual vector and every raw byte. -/
example : (fun outcome => ((outcome.1.values.map (fun values => List.ofFn (ByteLookupPairTyped.forget values)),
      outcome.1.raw.completed, ByteLookupPairVector.consumedBytes outcome.1.raw), outcome.2))
    ((simulateQ retryTape (ByteLookupPairTyped.sample reciprocalBasis bytePairTable 2 2 4 2)).run [2, 15, 5, 1, 15, 99]) =
      ((some [(2, 5), (1, 15)], [(2, 5), (1, 15)], 5), [99]) := by rfl

/-- Suspension stays optional; a typed fallback vector is never introduced. -/
example : (fun outcome => ((outcome.1.values.isNone, outcome.1.raw.completed,
      ByteLookupPairVector.consumedBytes outcome.1.raw), outcome.2))
    ((simulateQ retryTape (ByteLookupPairTyped.sample reciprocalBasis bytePairTable 2 2 4 2)).run [2, 5, 255, 49, 1, 15, 99]) =
      ((true, [(2, 5)], 4), [1, 15, 99]) := by rfl

private def byteHelperBuild (raw : ByteLookupPairTyped.Raw 17 1 (ZMod 17) 2)
    (_values : Fin 2 → StagedRepeatedLookup.Pair (ZMod 17)) :
    OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2))
      (StagedRepeatedLookup.HelperEmission 2 (Fin 2) (List ((ZMod 17) × (ZMod 17)))) := do
  let digest ← schemeHash (if ByteLookupPairVector.consumedBytes raw > 4 then .inl [1] else .inl [0])
  pure (fun _ => digest, [(9, 9), (9, 9)])

private noncomputable def byteHelperProgram :=
  ByteLookupPairMiddle.program reciprocalBasis bytePairTable 2 2 4 2 byteHelperBuild

/-- The builder observes real raw work and makes its cached hash call. Its
opaque memory contains a different vector, but cannot replace the trusted
verifier input, which keeps the actual sampled pairs and all earlier bytes. -/
example : (fun outcome => ((outcome.1.1.1.values.map (fun values => List.ofFn (ByteLookupPairTyped.forget values)),
      (ByteLookupPairMiddle.completed outcome.1.1).map (fun helper =>
        (List.ofFn (ByteLookupPairTyped.forget helper.2.1), helper.1 0, helper.2.2)),
      ByteLookupPairVector.consumedBytes outcome.1.1.1.raw, outcome.1.2.hash.log.length), outcome.2))
    ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) byteHelperProgram).run columnStart)).run [2, 15, 5, 1, 15, 99]) =
      ((some [(2, 5), (1, 15)], some ([(2, 5), (1, 15)], 1, [(9, 9), (9, 9)]), 5, 4), [99]) := by rfl

/-- Suspension in repetition two preserves the partial sample and skips the
helper builder's hash entirely; the cached transcript still has length three. -/
example : (fun outcome => ((outcome.1.1.1.values.isNone, outcome.1.1.2.isNone,
      (ByteLookupPairMiddle.completed outcome.1.1).isNone, outcome.1.1.1.raw.completed,
      ByteLookupPairVector.consumedBytes outcome.1.1.1.raw, outcome.1.2.hash.log.length), outcome.2))
    ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) byteHelperProgram).run columnStart)).run [2, 5, 255, 49, 1, 15, 99]) =
      ((true, true, true, [(2, 5)], 4, 3), [1, 15, 99]) := by rfl

example : Pr{let observed ← ByteLookupPairTyped.sample reciprocalBasis bytePairTable 2 2 4 2}[
      observed.values.elim False (LookupPairVector.AllPass byteVectorBadSource bytePairTable (fun _ => 1))] ≤
      TupleLookupPair.error 17 2 1 2 ^ 2 :=
  ByteLookupPairTyped.finite_bound (char := 17) (by decide) reciprocalBasis byteVectorBadSource bytePairTable
    (fun _ => 1) (by decide) (by decide) (by decide) 2 2 4 2

private def byteHelperNext (helper : LookupPairVectorMiddle.Emission (ZMod 17) (Fin 2)
    (List ((ZMod 17) × (ZMod 17))) 2) :
    OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) (List ((ZMod 17) × (ZMod 17)) × Fin 2) := do
  let digest ← schemeHash (.inl [0])
  pure (List.ofFn (ByteLookupPairTyped.forget helper.2.1), digest)

private noncomputable def byteStagedWitness := StagedCommitmentPrefix.witness columnEncoding 0 workerShape
  (fun _ : Unit => [((), (0 : Fin 2))])
  (fun _ => ByteLookupPairMiddle.helperRequests (fun helper => [((), helper.1 0)]))
  (pure ()) (fun _ => byteHelperProgram)
  (fun _ => ByteLookupPairMiddle.continueWith byteHelperNext) columnStart

set_option maxHeartbeats 800000 in
/-- The saved source state precedes actual byte sampling; helper hashes and
later verifier work appear only in their later states, using the same vector. -/
example : (fun outcome => ((outcome.1.1.2.hash.log.length,
      outcome.1.2.1.2.hash.log.length, outcome.1.2.2.2.hash.log.length,
      outcome.1.2.2.1, ByteLookupPairVector.consumedBytes outcome.1.2.1.1.1.raw), outcome.2))
    ((simulateQ retryTape byteStagedWitness).run [2, 15, 5, 1, 15, 99]) =
      ((3, 4, 5, some ([(2, 5), (1, 15)], 0), 5), [99]) := by rfl

/-- A suspended sample skips both helper construction and the later verifier.
Its original source snapshot, partial values and four bytes remain retained. -/
example : (fun outcome => ((outcome.1.1.2.hash.log.length,
      outcome.1.2.1.2.hash.log.length, outcome.1.2.2.2.hash.log.length,
      outcome.1.2.2.1.isNone, outcome.1.2.1.1.1.raw.completed,
      ByteLookupPairVector.consumedBytes outcome.1.2.1.1.1.raw), outcome.2))
    ((simulateQ retryTape byteStagedWitness).run [2, 5, 255, 49, 1, 15, 99]) =
      ((3, 3, 3, true, [(2, 5)], 4), [1, 15, 99]) := by rfl

end ByteLookupTypedMiddleSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.checked_forget' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.checked_forget

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.sample_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.sample_raw

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.value_event' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.value_event

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.sample_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.sample_values

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.event_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.event_law

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.expectedBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.expectedBytes

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairTyped.finite_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairTyped.finite_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.completed_none' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.completed_none

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.completed_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.completed_values

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.completed_raw' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.completed_raw

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.after_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.after_none

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.continueWith_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.continueWith_none

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.helperRequests_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.helperRequests_none

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.allPass_sampled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.allPass_sampled

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.retained_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.retained_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupPairMiddle.staged_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupPairMiddle.staged_bound


/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookup.allPass_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookup.allPass_iff

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookup.allPass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookup.allPass_bound


namespace StagedRepeatedLookupSmoke

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

open OracleSpec OracleComp

private noncomputable local instance byteMatrixSamples : ∀ root : LookupOpeningFamily.Root 1 3,
    SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod 17)
      (2 ^ (LookupOpeningFamily.layout geometry root).front) (1 + 0)) :=
  fun _ => (show SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod 17) 1 1) from SampleableType.ofFintype _)
private noncomputable local instance byteQuerySamples : ∀ root : LookupOpeningFamily.Root 1 3,
    SampleableType (Fin (LookupOpeningFamily.layout geometry root).queries → Fin (2 ^ heights (tag root))) :=
  fun _ => (show SampleableType (Fin 1 → Fin 2) from SampleableType.ofFintype _)

private def forgetByteEmission (emission : RepeatedLookupPCS.Emission 1 3 (Fin 2) Unit
    (LookupPairVectorMiddle.Memory (ZMod 17) Unit 3)) : RepeatedLookupPCS.Emission 1 3 (Fin 2) Unit Unit :=
  (emission.1, emission.2.1, (emission.2.2.1, emission.2.2.2.2))

private noncomputable def byteNativeNext := OptionalStagedLookup.continuation (heights := heights) (tag := tag) (g := geometry)
  columnEncoding .full 17 (by decide) LookupCompletionSmoke.basis (padding := 0) (c := 0) (row := 0) rfl
  1 (by decide) (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) (fun _ _ => 2)
  LookupPairVectorMiddle.pairs
  (fun _ emission => algebra (forgetByteEmission emission))
  (ByteLookupPairMiddle.completed (p := 17) (degree := 1)) domain RepeatedNativeAlgebraSmoke.fallback
  (fun _ emission => behavior (forgetByteEmission emission))

private noncomputable def byteNativeMiddle (_ : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit) :=
  ByteLookupPairMiddle.program (Cfg := Unit) (Input := ColumnInput) reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 2 2 4 3
    (fun _ _ => pure (fun _ => (0 : Fin 2), ()))

private noncomputable def byteNativeProgram := StagedCommitmentPrefix.program
  (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1))
  (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit byteNativeMiddle byteNativeNext


private noncomputable def byteNativePrefix := do
  let first ← sourceCommit
  let _ ← RecordRoots.program (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1) first)
  let second ← byteNativeMiddle first
  let _ ← RecordRoots.program (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag first second)
  pure (first, second)

private noncomputable def byteNativePrefixRun :=
  ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
    columnEncoding 0 workerShape) byteNativePrefix).run columnStart)).run [0, 1, 0, 1, 0, 1, 99])

/-- The actual byte prefix retains all three pairs and all six bytes before
native algebra starts; it records the same four original/helper roots. -/
example : (byteNativePrefixRun.1.1.2.1.values.map (fun values => List.ofFn (ByteLookupPairTyped.forget values)),
      ByteLookupPairVector.consumedBytes byteNativePrefixRun.1.1.2.1.raw,
      byteNativePrefixRun.1.2.hash.log.length, byteNativePrefixRun.1.2.checkpoints.checkpoints.length,
      byteNativePrefixRun.2) = (some [(0, 1), (0, 1), (0, 1)], 6, 3, 4, [99]) := by rfl

private def byteNativeEvent (algebraAccepted pcsAccepted : Bool)
    (roots : List (LookupOpeningFamily.Root 1 3)) (memory : Fin 2) (hashLength rootCount : ℕ) : Prop :=
  algebraAccepted = true ∧ pcsAccepted = false ∧ roots = [.inr (0 : Fin 3)] ∧
    memory = 1 ∧ hashLength = 8 ∧ rootCount = 4

/-- After that actual byte prefix, every supported ideal native-coin run
executes all three pair verifiers and only the first helper PCS batch. The
computed PCS rejection skips later roots, retaining all five native hashes. -/
example : Pr{let outcome ← (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
    (byteNativeNext byteNativePrefixRun.1.1.1 byteNativePrefixRun.1.1.2)).run byteNativePrefixRun.1.2}[
      outcome.1.elim False (fun native => byteNativeEvent native.1.accepted native.2.accepted
        (native.2.results.map Prod.fst) native.2.memory outcome.2.hash.log.length outcome.2.checkpoints.checkpoints.length)] = 1 := by
  have completedPairs : ByteLookupPairMiddle.completed byteNativePrefixRun.1.1.2 =
      some ((fun _ => (0 : Fin 2)), ((fun _ : Fin 3 => ((0 : ZMod 17), ⟨1, by decide⟩)), ())) := by
    apply congrArg some
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext index
      fin_cases index <;> rfl
    · rfl
  have incoming : byteNativePrefixRun.1.2 = recorded := by rfl
  have original : byteNativePrefixRun.1.1.1 = ((fun _ => (0 : Fin 2)), ()) := by rfl
  rw [incoming, original]
  simp only [byteNativeNext, OptionalStagedLookup.continuation]
  rw [completedPairs, simulateQ_map, StateT.run_map, prEvent_map]
  simp only [Option.elim_some]
  unfold byteMatrixSamples byteQuerySamples
  have sources : List.finRange 1 = [(0 : Fin 1)] := rfl
  have helpers : List.finRange 3 = [(0 : Fin 3), 1, 2] := rfl
  simp [LookupPairVectorMiddle.pairs,
    StagedRepeatedLookup.continuation, RepeatedLookupPCS.program, HeterogeneousBatchOpening.continuation,
    RepeatedLookupPCS.select, RepeatedLookupPCS.enabled, RepeatedLookupPCS.start,
    StagedRepeatedLookup.verifier, RepeatedLookupPCSAlgebra.run, RepeatedLookupAlgebra.run, algebra,
    RepeatedLookupSelector.program, ShortCircuitSequence.program, RepeatedLookupSelector.step, RepeatedLookupSelector.advance,
    PreparedLookupSoundness.program, PreparedLookupPair.program, LookupPairSequence.program,
    LookupPairSequence.sumProgram, LookupPairSequence.afterSum, LookupPairSequence.zeroProgram,
    PackedSumcheckOracle.program, PreparedLookupPair.prepare, io, LookupCompletionSmoke.zeroCheck,
    LookupPairArithmetic.tableSum, TupleHash.hash, TupleHash.powers, StagedRepeatedLookup.pairValues,
    StagedHeterogeneousBatchOpening.factors, StagedHeterogeneousBatchOpening.emission,
    DependentShortCircuitSequence.program, DependentShortCircuitSequence.step, DependentShortCircuitSequence.pack,
    NativeBatchVerifier.step, NativeBatchVerifier.sampledStep, StoppingJointMatrixOpening.step,
    StoppingJointMatrixOpening.checkedNext, InteractiveSampling.complete, InteractiveSampling.program,
    NativeBatchVerifier.next, HeterogeneousBatchOpening.protocol, LookupGroupedOpening.build, LookupOpeningFamily.bind,
    behavior, NativeBatchChecks.columnsCheck, geometry, LookupOpeningFamily.layout, heights, tag,
    SharedContinuation.program, ScalarSumcheckQuery.point,
    sources, helpers, prEvent_norm]
  unfold RepeatedLookupPCS.Result RepeatedLookupPCS.Selection HeterogeneousBatchOpening.Data
  dsimp only [geometry, LookupOpeningFamily.layout, heights, tag]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]

  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [0]) recorded 0 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [1]) state1 1 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [0]) state2 0 rfl]
  simp only [pure_bind]
  erw [schemeHash_run (.inl [1]) state3 1 rfl]
  simp only [pure_bind]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [PrivateSampling.run_probComp]
  simp only [bind_map_left]
  erw [schemeHash_run (.inl [0]) state4 0 rfl]
  have logLength : (zeroColumnStep state4 (.inl [0]) 0).hash.log.length = 8 := rfl
  have rootCount : (zeroColumnStep state4 (.inl [0]) 0).checkpoints.checkpoints.length = 4 := rfl
  simp [byteNativeEvent, prEvent_norm, logLength, rootCount]



set_option maxHeartbeats 800000 in
/-- An unfinished second repetition runs neither helper construction nor the
native selector/PCS. Only the original source root is recorded, and all four
spent bytes and the completed first pair remain in the real output. -/
example : (fun outcome => ((outcome.1.1.2.2.isNone,
      outcome.1.1.2.1.1.raw.completed, ByteLookupPairVector.consumedBytes outcome.1.1.2.1.1.raw,
      outcome.1.2.hash.log.length, outcome.1.2.checkpoints.checkpoints.length), outcome.2))
    ((simulateQ retryTape ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      columnEncoding 0 workerShape) byteNativeProgram).run columnStart)).run [0, 1, 255, 49, 0, 1, 99]) =
      ((true, [(0, 1)], 4, 3, 1), [0, 1, 99]) := by
  simp only [byteNativeProgram, StagedCommitmentPrefix.program, sourceCommit, byteNativeNext,
    OptionalStagedLookup.continuation, OptionalStagedLookup.helperRequests]
  rfl

end StagedRepeatedLookupSmoke

/-- info: 'FormalProof4FHE.HasteBoots.StagedLookupPrefixFacts.snapshots_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedLookupPrefixFacts.snapshots_recorded

/-- info: 'FormalProof4FHE.HasteBoots.StagedLookupPrefixFacts.reduce_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedLookupPrefixFacts.reduce_acceptance

/-- info: 'FormalProof4FHE.HasteBoots.StagedLookupPrefixFacts.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedLookupPrefixFacts.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.OptionalStagedLookup.continuation_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalStagedLookup.continuation_none

/-- info: 'FormalProof4FHE.HasteBoots.OptionalStagedLookup.continuation_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalStagedLookup.continuation_some

/-- info: 'FormalProof4FHE.HasteBoots.OptionalStagedLookup.bad_prefix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalStagedLookup.bad_prefix_bound

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupSecurity.false_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupSecurity.false_acceptance_bound



section CompletedTraceLimitSmoke

open OracleSpec OracleComp MeasureTheory
open scoped Classical

/-- Equal accepted values do not justify replacing raw observations: the
trace event distinguishes two otherwise identical completed outputs. -/
example : ¬CompletedObservation.LE
    (pure (some (1 : Fin 2), [0, 1])) (pure (some (1 : Fin 2), [1]))
    RejectionTraceOrder.complete := by
  intro ordered
  have impossible := ordered (fun observed => observed.2 = [0, 1])
  norm_num [RejectionTraceOrder.complete, prEvent_norm] at impossible

/-- Growing all three byte depths preserves events on rejected draws, not
just the final typed vector. -/
example : Pr{let observed ← ByteLookupPairTyped.sample reciprocalBasis bytePairTable 1 2 3 2}[
      ByteLookupUnbounded.complete observed ∧ ByteLookupPairVector.consumedBytes observed.raw > 4] ≤
    Pr{let observed ← ByteLookupPairTyped.sample reciprocalBasis bytePairTable 3 4 5 2}[
      ByteLookupUnbounded.complete observed ∧ ByteLookupPairVector.consumedBytes observed.raw > 4] :=
  ByteLookupTraceOrder.typed reciprocalBasis bytePairTable 2 (by decide) (by decide) (by decide) _

/-- The actual two-repetition ideal-byte limit is normalized without
conditioning on a finite prefix's successful mass. -/
example : IsProbabilityMeasure (ByteLookupUnbounded.measure reciprocalBasis bytePairTable 2) :=
  ByteLookupUnbounded.probability (by decide) reciprocalBasis bytePairTable (by decide) 2

example : ByteLookupUnbounded.measure reciprocalBasis bytePairTable 2
    {observed | observed.values = none} = 0 :=
  ByteLookupUnbounded.incomplete_zero reciprocalBasis bytePairTable 2

/-- Adaptive work can inspect the whole rejected-byte cost and return it;
the resulting full observation/result law still has mass one. -/
example : IsProbabilityMeasure (ByteLookupUnbounded.joint reciprocalBasis bytePairTable 2
    (fun observed => pure (ByteLookupPairVector.consumedBytes observed.raw))) :=
  ByteLookupUnbounded.joint_probability (by decide) reciprocalBasis bytePairTable (by decide) 2 _

/-- The actual continuation starts after both rejected candidates and the
accepted draw; it observes trace length three and consumes the next query. -/
example : (fun outcome => (outcome.1.2, outcome.2))
    ((simulateQ retryTape (CompletedContinuation.program
      (RejectionSampling.runPrefix ({1} : Finset (Fin 2)) 4) RejectionTraceOrder.complete
      (fun observed => (fun draw : Fin 2 => (observed.2.length, draw)) <$> ($ᵗ (Fin 2))))).run
        [0, 0, 1, 1, 99]) = (some (3, 1), [99]) := by
  let first : RejectionSampling.Result (Fin 2) := (some 1, [0, 0, 1])
  change (fun outcome => (outcome.1.2, outcome.2))
    ((simulateQ retryTape (if RejectionTraceOrder.complete first then
      (fun last => (first, some last)) <$>
        ((fun draw : Fin 2 => (first.2.length, draw)) <$> ($ᵗ (Fin 2)))
      else pure (first, none))).run [1, 99]) = (some (3, 1), [99])
  have done : RejectionTraceOrder.complete first := by simp [RejectionTraceOrder.complete, first]
  simp only [done, ite_true]
  rfl

/-- The same limit includes an adaptive real cached hash and its final state,
starting from the warm cache/log used by the native verifier regressions. -/
example : IsProbabilityMeasure (SharedCompletedContinuation.measure
    (ByteLookupUnbounded.steps reciprocalBasis bytePairTable 2) ByteLookupUnbounded.complete
    (ByteLookupUnbounded.grows reciprocalBasis bytePairTable 2) columnEncoding 0 workerShape
    (fun observed => schemeHash (if ByteLookupPairVector.consumedBytes observed.raw > 4 then .inl [1] else .inl [0]))
    columnStart) := by
  apply SharedCompletedContinuation.probability
  exact ByteLookupUnbounded.completion_sup (by decide) reciprocalBasis bytePairTable (by decide) 2

/-- The complete raw head marginal survives the actual shared continuation;
its cached hash log is still part of the resulting measure's outcome type. -/
example : SharedCompletedContinuation.measure
    (ByteLookupUnbounded.steps reciprocalBasis bytePairTable 2) ByteLookupUnbounded.complete
    (ByteLookupUnbounded.grows reciprocalBasis bytePairTable 2) columnEncoding 0 workerShape
    (fun observed => schemeHash (if ByteLookupPairVector.consumedBytes observed.raw > 4 then .inl [1] else .inl [0]))
    columnStart {outcome | ByteLookupPairVector.consumedBytes outcome.1.1.raw > 4} =
    ByteLookupUnbounded.measure reciprocalBasis bytePairTable 2
      {observed | ByteLookupPairVector.consumedBytes observed.raw > 4} := by
  simpa only [ByteLookupUnbounded.measure] using SharedCompletedContinuation.earlier_marginal
    (ByteLookupUnbounded.steps reciprocalBasis bytePairTable 2) ByteLookupUnbounded.complete
    (ByteLookupUnbounded.grows reciprocalBasis bytePairTable 2) columnEncoding 0 workerShape
    (fun observed => schemeHash (if ByteLookupPairVector.consumedBytes observed.raw > 4 then .inl [1] else .inl [0]))
    columnStart (fun observed => ByteLookupPairVector.consumedBytes observed.raw > 4)

end CompletedTraceLimitSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.refl

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.trans

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.pure_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.pure_incomplete

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.singleton

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.map

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.complete_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.complete_congr

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.bind

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.bind_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.bind_same

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservation.of_map_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservation.of_map_injective

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceOrder.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceOrder.step

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceOrder.monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceOrder.monotone

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceOrder.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceOrder.canonical

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceOrder.coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceOrder.coefficients

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceOrder.extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceOrder.extension

/-- info: 'FormalProof4FHE.HasteBoots.OptionalTraceOrder.loop_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalTraceOrder.loop_steps

/-- info: 'FormalProof4FHE.HasteBoots.OptionalTraceOrder.loop_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalTraceOrder.loop_step

/-- info: 'FormalProof4FHE.HasteBoots.OptionalTraceOrder.loop_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalTraceOrder.loop_outer

/-- info: 'FormalProof4FHE.HasteBoots.OptionalTraceOrder.vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalTraceOrder.vector

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.trial

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.reciprocal

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.pair

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.vector

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.raw_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.raw_injective

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.typed_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.typed_complete

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupTraceOrder.typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupTraceOrder.typed

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.prefix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.prefix_apply

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.prefix_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.prefix_mono

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.outer_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.outer_apply

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.measurable_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.measurable_outer

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.measure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.measure_apply

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.event_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.event_tends

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.probability

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.incomplete_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.incomplete_zero

/-- info: 'FormalProof4FHE.HasteBoots.CompletedObservationLimit.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedObservationLimit.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.CompletedContinuation.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedContinuation.ordered

/-- info: 'FormalProof4FHE.HasteBoots.CompletedContinuation.earlier_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedContinuation.earlier_event

/-- info: 'FormalProof4FHE.HasteBoots.CompletedContinuation.completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedContinuation.completion

/-- info: 'FormalProof4FHE.HasteBoots.CompletedContinuation.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedContinuation.probability

/-- info: 'FormalProof4FHE.HasteBoots.CompletedContinuation.event_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedContinuation.event_tends

/-- info: 'FormalProof4FHE.HasteBoots.CompletedContinuation.earlier_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedContinuation.earlier_marginal

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.grows

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.event_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.event_tends

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.all_depths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.all_depths

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.incomplete_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.incomplete_zero

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.earlier_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.earlier_marginal

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.completion_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.completion_sup

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.joint_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.joint_probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.lookup_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.lookup_bound

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupUnbounded.joint_lookup_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupUnbounded.joint_lookup_bound

/-- info: 'FormalProof4FHE.HasteBoots.SharedCompletedContinuation.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedCompletedContinuation.run_program

/-- info: 'FormalProof4FHE.HasteBoots.SharedCompletedContinuation.measure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedCompletedContinuation.measure_apply

/-- info: 'FormalProof4FHE.HasteBoots.SharedCompletedContinuation.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedCompletedContinuation.probability

/-- info: 'FormalProof4FHE.HasteBoots.SharedCompletedContinuation.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedCompletedContinuation.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.SharedCompletedContinuation.earlier_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedCompletedContinuation.earlier_marginal


namespace StagedRepeatedLookupSmoke

open OracleSpec OracleComp MeasureTheory
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private noncomputable def byteNativeLimit := StagedByteLookupLimit.measure reciprocalBasis
  (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) columnEncoding 0 workerShape
  (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1))
  (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit
  (fun _ _ _ => pure (fun _ => (0 : Fin 2), ())) byteNativeNext columnStart

/-- The full source/three-pair/native-algebra/PCS witness has mass one after
removing all byte/retry caps; it includes both snapshots and final shared state. -/
example : IsProbabilityMeasure byteNativeLimit := by
  unfold byteNativeLimit
  apply StagedByteLookupLimit.probability <;> decide

/-- Completion preserves the original source-time hash log and root history.
Helper roots and native hashes cannot move this snapshot to a later phase. -/
example : byteNativeLimit {outcome | outcome.1.2.hash.log.length = 3 ∧
    outcome.1.2.checkpoints.checkpoints.length = 0} = 1 := by
  unfold byteNativeLimit
  rw [StagedByteLookupLimit.source_marginal reciprocalBasis
    (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) columnEncoding 0 workerShape
    (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1))
    (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit
    (fun _ _ _ => pure (fun _ => (0 : Fin 2), ())) byteNativeNext columnStart (by decide) (by decide)
    (fun first => first.2.hash.log.length = 3 ∧ first.2.checkpoints.checkpoints.length = 0)]
  have sourceLog : columnStart.hash.log.length = 3 := rfl
  have sourceRoots : columnStart.checkpoints.checkpoints = [] := rfl
  simp [sourceCommit, simulateQ_pure, StateT.run_pure, prEvent_norm, sourceLog, sourceRoots]

/-- Erasing the proof-only source/helper snapshots leaves a normalized measure
on the actual native query program and its final cache/log. -/
example : IsProbabilityMeasure (StagedByteLookupLimit.operational reciprocalBasis
    (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) columnEncoding 0 workerShape
    (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1))
    (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag) sourceCommit
    (fun _ _ _ => pure (fun _ => (0 : Fin 2), ())) byteNativeNext columnStart) := by
  apply StagedByteLookupLimit.operational_probability <;> decide

end StagedRepeatedLookupSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupMiddleTrace.grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupMiddleTrace.grows

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupMiddleTrace.completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupMiddleTrace.completion

/-- info: 'FormalProof4FHE.HasteBoots.StagedCompletedObservation.witness_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedCompletedObservation.witness_order

/-- info: 'FormalProof4FHE.HasteBoots.StagedCompletedObservation.completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedCompletedObservation.completion

/-- info: 'FormalProof4FHE.HasteBoots.StagedCompletedObservation.source_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedCompletedObservation.source_event

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.ordered

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.completion

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.measure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.measure_apply

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.all_depths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.all_depths

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.event_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.event_tends

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.varying_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.varying_loss_bound

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.operational_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.operational_apply

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.probability

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.source_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.source_marginal

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupLimit.operational_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupLimit.operational_probability

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteLookupUnboundedSecurity.false_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteLookupUnboundedSecurity.false_acceptance_bound


section ChargeRecordingSmoke

open OracleSpec OracleComp MeasureTheory

private noncomputable def recordedQueryCost
    (query : (SharedSequence.Shared Unit ColumnInput (Fin 2)).Domain)
    (state : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) workerShape) : ENNReal :=
  match query with
  | .inl _ => 1
  | .inr (.inl input) => if state.hash.cache input = none then 11 else 3
  | .inr (.inr _) => 0

private noncomputable def chargedFailure : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) Bool := do
  let bit ← PrivateSampling.embed Unit ColumnInput (Fin 2) ($ᵗ (Fin 2))
  let _ ← schemeHash (if bit = 0 then .inl [0] else .inl [2])
  let _ ← schemeHash (.inl [2])
  pure false

/-- A rejected return keeps the private draw, fresh hash and cached hash costs.
The new answer is really cached before the second hash, and no extra draw is
consumed for that cache hit. The initial account is retained too. -/
example : (fun outcome => ((outcome.1.1, outcome.1.2.1.hash.log.length, outcome.1.2.2), outcome.2))
    ((simulateQ retryTape ((simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      recordedQueryCost) chargedFailure).run (columnStart, 5))).run [1, 1, 99]) =
      ((false, 5, 20), [99]) := by
  change ((false, 5, (5 + 1 + 11 + 3 : ENNReal)), [99]) = ((false, 5, 20), [99])
  norm_num

/-- Actual byte rejection has zero availability hazard, while the earlier
sampler regressions still retain and count all of its consumed bytes. -/
example : ExpectedHazard.charge
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
    (CheckpointCollision.loss unifSpec workerShape)
    (PrivateSampling.embed Unit ColumnInput (Fin 2) (CanonicalByteSampler.runPrefix 17 4)) columnStart = 0 :=
  PrivateSamplingCharge.availability_zero _ _ _ _ _ _

/-- The shared handler's recorded expected account equals the existing actual
whole-run charge even though this program returns false. -/
example : (∫⁻ value, value ∂𝒟[(fun outcome => outcome.2.2) <$>
    (simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      recordedQueryCost) chargedFailure).run (columnStart, 0)]) =
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      recordedQueryCost chargedFailure columnStart :=
  ChargedExecution.expected_zero _ _ _ _

open scoped Classical in
/-- The actual unbounded byte-observation mean is the supremum of gated
finite means. This assertion makes no unconditional-prefix substitution. -/
example : (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
      ∂ByteLookupUnbounded.measure reciprocalBasis bytePairTable 2) =
    ⨆ n, ∫⁻ value, value ∂𝒟[(fun observed => if ByteLookupUnbounded.complete observed
      then (ByteLookupPairVector.consumedBytes observed.raw : ENNReal) else 0) <$>
        ByteLookupUnbounded.steps reciprocalBasis bytePairTable 2 n] :=
  CompletedExpectation.gated _ _ _ _

end ChargeRecordingSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedChargeComposition.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedChargeComposition.bind

/-- info: 'FormalProof4FHE.HasteBoots.ExpectedChargeComposition.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpectedChargeComposition.map

/-- info: 'FormalProof4FHE.HasteBoots.ChargedExecution.run_handler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedExecution.run_handler

/-- info: 'FormalProof4FHE.HasteBoots.ChargedExecution.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedExecution.erase

/-- info: 'FormalProof4FHE.HasteBoots.ChargedExecution.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedExecution.expected

/-- info: 'FormalProof4FHE.HasteBoots.ChargedExecution.expected_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedExecution.expected_zero

/-- info: 'FormalProof4FHE.HasteBoots.ChargedExecution.event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedExecution.event

/-- info: 'FormalProof4FHE.HasteBoots.PrivateSamplingCharge.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateSamplingCharge.zero

/-- info: 'FormalProof4FHE.HasteBoots.PrivateSamplingCharge.availability_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateSamplingCharge.availability_zero

/-- info: 'FormalProof4FHE.HasteBoots.PrivateSamplingCharge.then_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateSamplingCharge.then_shared

/-- info: 'FormalProof4FHE.HasteBoots.CompletedExpectation.simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedExpectation.simple

/-- info: 'FormalProof4FHE.HasteBoots.CompletedExpectation.integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedExpectation.integral

/-- info: 'FormalProof4FHE.HasteBoots.CompletedExpectation.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedExpectation.completed

/-- info: 'FormalProof4FHE.HasteBoots.CompletedExpectation.gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedExpectation.gated


section PartialAccountSmoke

open OracleSpec OracleComp

/-- Actual partial byte work retains its complete trace and unchanged earlier
availability account. No helper or native query is moved before completion. -/
example : (fun outcome => ((outcome.1.1.values.isNone, outcome.1.1.completed,
      ByteLookupPairVector.consumedBytes outcome.1.1, outcome.1.2.1.hash.log.length, outcome.1.2.2), outcome.2))
    ((simulateQ retryTape ((simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (CheckpointCollision.loss unifSpec workerShape))
      (PrivateSampling.embed Unit ColumnInput (Fin 2)
        (ByteLookupPairVector.program reciprocalBasis bytePairTable 2 2 4 2))).run (columnStart, 7))).run
        [2, 5, 255, 49, 1, 15, 99]) = ((true, [(2, 5)], 4, 3, 7), [1, 15, 99]) := by
  rw [PrivateChargedSampling.run_probComp columnEncoding 0 workerShape
    (CheckpointCollision.loss unifSpec workerShape) (ByteLookupChargedLimit.private_zero workerShape)]
  rfl

end PartialAccountSmoke

namespace StagedRepeatedLookupSmoke

open OracleSpec OracleComp MeasureTheory
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def chargedSource : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit := (fun _ => 0, ())
private noncomputable def chargedIncoming := RecordRoots.state workerShape
  (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1) chargedSource) columnStart

private noncomputable def chargedNativeTail (observed : ByteLookupPairTyped.Sample 17 1 (ZMod 17) 3) := do
  let helper ← ByteLookupPairMiddle.after (Cfg := Unit) (Input := ColumnInput) (Digest := Fin 2)
    (fun _ _ => pure (fun _ => (0 : Fin 2), ())) observed
  let second := (observed, helper)
  let _ ← RecordRoots.program (OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag chargedSource second)
  byteNativeNext chargedSource second

private noncomputable def chargedNativeLaw := ByteLookupChargedLimit.measure reciprocalBasis
  (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3 columnEncoding 0 workerShape chargedNativeTail chargedIncoming

/-- After the original source root is recorded, the complete raw-byte/helper/
native-algebra/PCS continuation has a normalized final-state/account law. -/
example : IsProbabilityMeasure chargedNativeLaw := by
  unfold chargedNativeLaw
  apply ByteLookupChargedLimit.probability <;> decide

/-- This account is attached to that actual continuation measure; its mean is
the supremum of the corresponding whole-prefix availability charges. -/
example : (∫⁻ outcome, outcome.2.2 ∂chargedNativeLaw) =
    ⨆ n, ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (CheckpointCollision.loss unifSpec workerShape)
      (SharedCompletedContinuation.program
        (ByteLookupUnbounded.steps reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3 n)
        ByteLookupUnbounded.complete chargedNativeTail) chargedIncoming :=
  ByteLookupChargedLimit.expected _ _ _ _ _ _ _ _

/-- The account erasure preserves a joint event on rejected-byte cost and the
actual later hash log, including native runs whose computed PCS flag rejects. -/
example : chargedNativeLaw {outcome | ByteLookupPairVector.consumedBytes outcome.1.1.raw > 6 ∧
      outcome.2.1.hash.log.length > 5} =
    SharedCompletedContinuation.measure
      (ByteLookupUnbounded.steps reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3)
      ByteLookupUnbounded.complete
      (ByteLookupUnbounded.grows reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3)
      columnEncoding 0 workerShape chargedNativeTail chargedIncoming
      {outcome | ByteLookupPairVector.consumedBytes outcome.1.1.raw > 6 ∧ outcome.2.hash.log.length > 5} :=
by
  unfold chargedNativeLaw
  exact ByteLookupChargedLimit.erase_event reciprocalBasis
    (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3 columnEncoding 0 workerShape chargedNativeTail chargedIncoming
    (fun outcome => ByteLookupPairVector.consumedBytes outcome.1.1.raw > 6 ∧ outcome.2.hash.log.length > 5)

end StagedRepeatedLookupSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PrivateChargedSampling.run_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateChargedSampling.run_query

/-- info: 'FormalProof4FHE.HasteBoots.PrivateChargedSampling.run_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateChargedSampling.run_embed

/-- info: 'FormalProof4FHE.HasteBoots.PrivateChargedSampling.run_probComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrivateChargedSampling.run_probComp

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.run_program

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.gated_account' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.gated_account

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.ordered

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.completion

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.measure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.measure_apply

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.probability

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.erase_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.erase_event

/-- info: 'FormalProof4FHE.HasteBoots.SharedChargedCompletion.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SharedChargedCompletion.expected

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupChargedLimit.private_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupChargedLimit.private_zero

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupChargedLimit.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupChargedLimit.expected

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupChargedLimit.erase_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupChargedLimit.erase_event

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupChargedLimit.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupChargedLimit.probability

/-- info: 'FormalProof4FHE.HasteBoots.ByteLookupChargedLimit.lookup_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ByteLookupChargedLimit.lookup_bound


section EarlierChargeSmoke

open OracleSpec OracleComp

private noncomputable def prefixQueryCost
    (query : (SharedSequence.Shared Unit ColumnInput (Fin 2)).Domain)
    (_state : CheckpointExecution.State (Input := ColumnInput) (Digest := Fin 2) workerShape) : ENNReal :=
  match query with
  | .inr (.inl _) => 5
  | _ => 0

private noncomputable def earlierChargedWork : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) Unit := do
  let _ ← schemeHash (.inl [2])
  let _ ← RecordRoots.program [((), 0)]
  pure ()

private def skippedWork (_ : Unit) (_ : Bool) : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) Bool := do
  let _ ← schemeHash (.inl [3])
  pure false

/-- Suspension skips later work but preserves the actual earlier hash, source
root, positive account and unused response tape. The loss here charges each
hash five units to expose any accidental omission of the earlier phase. -/
example : (fun outcome => ((outcome.1.2.1.hash.log.length, outcome.1.2.1.checkpoints.checkpoints.length,
      outcome.1.2.2), outcome.2))
    ((simulateQ retryTape ((simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      prefixQueryCost)
      (ChargedPrefixCompletion.program (pure false) (fun bit => bit = true) earlierChargedWork skippedWork)).run
        (columnStart, 0))).run [1, 99]) = ((4, 1, 5), [99]) := by
  have suspended (first : Unit) : SharedCompletedContinuation.program (pure false) (fun bit => bit = true)
      (skippedWork first) = pure (false, none) := by
    simp [SharedCompletedContinuation.program, PrivateSampling.embed, simulateQ_pure]
  simp only [ChargedPrefixCompletion.program, suspended]
  change ((4, 1, (0 + 5 + 0 : ENNReal)), [99]) = ((4, 1, 5), [99])
  norm_num

end EarlierChargeSmoke

namespace StagedRepeatedLookupSmoke

open OracleSpec OracleComp MeasureTheory
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

/-- A real earlier hash is charged before the original source root is recorded
and before any challenge bytes are sampled. -/
private noncomputable def chargedNativeBefore : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2))
    (StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit) := do
  let _ ← schemeHash (.inl [2])
  let first ← sourceCommit
  let _ ← RecordRoots.program (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1) first)
  pure first

private noncomputable def fullChargedNativeLaw := ChargedPrefixCompletion.operational columnEncoding 0 workerShape
  (CheckpointCollision.loss unifSpec workerShape) (ByteLookupChargedLimit.private_zero workerShape)
  chargedNativeBefore (fun _ => chargedNativeTail) columnStart
  (ByteLookupUnbounded.steps reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3)
  ByteLookupUnbounded.complete
  (ByteLookupUnbounded.grows reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3)

/-- Earlier charged work and root recording stay before the actual repeated
byte/helper/native-algebra/PCS continuation in a normalized account law. -/
example : IsProbabilityMeasure fullChargedNativeLaw := by
  unfold fullChargedNativeLaw
  apply ChargedPrefixCompletion.operational_probability
  exact ByteLookupUnbounded.completion_sup (by decide) reciprocalBasis
    (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) (by decide) 3

/-- The complete mean equals the charges of the same full source-before-byte
query program, rather than just the conditional later phase. -/
example : (∫⁻ outcome, outcome.2.2 ∂fullChargedNativeLaw) =
    ⨆ n, ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (CheckpointCollision.loss unifSpec workerShape)
      (ChargedPrefixCompletion.program
        (ByteLookupUnbounded.steps reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 3 n)
        ByteLookupUnbounded.complete chargedNativeBefore (fun _ => chargedNativeTail)) columnStart := by
  unfold fullChargedNativeLaw
  apply ChargedPrefixCompletion.expected
  exact ByteLookupUnbounded.completion_sup (by decide) reciprocalBasis
    (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) (by decide) 3

end StagedRepeatedLookupSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ChargeAccountShift.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargeAccountShift.run

/-- info: 'FormalProof4FHE.HasteBoots.CompletedPrefixMixture.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedPrefixMixture.ordered

/-- info: 'FormalProof4FHE.HasteBoots.CompletedPrefixMixture.prefix_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedPrefixMixture.prefix_integral

/-- info: 'FormalProof4FHE.HasteBoots.CompletedPrefixMixture.inner_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedPrefixMixture.inner_monotone

/-- info: 'FormalProof4FHE.HasteBoots.CompletedPrefixMixture.finite_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedPrefixMixture.finite_integral

/-- info: 'FormalProof4FHE.HasteBoots.CompletedPrefixMixture.integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedPrefixMixture.integral

/-- info: 'FormalProof4FHE.HasteBoots.CompletedPrefixMixture.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedPrefixMixture.probability

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.tail_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.tail_ordered

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.finite_operational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.finite_operational

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.operational_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.operational_apply

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.probability

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.operational_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.operational_probability

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.tail_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.tail_charge

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.tail_charge_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.tail_charge_monotone

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.whole_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.whole_charge

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.expected_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.expected_split

/-- info: 'FormalProof4FHE.HasteBoots.ChargedPrefixCompletion.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChargedPrefixCompletion.expected


namespace StagedRepeatedLookupSmoke

open OracleSpec OracleComp MeasureTheory
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def stagedChargeRequests (first : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit)
    (second : ByteLookupPairMiddle.Emission 17 1 (ZMod 17) (Fin 2) Unit 3) :=
  OptionalStagedLookup.helperRequests ByteLookupPairMiddle.completed tag first second

private def stagedChargeBuild (_first : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit)
    (_raw : ByteLookupPairTyped.Raw 17 1 (ZMod 17) 3) (_values : Fin 3 → StagedRepeatedLookup.Pair (ZMod 17)) :
    OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2)) (StagedRepeatedLookup.HelperEmission 3 (Fin 2) Unit) :=
  pure (fun _ => 0, ())

private noncomputable def stagedChargeSource : OracleComp (SharedSequence.Shared Unit ColumnInput (Fin 2))
    (StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit) := do
  let _ ← schemeHash (.inl [2])
  sourceCommit

private theorem stagedChargeRequests_none (first : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit)
    (observed : ByteLookupPairTyped.Sample 17 1 (ZMod 17) 3) (suspended : observed.values = none) :
    stagedChargeRequests first (observed, none) = [] := by
  simp only [stagedChargeRequests, OptionalStagedLookup.helperRequests, ByteLookupPairMiddle.completed, suspended]
  rfl

private theorem stagedChargeNext_none (first : StagedRepeatedLookup.SourceEmission 1 (Fin 2) Unit)
    (observed : ByteLookupPairTyped.Sample 17 1 (ZMod 17) 3) (suspended : observed.values = none) :
    byteNativeNext first (observed, none) = pure none := by
  simp only [byteNativeNext, OptionalStagedLookup.continuation, ByteLookupPairMiddle.completed, suspended]

private noncomputable def stagedChargeLaw := StagedByteChargedLimit.measure reciprocalBasis
  (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) columnEncoding 0 workerShape
  (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1)) stagedChargeRequests
  stagedChargeSource stagedChargeBuild byteNativeNext columnStart

/-- The factorization is equality of the actual native query programs. Root
recording stays on its original side of the raw byte/helper phases. -/
example : StagedByteFactor.project <$>
    ChargedPrefixCompletion.program
      (ByteLookupPairTyped.sample reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17)) 2 2 4 3)
      (fun observed => observed.values ≠ none)
      (StagedByteFactor.before (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1)) stagedChargeSource)
      (StagedByteFactor.tail stagedChargeRequests stagedChargeBuild byteNativeNext) =
    StagedCommitmentPrefix.program (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1)) stagedChargeRequests
      stagedChargeSource
      (fun first => ByteLookupPairMiddle.program reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17))
        2 2 4 3 (stagedChargeBuild first)) byteNativeNext :=
  StagedByteFactor.factor _ _ _ _ _ _ _ _ _ _ stagedChargeRequests_none stagedChargeNext_none

/-- The original source/typed helper/native result shape has a normalized
account law; native rejection is not conditioned away. -/
example : IsProbabilityMeasure stagedChargeLaw := by
  unfold stagedChargeLaw
  apply StagedByteChargedLimit.probability <;> decide

/-- The mean is the charge supremum of the original staged native program,
including its earlier source hash and both root-recording times. -/
example : (∫⁻ outcome, outcome.2.2 ∂stagedChargeLaw) =
    ⨆ n, ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) columnEncoding 0 workerShape)
      (CheckpointCollision.loss unifSpec workerShape)
      (StagedCommitmentPrefix.program (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange 1)) stagedChargeRequests
        stagedChargeSource
        (fun first => ByteLookupPairMiddle.program reciprocalBasis (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ZMod 17))
          n n n 3 (stagedChargeBuild first)) byteNativeNext) columnStart := by
  unfold stagedChargeLaw
  apply StagedByteChargedLimit.expected
  · decide
  · decide
  · exact stagedChargeRequests_none
  · exact stagedChargeNext_none

end StagedRepeatedLookupSmoke

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteFactor.factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteFactor.factor

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteFactor.charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteFactor.charge

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteChargedLimit.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteChargedLimit.probability

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteChargedLimit.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteChargedLimit.expected

/-- info: 'FormalProof4FHE.HasteBoots.StagedByteExpectedSecurity.false_acceptance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StagedByteExpectedSecurity.false_acceptance_bound


section CompletedByteWorkSmoke

open OracleSpec OracleComp MeasureTheory

/-- A genuine unbounded completed trace law, not a successful-value marginal. -/
example : IsProbabilityMeasure (RejectionTraceWork.measure ({1} : Finset (Fin 2))) :=
  RejectionTraceWork.probability _ (by simp)

example : (∫⁻ result, (result.2.length : ENNReal)
    ∂RejectionTraceWork.measure ({1} : Finset (Fin 2))) = 2 := by
  rw [RejectionTraceWork.expected _ (by simp)]
  norm_num

open scoped Classical in
/-- Incomplete work is still positive at finite depth; it cannot be erased
merely because successful mass eventually tends to one. -/
example : (∫⁻ value, value ∂𝒟[(fun result : RejectionSampling.Result (Fin 2) =>
    if RejectionTraceOrder.complete result then 0 else (result.2.length : ENNReal)) <$>
      RejectionSampling.runPrefix ({1} : Finset (Fin 2)) 2]) = 1 / 2 := by
  rw [RejectionTraceWork.partial_mean]
  have reject : RejectionSampling.reject ({1} : Finset (Fin 2)) = 1 / 2 := by
    unfold RejectionSampling.reject
    simp only [Finset.mem_singleton]
    rw [SampleableType.prEvent_uniformSample]
    norm_num [Finset.filter_ne']
  rw [reject]
  norm_num [pow_two, ENNReal.mul_inv_cancel_left]

/-- Without an accepted candidate the completed measure is zero while the
unconditional retry mean is infinite. The nonempty-domain guard matters. -/
example : (∫⁻ result, (result.2.length : ENNReal)
    ∂RejectionTraceWork.measure (∅ : Finset (Fin 2))) ≠
      RejectionSampling.totalExpectedAttempts (∅ : Finset (Fin 2)) := by
  rw [RejectionTraceWork.empty_measure, RejectionSampling.totalExpectedAttempts_fraction]
  norm_num [ENNReal.div_zero]

/-- Every retained rejected byte is included in the completed native-mask mean. -/
example : (∫⁻ result, (CanonicalByteSampler.consumedBytes 17 result : ENNReal)
    ∂CanonicalTraceWork.measure 17) = 32 / 17 := by
  rw [CanonicalTraceWork.expected 17 (by decide)]
  rw [show CanonicalByteSampler.byteCount 17 = 1 from by decide,
    show CanonicalByteSampler.bits 17 = 5 from by decide]
  norm_num

/-- Goldilocks uses eight raw bytes per base-field chunk, independently of
the protocol's packed-algebra width. -/
example : (∫⁻ result, (CanonicalByteSampler.consumedBytes NativeFields.goldilocksModulus result : ENNReal)
    ∂CanonicalTraceWork.measure NativeFields.goldilocksModulus) =
      8 * (((2 ^ 64 : ℕ) : ENNReal) / NativeFields.goldilocksModulus) := by
  rw [CanonicalTraceWork.expected NativeFields.goldilocksModulus (by decide)]
  rfl

/-- BabyBear uses four raw bytes per base-field chunk; all rejected chunks
remain charged in this exact completed-trace mean. -/
example : (∫⁻ result, (CanonicalByteSampler.consumedBytes NativeFields.babyBearModulus result : ENNReal)
    ∂CanonicalTraceWork.measure NativeFields.babyBearModulus) =
      4 * (((2 ^ 31 : ℕ) : ENNReal) / NativeFields.babyBearModulus) := by
  rw [CanonicalTraceWork.expected NativeFields.babyBearModulus (by decide)]
  rfl

end CompletedByteWorkSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CompletedCostTransfer.indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedCostTransfer.indicator

/-- info: 'FormalProof4FHE.HasteBoots.CompletedCostTransfer.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedCostTransfer.split

/-- info: 'FormalProof4FHE.HasteBoots.CompletedCostTransfer.gated_tends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedCostTransfer.gated_tends

/-- info: 'FormalProof4FHE.HasteBoots.CompletedCostTransfer.of_partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompletedCostTransfer.of_partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.length_le

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.suspended_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.suspended_length

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.partial_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.partial_mean

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.geometric_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.geometric_tail

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.empty_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.empty_measure

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.expected

/-- info: 'FormalProof4FHE.HasteBoots.RejectionTraceWork.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RejectionTraceWork.probability

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.measure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.measure_apply

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.probability

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.consumed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.consumed_le

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.partial_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.partial_mean

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.expected

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTraceWork.expected_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalTraceWork.expected_eq_total


section CompletedCoefficientWorkSmoke

open OracleSpec OracleComp MeasureTheory

example : IsProbabilityMeasure (CoefficientTraceWork.measure 17 2) :=
  CoefficientTraceWork.probability 17 (by decide) 2

/-- Completed coefficient traces count rejected chunks before either acceptance. -/
example : (∫⁻ result, (CanonicalCoefficientWork.consumedBytes 17 result : ENNReal)
    ∂CoefficientTraceWork.measure 17 2) = (2 : ENNReal) * (32 / 17) := by
  rw [CoefficientTraceWork.expected_eq_total 17 (by decide),
    CanonicalCoefficientWork.totalExpectedBytes_formula 17 (by decide)]
  rw [show CanonicalByteSampler.byteCount 17 = 1 by decide,
    show CanonicalByteSampler.bits 17 = 5 by decide]
  norm_num

/-- Zero requested coefficients complete without raw-byte work. -/
example : (∫⁻ result, (CanonicalCoefficientWork.consumedBytes 17 result : ENNReal)
    ∂CoefficientTraceWork.measure 17 0) = 0 := by
  rw [CoefficientTraceWork.expected 17 (by decide)]
  simp

/-- The second coefficient suspends after the first succeeds, retaining
both issued chunks and the first accepted value. -/
example : (fun outcome => ((outcome.1.values.isSome, outcome.1.completed,
      outcome.1.chunks.map CanonicalByteMask.decode, CanonicalCoefficientWork.consumedBytes 17 outcome.1), outcome.2))
    ((simulateQ retryTape (CanonicalCoefficientVector.program 17 1 2)).run [1, 255, 99]) =
      ((false, [1], [1, 255], 2), [99]) := by rfl

/-- The support bound includes both earlier success and current suspension. -/
example (result : CanonicalCoefficientVector.Result 17 2)
    (supported : result ∈ support (CanonicalCoefficientVector.program 17 1 2)) :
    result.chunks.length ≤ 2 := CoefficientTraceWork.chunks_le 17 1 2 result supported

private noncomputable def completedCoordinateBasis : Module.Basis (Fin 2) (ZMod 17) (Fin 2 → ZMod 17) :=
  Pi.basisFun _ _

example : IsProbabilityMeasure (ExtensionTraceWork.measure completedCoordinateBasis 2) :=
  ExtensionTraceWork.probability (by decide) completedCoordinateBasis 2

/-- Pure assembly preserves the full cost of four sequential coefficients. -/
example : (∫⁻ result, (CanonicalCoefficientWork.consumedBytes 17 result.2 : ENNReal)
    ∂ExtensionTraceWork.measure completedCoordinateBasis 2) = (4 : ENNReal) * (32 / 17) := by
  rw [ExtensionTraceWork.expected (by decide), CanonicalByteSampler.totalExpectedBytes_eq 17 (by decide)]
  rw [show CanonicalByteSampler.byteCount 17 = 1 by decide,
    show CanonicalByteSampler.bits 17 = 5 by decide]
  norm_num

/-- Native lookup extension degrees are independent of PCS packing widths. -/
example : (∫⁻ result, (CanonicalCoefficientWork.consumedBytes NativeFields.goldilocksModulus result : ENNReal)
    ∂CoefficientTraceWork.measure NativeFields.goldilocksModulus 3) =
      (24 : ENNReal) * (((2 ^ 64 : ℕ) : ENNReal) / NativeFields.goldilocksModulus) := by
  rw [CoefficientTraceWork.expected_eq_total _ (by decide),
    CanonicalCoefficientWork.totalExpectedBytes_formula _ (by decide)]
  rw [show CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 by decide,
    show CanonicalByteSampler.bits NativeFields.goldilocksModulus = 64 by decide]
  norm_num [← mul_assoc]

example : (∫⁻ result, (CanonicalCoefficientWork.consumedBytes NativeFields.babyBearModulus result : ENNReal)
    ∂CoefficientTraceWork.measure NativeFields.babyBearModulus 6) =
      (24 : ENNReal) * ((2147483648 : ENNReal) / NativeFields.babyBearModulus) := by
  rw [CoefficientTraceWork.expected_eq_total _ (by decide),
    CanonicalCoefficientWork.totalExpectedBytes_formula _ (by decide)]
  rw [show CanonicalByteSampler.byteCount NativeFields.babyBearModulus = 4 by decide,
    show CanonicalByteSampler.bits NativeFields.babyBearModulus = 31 by decide]
  norm_num [← mul_assoc]

end CompletedCoefficientWorkSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.chunks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.chunks_le

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.partial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.partial_le

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.expected

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.expected_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.expected_eq_total

/-- info: 'FormalProof4FHE.HasteBoots.CoefficientTraceWork.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CoefficientTraceWork.probability

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionTraceWork.partial_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionTraceWork.partial_mean

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionTraceWork.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionTraceWork.expected

/-- info: 'FormalProof4FHE.HasteBoots.ExtensionTraceWork.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionTraceWork.probability


section CompletedReciprocalWorkSmoke

open OracleSpec OracleComp MeasureTheory

/-- An incomplete inner observation stops the optional loop immediately,
retaining that observation even when the outer analysis depth is larger. -/
example : OptionalRejectionLoop.program (pure (none : Option (Fin 2))) id (fun _ => True) 3 =
    pure (⟨none, [none]⟩ : OptionalRejectionLoop.Result (Fin 2) (Option (Fin 2))) := by rfl

example : IsProbabilityMeasure (ReciprocalTraceWork.measure reciprocalBasis bytePoleTable) :=
  ReciprocalTraceWork.probability (by decide) reciprocalBasis bytePoleTable (by decide)

/-- The completed measure counts the full nested unconditional byte mean. -/
example : (∫⁻ result, (ByteReciprocalSampler.consumedBytes result : ENNReal)
    ∂ReciprocalTraceWork.measure reciprocalBasis bytePoleTable) =
      ByteReciprocalLimit.totalExpectedBytes reciprocalBasis bytePoleTable :=
  ReciprocalTraceWork.expected_eq_total (by decide) reciprocalBasis bytePoleTable (by decide)

/-- Two excluded field values give the exact completed raw-byte mean 32/15. -/
example : (∫⁻ result, (ByteReciprocalSampler.consumedBytes result : ENNReal)
    ∂ReciprocalTraceWork.measure reciprocalBasis bytePoleTable) = (32 / 15 : ENNReal) := by
  rw [ReciprocalTraceWork.expected (by decide) reciprocalBasis bytePoleTable (by decide), reciprocalDomain]
  have single : ByteReciprocalLimit.fieldCost 17 1 = (32 / 17 : ENNReal) := by
    rw [ByteReciprocalLimit.fieldCost, CanonicalByteSampler.totalExpectedBytes_eq 17 (by decide)]
    rw [show CanonicalByteSampler.byteCount 17 = 1 by decide, show CanonicalByteSampler.bits 17 = 5 by decide]
    norm_num
  rw [single]
  have domainCard : (Finset.univ \ ({0, 16} : Finset (ZMod 17))).card = 15 := by decide
  rw [domainCard]
  norm_num [ZMod.card]
  have numeric : (32 / 17 * (17 / 15) : NNReal) = 32 / 15 := by norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (17 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (15 : NNReal) ≠ 0), ENNReal.coe_ofNat] using
      congrArg (fun value : NNReal => (value : ENNReal)) numeric

/-- The support bound includes raw bytes on either suspension path. -/
example (result : OptionalRejectionLoop.Result (ZMod 17) (ByteReciprocalSampler.Trial 17 1 (ZMod 17)))
    (supported : result ∈ support (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 2 3)) :
    ByteReciprocalSampler.consumedBytes result ≤ 6 := by
  simpa only [show CanonicalByteSampler.byteCount 17 = 1 by decide, Nat.reduceMul] using
    ReciprocalTraceWork.consumed_le reciprocalBasis bytePoleTable 2 3 result supported

/-- The last incomplete field retains bytes and cannot start another trial. -/
example : (fun outcome => ((outcome.1.value, outcome.1.trials.map ByteReciprocalSampler.candidate,
      ByteReciprocalSampler.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteReciprocalSampler.program reciprocalBasis bytePoleTable 2 4)).run [0, 16, 255, 49, 144, 5, 99]) =
      ((none, [some 0, some 16, none], 4), [144, 5, 99]) := by rfl

/-- Cofinality applies to a cost-sensitive raw-trace event, not only values. -/
example : ReciprocalTraceWork.measure reciprocalBasis bytePoleTable
      {result | 0 < ByteReciprocalSampler.consumedBytes result} =
    ⨆ outer, ⨆ inner, Pr{let result ← ByteReciprocalSampler.program reciprocalBasis bytePoleTable inner outer}[
      OptionalTraceOrder.loopComplete result ∧ 0 < ByteReciprocalSampler.consumedBytes result] :=
  ReciprocalTraceWork.all_depths reciprocalBasis bytePoleTable _

end CompletedReciprocalWorkSmoke

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionTail.consumed_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionTail.consumed_le

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionTail.suspended_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionTail.suspended_succ

/-- info: 'FormalProof4FHE.HasteBoots.OptionalRejectionTail.suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptionalRejectionTail.suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.polynomial_geometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.polynomial_geometric

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.diagonal_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.diagonal_sup

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.trial_suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.trial_suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.trial_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.trial_cost_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.consumed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.consumed_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.rejected_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.rejected_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.partial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.partial_le

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.work_monotone_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.work_monotone_outer

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.work_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.work_sup

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.expected

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.expected_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.expected_eq_total

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.all_depths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.all_depths

/-- info: 'FormalProof4FHE.HasteBoots.ReciprocalTraceWork.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReciprocalTraceWork.probability


section CompletedPairVectorWorkSmoke

open OracleSpec OracleComp MeasureTheory

example : IsProbabilityMeasure (PairTraceWork.measure reciprocalBasis bytePairTable) :=
  PairTraceWork.probability (by decide) reciprocalBasis bytePairTable (by decide)

/-- The completed pair mean retains the true challenge-dependent domains. -/
example : (∫⁻ result, (ByteLookupPairWork.consumedBytes result : ENNReal)
    ∂PairTraceWork.measure reciprocalBasis bytePairTable) =
      ByteLookupPairWork.totalExpectedBytes reciprocalBasis bytePairTable :=
  PairTraceWork.expected_eq_total (by decide) reciprocalBasis bytePairTable (by decide)

/-- The support bound includes first-challenge bytes and partial offset work. -/
example (result : ByteLookupPairSampler.Result 17 1 (ZMod 17))
    (supported : result ∈ support (ByteLookupPairSampler.program reciprocalBasis bytePairTable 2 2 2)) :
    ByteLookupPairWork.consumedBytes result ≤ 6 := by
  simpa only [show CanonicalByteSampler.byteCount 17 = 1 by decide, Nat.reduceMul, Nat.reduceAdd] using
    PairTraceWork.consumed_le reciprocalBasis bytePairTable 2 2 2 result supported

/-- Actual typed completed bytes equal the unconditional repeated byte mean. -/
example : (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
    ∂ByteLookupUnbounded.measure reciprocalBasis bytePairTable 3) =
      ByteLookupPairVector.totalExpectedBytes reciprocalBasis bytePairTable 3 :=
  VectorTraceWork.typed_expected_eq_total (by decide) reciprocalBasis bytePairTable (by decide) 3

/-- The true repetition count is separate from degree and packed width. -/
example : (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
    ∂ByteLookupUnbounded.measure reciprocalBasis bytePairTable 3) =
      ByteLookupPairWork.totalExpectedBytes reciprocalBasis bytePairTable * 3 := by
  exact VectorTraceWork.typed_expected_formula (by decide) reciprocalBasis bytePairTable (by decide) 3

/-- Zero repetitions has zero completed byte mean without a fallback pair. -/
example : (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
    ∂ByteLookupUnbounded.measure reciprocalBasis bytePairTable 0) = 0 := by
  rw [VectorTraceWork.typed_expected_formula (by decide) reciprocalBasis bytePairTable (by decide)]
  simp

/-- The public size bound applies to the actual typed completed measure. -/
example : (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
    ∂ByteLookupUnbounded.measure reciprocalBasis bytePairTable 3) ≤
      (ByteReciprocalLimit.fieldCost 17 1 * (1 + (17 : ENNReal) / 14)) * 3 := by
  simpa only [ZMod.card, Nat.reduceSub, Nat.cast_ofNat] using
    VectorTraceWork.typed_expected_bound (by decide) reciprocalBasis bytePairTable (by decide) 3

/-- Typing retains the first completed pair and every byte of a suspended
second pair. Later raw responses are not consumed by a third repetition. -/
example : (fun outcome => ((outcome.1.values.isNone, outcome.1.completed,
      outcome.1.trials.map (fun trial => trial.offsetTrials.map (fun last => last.trials.map
        (fun field => field.2.chunks.map CanonicalByteMask.decode))),
      ByteLookupPairVector.consumedBytes (p := 17) (degree := 1) outcome.1), outcome.2))
    ((simulateQ retryTape (ByteLookupPairTyped.Sample.raw <$>
      ByteLookupPairTyped.sample reciprocalBasis bytePairTable 2 2 2 3)).run [1, 15, 2, 15, 255, 49, 5, 99]) =
      ((true, [(1, 15)], [some [[15]], some [[15], [255, 49]]], 6), [5, 99]) := by
  rw [ByteLookupPairTyped.sample_raw]
  rfl

end CompletedPairVectorWorkSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.consumed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.consumed_le

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.scaled_suspension_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.scaled_suspension_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.partial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.partial_le

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.expected_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.expected_eq_total

/-- info: 'FormalProof4FHE.HasteBoots.PairTraceWork.probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PairTraceWork.probability

/-- info: 'FormalProof4FHE.HasteBoots.ObservedVectorTail.consumed_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedVectorTail.consumed_le

/-- info: 'FormalProof4FHE.HasteBoots.ObservedVectorTail.suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedVectorTail.suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.consumed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.consumed_le

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.suspended_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.suspended_le

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.scaled_suspension_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.scaled_suspension_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.partial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.partial_le

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.partial_tends_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.partial_tends_zero

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.typed_partial_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.typed_partial_mean

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.typed_expected_eq_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.typed_expected_eq_total

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.typed_expected_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.typed_expected_formula

/-- info: 'FormalProof4FHE.HasteBoots.VectorTraceWork.typed_expected_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VectorTraceWork.typed_expected_bound


section SecurityExperimentSmoke
open SecurityExperiment
private def sevenSteps : Work := ⟨⟨0, 0, 0⟩, 0, 0, 7⟩
example : steps .attacker ([.work .verifier sevenSteps, .work .attacker sevenSteps] : Trace Unit Unit) = 7 := by
  decide
example : steps .attacker ([.work .setup sevenSteps] : Trace Unit Unit) = 0 := by decide
example : Bad (fun (_ : Unit) (_ : Unit) => False)
    ([.submission () () true, .submission () () false] : Trace Unit Unit) := by
  exact ⟨(), (), by simp, by simp⟩
/-- Infinite histories have no analysis-depth maximum. -/
example (n : ℕ) : prefixSteps .attacker (fun _ : ℕ => some (.work .attacker sevenSteps : Event Unit Unit)) n = n * 7 := by
  simp [prefixSteps, eventSteps, sevenSteps]
end SecurityExperimentSmoke

/-- info: 'FormalProof4FHE.HasteBoots.SecurityExperiment.steps_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SecurityExperiment.steps_append

/-- info: 'FormalProof4FHE.HasteBoots.SecurityExperiment.bad_persists' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SecurityExperiment.bad_persists

/-- info: 'FormalProof4FHE.HasteBoots.SecurityExperiment.other_actor_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SecurityExperiment.other_actor_zero

/-- info: 'FormalProof4FHE.HasteBoots.SecurityExperiment.expectedWork_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SecurityExperiment.expectedWork_mono

section InputIndexedOracleSmoke
open InputIndexedOracle

/-- Splitting the native reader around an empty read reuses the same stream. -/
example (world : World) (input : Input) (offset : ℕ) :
    (read world ⟨input, offset⟩ 3).1 ++
      (read world (read world ⟨input, offset⟩ 3).2 5).1 =
      (read world ⟨input, offset⟩ 8).1 := by
  exact (congrArg Prod.fst (read_split world ⟨input, offset⟩ 3 5)).symm

example (world : World) (reader : Reader) :
    read world (read world reader 7).2 0 = ([], (read world reader 7).2) :=
  read_zero world _

/-- Two readers of the same input start with the same bytes in every world. -/
example (world : World) (input : Input) :
    (read world (start input) 8).1 = bytes world input 0 8 := restart world input 8

/-- Repeating an already observed coordinate does not gain independent mass. -/
example (coordinate : Coordinate) (values : Coordinate → Byte) :
    law (assignment (insert coordinate {coordinate}) values) = (256 : ENNReal)⁻¹ := by
  simp [assignment_mass]

example : MeasureTheory.IsProbabilityMeasure law := law_probability
end InputIndexedOracleSmoke

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.read_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.read_split

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.read_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.read_zero

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.law_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.law_probability

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.block_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.block_law

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.hash_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.hash_law

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.shake_hash_pair_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.shake_hash_pair_law

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.assignment_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.assignment_measurable

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.assignment_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.assignment_mass

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.fresh_assignment_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.fresh_assignment_mass

/-- info: 'FormalProof4FHE.HasteBoots.InputIndexedOracle.finite_coordinates_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InputIndexedOracle.finite_coordinates_uniform

section TranscriptFrameSmoke
open TranscriptFrame

/-- The ABI length is little-endian and fixed at eight bytes. -/
example : littleEndian 8 256 = [0, 1, 0, 0, 0, 0, 0, 0] := by decide

/-- Independent byte fixture for kind 4, label x, and payload [1,2]. -/
example : encode ⟨4, [120], [1, 2]⟩ =
    [4, 1, 0, 0, 0, 0, 0, 0, 0, 120, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2] := by decide

example : decode [9] = none := decode_reject_kind 9 [] (by decide)

/-- A truncated header rejects. -/
example : decode [0, 0, 0, 0] = none := by decide

/-- Full headers declaring one absent payload byte also reject. -/
example : decode [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] = none := by decide

/-- The valid-length premise excludes truncation at the u64 boundary. -/
example : littleEndian 8 (2 ^ 64) = littleEndian 8 0 := by decide
end TranscriptFrameSmoke

section NativeTranscriptSmoke
open NativeTranscript
open InputIndexedOracle (World Input)

/-- Empty challenges retain the start and the empty output event. -/
example (world : World) (state : Transcript) (label : Input) :
    (challengeBytes world state label 0).run.2.length = 2 := rfl

/-- Zero requested field values still finalize the request reader. -/
example (state : Transcript) (label : Input) :
    (beginField state label 17 0).run.2.length = 1 := rfl

/-- All raw candidate bytes remain, independent of later acceptance tests. -/
example (world : World) (state : Transcript) (label : Input) :
    (drawField world
      (drawField world (beginField state label 17 2).run.1 3).run.1.2 5).run.1.2.consumed.length = 8 := by
  simp [drawField, beginField, WriterT.run_mk, InputIndexedOracle.bytes_length]

example (world : World) (consumed : Input) :
    (receipt world consumed).run.1.length = 80 := receipt_length world consumed
end NativeTranscriptSmoke

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.fromLittleEndian_littleEndian' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.fromLittleEndian_littleEndian

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.readSized_sized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.readSized_sized

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decode_encode

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.boundary_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.boundary_unique

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.encodeMany_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.encodeMany_injective

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.challenge_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.challenge_state

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.begin_coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.begin_coherent

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.draw_coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.draw_coherent

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.draw_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.draw_split

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.receipt_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.receipt_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.receipt_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.receipt_observations

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.fork_profiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.fork_profiles

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.receipt_domain_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.receipt_domain_separated

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.challenge_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.challenge_observations

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.request_label_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.request_label_injective

section OracleReplaySmoke
open InputIndexedOracle (Byte Input Coordinate World bytes sha512)
open OracleProgram

private def adaptiveMixed : Program Input :=
  .read [] 0 1 (fun first => .hash first (fun digest => .read (List.ofFn digest) 0 1 .pure))

/-- The next hash input is chosen from the earlier returned XOF byte. -/
example (world : World) :
    nextRequest (runPrefix 1 adaptiveMixed world).run.1 = some (.hash (bytes world [] 0 1)) := rfl

/-- Only after receiving the hash result can it determine a later XOF input. -/
example (world : World) :
    nextRequest (runPrefix 2 adaptiveMixed world).run.1 =
      some (.read (List.ofFn (sha512 world (bytes world [] 0 1))) 0 1) := rfl

private def repeatRead : Program Input :=
  .read [] 0 1 (fun _ => .read [] 0 1 .pure)

/-- Repeated reads remain two events but reveal only one distinct byte. -/
example (world : World) :
    (ObservationReplay.footprint (run repeatRead world).run.2).card = 1 := by
  change (ObservationReplay.footprint
    [.output [] 0 (bytes world [] 0 1), .output [] 0 (bytes world [] 0 1)]).card = 1
  simp [ObservationReplay.footprint, ObservationReplay.coordinates, InputIndexedOracle.bytes_length]

/-- A start alone does not reveal any output, including for an empty challenge. -/
example (world : World) (state : NativeTranscript.Transcript) (label : Input) :
    nextRequest (runPrefix 1 (NativeTranscriptProgram.challengeBytes state label 0) world).run.1 =
      some (.read (NativeTranscript.requestInput state label 0) 0 0) := rfl

private def zeroWorld : World := fun _ => 0

/-- Updating an observed byte changes the response: the freshness premise matters. -/
example : (ObservationReplay.read (Function.update zeroWorld (.inl ([], 0)) 1) [] 0 1).run.1 = [1] := by decide
example : (ObservationReplay.read zeroWorld [] 0 1).run.1 = [0] := by decide

example (world : World) :
    InputIndexedOracle.law {other | (runPrefix 2 adaptiveMixed other).run = (runPrefix 2 adaptiveMixed world).run} =
      (256 : ENNReal)⁻¹ ^ (ObservationReplay.footprint (runPrefix 2 adaptiveMixed world).run.2).card :=
  ObservationReplay.fiber_mass (prefix_replay 2 adaptiveMixed) world
end OracleReplaySmoke

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.bind_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.bind_replay

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.read_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.read_replay

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.hash_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.hash_replay

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.same_of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.same_of_agrees

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.fiber_eq_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.fiber_eq_assignment

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.fiber_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.fiber_measurable

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.fiber_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.fiber_mass

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.update_unobserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.update_unobserved

/-- info: 'FormalProof4FHE.HasteBoots.ObservationReplay.fresh_byte_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ObservationReplay.fresh_byte_mass

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgram.run_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgram.run_bind

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgram.run_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgram.run_replay

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgram.prefix_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgram.prefix_replay

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgram.next_request_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgram.next_request_replay

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgram.prefix_update_unobserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgram.prefix_update_unobserved

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_query' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_query

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_challengeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_challengeBytes

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_checkpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_checkpoint

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_beginField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_beginField

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_drawField' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_drawField

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_receipt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_receipt

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_finishField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_finishField

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_forkChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_forkChild

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_finishLinkedChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_finishLinkedChild

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_linkedChild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.run_linkedChild

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.native_fork_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.native_fork_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscriptProgram.linked_child_prefix_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscriptProgram.linked_child_prefix_replay

section CanonicalTranscriptSamplerSmoke
open InputIndexedOracle (Byte Input World)
open CanonicalTranscriptSampler

private def samplerPhase : NativeTranscript.FieldPhase := ⟨⟨[], fun _ => 0⟩, [], []⟩
private def rejectThenAccept : World
  | .inl (_, position) => if position = 0 then 3 else 2
  | .inr _ => 0
private def alwaysReject : World
  | .inl _ => 3
  | .inr _ => 0

/-- Modulus 3 rejects the first masked value 3, then accepts 2. -/
example : (executePrefix 3 1 samplerPhase rejectThenAccept).1.accepted = none := by decide +kernel
example : value 3 (executePrefix 3 2 samplerPhase rejectThenAccept).1 = some 2 := by decide +kernel

/-- The rejected bytes are retained in order and no receipt is emitted. -/
example : (executePrefix 3 2 samplerPhase rejectThenAccept).1.chunks = [[3], [2]] := by decide +kernel
example : (executePrefix 3 2 samplerPhase rejectThenAccept).1.phase.consumed = [3, 2] := by decide +kernel
example : (executePrefix 3 1 samplerPhase rejectThenAccept).2 = [.output [] 0 [3]] := by decide +kernel

example : (OracleProgram.run (samplePrefix 3 2 samplerPhase) rejectThenAccept).run.1.accepted = some [2] := by
  rw [run_samplePrefix]
  decide +kernel

/-- Completion stops further reads at every larger analysis depth. -/
example (extra : ℕ) : executePrefix 3 (2 + extra) samplerPhase rejectThenAccept =
    executePrefix 3 2 samplerPhase rejectThenAccept :=
  completed_stable 3 2 extra samplerPhase rejectThenAccept (by decide +kernel)

/-- Suspension is not rejection by the verifier or an implementation cutoff. -/
example : (executePrefix 3 5 samplerPhase alwaysReject).1.chunks.length = 5 :=
  suspended_attempts 3 5 samplerPhase alwaysReject (by decide +kernel)

private def unusedHighBits : World
  | .inl (_, position) => if position = 0 then 0 else 129
  | .inr _ => 0

/-- 0x8100 is masked to 0x100, but the raw high bit stays in the receipt input. -/
example : value 257 (executePrefix 257 1 samplerPhase unusedHighBits).1 = some 256 := by decide +kernel
example : (executePrefix 257 1 samplerPhase unusedHighBits).1.phase.consumed = [0, 129] := by decide +kernel
end CanonicalTranscriptSamplerSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.fromLittleEndian_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.fromLittleEndian_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.candidate_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.candidate_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.scratch_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.scratch_decode

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.scratch_fits_u128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.scratch_fits_u128

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.vector_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.vector_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.ofFn_vector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.ofFn_vector

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.candidate_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.candidate_vector

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.run_samplePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.run_samplePrefix

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.phase_retains_chunks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.phase_retains_chunks

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.chunks_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.chunks_width

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.accepted_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.accepted_below

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.final_coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.final_coherent

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.completed_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.completed_stable

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.log_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.log_refines

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.resume_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.resume_exact

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.typed_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.typed_supported

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.attempts_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.attempts_le

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.suspended_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.suspended_attempts

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.added_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.added_bytes

/-- info: 'FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.sample_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler.sample_replay

section NativeFieldVectorSmoke
open InputIndexedOracle (World)
open NativeFieldVector

private def collectorRoot : NativeTranscript.Transcript := ⟨[], fun _ => 0⟩
private def collectorWorld : World
  | .inl (_, position) => if position = 0 then 3 else 2
  | .inr _ => 0
private def collectorObserved (fuel count : ℕ) : Status × List NativeTranscript.Observation :=
  (OracleProgram.run (request 3 fuel collectorRoot [] count) collectorWorld).run
private def collectorValues : Status → Option (List ℕ)
  | .suspended _ => none
  | .finished state _ => some state.values

/-- Rejection consumes a trial without advancing the requested coefficient. -/
example : (stateOf (collectorObserved 1 2).1).remaining = 2 := by decide +kernel
example : (stateOf (collectorObserved 2 2).1).values = [2] := by decide +kernel
example : collectorValues (collectorObserved 2 2).1 = none := by decide +kernel
example : (collectorObserved 2 2).2.length = 3 := by decide +kernel

/-- A later trial completes the vector in the same reader, retaining rejection bytes. -/
example : collectorValues (collectorObserved 3 2).1 = some [2, 2] := by decide +kernel
example : (stateOf (collectorObserved 3 2).1).phase.consumed = [3, 2, 2] := by decide +kernel
example : (collectorObserved 3 2).2.length = 6 := by decide +kernel

example : collectorValues
    (OracleProgram.run (resume 3 1 (collectorObserved 2 2).1) collectorWorld).run.1 = some [2, 2] := by decide +kernel
example : (OracleProgram.run (resume 3 10 (collectorObserved 3 2).1) collectorWorld).run.2 = [] := by decide +kernel

/-- Zero requested coefficients still create a reader and an empty-prefix receipt. -/
example : collectorValues (collectorObserved 0 0).1 = some [] := by decide +kernel
example : (collectorObserved 0 0).2.length = 3 := by decide +kernel
example : (stateOf (collectorObserved 0 0).1).phase.consumed = [] := by decide +kernel

private def collectorHighBits : World
  | .inl (_, position) => if position = 0 then 0 else 129
  | .inr _ => 0

/-- The finished request keeps raw 0x8100 while returning masked coefficient 0x100. -/
example : collectorValues
    (OracleProgram.run (request 257 1 collectorRoot [] 1) collectorHighBits).run.1 = some [256] := by decide +kernel
example : (stateOf
    (OracleProgram.run (request 257 1 collectorRoot [] 1) collectorHighBits).run.1).phase.consumed = [0, 129] := by decide +kernel
end NativeFieldVectorSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.run_collect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.run_collect

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.execute_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.execute_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.execute_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.execute_add

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.advance_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.advance_count

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.count_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.count_invariant

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.completed_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.completed_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.advance_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.advance_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.values_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.values_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.advance_retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.advance_retains

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.retains

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.advance_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.advance_header

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.header_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.header_preserved

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.advance_coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.advance_coherent

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.coherent

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.run_finalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.run_finalize

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.run_drive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.run_drive

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.run_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.run_resume

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.run_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.run_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.finish_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.finish_state

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.finish_status' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.finish_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_status

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_count

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_values_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_values_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_finished_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_finished_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.drive_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.drive_add

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_add

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.no_premature_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.no_premature_receipt

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.finished_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.finished_resume

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldVector.request_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldVector.request_replay

/-- Native challenge cardinalities use degrees 3 and 6, separately from PCS degrees 4 and 8. -/
example : Fintype.card NativeExtensionFields.Goldilocks3 = NativeFields.goldilocksModulus ^ 3 :=
  NativeExtensionFields.goldilocks_card

example : Fintype.card NativeExtensionFields.BabyBear6 = NativeFields.babyBearModulus ^ 6 :=
  NativeExtensionFields.babyBear_card

/-- The final coordinate of the second native Goldilocks value is flat index five. -/
example :
    (NativeExtensionFields.goldilocksBasis.equivFun
      (NativeFieldAssembly.goldilocks 2 [0, 1, 2, 3, 4, 5] (by decide) 1) 2).val = 5 := by
  exact NativeFieldAssembly.assemble_canonical_coordinate
    NativeExtensionFields.goldilocksBasis 2 [0, 1, 2, 3, 4, 5] (by decide)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with h | h | h | h | h | h <;> subst v <;> decide) 1 2

/-- The next BabyBear element starts at coefficient six, rather than the PCS stride eight. -/
example :
    (NativeExtensionFields.babyBearBasis.equivFun
      (NativeFieldAssembly.babyBear 2 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] (by decide) 1) 0).val = 6 := by
  apply NativeFieldAssembly.assemble_canonical_coordinate
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h | h | h <;> subst v <;> decide

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.no_power_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.no_power_of_witness

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_seven_not_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_seven_not_cube

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_thirtyOne_not_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_thirtyOne_not_cube

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_thirtyOne_not_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_thirtyOne_not_square

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_irreducible

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_cubic_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_cubic_irreducible

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_irreducible

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_basis_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_basis_power

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_basis_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_basis_power

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.goldilocks_card

/-- info: 'FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeExtensionFields.babyBear_card

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldAssembly.coefficients_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldAssembly.coefficients_canonical

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldAssembly.assemble_canonical_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldAssembly.assemble_canonical_coordinate

/-- info: 'FormalProof4FHE.HasteBoots.NativeFieldAssembly.finished_request_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeFieldAssembly.finished_request_coordinate

/-- A successful arbitrary parse certifies exact bytes and native length bounds. -/
example (input suffix : InputIndexedOracle.Input) (frame : TranscriptFrame.Frame)
    (parsed : TranscriptFrame.decode input = some (frame, suffix)) :
    TranscriptFrame.Valid frame ∧ input = TranscriptFrame.encode frame ++ suffix :=
  TranscriptFrame.decode_sound input frame suffix parsed

/-- Truncated kind/header and declared body are rejected rather than padded. -/
example : TranscriptFrame.decodeAll [4] = none := by decide +kernel

example : TranscriptFrame.decodeAll ([4] ++ TranscriptFrame.littleEndian 8 1) = none := by
  decide +kernel

/-- An adversarial maximum-u64 length is checked before taking the missing body. -/
example : TranscriptFrame.decodeAll ([4] ++ List.replicate 8 255) = none := by decide +kernel

/-- A one-frame parse retains trailing bytes; full-stream parsing rejects them. -/
example : TranscriptFrame.decode
    (TranscriptFrame.encode ⟨0, [], []⟩ ++ [9]) = some (⟨0, [], []⟩, [9]) := by
  decide +kernel

example : TranscriptFrame.decodeAll
    (TranscriptFrame.encode ⟨0, [], []⟩ ++ [9]) = none := by decide +kernel

/-- Every structural tag is accepted, preserving zero and high bytes in payloads. -/
example :
    let frames : List TranscriptFrame.Frame := (List.finRange 9).map (fun kind => ⟨kind, [255, 0, 1], [2, 0, 255]⟩)
    TranscriptFrame.decodeAll (TranscriptFrame.encodeMany frames) = some frames := by
  decide +kernel

example : TranscriptFrame.decodeAll [] = some [] := by decide +kernel

/-- Receipt-domain rejection covers arbitrary consumed bytes, rather than only encoded examples. -/
example (consumed : InputIndexedOracle.Input) :
    TranscriptFrame.decodeAll (NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ consumed) = none :=
  NativeTranscript.receipt_decode_rejected consumed

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.fromLittleEndian_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.fromLittleEndian_lt

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.littleEndian_fromLittleEndian' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.littleEndian_fromLittleEndian

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.takeBytes_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.takeBytes_sound

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.readSized_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.readSized_sound

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decode_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decode_sound

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decode_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decode_eq_some_iff

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decode_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decode_progress

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decode_complete_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decode_complete_iff

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll_sound

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll_encodeMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll_encodeMany

/-- info: 'FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.TranscriptFrame.decodeAll_eq_some_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.receipt_not_frame_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.receipt_not_frame_stream

/-- info: 'FormalProof4FHE.HasteBoots.NativeTranscript.receipt_decode_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeTranscript.receipt_decode_rejected

end HasteBootsSmoke
