module
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.PreparedMerklePayloads
import all FormalProof4FHE.HasteBoots.NTTDomainCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.DenseCandidateCheck
import all FormalProof4FHE.HasteBoots.DenseBerlekampWelch
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.BlockEvaluationCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
import all FormalProof4FHE.HasteBoots.ExecutableCommonSource
import all FormalProof4FHE.HasteBoots.DenseCommonSource
import all FormalProof4FHE.HasteBoots.DenseSourceExtraction
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all FormalProof4FHE.HasteBoots.RowLayout
import all FormalProof4FHE.HasteBoots.NativeFields
import all ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
import all FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
import all FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
import all FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
import all FormalProof4FHE.HasteBoots.NativeFieldWire
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all VCVio.CryptoFoundations.MerkleTree.Extractor
import all ToMathlib.Data.IndexedBinaryTree.Perfect
import all ToMathlib.Data.IndexedBinaryTree.Basic
open FormalProof4FHE.HasteBoots
open PreparedMerklePayloads
private def digest (value : Fin 256) : NativeRootMessage.Digest := fun _ => value
private def row : NativeLookupRequestWire.Row := ⟨[7,8],by decide⟩
private def otherRow : NativeLookupRequestWire.Row := ⟨[9],by decide⟩
private def good : ExecutableMerkleAvailability.Log :=
  [⟨NativeGoldColumnAuthentication.leafInput row,digest 11⟩]
private def malformed : ExecutableMerkleAvailability.Log := [⟨[99],digest 11⟩]

/-- info: true -/
#guard_msgs in
#eval let result := scan (prepare good) (store (digest 11))
      decide (result.value = some row ∧ result.cost = 389)

-- A malformed matching entry is skipped and both matching digests are read.
/-- info: true -/
#guard_msgs in
#eval let result := scan (prepare (malformed++good)) (store (digest 11))
      decide (result.value = some row ∧ result.cost = 778)

/-- info: true -/
#guard_msgs in
#eval let result := scan (prepare malformed) (store (digest 11))
      decide (result.value = none ∧ result.cost = 390)

-- First valid original payload wins over later conflicting payloads.
/-- info: true -/
#guard_msgs in
#eval let result := scan (prepare (good++[⟨NativeGoldColumnAuthentication.leafInput otherRow,digest 11⟩])) (store (digest 11))
      decide (result.value = some row ∧ result.cost = 389)

-- A successful initial has the same scan charge after arbitrary appends;
-- preparing the log is a separate phase and is not included in this charge.
/-- info: true -/
#guard_msgs in
#eval let initial := prepare (malformed++good)
      let first := scan initial (store (digest 11))
      let extended := scan (initial++prepare (List.replicate 12 ⟨[99],digest 22⟩)) (store (digest 11))
      decide (first.value = extended.value ∧ first.cost = extended.cost)

-- Digest comparison uses every byte, including byte 63.
/-- info: true -/
#guard_msgs in
#eval let changed : NativeRootMessage.Digest := fun i => if i.val = 63 then 12 else 11
      let result := scan (prepare good) (store changed)
      decide (result.value = none ∧ result.cost = 389)

-- Unrelated labels stop comparison on the first byte; no decoder runs in scan.
/-- info: true -/
#guard_msgs in
#eval let result := scan (prepare (good++good)) (store (digest 12))
      decide (result.value = none ∧ result.cost = 21)

/-- info: true -/
#guard_msgs in
#eval let result := scan [] (store (digest 11))
      decide (result.value = none ∧ result.cost = 1)

/-- info: true -/
#guard_msgs in
#eval !(byteEqual [1,2] [1]).value && !(byteEqual [1] [1,2]).value
