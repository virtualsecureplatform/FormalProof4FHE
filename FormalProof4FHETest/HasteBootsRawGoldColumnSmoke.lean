module
import all FormalProof4FHE.HasteBoots.RawGoldColumnCost
import all FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
import all FormalProof4FHE.HasteBoots.CostedMerkleWord
import all FormalProof4FHE.HasteBoots.StoredDigestView
import all FormalProof4FHE.HasteBoots.CostedMerkleTree
import all FormalProof4FHE.HasteBoots.PreparedMerkleNodes
import all FormalProof4FHE.HasteBoots.FixedByteReadCost
import all FormalProof4FHE.HasteBoots.CostedMerkleNode
import all FormalProof4FHE.HasteBoots.BytePrefixMatchCost
import all FormalProof4FHE.HasteBoots.IntegerEncodingCost
import all FormalProof4FHE.HasteBoots.RowEncodingCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeaf
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.PreparedMerklePayloads
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.DenseCandidateCheck
import all FormalProof4FHE.HasteBoots.DenseBerlekampWelch
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.BlockEvaluationCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
import all FormalProof4FHE.HasteBoots.CommonSourceReindex
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
import all FormalProof4FHE.HasteBoots.NativeGoldExecutableExtraction
import all FormalProof4FHE.HasteBoots.NativeGoldPublicSource
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCode
import all FormalProof4FHE.HasteBoots.NativeFieldRepresentation
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.NTTDomainCost
import all FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
import all FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
import all FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
import all FormalProof4FHE.HasteBoots.NativeFieldWire
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all VCVio.CryptoFoundations.MerkleTree.Extractor
import all ToMathlib.Data.IndexedBinaryTree.Perfect
import all ToMathlib.Data.IndexedBinaryTree.Basic
open FormalProof4FHE.HasteBoots
private def usize (n : Nat) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide)⟩
private def digest : NativeRootMessage.Digest := fun _ => 0
private def ctx : NativeGoldBatchPcsProgram.Context :=
  ⟨⟨fun _ => false,fun _ => false,fun _ => none⟩,
    ⟨usize 3,usize 3,usize 1,usize 0,
      ⟨usize 3,usize 2,usize 2,usize 4,⟨[],by decide⟩,usize 3⟩⟩,
    NativeTranscript.new [] digest,digest,⟨[],by decide⟩,⟨[],by decide⟩,
    ⟨⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩⟩,0⟩

open NativeFieldRepresentation (GoldWord)
private def rawRow (values : List GoldWord) : NativeLookupRequestWire.Row :=
  ⟨values.take 16,by have bound := List.length_take_le 16 values; omega⟩
private def rawColumns : Vector NativeLookupRequestWire.Row 2 :=
  #v[rawRow [1,2,3],rawRow [⟨NativeFields.goldilocksModulus+1,by decide⟩]]
private def values {n r b : Nat} (result : Vector (Vector (Vector NativeFields.Goldilocks b) r) n) :=
  result.toList.map (fun column => column.toList.map (fun row => row.toList.map (fun x => x.val)))

-- List traversal charges every cons, including the end of a short row.
/-- info: true -/
#guard_msgs in
#eval decide ((RawGoldColumnCost.read [1,2,3] 1).value = 2 ∧
  (RawGoldColumnCost.read [1,2,3] 1).cost = 4 ∧
  (RawGoldColumnCost.read [1,2,3] 100).value = 0 ∧
  (RawGoldColumnCost.read [1,2,3] 100).cost = 7)

-- Preserve row/lane order, zero padding, lazy u64 interpretation, and wrapped
-- source indices when output and raw column counts differ.
/-- info: true -/
#guard_msgs in
#eval let result := RawGoldColumnCost.columns 3 2 2 rawColumns
  decide (values result.value = [[[1,2],[3,0]],[[1,0],[0,0]],[[1,2],[3,0]]] ∧ result.cost = 149)

/-- info: true -/
#guard_msgs in
#eval decide ((RawGoldColumnCost.columns 0 2 2 rawColumns).cost = 1 ∧
  (RawGoldColumnCost.columns 2 0 2 rawColumns).cost = 11 ∧
  (RawGoldColumnCost.columns 2 2 0 rawColumns).cost = 19)

-- A complete public empty-log materialization includes reconstruction once.
/-- info: true -/
#guard_msgs in
#eval let result := NativeGoldPublicSource.materializeWithCost digest digest ctx []
  let raw := CostedMerkleWord.prepareWord 2 (Vector.ofFn digest) [] (PreparedMerklePayloads.store digest)
  let converted := RawGoldColumnCost.columns 4 6 2 raw.value
  decide (values result.value = List.replicate 4 (List.replicate 6 [0,0]) ∧
    result.cost = raw.cost+converted.cost+2 ∧ result.cost ≤ NativeGoldPublicSource.materializeBound ctx [])

-- Extraction includes measured preparation and the complete prepared extractor.
/-- info: true -/
#guard_msgs in
#eval let prepared := NativeGoldPublicSource.materializeWithCost digest digest ctx []
  let extracted := NativeGoldExecutableExtraction.extractPreparedWithCost ctx 0 (by decide) prepared.value
  let result := NativeGoldPublicSource.extractWithCost digest digest ctx [] 0 (by decide)
  decide (result.cost = prepared.cost+extracted.cost+1 ∧ result.value = extracted.value)
