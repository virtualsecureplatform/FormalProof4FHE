module
import all FormalProof4FHE.HasteBoots.StoredGoldPublicSource
import all FormalProof4FHE.HasteBoots.PublicSourceByteInputs
import all FormalProof4FHE.HasteBoots.PublicGoldByteExtraction
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


private def zero : List InputIndexedOracle.Byte := List.replicate 64 0
private def one : List InputIndexedOracle.Byte := List.replicate 64 1
private def hashes : PublicSourceByteInputs.ByteLog := [([0],zero),([1],one),([0],zero)]

-- The fixed-width adapters reject truncation and suffixes at every nearby size.
/-- info: true -/
#guard_msgs in
#eval (List.range 72).all (fun size =>
  let result := PublicSourceByteInputs.digest (List.replicate size 0)
  decide (result.value.isSome = (size == 64) ∧ result.cost ≤ 455))

-- All original entries survive in order, including repeated inputs/labels.
/-- info: true -/
#guard_msgs in
#eval decide ((PublicSourceByteInputs.log hashes).value.map PublicSourceByteInputs.encodeLog = some hashes)

-- Any malformed output rejects the whole log, including one before a valid alias.
/-- info: true -/
#guard_msgs in
#eval let malformed := ([0],zero ++ [0])::hashes
  decide ((PublicSourceByteInputs.log malformed).value.isNone ∧
    (PublicSourceByteInputs.log (hashes ++ [([0],zero.take 63)])).value.isNone ∧
    (PublicSourceByteInputs.log malformed).cost ≤ 589*malformed.length+1)

-- Dummy/root failure is explicit; no arbitrary digest callback is evaluated.
/-- info: true -/
#guard_msgs in
#eval decide ((PublicSourceByteInputs.read (zero.take 63) zero hashes).value.isNone ∧
  (PublicSourceByteInputs.read zero (zero ++ [0]) hashes).value.isNone ∧
  (PublicSourceByteInputs.read zero one hashes).value.isSome)

-- Stored extraction and the functional analysis interface agree in value AND charge.
/-- info: true -/
#guard_msgs in
#eval let dummy := Vector.replicate 64 (0 : InputIndexedOracle.Byte)
  let root : PreparedMerklePayloads.StoredDigest := ⟨zero,by decide⟩
  let result := StoredGoldPublicSource.extract dummy root ctx [] 0 (by decide)
  let reference := NativeGoldPublicSource.extractWithCost dummy.get (StoredDigestView.view root) ctx [] 0 (by decide)
  decide (result.value = reference.value ∧ result.cost = reference.cost)

-- Successful byte entry includes adapters plus the full stored extractor once.
/-- info: true -/
#guard_msgs in
#eval let parsed := PublicSourceByteInputs.read zero one hashes
  match parsed.value with
  | none => false
  | some inputs =>
    let result := PublicGoldByteExtraction.run zero one ctx hashes 0 (by decide)
    let extracted := StoredGoldPublicSource.extract inputs.dummy inputs.root ctx inputs.hashes 0 (by decide)
    decide (result.value = some extracted.value ∧ result.cost = parsed.cost+extracted.cost+3 ∧
      result.cost ≤ 589*hashes.length+1052+PublicGoldByteExtraction.sourceBound ctx inputs 0)

-- Rejected adapters retain their measured cost and never run field extraction.
/-- info: true -/
#guard_msgs in
#eval let badRoot := one ++ [0]
  let parsed := PublicSourceByteInputs.read zero badRoot hashes
  let result := PublicGoldByteExtraction.run zero badRoot ctx hashes 0 (by decide)
  decide (result.value.isNone ∧ result.cost = parsed.cost+2 ∧ result.cost ≤ 589*hashes.length+1051)

/-- info: [455, 586, 1768, 2816] -/
#guard_msgs in
#eval [(PublicSourceByteInputs.digest zero).cost,(PublicSourceByteInputs.storedDigest zero).cost,
  (PublicSourceByteInputs.log hashes).cost,(PublicSourceByteInputs.read zero one hashes).cost]
