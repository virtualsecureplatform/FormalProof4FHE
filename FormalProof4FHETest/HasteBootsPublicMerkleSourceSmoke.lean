module
import all FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
import all FormalProof4FHE.HasteBoots.ExecutableCommonSource
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
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
open NativeGoldColumnAuthentication (leafInput nodeInput)
private def digest (value : Fin 256) : NativeRootMessage.Digest := fun _ => value
private def leftRow : NativeLookupRequestWire.Row := ⟨[1,2],by decide⟩
private def rightRow : NativeLookupRequestWire.Row := ⟨[3,4],by decide⟩
private def node : ExecutableMerkleAvailability.Log := [⟨nodeInput (digest 11) (digest 12),digest 10⟩]
private def leaves : ExecutableMerkleAvailability.Log := [⟨leafInput leftRow,digest 11⟩,⟨leafInput rightRow,digest 12⟩]
private def fullLog : ExecutableMerkleAvailability.Log := node ++ leaves

/-- info: true -/
#guard_msgs in
#eval let word := ExecutableMerkleAvailability.reconstruct 1 (digest 0) fullLog (digest 10)
      decide (word.get 0 = leftRow ∧ word.get 1 = rightRow)

-- Freeze before the second leaf is logged: it keeps the empty fallback.
/-- info: true -/
#guard_msgs in
#eval let word := ExecutableMerkleAvailability.reconstruct 1 (digest 0) (node ++ leaves.take 1) (digest 10)
      decide (word.get 0 = leftRow ∧ word.get 1 = NativeGoldRawAvailability.emptyRow)

-- Node resolution retains the first matching response, including a non-node input.
/-- info: true -/
#guard_msgs in
#eval let word := ExecutableMerkleAvailability.reconstruct 1 (digest 0) (⟨[99],digest 10⟩ :: fullLog) (digest 10)
      decide (word.get 0 = NativeGoldRawAvailability.emptyRow ∧ word.get 1 = NativeGoldRawAvailability.emptyRow)

-- Leaf resolution skips malformed candidates, as the original filterMap does.
/-- info: true -/
#guard_msgs in
#eval let word := ExecutableMerkleAvailability.reconstruct 1 (digest 0) (⟨[99],digest 11⟩ :: fullLog) (digest 10)
      decide (word.get 0 = leftRow ∧ word.get 1 = rightRow)

/-- info: true -/
#guard_msgs in
#eval let word := ExecutableMerkleAvailability.reconstruct 0 (digest 0) leaves (digest 11)
      decide (word.get 0 = leftRow)

-- Both role decoders reject trailing bytes and truncated complete encodings.
/-- info: true -/
#guard_msgs in
#eval (NativeMerkleRoleDecoders.leaf.decode (leafInput leftRow ++ [0])).isNone &&
      (NativeMerkleRoleDecoders.leaf.decode ((leafInput leftRow).dropLast)).isNone &&
      (NativeMerkleRoleDecoders.node.decode (nodeInput (digest 11) (digest 12) ++ [0])).isNone &&
      (NativeMerkleRoleDecoders.node.decode ((nodeInput (digest 11) (digest 12)).dropLast)).isNone

-- A forged enormous row count with no payload fails without enumerating it.
/-- info: true -/
#guard_msgs in
#eval (NativeMerkleRoleDecoders.leaf.decode (NativeFieldWire.columnDomain ++
  NativeUsizeMessage.encode ⟨2^64-1,by decide⟩)).isNone

-- Raw u64 spelling is preserved, including a noncanonical lazy Goldilocks word.
/-- info: true -/
#guard_msgs in
#eval let row : NativeLookupRequestWire.Row := ⟨[⟨2^64-1,by decide⟩],by decide⟩
      decide (NativeMerkleRoleDecoders.leaf.decode (leafInput row) = some row)

-- Compose public-log reconstruction with coefficient extraction over Goldilocks.
/-- info: true -/
#guard_msgs in
#eval let log : ExecutableMerkleAvailability.Log := node ++
        [⟨leafInput leftRow,digest 11⟩,⟨leafInput leftRow,digest 12⟩]
      let rows := ExecutableMerkleAvailability.reconstruct 1 (digest 0) log (digest 10)
      let raw : Fin 2 → Fin 1 → Fin 2 → NativeFields.Goldilocks :=
        fun pos _ lane => ((rows.get pos).val[lane.val]?.getD 0).val
      let table := ExecutableSourceCoefficients.extract (m := 1) (b := 2) (size := 2) 0
        (fun pos : Fin 2 => (pos.val : NativeFields.Goldilocks)) (by decide) raw
      decide ((table.get 0).get 0 = 1 ∧ (table.get 0).get 1 = 2)
