module
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
private def emptyCtx : NativeGoldBatchPcsProgram.Context :=
  { ctx with parameters := { ctx.parameters with width := usize 0, code := { ctx.parameters.code with messageLength := usize 0 } } }
private def raw : DenseCommonSource.Columns NativeFields.Goldilocks 4 6 2 :=
  let domain := (NativeGoldExecutableExtraction.pointTableWithCost ctx).value
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane =>
    (1+row.val+lane.val : NativeFields.Goldilocks)+(2+row.val)*domain.get pos)))

-- Packing three, code width two, and original size three: one padding entry
-- per source row is discarded. Check every returned left/right/channel entry.
/-- info: true -/
#guard_msgs in
#eval let result := NativeGoldExecutableExtraction.extractPreparedWithCost ctx 0 (by decide) raw
      (List.finRange 2).all (fun left => (List.finRange 3).all (fun right =>
        (List.finRange 3).all (fun lane =>
          let row := left.val*3+lane.val
          let expected : NativeFields.Goldilocks := if right.val = 0 then 1+row else 2+row
          decide ((((result.value.get left).get right).get lane) = expected))))

-- Complete runs, including measured charges, agree with the function wrapper.
/-- info: true -/
#guard_msgs in
#eval let prepared := NativeGoldExecutableExtraction.extractPreparedWithCost ctx 0 (by decide) raw
      let wrapped := NativeGoldExecutableExtraction.extractWithCost ctx 0 (by decide)
        (NativeGoldExecutableExtraction.preparedWord ctx raw)
      decide (prepared.value = wrapped.value ∧ prepared.cost = wrapped.cost)

-- A frozen empty public log keeps the explicit zero fallback through the new
-- direct stored-column path, including original-message padding removal.
/-- info: true -/
#guard_msgs in
#eval let result := NativeGoldPublicSource.extract digest digest ctx [] 0 (by decide)
      result.toList.all (fun row => row.toList.all (fun entry => entry.toList.all (fun x => decide (x = 0))))

-- An out-of-codeword source retains the fail-closed zero table, with no
-- constructor or primitive-root premise needed for total executable behavior.
/-- info: true -/
#guard_msgs in
#eval let corrupted := Vector.ofFn (fun pos : Fin 4 => Vector.ofFn (fun row : Fin 6 =>
        Vector.ofFn (fun lane : Fin 2 => DenseCommonSource.input raw pos row lane +
          if pos.val = 0 then 1 else 0)))
      let result := NativeGoldExecutableExtraction.extractPreparedWithCost ctx 0 (by decide) corrupted
      result.value.toList.all (fun row => row.toList.all (fun entry => entry.toList.all (fun x => decide (x = 0))))

-- Zero packing and zero original size still return both original left rows.
/-- info: true -/
#guard_msgs in
#eval let emptyRaw : DenseCommonSource.Columns NativeFields.Goldilocks 4 0 2 := Vector.ofFn (fun _ : Fin 4 => Vector.ofFn (fun row : Fin 0 => Fin.elim0 row))
      let result := NativeGoldExecutableExtraction.extractPreparedWithCost emptyCtx 0 (by decide) emptyRaw
      decide (result.value.toList.map (fun row => row.toList.length) = [0,0])
