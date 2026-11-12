module
public import FormalProof4FHE.HasteBoots.ExecutionDerivedIdentityWork
@[expose] public section

/-! Executed lookup metadata and allocated helper parameters bound the
scalar statement. Original root bytes pay for all jobs, without a count cutoff. -/
namespace FormalProof4FHE.HasteBoots.CheckedScalarStatementSize
open NativeUsizeMessage (Usize)
open NativeScalarBatchWire (Info Statement)
open NativeSharedLookupStatement (Request Prepared)
open NativeTranscript (Transcript)

theorem usize_small (value : Usize) (small : value.val < 251) :
    (NativeUsizeMessage.encode value).length = 1 := by
  simp only [NativeUsizeMessage.encode,small,dite_eq_left,List.length_cons,List.length_nil]

theorem gold_length (value : NativeFieldWire.GoldExtension) :
    (NativeFieldWire.goldExtension value).length ≤ 28 := by
  have body := CheckedPcsMetadataSize.flatMap_length_le NativeUsizeMessage.encode (List.ofFn value) 9
    (fun word _ => NativeUsizeMessage.encode_length word)
  have header := usize_small (⟨3,by decide⟩ : Usize) (by decide)
  change (NativeUsizeMessage.encode ⟨3,by decide⟩ ++ (List.ofFn value).flatMap NativeUsizeMessage.encode).length ≤ _
  rw [List.length_append,header]
  simp only [List.length_ofFn] at body
  omega

theorem info_length (info : Info) (degree : info.maxMultiplicands.val ≤ 4) (numVars : info.numVariables.val < 64) :
    (NativeScalarBatchWire.infoCodec.encode info).length = 2 := by
  rw [NativeScalarBatchWire.info_encode,List.length_append,usize_small _ (by omega),usize_small _ (by omega)]

theorem infos_small (n : Usize) (requests : List Request) (info : Info)
    (member : info ∈ NativeSharedLookupStatement.infos n requests) : info.maxMultiplicands.val ≤ 4 := by
  obtain ⟨request,_,atRequest⟩ := List.mem_flatMap.mp member
  obtain ⟨_,_,atPair⟩ := List.mem_flatMap.mp atRequest
  simp only [NativeSharedLookupStatement.pair,List.mem_cons,List.not_mem_nil,or_false] at atPair
  rcases atPair with rfl | rfl
  · exact (by decide +kernel : 1 ≤ 4)
  · split
    · exact (by decide +kernel : 3 ≤ 4)
    · exact Nat.le_refl 4

theorem built_length (n : Usize) (requests : List Request) (jobs : List Prepared)
    (multiplicities : List (List NativeFieldRepresentation.GoldWord)) (statement : Statement)
    (built : NativeSharedLookupStatement.build n requests jobs multiplicities = some statement)
    (numVars : n.val < 64) (sameCount : statement.infos.val.length = statement.claims.val.length) :
    (NativeScalarBatchWire.statementCodec.encode statement).length ≤ 18+60*jobs.length := by
  have spec := NativeSharedLookupStatement.build_spec n requests jobs multiplicities statement built
  have count := NativeSharedLookupStatement.initialClaims_length multiplicities jobs statement.claims.val spec.2
  have infos := CheckedPcsMetadataSize.flatMap_length_le NativeScalarBatchWire.infoCodec.encode statement.infos.val 2 (by
    intro info member
    rw [spec.1] at member
    apply Nat.le_of_eq (info_length info (infos_small n requests info member) ?_)
    rw [NativeSharedLookupStatement.infos_numVariables n requests info member]
    exact numVars)
  have claims := CheckedPcsMetadataSize.flatMap_length_le NativeFieldWire.goldExtension statement.claims.val 28 (fun value _ => gold_length value)
  have first := NativeUsizeMessage.encode_length (⟨statement.infos.val.length,statement.infos.property⟩ : Usize)
  have second := NativeUsizeMessage.encode_length (⟨statement.claims.val.length,statement.claims.property⟩ : Usize)
  rw [NativeScalarBatchWire.statement_encode]
  simp only [List.length_append]
  change (NativePrefixCodec.usize.encode ⟨statement.infos.val.length,statement.infos.property⟩).length ≤ 9 at first
  change (NativePrefixCodec.usize.encode ⟨statement.claims.val.length,statement.claims.property⟩).length ≤ 9 at second
  rw [sameCount,count] at infos
  rw [count] at claims
  omega

theorem fits_of_roots (statement : Statement) (jobs : List Prepared)
    (roots : NativePrefixCodec.Vector NativeRootMessage.Digest)
    (lengthBound : (NativeScalarBatchWire.statementCodec.encode statement).length ≤ 18+60*jobs.length)
    (rootCount : roots.val.length = jobs.length)
    (rootsFit : (NativeRootMessage.encode roots.val roots.property).length < TranscriptFrame.lengthLimit) :
    (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit := by
  rw [NativeRootMessage.encode_length] at rootsFit
  have payload : 64*roots.val.length < TranscriptFrame.lengthLimit := by omega
  rw [rootCount] at payload
  norm_num [TranscriptFrame.lengthLimit] at payload ⊢
  omega

variable {Memory A : Type}
    {ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A}
    {world : InputIndexedOracle.World}

theorem allocated_numVariables (allocation : AllocatedFamilyFunctions.Allocation ctx) : ctx.helper.numVariables.val < 64 := by
  obtain ⟨entry,_,good,same⟩ := AllocatedLookupContext.helper_entry allocation.entries allocation.reachable allocation.helperHandle
    allocation.references allocation.template ctx allocation.assembled
  have built := NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2
  have parameters := congrArg (fun value => value.helper) same
  rw [parameters]
  exact (NativeBrakedownParameters.build_spec NativeGoldBlockCode.description _ _ built).basic.2.2.1

theorem retained_fits (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit := by
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world data.origin.ready data.origin.prepared
  have small : data.origin.geometry.geometry.1.val < 64 := by
    rw [← data.origin.helper_dimensions.1]
    exact allocated_numVariables allocation
  exact fits_of_roots data.origin.ready.statement data.origin.ready.jobs ctx.proof.roots
    (built_length _ _ _ _ _ contract.built small contract.dimensions.1) contract.rootCount
    (CallerFramedAllocatedJob.domain data).rootsFit

end FormalProof4FHE.HasteBoots.CheckedScalarStatementSize
