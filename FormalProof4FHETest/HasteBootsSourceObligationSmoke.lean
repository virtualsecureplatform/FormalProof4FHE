module
import all FormalProof4FHE.HasteBoots.SourceOpeningObligationLifetime
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke

namespace FormalProof4FHE.HasteBoots.SourceObligationSmoke
open HasteBootsBatchMeaningSmoke (ctx world work prepared usize root)
open NativeFields (Goldilocks)
open OracleProgram (run)
noncomputable section

/-- Two original right queries remain indexed although one response group is shared. -/
example : work.binding.queries.val.length = 2 ∧ work.evaluations.length = 1 ∧
    NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨0,by decide +kernel⟩ =
      NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨1,by decide +kernel⟩ := by decide +kernel

example : work.binding.queries.val[0]? ≠ work.binding.queries.val[1]? := by decide +kernel

/-- Every original query, including the non-owner member, gets its own actual interpretation. -/
example (index : NativeGoldBatchRectangularData.Query work) :
    NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val
      ⟨(work.binding.queries.val.get index).models,none⟩ = some (BatchOpeningNativeObligation.query ctx world work prepared index) :=
  BatchOpeningNativeObligation.query_read ctx world work prepared index

/-- The original batch prefix supplies both public split dimensions. -/
example : ctx.parameters.numVariables.val = ctx.parameters.leftVariables.val +
      (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) ∧
    ctx.parameters.code.messageLength.val = 2^(ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) :=
  BatchOpeningNativeObligation.dimensions ctx world work prepared

/-- Alias spelling and batch position are preserved while field meaning transfers. -/
def row : NativeLookupRequestWire.Row := ⟨[1,0,0],by decide⟩
def aliasRow : NativeLookupRequestWire.Row := ⟨[usize (NativeFields.goldilocksModulus+1),0,0],by decide⟩
example : row ≠ aliasRow ∧ NativeGoldPcsClaim.equal row.val aliasRow.val = true := by decide +kernel

example : row.val.map NativeFieldRepresentation.goldValue = List.ofFn (fun lane : Fin 3 => if lane.val = 0 then 1 else 0) :=
  BatchOpeningNativeObligation.alias_encoded 3 row aliasRow (by decide +kernel) _ (by decide +kernel)

example : (fun lane : Fin 3 => NativeGoldBatchFixedResponseData.claimed
    (⟨[row,aliasRow],by decide⟩ : NativePrefixCodec.Vector NativeLookupRequestWire.Row) 1 lane.val) =
      fun lane => if lane.val = 0 then 1 else 0 :=
  BatchOpeningNativeObligation.claimed_of_encoded 3 _ 1 aliasRow rfl _ (by decide +kernel)

def frames : List TranscriptFrame.Frame :=
  [⟨0,NativeTranscript.utf8 "protocol",NativeTranscript.utf8 "HasteBoots framed SHAKE256 v1"⟩,
   ⟨0,NativeTranscript.utf8 "application",[]⟩,
   ⟨0,NativeTranscript.utf8 "trusted profile",List.ofFn root⟩]

theorem parent_frames : ctx.parent.input = TranscriptFrame.encodeMany frames := by
  change (NativeTranscript.new [] root).input = _
  simp only [NativeTranscript.new,NativeTranscript.absorb,frames,TranscriptFrame.encodeMany,
    List.nil_append,List.append_nil,List.append_assoc]

theorem valid_frames : ∀ frame ∈ frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> unfold TranscriptFrame.Valid <;> decide +kernel

/-- Strict parsing of the original batch nonce yields the common-source
obligation equivalence, retaining the existential original query index. -/
example (origin : CacheBackedCodeOrigin.Origin ctx) (history : List NativeTranscript.Observation) (radius : ℕ) :
    ∃ decoded, NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded ∧
      (NativeGoldBatchCausalCoverage.FalseClaim root ctx (origin.primitiveAt ctx rfl) work decoded history (origin.capacityAt ctx rfl) radius ↔
        BatchOpeningNativeObligation.Wrong root ctx (origin.primitiveAt ctx rfl) (origin.capacityAt ctx rfl) world work prepared decoded history radius) := by
  obtain ⟨context,_,parsed,_,_⟩ := NativeGoldBatchPreparedChallenge.prepared_link ctx world work prepared frames
    parent_frames valid_frames
    (by decide +kernel) (by decide +kernel)
  refine ⟨_,parsed,?_⟩
  exact BatchOpeningNativeObligation.false_claim_iff root ctx (origin.primitiveAt ctx rfl) (origin.capacityAt ctx rfl)
    world work prepared _ history radius ⟨frames,parent_frames,valid_frames,by decide +kernel⟩
    (by decide +kernel) parsed

end
end FormalProof4FHE.HasteBoots.SourceObligationSmoke
