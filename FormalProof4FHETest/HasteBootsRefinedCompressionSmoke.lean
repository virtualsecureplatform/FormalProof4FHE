module
import all FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery
import all FormalProof4FHE.HasteBoots.PrivateCoinCompressionClassProbability
import all FormalProof4FHETest.HasteBootsRefinedEqualitySmoke
import all FormalProof4FHETest.HasteBootsLookupScalarKernelSmoke
import all Init.Data.String.Defs

namespace HasteBootsRefinedCompressionSmoke
open FormalProof4FHE.HasteBoots
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFields (goldilocksModulus)
open HasteBootsSamplerAncestrySmoke (parent child worldReject)
open HasteBootsLookupScalarKernelSmoke (zeros)
noncomputable section

def initial := (NativeLookupChallenge.initialExecute (K := Goldilocks3) goldilocksModulus 3 7 child).1
def key : InputIndexedOracle.Input := match initial.control with
  | .compression field => field.phase.pending.input
  | _ => []
def suspended := (NativeLookupChallenge.execute goldilocksBasis 7 1 [[0]] 2 initial worldReject).1

theorem first_input_not_parent : NativeParentInputView.parseParent key = none := by
  apply HasteBootsRefinedEqualitySmoke.reject _ (by decide +kernel)
  decide +kernel

/-- The retained forbidden offsets, including the retry, keep kind-4 keys. -/
theorem rejected_offsets_not_parent : NativeParentInputView.parseParent
    (zeros.1.draws[1]'(by decide +kernel)).coefficients.phase.pending.input = none ∧
    NativeParentInputView.parseParent (zeros.1.draws[2]'(by decide +kernel)).coefficients.phase.pending.input = none := by
  constructor <;> apply HasteBootsRefinedEqualitySmoke.reject _ (by decide +kernel) <;> decide +kernel

theorem suspension_preserves_input :
    (match suspended.control with
      | .compression field => (field.phase.pending.input,field.phase.consumed.length)
      | _ => ([],0)) = (key,16) := by decide +kernel

theorem receipt_input_apart : key ≠ NativeFieldReceipt.input
    ⟨⟨[],fun _ => 0⟩,[],[1,2,3]⟩ := by decide +kernel

def parentKey := NativeForkAncestry.seedInput parent [7] [8]
def program : OracleProgram.Program Unit := .read parentKey 0 1 (fun _ => .read key 4096 1 (fun _ => .pure ()))

/-- A partial parent read causes auxiliary parent completion; the original
far-offset lookup read remains eligible after both completion passes. -/
theorem far_read_refinement_unseen :
    CausalStreamExposure.firstRead OracleProgramMachine.step (OracleProgram.runPrefix 1 program worldReject).run = some key ∧
    CausalStreamExposure.seen (ParentFactorFiber.extend (OracleProgram.runPrefix 1 program) worldReject).run.2 key = false := by
  constructor
  · decide +kernel
  · have oldFresh : CausalStreamExposure.seen (OracleProgram.runPrefix 1 program worldReject).run.2 key = false := by decide +kernel
    have parentFresh := ParentSeedCompletion.unseen (OracleProgram.runPrefix 1 program) worldReject key oldFresh first_input_not_parent
    apply ReceiptCandidateCompletion.unseen_extended (ParentSeedCompletion.extend (OracleProgram.runPrefix 1 program)) worldReject key parentFresh
    intro raw _
    let frames := (TranscriptFrame.decodeAll key).getD []
    have decoded : TranscriptFrame.decodeAll key = some frames := by decide +kernel
    rw [(TranscriptFrame.decodeAll_sound key frames decoded).2]
    exact NativeTranscript.receipt_not_frame_stream raw frames

/-- The parser still recognizes actual native parent keys in this same test. -/
theorem parent_recognized : (NativeParentInputView.parseParent parentKey).isSome = true := by
  let frames := (TranscriptFrame.decodeAll parent.input).getD []
  have bytes : parent.input = TranscriptFrame.encodeMany frames := by decide +kernel
  have decoded : TranscriptFrame.decodeAll parent.input = some frames := by decide +kernel
  have valid := (TranscriptFrame.decodeAll_sound parent.input frames decoded).1
  rw [parentKey,NativeForkAncestry.seedInput_parsed parent frames [7] [8] bytes valid (by decide +kernel) (by decide +kernel)]
  rfl

end
end HasteBootsRefinedCompressionSmoke
