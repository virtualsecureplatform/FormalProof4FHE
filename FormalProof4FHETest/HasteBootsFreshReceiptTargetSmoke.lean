module
import all FormalProof4FHE.HasteBoots.FreshReceiptTargetLifetime
import all FormalProof4FHE.HasteBoots.LookupSampleReceiptTargets
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.FreshReceiptTargetSmoke
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeReceiptPrefixView (key)
open OracleProgram (Program runPrefix)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open HasteBootsSamplerAncestrySmoke (child worldZero)
noncomputable section

def phase : NativeTranscript.FieldPhase := ⟨child,[],[1,2,3]⟩
def receiptFrame := ReceiptFrameView.frame worldZero phase
def input := TranscriptFrame.encodeMany [receiptFrame]

theorem decoded : TranscriptFrame.decodeAll input = some [receiptFrame] :=
  TranscriptFrame.decodeAll_encodeMany _ (by
    intro entry member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨by decide,by rw [show receiptFrame.message.length = 80 from NativeTranscript.receipt_length worldZero phase.consumed]; decide +kernel⟩)

theorem input_target : ReceiptDigestTargets.fromInput input = [InputIndexedOracle.block worldZero (key phase.consumed) 0 64] := by
  simp only [ReceiptDigestTargets.fromInput,ReceiptFrameView.frames,decoded,Option.getD_some,
    List.filter_cons,receiptFrame,ReceiptFrameView.frame,decide_true,ite_true,List.filter_nil,
    List.filterMap_cons,List.filterMap_nil,NativeTranscript.receipt_length,NativeFreshReceiptDigest.digest_receipt]

/-- One repeated transcript key adds one target, despite two independent
naming observations. Empty reads and starts do not add candidates. -/
example : ReceiptDigestTargets.targets [.start input,.output input 1 [],.output input 77 [0],.hash input [8]] =
    {InputIndexedOracle.block worldZero (key phase.consumed) 0 64} := by
  simp [ReceiptDigestTargets.targets,List.flatMap_cons,List.flatMap_nil,ReceiptDigestTargets.candidate,input_target]

def tail : Program Unit := .read (key phase.consumed) 0 64 (fun _ => .pure ())
def program : Program Unit := .start (key phase.consumed) (.read (key phase.consumed) 1000 0 (fun _ =>
  .hash (key phase.consumed) (fun _ => .read input 77 1 (fun _ => .read (key phase.consumed) 999 1 (fun _ => tail)))))
def past (world : World) := runPrefix 4 program world

theorem selected : FreshReceiptTargetRisk.select OracleProgramMachine.step (past worldZero).run = some phase.consumed := by
  change (if 0 < (1 : ℕ) ∧ CausalStreamExposure.seen
    [.start (key phase.consumed),.output (key phase.consumed) 1000 [],
      .hash (key phase.consumed) (List.ofFn (InputIndexedOracle.sha512 worldZero (key phase.consumed))),.output input 77 [0]]
      (key phase.consumed) = false then some (key phase.consumed) else none).bind ReceiptPayloadView.read = _
  simp [CausalStreamExposure.seen,CausalStreamExposure.touches,
    show input ≠ key phase.consumed from (NativeTranscript.receipt_not_frame_stream phase.consumed [receiptFrame]).symm,
    ReceiptPayloadView.read_key]

/-- The read at offset 999 is the only charged first read. A later offset-zero
full digest read is ineligible after that positive partial observation. -/
example : FreshReceiptTargetRisk.select OracleProgramMachine.step (runPrefix 5 program worldZero).run = none := by
  change (if 0 < (64 : ℕ) ∧ CausalStreamExposure.seen
    [Observation.start (key phase.consumed),.output (key phase.consumed) 1000 [],
      .hash (key phase.consumed) (List.ofFn (InputIndexedOracle.sha512 worldZero (key phase.consumed))),
      .output input 77 [0],.output (key phase.consumed) 999 [0]] (key phase.consumed) = false
      then some (key phase.consumed) else none).bind ReceiptPayloadView.read = none
  simp [CausalStreamExposure.seen,CausalStreamExposure.touches]

theorem actual_target : InputIndexedOracle.block worldZero (key phase.consumed) 0 64 ∈ ReceiptDigestTargets.targets (past worldZero).run.2 := by
  apply ReceiptDigestTargets.observed input [0] 77 worldZero phase _ (by simp)
  · change _ ∈ [Observation.start (key phase.consumed),.output (key phase.consumed) 1000 [],
      .hash (key phase.consumed) (List.ofFn (InputIndexedOracle.sha512 worldZero (key phase.consumed))),.output input 77 [0]]
    simp
  · simp only [ReceiptFrameView.frames,decoded,Option.getD_some,List.mem_filter,List.mem_singleton]
    exact ⟨rfl,rfl⟩

example : FreshReceiptTargetRisk.event OracleProgramMachine.step (past worldZero).run worldZero := by
  simpa only [FreshReceiptTargetRisk.event,selected] using actual_target


theorem targets_one : ReceiptDigestTargets.targets (past worldZero).run.2 =
    {InputIndexedOracle.block worldZero (key phase.consumed) 0 64} := by
  change ReceiptDigestTargets.targets [Observation.start (key phase.consumed),.output (key phase.consumed) 1000 [],
    .hash (key phase.consumed) (List.ofFn (InputIndexedOracle.sha512 worldZero (key phase.consumed))),.output input 77 [0]] = _
  simp [ReceiptDigestTargets.targets,List.flatMap_cons,List.flatMap_nil,ReceiptDigestTargets.candidate,
    ReceiptDigestTargets.from_receipt_key,input_target]

/-- The first far-offset read still has the exact full-block target law,
even after hashing that same key through the independent SHA-512 channel. -/
example : (InputIndexedOracle.law[|{other | (past other).run = (past worldZero).run}])
    {other | FreshReceiptTargetRisk.event OracleProgramMachine.step (past other).run other} = 1/(2 : ENNReal)^512 := by
  rw [FreshReceiptTargetRisk.conditional_event (past := past) OracleProgramMachine.step (OracleProgram.prefix_replay 4 program) worldZero]
  simp only [FreshReceiptTargetRisk.risk,selected,targets_one,Finset.card_singleton,Nat.cast_one]

end
end FormalProof4FHE.HasteBoots.FreshReceiptTargetSmoke
