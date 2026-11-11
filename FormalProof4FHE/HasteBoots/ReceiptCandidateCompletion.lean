module
public import FormalProof4FHE.HasteBoots.ReceiptPayloadView
public import FormalProof4FHE.HasteBoots.OracleProgramHistory
public import FormalProof4FHE.HasteBoots.NativeFieldReceipt
public import FormalProof4FHE.HasteBoots.NativeEarlyReceiptPrefixRisk
@[expose] public section

/-! Analysis-only completion of all earlier named receipt keys. The entire
old packet is retained. No scalar input is read when it differs from these
keys; full receipt digests then become fixed on the refined replay fiber. -/
namespace FormalProof4FHE.HasteBoots.ReceiptCandidateCompletion
open InputIndexedOracle (Input World Coordinate bytes block)
open NativeTranscript (Observation Execution)
open NativeReceiptPrefixView (key)
open OracleProgram (Program bind run)
open scoped Classical
noncomputable section

def program : List Input → Program Unit
  | [] => .pure ()
  | raw :: rest => bind (NativeTranscriptProgram.query (key raw) 64) (fun _ => program rest)

def observations (raws : List Input) (world : World) : List Observation :=
  raws.flatMap (fun raw => [.start (key raw),.output (key raw) 0 (bytes world (key raw) 0 64)])

theorem run_program (raws : List Input) (world : World) :
    (run (program raws) world).run = ((),observations raws world) := by
  induction raws with
  | nil => rfl
  | cons raw rest ih =>
    simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind,NativeTranscriptProgram.run_query,
      NativeTranscript.query,WriterT.run_mk,ih,observations,List.flatMap_cons]

theorem output_member (raws : List Input) (world : World) (raw : Input) (member : raw ∈ raws) :
    .output (key raw) 0 (bytes world (key raw) 0 64) ∈ observations raws world := by
  exact List.mem_flatMap.mpr ⟨raw,member,by simp⟩

theorem known_coordinate (history : List Observation) (world : World) (raw : Input)
    (member : .output (key raw) 0 (bytes world (key raw) 0 64) ∈ history) (position : Fin 64) :
    (.inl (key raw,position.val) : Coordinate) ∈ ObservationReplay.footprint history := by
  apply Finset.mem_biUnion.mpr
  refine ⟨_,List.mem_toFinset.mpr member,?_⟩
  apply (NativeShakeProjection.output_coordinate _ _ _ _).mpr
  exact ⟨rfl,by omega,by simpa only [InputIndexedOracle.bytes_length,Nat.zero_add] using position.isLt⟩

theorem unseen (raws : List Input) (world : World) (input : Input)
    (apart : ∀ raw ∈ raws, key raw ≠ input) : CausalStreamExposure.seen (observations raws world) input = false := by
  apply List.any_eq_false.mpr
  intro entry present
  obtain ⟨raw,member,present⟩ := List.mem_flatMap.mp present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl
  · simp only [CausalStreamExposure.touches,Bool.false_eq_true,not_false_eq_true]
  · simp only [CausalStreamExposure.touches,apart raw member,false_and,decide_false,Bool.false_eq_true,not_false_eq_true]

def extend {A : Type} (past : World → Execution A) :=
  OracleProgramHistory.extend past (fun packet => program (ReceiptPayloadView.payloads packet.2).toList)

theorem replay {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past) :
    ObservationReplay.Replayable (extend past) := OracleProgramHistory.replay old _

theorem old_packet {A : Type} (past : World → Execution A) (world other : World)
    (same : (extend past other).run = (extend past world).run) : (past other).run = (past world).run :=
  congrArg (fun packet => packet.1.1) same

theorem named_output {A : Type} (past : World → Execution A) (world : World) (raw : Input)
    (named : raw ∈ ReceiptPayloadView.payloads (past world).run.2) :
    .output (key raw) 0 (bytes world (key raw) 0 64) ∈ (extend past world).run.2 := by
  change _ ∈ (past world).run.2 ++ (run (program _) world).run.2
  rw [run_program]
  exact List.mem_append_right _ (output_member _ world raw (Finset.mem_toList.mpr named))

def digest (world : World) (raw : Input) : NativeRootMessage.Digest := block world (key raw) 0 64

theorem digest_on_fiber {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (world other : World) (raw : Input) (named : raw ∈ ReceiptPayloadView.payloads (past world).run.2)
    (same : (extend past other).run = (extend past world).run) : digest other raw = digest world raw := by
  have truthful := (replay old).truthful other
  rw [same] at truthful
  have equal := ObservationReplay.same_of_agrees world other _ ((replay old).truthful world) truthful
  funext position
  exact equal _ (by simpa only [Nat.zero_add] using known_coordinate _ world raw (named_output past world raw named) position)

theorem unseen_extended {A : Type} (past : World → Execution A) (world : World) (input : Input)
    (fresh : CausalStreamExposure.seen (past world).run.2 input = false)
    (apart : ∀ raw ∈ ReceiptPayloadView.payloads (past world).run.2, key raw ≠ input) :
    CausalStreamExposure.seen (extend past world).run.2 input = false := by
  change CausalStreamExposure.seen ((past world).run.2 ++ (run (program _) world).run.2) input = false
  rw [run_program]
  simp only [CausalStreamExposure.seen,List.any_append]
  rw [show (past world).run.2.any (CausalStreamExposure.touches input) = false from fresh,
    show (observations _ world).any (CausalStreamExposure.touches input) = false from
      unseen _ world input (fun raw member => apart raw (Finset.mem_toList.mp member))]
  rfl

theorem framed_unseen_extended {A : Type} (past : World → Execution A) (world : World) (frames : List TranscriptFrame.Frame)
    (fresh : CausalStreamExposure.seen (past world).run.2 (TranscriptFrame.encodeMany frames) = false) :
    CausalStreamExposure.seen (extend past world).run.2 (TranscriptFrame.encodeMany frames) = false :=
  unseen_extended past world _ fresh (fun raw _ => NativeTranscript.receipt_not_frame_stream raw frames)


open OracleSpec OracleComp MeasureTheory ProbabilityTheory in
/-- Completing earlier receipt keys preserves the exact fresh-block law of
an unseen framed stream under the refined posterior, not just marginally. -/
theorem framed_fresh_targets {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (world : World) (frames : List TranscriptFrame.Frame) (count : ℕ)
    (targets : Finset (Fin count → InputIndexedOracle.Byte))
    (fresh : CausalStreamExposure.seen (past world).run.2 (TranscriptFrame.encodeMany frames) = false) :
    (InputIndexedOracle.law[|{other | (extend past other).run = (extend past world).run}])
      {other | block other (TranscriptFrame.encodeMany frames) 0 count ∈ targets} =
        (targets.card : ENNReal)/(256 : ENNReal)^count :=
  NativeEarlyReceiptPrefixRisk.fresh_targets (replay old) world _ count targets
    (framed_unseen_extended past world frames fresh)

end
end FormalProof4FHE.HasteBoots.ReceiptCandidateCompletion
