module
public import FormalProof4FHE.HasteBoots.ScalarProofPrefixExecution
@[expose] public section

/-! Exact scalar transcript history through the original native execution.
Receipt bytes are obtained from actual finalization, never interpreted as
challenge values. Failed/terminal states cannot start a later scalar request. -/
namespace FormalProof4FHE.HasteBoots.ScalarExecutionTranscript
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeRootMessage (Digest)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
open TranscriptFrame (Frame encodeMany)

abbrev Rounds := List (RoundPacket × Input)
def history (before : List Frame) (statement : Statement) (rounds : Rounds) : ScalarTranscriptPrefix.History :=
  ⟨before,statement,rounds⟩
def base (before : List Frame) (statement : Statement) (profile : Digest) (rounds : Rounds) : Transcript :=
  ⟨encodeMany (history before statement rounds).frames,profile⟩

def Records (rounds : Rounds) (machine : Machine) : Prop :=
  rounds.map Prod.fst = machine.completed.map (fun entry => entry.packet) ∧
    ∀ pair ∈ rounds, pair.2.length = 80

def Aligned (before : List Frame) (statement : Statement) (profile : Digest) (machine : Machine) : Prop :=
  match machine.control with
  | .ready => ∃ rounds, Records rounds machine ∧ machine.state.transcript = base before statement profile rounds
  | .sampling packet field => ∃ rounds, Records rounds machine ∧
      machine.state.transcript = NativeScalarBatchWire.bindRound (base before statement profile rounds) packet ∧
      field.phase.pending = (ScalarRoundChallengeMeaning.phase (base before statement profile rounds) packet).pending ∧
      field.phase.label = NativeScalarBatchWire.challengeLabel
  | _ => True

theorem base_nil (before : List Frame) (statement : Statement) (profile : Digest) :
    base before statement profile [] = NativeScalarBatchWire.bindStatement ⟨encodeMany before,profile⟩ statement := by
  simp only [base,history,ScalarTranscriptPrefix.History.frames,List.flatMap_nil,List.append_nil,
    SingleOpeningExposure.encodeMany_append,encodeMany]
  rfl

theorem base_snoc (before : List Frame) (statement : Statement) (profile : Digest) (rounds : Rounds)
    (packet : RoundPacket) (receipt : Input) :
    base before statement profile (rounds ++ [(packet,receipt)]) =
      NativeTranscript.absorb (ScalarRoundChallengeMeaning.phase (base before statement profile rounds) packet).pending
        5 NativeScalarBatchWire.challengeLabel receipt := by
  have framed := ScalarChallengeInputView.phase_input
    (ScalarChallengeInputView.View.mk (history before statement rounds).frames packet) profile
  change (ScalarRoundChallengeMeaning.phase (base before statement profile rounds) packet).pending.input = _ at framed
  change (⟨encodeMany (history before statement (rounds ++ [(packet,receipt)])).frames,profile⟩ : Transcript) =
    ⟨(ScalarRoundChallengeMeaning.phase (base before statement profile rounds) packet).pending.input ++
      TranscriptFrame.encode (ScalarTranscriptPrefix.receiptFrame receipt),profile⟩
  rw [framed]
  apply congrArg (fun input => (⟨input,profile⟩ : Transcript))
  simp only [history,ScalarTranscriptPrefix.History.frames,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,ScalarTranscriptPrefix.block,ScalarChallengeInputView.View.frames,
    SingleOpeningExposure.encodeMany_append,encodeMany,List.append_nil,List.append_assoc]

/-- A native drive retains the same header even when it suspends or rejects. -/
theorem drive_header (p fuel : ℕ) (field : NativeFieldVector.State) (world : World) :
    (NativeFieldVector.stateOf (NativeFieldVector.driveExecute p fuel field world).1).phase.pending = field.phase.pending ∧
    (NativeFieldVector.stateOf (NativeFieldVector.driveExecute p fuel field world).1).phase.label = field.phase.label := by
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  exact NativeFieldVector.header_preserved p fuel field world

/-- Successful native finalization supplies the literal receipt and its size. -/
theorem finished_receipt (p fuel : ℕ) (field completed : NativeFieldVector.State) (world : World) (next : Transcript)
    (finished : (NativeFieldVector.driveExecute p fuel field world).1 = .finished completed next) :
    ∃ receipt, receipt.length = 80 ∧ next = NativeTranscript.absorb field.phase.pending 5 field.phase.label receipt := by
  have header := NativeFieldVector.header_preserved p fuel field world
  unfold NativeFieldVector.driveExecute NativeFieldVector.finishExecute at finished
  dsimp only at finished
  split at finished
  next done =>
    cases finished
    refine ⟨(NativeTranscript.receipt world (NativeFieldVector.execute p fuel field world).1.phase.consumed).run.1,
      NativeTranscript.receipt_length _ _,?_⟩
    change NativeTranscript.absorb (NativeFieldVector.execute p fuel field world).1.phase.pending 5
      (NativeFieldVector.execute p fuel field world).1.phase.label _ = _
    rw [header.1,header.2]
    rfl
  next => contradiction

theorem initial (before : List Frame) (statement : Statement) (proof : Proof) (profile : Digest) (result : Transcript)
    (accepted : NativeScalarBatchPreflight.beginVerify ⟨encodeMany before,profile⟩ statement proof = .ok result) :
    Aligned before statement profile (NativeScalarBatchVerifier.initial ⟨encodeMany before,profile⟩ statement proof) := by
  rw [NativeScalarBatchVerifier.initial_success _ result statement proof accepted]
  refine ⟨[],⟨rfl,by simp⟩,?_⟩
  exact ((NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mp accepted).2.2.trans (base_nil before statement profile).symm

/-- Actual field completion appends the packet and its actual receipt to the
retained history only on the native successful interpolation branch. -/
theorem after_field (before : List Frame) (statement : Statement) (profile : Digest) (machine : Machine)
    (packet : RoundPacket) (field : NativeFieldVector.State) (world : World)
    (active : machine.control = .sampling packet field) (aligned : Aligned before statement profile machine) :
    Aligned before statement profile (NativeScalarBatchVerifier.afterField machine packet
      (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).1) := by
  rw [Aligned,active] at aligned
  obtain ⟨rounds,records,parent,pending,label⟩ := aligned
  have header := drive_header NativeFields.goldilocksModulus 1 field world
  cases result : (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).1 with
  | suspended next =>
    rw [result] at header
    exact ⟨rounds,records,parent,header.1.trans pending,header.2.trans label⟩
  | finished completed transcript =>
    obtain ⟨receipt,length,finished⟩ := finished_receipt NativeFields.goldilocksModulus 1 field completed world transcript result
    cases decoded : NativeGoldLookupProducer.decode completed.values with
    | none => simp only [NativeScalarBatchVerifier.afterField,decoded,Aligned,NativeScalarBatchVerifier.fail]
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none => simp only [NativeScalarBatchVerifier.afterField,decoded,updated,Aligned,NativeScalarBatchVerifier.fail]
      | some expected =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated,Aligned]
        refine ⟨rounds ++ [(packet,receipt)],⟨?_,?_⟩,?_⟩
        · simpa only [List.map_append,List.map_cons,List.map_nil] using congrArg (fun rows => rows ++ [packet]) records.1
        · intro pair member
          rcases List.mem_append.mp member with old | new
          · exact records.2 pair old
          · cases List.mem_singleton.mp new; exact length
        · rw [finished,pending,label,base_snoc]

/-- Exact alignment is preserved by every original native tick. -/
theorem tick (before : List Frame) (statement : Statement) (proof : Proof) (profile : Digest)
    (first : NativeScalarBatchWire.Info) (shape : NativeScalarBatchPreflight.proofShape statement proof = true)
    (admitted : NativeScalarBatchPreflight.dimensions statement = true)
    (head : statement.infos.val.head? = some first) (machine : Machine) (world : World)
    (aligned : Aligned before statement profile machine) :
    Aligned before statement profile (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 := by
  cases control : machine.control with
  | finished claims => simp only [NativeScalarBatchVerifier.tickExecute,control,Aligned]
  | failed error => simp only [NativeScalarBatchVerifier.tickExecute,control,Aligned]
  | sampling packet field =>
    simpa only [NativeScalarBatchVerifier.tickExecute,control] using after_field before statement profile machine packet field world control aligned
  | ready =>
    rw [Aligned,control] at aligned
    obtain ⟨rounds,records,parent⟩ := aligned
    by_cases inside : machine.state.round < first.numVariables.val
    · have fits : machine.state.round < 2^64 := inside.trans first.numVariables.isLt
      obtain ⟨packet,found,_,_,_⟩ := NativeScalarBatchRoundPacket.packet_success statement proof
        ⟨machine.state.round,fits⟩ first shape admitted head inside
      cases checked : NativeScalarBatchPreflight.check packet.messages.val machine.state.expected with
      | false =>
        simp only [NativeScalarBatchVerifier.tickExecute,control,NativeScalarBatchVerifier.prepare,head,inside,
          ite_true,dite_eq_left fits,found,NativeScalarBatchPreflight.bindCheckedRound,checked,Bool.false_eq_true,ite_false,
          NativeScalarBatchVerifier.fail,Aligned]
      | true =>
        simp only [NativeScalarBatchVerifier.tickExecute,control,NativeScalarBatchVerifier.prepare,head,inside,
          ite_true,dite_eq_left fits,found,NativeScalarBatchPreflight.bindCheckedRound,checked,Aligned]
        refine ⟨rounds,records,?_,?_,?_⟩
        · rw [parent]
        · rw [parent]; rfl
        · rfl
    · simp only [NativeScalarBatchVerifier.tickExecute,control,NativeScalarBatchVerifier.prepare,head,inside,ite_false,Aligned]

theorem execute (before : List Frame) (statement : Statement) (proof : Proof) (profile : Digest)
    (first : NativeScalarBatchWire.Info) (shape : NativeScalarBatchPreflight.proofShape statement proof = true)
    (admitted : NativeScalarBatchPreflight.dimensions statement = true)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (machine : Machine) (world : World)
    (aligned : Aligned before statement profile machine) :
    Aligned before statement profile (NativeScalarBatchVerifier.execute statement proof fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact aligned
  | succ fuel ih => exact ih _ (tick before statement proof profile first shape admitted head machine world aligned)

/-- Every prefix of an actual initialized native verifier has the recovered
history shape whenever it is ready or sampling. -/
theorem initialized (transcript result : Transcript) (before : List Frame) (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (fuel : ℕ) (world : World) :
    Aligned before statement transcript.profile
      (NativeScalarBatchVerifier.execute statement proof fuel (NativeScalarBatchVerifier.initial transcript statement proof) world).1 := by
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  have restored := ScalarChallengeInputView.rebuild_transcript transcript before decoded
  have start := initial before statement proof transcript.profile result (by rw [restored]; exact accepted)
  rw [restored] at start
  exact execute before statement proof transcript.profile first preflight.1 preflight.2.1 head fuel _ world start

end FormalProof4FHE.HasteBoots.ScalarExecutionTranscript
