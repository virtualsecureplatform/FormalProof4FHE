module
public import FormalProof4FHE.HasteBoots.ScalarExecutionRecovery
@[expose] public section

/-! Recovered packet associations imply agreement of the original and
reconstructed native execution through an active original scalar request. -/
namespace FormalProof4FHE.HasteBoots.ScalarExecutionPrefixAgreement
open InputIndexedOracle (Input World)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)

/-- Native preparation never changes the current round counter. -/
theorem prepare_round (statement : Statement) (proof : Proof) (machine : Machine) :
    match NativeScalarBatchVerifier.prepare statement proof machine with
    | .inl next => next.state.round = machine.state.round
    | .inr (next,_) => next.state.round = machine.state.round := by
  cases head : statement.infos.val.head? with
  | none => simp only [NativeScalarBatchVerifier.prepare,head]; rfl
  | some first =>
    by_cases inside : machine.state.round < first.numVariables.val
    · by_cases fits : machine.state.round < 2^64
      · cases found : NativeScalarBatchRoundPacket.packet ⟨machine.state.round,fits⟩ proof with
        | none => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found]; rfl
        | some packet =>
          cases checked : NativeScalarBatchPreflight.bindCheckedRound machine.state.transcript packet machine.state.expected with
          | error error => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found,checked]; rfl
          | ok transcript => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found,checked]
      · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_right fits]; rfl
    · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_false]

theorem after_field_round (machine : Machine) (packet : RoundPacket) (status : NativeFieldVector.Status) :
    machine.state.round ≤ (NativeScalarBatchVerifier.afterField machine packet status).state.round := by
  cases status with
  | suspended field => exact le_rfl
  | finished coefficients transcript =>
    cases decoded : NativeGoldLookupProducer.decode coefficients.values with
    | none => simp only [NativeScalarBatchVerifier.afterField,decoded]; exact le_rfl
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none => simp only [NativeScalarBatchVerifier.afterField,decoded,updated]; exact le_rfl
      | some expected => simp only [NativeScalarBatchVerifier.afterField,decoded,updated]; exact Nat.le_succ _

theorem tick_round (statement : Statement) (proof : Proof) (machine : Machine) (world : World) :
    machine.state.round ≤ (NativeScalarBatchVerifier.tickExecute statement proof machine world).1.state.round := by
  cases control : machine.control with
  | finished claims => simp only [NativeScalarBatchVerifier.tickExecute,control]; exact le_rfl
  | failed error => simp only [NativeScalarBatchVerifier.tickExecute,control]; exact le_rfl
  | sampling packet field =>
    simpa only [NativeScalarBatchVerifier.tickExecute,control] using after_field_round machine packet
      (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).1
  | ready =>
    have kept := prepare_round statement proof machine
    cases prepared : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl next =>
      simp only [prepared] at kept
      simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,kept]
      exact Nat.le_refl _
    | inr pair =>
      obtain ⟨next,packet⟩ := pair
      simp only [prepared] at kept
      simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,kept]
      exact Nat.le_refl _

theorem execute_round (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) :
    machine.state.round ≤ (NativeScalarBatchVerifier.execute statement proof fuel machine world).1.state.round := by
  induction fuel generalizing machine with
  | zero => exact le_rfl
  | succ fuel ih => exact (tick_round statement proof machine world).trans (ih _)

theorem earlier_round (statement : Statement) (proof : Proof) (earlier later : ℕ) (ordered : earlier ≤ later)
    (machine : Machine) (world : World) :
    (NativeScalarBatchVerifier.execute statement proof earlier machine world).1.state.round ≤
      (NativeScalarBatchVerifier.execute statement proof later machine world).1.state.round := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [NativeScalarBatchVerifier.execute_add]
  exact execute_round statement proof extra _ world

/-- Every getter up to the selected ordinal agrees with the original proof.
Original associations are the facts supplied by execution coverage. -/
theorem getters (view : ScalarTranscriptPrefix.View) (original reconstructed : Proof)
    (built : ScalarPrefixProof.reconstruct view = some reconstructed)
    (first : NativeScalarBatchWire.Info) (head : view.history.statement.infos.val.head? = some first)
    (previous : ∀ pair ∈ view.history.rounds, NativeScalarBatchRoundPacket.packet pair.1.round original = some pair.1)
    (current : NativeScalarBatchRoundPacket.packet view.packet.round original = some view.packet)
    (index : NativeUsizeMessage.Usize) (inside : index.val ≤ view.packet.round.val) :
    NativeScalarBatchRoundPacket.packet index original = NativeScalarBatchRoundPacket.packet index reconstructed := by
  have ordinal := ScalarPrefixProof.reconstruct_ordinals view reconstructed built first head
  by_cases old : index.val < view.history.rounds.length
  · let pair := view.history.rounds[index.val]
    have found : view.history.rounds[index.val]? = some pair := List.getElem?_eq_getElem old
    have order := congrArg (fun rows => rows[index.val]?) ordinal.1
    simp only [List.getElem?_map,found,Option.map_some,List.getElem?_range old] at order
    have same : pair.1.round = index := Fin.ext (Option.some.inj order)
    rw [← same,previous pair (List.getElem_mem old)]
    exact (ScalarPrefixProof.reconstruct_prior view reconstructed built first head index.val pair found).symm
  · have same : index = view.packet.round := Fin.ext (by omega)
    rw [same,current,ScalarPrefixProof.reconstruct_current view reconstructed built first head]

/-- Original packet associations cover every earlier reached ready state,
using the native round counter's monotonicity rather than supplied per-tick
packet agreement certificates. -/
theorem execute_agreement (view : ScalarTranscriptPrefix.View) (original reconstructed : Proof)
    (built : ScalarPrefixProof.reconstruct view = some reconstructed)
    (first : NativeScalarBatchWire.Info) (head : view.history.statement.infos.val.head? = some first)
    (previous : ∀ pair ∈ view.history.rounds, NativeScalarBatchRoundPacket.packet pair.1.round original = some pair.1)
    (current : NativeScalarBatchRoundPacket.packet view.packet.round original = some view.packet)
    (fuel : ℕ) (machine : Machine) (world : World)
    (lastRound : (NativeScalarBatchVerifier.execute view.history.statement original fuel machine world).1.state.round = view.packet.round.val) :
    NativeScalarBatchVerifier.execute view.history.statement original fuel machine world =
      NativeScalarBatchVerifier.execute view.history.statement reconstructed fuel machine world := by
  apply ScalarProofPrefixExecution.execute_eq
  intro index bound _ round sameRound
  have monotone := earlier_round view.history.statement original index fuel (Nat.le_of_lt bound) machine world
  rw [lastRound] at monotone
  exact getters view original reconstructed built first head previous current round (by omega)

/-- Coverage and prefix agreement combined for an arbitrary original native
initialized run. The recovered replay starts at the original initial state,
and yields exactly the original state and full log through the active round. -/
theorem sampling (transcript result : NativeTranscript.Transcript) (before : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some before)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof)
    (fuel : ℕ) (world : World) (packet : RoundPacket) (field : NativeFieldVector.State)
    (active : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .sampling packet field) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover field.phase.pending.input = some configuration ∧
      configuration.view.history.statement = statement ∧ configuration.view.packet = packet ∧
      NativeScalarBatchVerifier.execute statement proof fuel (NativeScalarBatchVerifier.initial transcript statement proof) world =
        NativeScalarBatchVerifier.execute statement configuration.proof fuel (configuration.initial transcript.profile) world := by
  obtain ⟨rounds,reconstructed,found,_,previous,current⟩ := ScalarExecutionRecovery.sampling
    transcript result before statement proof decoded accepted statementFits domain fuel world packet field active
  let configuration : ScalarRecoveredReplay.Configuration := ⟨⟨ScalarExecutionTranscript.history before statement rounds,packet⟩,reconstructed⟩
  have recoverFound : ScalarRecoveredReplay.recover field.phase.pending.input = some configuration := found
  have built := (ScalarRecoveredReplay.recover_sound _ configuration recoverFound).2
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  have valid := NativeScalarBatchVerifierInvariant.execute_valid statement proof first preflight.1 preflight.2.1 head fuel
    (NativeScalarBatchVerifier.initial transcript statement proof) world
    (NativeScalarBatchVerifierInvariant.initial_valid transcript result statement proof first accepted)
  have phase := valid.2.2.2.2
  rw [active] at phase
  have exactPrefix := execute_agreement configuration.view proof reconstructed built first head previous current fuel
    (NativeScalarBatchVerifier.initial transcript statement proof) world phase.2.1.symm
  have parentEq : configuration.parent transcript.profile = transcript :=
    ScalarChallengeInputView.rebuild_transcript transcript before decoded
  have reconstructedOk := ScalarRecoveredReplay.initialized _ configuration recoverFound transcript.profile
  change NativeScalarBatchPreflight.beginVerify (configuration.parent transcript.profile) statement reconstructed =
    .ok (NativeScalarBatchWire.bindStatement (configuration.parent transcript.profile) statement) at reconstructedOk
  rw [parentEq,← preflight.2.2] at reconstructedOk
  have startEq : configuration.initial transcript.profile = NativeScalarBatchVerifier.initial transcript statement proof := by
    change NativeScalarBatchVerifier.initial (configuration.parent transcript.profile) statement reconstructed = _
    rw [parentEq]
    exact (ScalarProofPrefixExecution.initial_eq transcript result statement proof reconstructed accepted reconstructedOk).symm
  refine ⟨configuration,recoverFound,rfl,rfl,?_⟩
  rw [startEq]
  exact exactPrefix

end FormalProof4FHE.HasteBoots.ScalarExecutionPrefixAgreement
