module
public import FormalProof4FHE.HasteBoots.ScalarRecoveredUnboundedLaw
@[expose] public section

/-! Every active and retained completed native scalar collector is an actual
finite prefix of its original three-coordinate reader, including all rejected
candidates. Finalization does not replace or resample its coefficient state. -/
namespace FormalProof4FHE.HasteBoots.ScalarCollectorTrace
open InputIndexedOracle (World)
open NativeTranscript (Transcript FieldPhase)
open NativeScalarBatchWire (Statement RoundPacket challengeLabel)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine CompletedRound)
open NativeFields (goldilocksModulus)

def start (field : NativeFieldVector.State) : FieldPhase := ⟨field.phase.pending,challengeLabel,[]⟩
def Source (field : NativeFieldVector.State) (world : World) : Prop :=
  ∃ fuel, (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial (start field) 3) world).1 = field

def Traced (machine : Machine) (world : World) : Prop :=
  (match machine.control with | .sampling _ field => Source field world | _ => True) ∧
    ∀ entry ∈ machine.completed, Source entry.coefficients world ∧ entry.coefficients.remaining = 0 ∧
      NativeGoldLookupProducer.decode entry.coefficients.values = some entry.challenge

theorem begin_source (transcript : Transcript) (world : World) :
    Source (TypedFieldRequest.beginExecute goldilocksModulus 3 7 transcript challengeLabel).1 world := ⟨0,rfl⟩

theorem collect_source (fuel : ℕ) (field : NativeFieldVector.State) (world : World) (source : Source field world) :
    Source (NativeFieldVector.execute goldilocksModulus fuel field world).1 world := by
  obtain ⟨prior,old⟩ := source
  have header := NativeFieldVector.header_preserved goldilocksModulus fuel field world
  have startEq : start (NativeFieldVector.execute goldilocksModulus fuel field world).1 = start field := by
    unfold start
    rw [header.1]
  refine ⟨prior + fuel,?_⟩
  rw [startEq,NativeFieldVector.execute_add]
  dsimp only
  rw [old]

theorem drive_source (fuel : ℕ) (field : NativeFieldVector.State) (world : World) (source : Source field world) :
    Source (NativeFieldVector.stateOf (NativeFieldVector.driveExecute goldilocksModulus fuel field world).1) world := by
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  exact collect_source fuel field world source

theorem initial (transcript : Transcript) (statement : Statement) (proof : Proof) (world : World) :
    Traced (NativeScalarBatchVerifier.initial transcript statement proof) world := by
  unfold NativeScalarBatchVerifier.initial
  split <;> exact ⟨True.intro,by simp⟩

theorem after_field (machine : Machine) (packet : RoundPacket) (field : NativeFieldVector.State) (world : World)
    (active : machine.control = .sampling packet field) (traced : Traced machine world) :
    Traced (NativeScalarBatchVerifier.afterField machine packet
      (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1) world := by
  obtain ⟨source,entries⟩ := traced
  rw [active] at source
  have collected := drive_source 1 field world source
  have done := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
  change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at done
  cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
  | suspended next =>
    rw [result] at collected
    exact ⟨collected,entries⟩
  | finished coefficients transcript =>
    rw [result] at collected done
    cases decoded : NativeGoldLookupProducer.decode coefficients.values with
    | none =>
      simp only [NativeScalarBatchVerifier.afterField,decoded,NativeScalarBatchVerifier.fail,Traced]
      exact ⟨True.intro,entries⟩
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated,NativeScalarBatchVerifier.fail,Traced]
        exact ⟨True.intro,entries⟩
      | some expected =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated,Traced]
        refine ⟨True.intro,?_⟩
        intro entry member
        rcases List.mem_append.mp member with old | added
        · exact entries entry old
        · cases List.mem_singleton.mp added
          exact ⟨collected,done,decoded⟩

/-- A failed preparation cannot return an active sampler or a ready state. -/
theorem prepare_stopped (statement : Statement) (proof : Proof) (machine : Machine) :
    match NativeScalarBatchVerifier.prepare statement proof machine with
    | .inl next => match next.control with | .ready | .sampling _ _ => False | _ => True
    | .inr _ => True := by
  cases head : statement.infos.val.head? with
  | none => simp only [NativeScalarBatchVerifier.prepare,head,NativeScalarBatchVerifier.fail]
  | some first =>
    by_cases inside : machine.state.round < first.numVariables.val
    · by_cases fits : machine.state.round < 2^64
      · cases found : NativeScalarBatchRoundPacket.packet ⟨machine.state.round,fits⟩ proof with
        | none => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found,NativeScalarBatchVerifier.fail]
        | some packet =>
          cases checked : NativeScalarBatchPreflight.bindCheckedRound machine.state.transcript packet machine.state.expected with
          | error error => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found,checked,NativeScalarBatchVerifier.fail]
          | ok transcript => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found,checked]
      · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_right fits,NativeScalarBatchVerifier.fail]
    · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_false]

theorem tick (statement : Statement) (proof : Proof) (machine : Machine) (world : World) (traced : Traced machine world) :
    Traced (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 world := by
  cases control : machine.control with
  | finished claims => simpa only [NativeScalarBatchVerifier.tickExecute,control] using traced
  | failed error => simpa only [NativeScalarBatchVerifier.tickExecute,control] using traced
  | sampling packet field =>
    simpa only [NativeScalarBatchVerifier.tickExecute,control] using after_field machine packet field world control traced
  | ready =>
    have kept := ScalarPriorStability.prepare_prior statement proof machine
    cases prepared : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl next =>
      have keptNow : ScalarPriorStability.prior next = ScalarPriorStability.prior machine := by simpa only [prepared] using kept
      have entries := congrArg (fun prior => prior.2.2) keptNow
      dsimp only [ScalarPriorStability.prior] at entries
      have terminal := prepare_stopped statement proof machine
      rw [prepared] at terminal
      cases controlNext : next.control with
      | ready => simp only [controlNext] at terminal
      | sampling packet field => simp only [controlNext] at terminal
      | finished claims =>
        simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,Traced,controlNext]
        exact ⟨True.intro,by rw [entries]; exact traced.2⟩
      | failed error =>
        simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,Traced,controlNext]
        exact ⟨True.intro,by rw [entries]; exact traced.2⟩
    | inr pair =>
      obtain ⟨next,packet⟩ := pair
      have keptNow : ScalarPriorStability.prior next = ScalarPriorStability.prior machine := by simpa only [prepared] using kept
      have entries := congrArg (fun prior => prior.2.2) keptNow
      dsimp only [ScalarPriorStability.prior] at entries
      simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,Traced]
      exact ⟨begin_source next.state.transcript world,by rw [entries]; exact traced.2⟩

theorem execute (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World)
    (traced : Traced machine world) : Traced (NativeScalarBatchVerifier.execute statement proof fuel machine world).1 world := by
  induction fuel generalizing machine with
  | zero => exact traced
  | succ fuel ih => exact ih _ (tick statement proof machine world traced)

theorem initialized (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World) :
    Traced (NativeScalarBatchVerifier.execute statement proof fuel (NativeScalarBatchVerifier.initial transcript statement proof) world).1 world :=
  execute statement proof fuel _ world (initial transcript statement proof world)

/-- Literal retained coefficient states yield exactly their decoded cubic
challenge at some original collector prefix. This is not a uniform draw
assumption on the stored challenge word. -/
theorem decoded_value (field : NativeFieldVector.State) (world : World) (source : Source field world)
    (complete : field.remaining = 0) (challenge : NativeGoldExtensionArithmetic.Word)
    (decoded : NativeGoldLookupProducer.decode field.values = some challenge) :
    ∃ fuel, GoldScalarChallengeLaw.values fuel (start field) world = some (NativeFieldWire.goldExtensionValue challenge) := by
  obtain ⟨fuel,origin⟩ := source
  refine ⟨fuel,?_⟩
  unfold GoldScalarChallengeLaw.values NativeFieldVectorLaw.values
  rw [origin]
  simp only [NativeFieldVectorValues.project,complete,ite_true,Nat.zero_add,Option.map_some]
  exact congrArg some (ScalarRoundChallengeMeaning.decode_value field challenge decoded)

end FormalProof4FHE.HasteBoots.ScalarCollectorTrace
