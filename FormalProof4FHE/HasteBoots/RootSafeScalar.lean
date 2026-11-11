module

public import FormalProof4FHE.HasteBoots.RootSafeExtension
public import FormalProof4FHE.HasteBoots.NativeScalarBatchVerifier
import all Init.Data.String.Defs

@[expose] public section

/-! The actual scalar verifier appends no helper-roots frames. Checked
statement/round binding, retries, failure branches and completed coefficient
readers preserve the exact most recent original helper-root vector. -/
namespace FormalProof4FHE.HasteBoots.RootSafeScalar
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open RootSafeExtension (Extends StateExtends StatusExtends)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)
noncomputable section

def RoundDomain (proof : Proof) : Prop :=
  ∀ round packet, NativeScalarBatchRoundPacket.packet round proof = some packet →
    (NativeScalarBatchWire.roundCodec.encode packet).length < TranscriptFrame.lengthLimit

def Preserves (base : Transcript) (machine : Machine) : Prop :=
  Extends base machine.state.transcript ∧
    (match machine.control with | .sampling _ field => StateExtends base field | _ => True) ∧
    ∀ round ∈ machine.completed, StateExtends base round.coefficients

theorem bind_statement (state : Transcript) (statement : Statement)
    (fits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit) :
    Extends state (NativeScalarBatchWire.bindStatement state statement) :=
  RootSafeExtension.absorb state 1 NativeScalarBatchWire.statementLabel _
    ⟨by change NativeScalarBatchWire.statementLabel.length < _; decide +kernel,fits⟩
    (RootSafeExtension.clean_label _ _ (by decide +kernel))

theorem bind_round (state : Transcript) (packet : RoundPacket)
    (fits : (NativeScalarBatchWire.roundCodec.encode packet).length < TranscriptFrame.lengthLimit) :
    Extends state (NativeScalarBatchWire.bindRound state packet) :=
  RootSafeExtension.absorb state 1 NativeScalarBatchWire.roundLabel _
    ⟨by change NativeScalarBatchWire.roundLabel.length < _; decide +kernel,fits⟩
    (RootSafeExtension.clean_label _ _ (by decide +kernel))

theorem initial (state : Transcript) (statement : Statement) (proof : Proof)
    (fits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit) :
    Preserves state (NativeScalarBatchVerifier.initial state statement proof) := by
  cases checked : NativeScalarBatchPreflight.beginVerify state statement proof with
  | error reason =>
    simp only [Preserves,NativeScalarBatchVerifier.initial,checked]
    exact ⟨Extends.refl state,True.intro,by simp⟩
  | ok bound =>
    have same := ((NativeScalarBatchPreflight.beginVerify_ok_iff state bound statement proof).mp checked).2.2
    simp only [Preserves,NativeScalarBatchVerifier.initial,checked,same]
    exact ⟨bind_statement state statement fits,True.intro,by simp⟩

theorem fail (base : Transcript) (machine : Machine) (reason : NativeScalarBatchVerifier.Error)
    (valid : Preserves base machine) : Preserves base (NativeScalarBatchVerifier.fail machine reason) :=
  ⟨valid.1,True.intro,valid.2.2⟩

/-- Every guard branch preserves earlier state; successful binding appends only its actual checked packet. -/
theorem prepare (base : Transcript) (statement : Statement) (proof : Proof) (machine : Machine)
    (domain : RoundDomain proof) (valid : Preserves base machine) :
    match NativeScalarBatchVerifier.prepare statement proof machine with
    | .inl stopped => Preserves base stopped
    | .inr (bound,_) => Preserves base bound := by
  cases head : statement.infos.val.head? with
  | none =>
    simp only [NativeScalarBatchVerifier.prepare,head]
    exact fail base machine _ valid
  | some first =>
    by_cases inside : machine.state.round < first.numVariables.val
    · by_cases fits : machine.state.round < 2^64
      · cases computed : NativeScalarBatchRoundPacket.packet ⟨machine.state.round,fits⟩ proof with
        | none =>
          simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,fits,dite_true,computed]
          exact fail base machine _ valid
        | some packet =>
          cases checked : NativeScalarBatchPreflight.bindCheckedRound machine.state.transcript packet machine.state.expected with
          | error reason =>
            simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,fits,dite_true,computed,checked]
            exact fail base machine _ valid
          | ok bound =>
            have boundExt : Extends machine.state.transcript bound := by
              unfold NativeScalarBatchPreflight.bindCheckedRound at checked
              split at checked
              · have same := Except.ok.inj checked
                rw [← same]
                exact bind_round _ packet (domain _ packet computed)
              · contradiction
            simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,fits,dite_true,computed,checked]
            exact ⟨valid.1.trans boundExt,valid.2⟩
      · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,fits,dite_false]
        exact fail base machine _ valid
    · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_false]
      exact ⟨valid.1,True.intro,valid.2.2⟩

theorem after_field (base : Transcript) (machine : Machine) (packet : RoundPacket) (status : NativeFieldVector.Status)
    (valid : Preserves base machine) (field : StatusExtends base status) :
    Preserves base (NativeScalarBatchVerifier.afterField machine packet status) := by
  cases status with
  | suspended state => exact ⟨valid.1,field,valid.2.2⟩
  | finished state transcript =>
    cases decoded : NativeGoldLookupProducer.decode state.values with
    | none =>
      simp only [NativeScalarBatchVerifier.afterField,decoded]
      exact ⟨field.2,True.intro,valid.2.2⟩
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated]
        exact ⟨field.2,True.intro,valid.2.2⟩
      | some expected =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated]
        refine ⟨field.2,True.intro,?_⟩
        intro round member
        rcases List.mem_append.mp member with old | added
        · exact valid.2.2 round old
        · obtain rfl := List.mem_singleton.mp added
          exact field.1

theorem tick (base : Transcript) (statement : Statement) (proof : Proof) (machine : Machine) (world : World)
    (domain : RoundDomain proof) (valid : Preserves base machine) :
    Preserves base (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 := by
  cases control : machine.control with
  | finished claims => simpa only [NativeScalarBatchVerifier.tickExecute,control] using valid
  | failed reason => simpa only [NativeScalarBatchVerifier.tickExecute,control] using valid
  | ready =>
    have prepared := prepare base statement proof machine domain valid
    cases result : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl stopped => simpa only [NativeScalarBatchVerifier.tickExecute,control,result] using prepared
    | inr pair =>
      obtain ⟨bound,packet⟩ := pair
      simp only [result] at prepared
      simp only [Preserves,NativeScalarBatchVerifier.tickExecute,control,result]
      exact ⟨prepared.1,StateExtends.trans prepared.1
        (RootSafeExtension.scalar_begin NativeFields.goldilocksModulus 3 7 bound.state.transcript NativeScalarBatchWire.challengeLabel
          (by decide +kernel) (by decide +kernel)),prepared.2.2⟩
  | sampling packet field =>
    have active : StateExtends base field := by simpa only [control] using valid.2.1
    simpa only [NativeScalarBatchVerifier.tickExecute,control] using after_field base machine packet _ valid
      (RootSafeExtension.drive_status base NativeFields.goldilocksModulus 1 field world active)

theorem execute (base : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World)
    (domain : RoundDomain proof) (valid : Preserves base machine) :
    Preserves base (NativeScalarBatchVerifier.execute statement proof fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick base statement proof machine world domain valid)

theorem verify (state : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : RoundDomain proof) :
    Preserves state (OracleProgram.run (NativeScalarBatchVerifier.verifyPrefix fuel state statement proof) world).run.1 := by
  rw [NativeScalarBatchVerifier.verifyPrefix,NativeScalarBatchVerifier.run_steps]
  exact execute state statement proof fuel _ world domain (initial state statement proof statementFits)

end
end FormalProof4FHE.HasteBoots.RootSafeScalar
