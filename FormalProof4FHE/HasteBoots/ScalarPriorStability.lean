module
public import FormalProof4FHE.HasteBoots.ScalarExecutionPrefixAgreement
@[expose] public section

/-! The actual native prior expected vector, common point and completed
records can change only when a scalar round counter advances. -/
namespace FormalProof4FHE.HasteBoots.ScalarPriorStability
open InputIndexedOracle (World)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine)

def prior (machine : Machine) := (machine.state.expected,machine.state.point,machine.completed)

theorem prepare_prior (statement : Statement) (proof : Proof) (machine : Machine) :
    match NativeScalarBatchVerifier.prepare statement proof machine with
    | .inl next => prior next = prior machine
    | .inr (next,_) => prior next = prior machine := by
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
          | ok transcript => simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_left fits,found,checked]; rfl
      · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_true,dite_eq_right fits]; rfl
    · simp only [NativeScalarBatchVerifier.prepare,head,inside,ite_false]; rfl

theorem after_field (machine : Machine) (packet : RoundPacket) (status : NativeFieldVector.Status)
    (sameRound : (NativeScalarBatchVerifier.afterField machine packet status).state.round = machine.state.round) :
    prior (NativeScalarBatchVerifier.afterField machine packet status) = prior machine := by
  cases status with
  | suspended field => rfl
  | finished coefficients transcript =>
    cases decoded : NativeGoldLookupProducer.decode coefficients.values with
    | none => simp only [NativeScalarBatchVerifier.afterField,decoded]; rfl
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none => simp only [NativeScalarBatchVerifier.afterField,decoded,updated]; rfl
      | some expected =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated] at sameRound
        omega

theorem tick (statement : Statement) (proof : Proof) (machine : Machine) (world : World)
    (sameRound : (NativeScalarBatchVerifier.tickExecute statement proof machine world).1.state.round = machine.state.round) :
    prior (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 = prior machine := by
  cases control : machine.control with
  | finished claims => simp only [NativeScalarBatchVerifier.tickExecute,control]
  | failed error => simp only [NativeScalarBatchVerifier.tickExecute,control]
  | sampling packet field =>
    simp only [NativeScalarBatchVerifier.tickExecute,control] at sameRound ⊢
    exact after_field machine packet _ sameRound
  | ready =>
    have kept := prepare_prior statement proof machine
    cases prepared : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl next => simpa only [NativeScalarBatchVerifier.tickExecute,control,prepared,prior] using kept
    | inr pair =>
      obtain ⟨next,packet⟩ := pair
      simpa only [NativeScalarBatchVerifier.tickExecute,control,prepared,prior] using kept

theorem execute (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World)
    (sameRound : (NativeScalarBatchVerifier.execute statement proof fuel machine world).1.state.round = machine.state.round) :
    prior (NativeScalarBatchVerifier.execute statement proof fuel machine world).1 = prior machine := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    have first := ScalarExecutionPrefixAgreement.tick_round statement proof machine world
    have later := ScalarExecutionPrefixAgreement.execute_round statement proof fuel
      (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 world
    have atFirst : (NativeScalarBatchVerifier.tickExecute statement proof machine world).1.state.round = machine.state.round := by
      change (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 world).1.state.round = machine.state.round at sameRound
      omega
    exact (ih _ (sameRound.trans atFirst.symm)).trans (tick statement proof machine world atFirst)

theorem earlier (statement : Statement) (proof : Proof) (first later : ℕ) (ordered : first ≤ later)
    (machine : Machine) (world : World)
    (sameRound : (NativeScalarBatchVerifier.execute statement proof later machine world).1.state.round =
      (NativeScalarBatchVerifier.execute statement proof first machine world).1.state.round) :
    prior (NativeScalarBatchVerifier.execute statement proof later machine world).1 =
      prior (NativeScalarBatchVerifier.execute statement proof first machine world).1 := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [NativeScalarBatchVerifier.execute_add] at sameRound ⊢
  exact execute statement proof extra _ world sameRound

end FormalProof4FHE.HasteBoots.ScalarPriorStability
