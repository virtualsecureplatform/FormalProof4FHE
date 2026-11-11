module
public import FormalProof4FHE.HasteBoots.ScalarCollectorTrace
@[expose] public section

/-! Every retained completed scalar record has an actual producing native
tick. Initial records are empty; rejected and suspended branches do not invent
records. The witness retains original prior expected values and raw updates. -/
namespace FormalProof4FHE.HasteBoots.ScalarCompletedOrigin
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine CompletedRound)

def Produced (machine : Machine) (world : World) (entry : CompletedRound) : Prop :=
  ∃ field transcript, machine.control = .sampling entry.packet field ∧
    (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).1 = .finished entry.coefficients transcript ∧
    entry.priorExpected = machine.state.expected ∧
    NativeGoldLookupProducer.decode entry.coefficients.values = some entry.challenge ∧
    NativeScalarBatchUpdate.update machine.state.expected entry.packet.messages.val entry.challenge = some entry.expected

/-- A retained record is either old, or created by this exact native drive,
decode and interpolation. -/
theorem tick (statement : Statement) (proof : Proof) (machine : Machine) (world : World) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.tickExecute statement proof machine world).1.completed) :
    entry ∈ machine.completed ∨ Produced machine world entry := by
  cases control : machine.control with
  | finished claims => exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control] using member)
  | failed error => exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control] using member)
  | ready =>
    have kept := ScalarPriorStability.prepare_prior statement proof machine
    cases prepared : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl next =>
      have equal : ScalarPriorStability.prior next = ScalarPriorStability.prior machine := by simpa only [prepared] using kept
      have records := congrArg (fun prior => prior.2.2) equal
      dsimp only [ScalarPriorStability.prior] at records
      exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control,prepared,records] using member)
    | inr pair =>
      obtain ⟨next,packet⟩ := pair
      have equal : ScalarPriorStability.prior next = ScalarPriorStability.prior machine := by simpa only [prepared] using kept
      have records := congrArg (fun prior => prior.2.2) equal
      dsimp only [ScalarPriorStability.prior] at records
      exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control,prepared,records] using member)
  | sampling packet field =>
    cases result : (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).1 with
    | suspended next => exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control,result,NativeScalarBatchVerifier.afterField] using member)
    | finished coefficients transcript =>
      cases decoded : NativeGoldLookupProducer.decode coefficients.values with
      | none => exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control,result,NativeScalarBatchVerifier.afterField,decoded,NativeScalarBatchVerifier.fail] using member)
      | some challenge =>
        cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
        | none => exact Or.inl (by simpa only [NativeScalarBatchVerifier.tickExecute,control,result,NativeScalarBatchVerifier.afterField,decoded,updated,NativeScalarBatchVerifier.fail] using member)
        | some expected =>
          simp only [NativeScalarBatchVerifier.tickExecute,control,result,NativeScalarBatchVerifier.afterField,decoded,updated] at member
          rcases List.mem_append.mp member with old | added
          · exact Or.inl old
          · cases List.mem_singleton.mp added
            exact Or.inr ⟨field,transcript,control,result,rfl,decoded,updated⟩

/-- No completed record appears without an original producing prefix. -/
theorem execute (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel machine world).1.completed) :
    entry ∈ machine.completed ∨ ∃ index < fuel,
      Produced (NativeScalarBatchVerifier.execute statement proof index machine world).1 world entry := by
  induction fuel generalizing machine with
  | zero => exact Or.inl member
  | succ fuel ih =>
    rcases ih (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 member with old | created
    · rcases tick statement proof machine world entry old with prior | now
      · exact Or.inl prior
      · exact Or.inr ⟨0,Nat.zero_lt_succ fuel,now⟩
    · obtain ⟨index,bound,origin⟩ := created
      exact Or.inr ⟨index + 1,by omega,by simpa only [NativeScalarBatchVerifier.execute] using origin⟩

theorem initialized (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World) (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed) :
    ∃ index < fuel, Produced (NativeScalarBatchVerifier.execute statement proof index
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1 world entry := by
  rcases execute statement proof fuel _ world entry member with impossible | actual
  · unfold NativeScalarBatchVerifier.initial at impossible
    split at impossible <;> simp only [List.not_mem_nil] at impossible
  · exact actual

end FormalProof4FHE.HasteBoots.ScalarCompletedOrigin
