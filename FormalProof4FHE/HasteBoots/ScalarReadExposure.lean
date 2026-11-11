module
public import FormalProof4FHE.HasteBoots.ScalarCompletedOrigin
public import FormalProof4FHE.HasteBoots.NativeFieldObservationScope
@[expose] public section

/-! Every actual completed scalar record has a positive native read in the
same execution log. The read comes from its producing tick, with its actual
pending input and cursor; neither freshness nor a supplied exposure is assumed. -/
namespace FormalProof4FHE.HasteBoots.ScalarReadExposure
open NativeScalarBatchVerifier (Machine CompletedRound)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (Input World)
open NativeFields (goldilocksModulus)
noncomputable section

def Pending (machine : Machine) : Prop :=
  ∀ packet field, machine.control = .sampling packet field → field.remaining ≠ 0

theorem after_field (machine : Machine) (packet : RoundPacket) (status : NativeFieldVector.Status)
    (valid : NativeFieldVector.StatusValid status) : Pending (NativeScalarBatchVerifier.afterField machine packet status) := by
  cases status with
  | suspended field =>
    intro other candidate active
    have same := NativeScalarBatchVerifier.Control.sampling.inj active
    exact same.2 ▸ valid
  | finished field transcript =>
    cases decoded : NativeGoldLookupProducer.decode field.values with
    | none => simp only [Pending,NativeScalarBatchVerifier.afterField,decoded,NativeScalarBatchVerifier.fail]; intro _ _ impossible; contradiction
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none => simp only [Pending,NativeScalarBatchVerifier.afterField,decoded,updated,NativeScalarBatchVerifier.fail]; intro _ _ impossible; contradiction
      | some expected => simp only [Pending,NativeScalarBatchVerifier.afterField,decoded,updated]; intro _ _ impossible; contradiction

theorem initial (transcript : Transcript) (statement : Statement) (proof : Proof) :
    Pending (NativeScalarBatchVerifier.initial transcript statement proof) := by
  unfold NativeScalarBatchVerifier.initial
  split <;> intro _ _ impossible <;> contradiction

theorem tick (statement : Statement) (proof : Proof) (machine : Machine) (world : World) (valid : Pending machine) :
    Pending (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 := by
  cases control : machine.control with
  | finished claims => simpa only [NativeScalarBatchVerifier.tickExecute,control] using valid
  | failed reason => simpa only [NativeScalarBatchVerifier.tickExecute,control] using valid
  | sampling packet field =>
    have status := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
    change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at status
    simpa only [NativeScalarBatchVerifier.tickExecute,control] using after_field machine packet _ status
  | ready =>
    have stopped := ScalarCollectorTrace.prepare_stopped statement proof machine
    cases prepared : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl next =>
      simp only [prepared] at stopped
      cases nextControl : next.control <;>
        simp only [nextControl] at stopped <;>
        simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,Pending,nextControl] <;>
        intro _ _ impossible <;> contradiction
    | inr pair =>
      obtain ⟨bound,packet⟩ := pair
      simp only [NativeScalarBatchVerifier.tickExecute,control,prepared,Pending]
      intro other field active
      have same := NativeScalarBatchVerifier.Control.sampling.inj active
      rw [← same.2]
      change (3 : ℕ) ≠ 0
      decide

theorem execute (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World) :
    Pending (NativeScalarBatchVerifier.execute statement proof fuel (NativeScalarBatchVerifier.initial transcript statement proof) world).1 := by
  have general (fuel : ℕ) (machine : Machine) (valid : Pending machine) :
      Pending (NativeScalarBatchVerifier.execute statement proof fuel machine world).1 := by
    induction fuel generalizing machine with
    | zero => exact valid
    | succ fuel ih => exact ih _ (tick statement proof machine world valid)
  exact general fuel _ (initial transcript statement proof)

/-- A tick's raw observations occur in the full scalar execution, including
later suspended/rejected branches and all earlier observations. -/
theorem tick_log (statement : Statement) (proof : Proof) (fuel index : ℕ) (machine : Machine) (world : World)
    (inside : index < fuel) :
    (NativeScalarBatchVerifier.tickExecute statement proof (NativeScalarBatchVerifier.execute statement proof index machine world).1 world).2.Sublist
      (NativeScalarBatchVerifier.execute statement proof fuel machine world).2 := by
  induction fuel generalizing index machine with
  | zero => omega
  | succ fuel ih =>
    cases index with
    | zero => exact List.sublist_append_left _ _
    | succ index =>
      have later := ih index (NativeScalarBatchVerifier.tickExecute statement proof machine world).1 (by omega)
      exact later.trans (List.sublist_append_right _ _)

/-- A pending one-step Goldilocks drive really returns eight positive bytes,
regardless of whether this candidate is accepted or rejected. -/
theorem drive_read (field : NativeFieldVector.State) (world : World) (pending : field.remaining ≠ 0) :
    Observation.output field.phase.pending.input field.phase.consumed.length
      (InputIndexedOracle.bytes world field.phase.pending.input field.phase.consumed.length 8) ∈
        (NativeFieldVector.driveExecute goldilocksModulus 1 field world).2 := by
  have width : CanonicalByteSampler.byteCount goldilocksModulus = 8 := by decide +kernel
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.execute,pending,ite_false,
    NativeFieldObservationScope.trial_log,width,List.append_nil]
  exact List.mem_append_left _ List.mem_cons_self

/-- The actual producing drive supplies a real positive output at its actual
byte cursor under the retained completed record's exact input. -/
theorem completed (transcript : Transcript) (statement : Statement) (proof : Proof) (fuel : ℕ) (world : World)
    (entry : CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed) :
    ∃ position offset : ℕ, (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).2[position]? =
      some (Observation.output entry.coefficients.phase.pending.input offset (InputIndexedOracle.bytes world entry.coefficients.phase.pending.input offset 8)) := by
  obtain ⟨index,inside,field,after,active,finished,_,_,_⟩ := ScalarCompletedOrigin.initialized transcript statement proof fuel world entry member
  have pending := execute transcript statement proof index world entry.packet field active
  have stateEq := congrArg NativeFieldVector.stateOf finished
  change NativeFieldVector.stateOf (NativeFieldVector.finishExecute world (NativeFieldVector.execute goldilocksModulus 1 field world).1).1 = entry.coefficients at stateEq
  rw [NativeFieldVector.finish_state] at stateEq
  have header := (NativeFieldVector.header_preserved goldilocksModulus 1 field world).1
  rw [stateEq] at header
  have inputEq := congrArg Transcript.input header
  have read := drive_read field world pending
  rw [← inputEq] at read
  have tickRead : Observation.output entry.coefficients.phase.pending.input field.phase.consumed.length
      (InputIndexedOracle.bytes world entry.coefficients.phase.pending.input field.phase.consumed.length 8) ∈
      (NativeScalarBatchVerifier.tickExecute statement proof (NativeScalarBatchVerifier.execute statement proof index
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1 world).2 := by
    simpa only [NativeScalarBatchVerifier.tickExecute,active] using read
  have present := (tick_log statement proof fuel index _ world inside).subset tickRead
  obtain ⟨position,same⟩ := List.mem_iff_get.mp present
  exact ⟨position.val,field.phase.consumed.length,(List.getElem?_eq_getElem position.isLt).trans (congrArg some same)⟩

end
end FormalProof4FHE.HasteBoots.ScalarReadExposure
