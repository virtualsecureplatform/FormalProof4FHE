module
public import FormalProof4FHE.HasteBoots.NativeFieldVector
public import FormalProof4FHE.HasteBoots.NativeShakeProjection
@[expose] public section

/-! The completed collector's actual receipt and its history replay. Receipt
queries are not repeated or replaced by a supplied digest. Recorded receipts
pin the parent transcript; unrecorded/partial receipt lineage remains separate. -/
namespace FormalProof4FHE.HasteBoots.NativeFieldReceipt
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript FieldPhase Observation)
open NativeFieldVector (State)
open OracleProgram (run)
noncomputable section

def input (phase : FieldPhase) : Input := NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ phase.consumed

/-- Receipt bytes can have been learned through arbitrary split/cloned reads,
not necessarily through one earlier native finalization call. -/
def Known (history : List Observation) (phase : FieldPhase) : Prop :=
  ∀ position : Fin 64, (.inl (input phase,position.val) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.footprint history

/-- Native completion exposes the exact collector log followed by the one
actual receipt log. No completed candidate or rejected byte is erased. -/
theorem finished_origin (p fuel count : ℕ) (parent : Transcript) (label : Input) (world : World)
    (state : State) (result : Transcript)
    (finished : (run (NativeFieldVector.request p fuel parent label count) world).run.1 = .finished state result) :
    ∃ log : List Observation,
      (NativeFieldVector.execute p fuel (NativeFieldVector.initial (NativeTranscript.beginField parent label p count).run.1 count) world) = (state,log) ∧
      result = (NativeTranscript.finishField world state.phase).run.1 ∧
      (run (NativeFieldVector.request p fuel parent label count) world).run.2 =
        [.start (NativeTranscript.beginField parent label p count).run.1.pending.input] ++ log ++
          (NativeTranscript.finishField world state.phase).run.2 := by
  let collected := NativeFieldVector.execute p fuel (NativeFieldVector.initial (NativeTranscript.beginField parent label p count).run.1 count) world
  have status := finished
  rw [NativeFieldVector.run_request] at status
  change (NativeFieldVector.finishExecute world collected.1).1 = .finished state result at status
  unfold NativeFieldVector.finishExecute at status
  split at status
  next complete =>
    obtain ⟨sameState,sameResult⟩ := NativeFieldVector.Status.finished.inj status
    refine ⟨collected.2,?_,?_,?_⟩
    · exact Prod.ext sameState rfl
    · rw [sameState] at sameResult
      exact sameResult.symm
    · rw [NativeFieldVector.run_request]
      change [.start (NativeTranscript.beginField parent label p count).run.1.pending.input] ++
        (collected.2 ++ (NativeFieldVector.finishExecute world collected.1).2) = _
      rw [sameState]
      have done : state.remaining = 0 := sameState ▸ complete
      simp only [NativeFieldVector.finishExecute,done,ite_true,List.append_assoc]
  next pending => contradiction

theorem transcript_replay (phase : FieldPhase) (world other : World) (history : List Observation)
    (observed : (NativeTranscript.finishField world phase).run.2.Sublist history)
    (agrees : ObservationReplay.Agrees other history) :
    (NativeTranscript.finishField other phase).run = (NativeTranscript.finishField world phase).run := by
  have same := (OracleProgram.run_replay (NativeTranscriptProgram.finishField phase)).replay world other
    (fun entry member => agrees entry (observed.subset member))
  simpa only [NativeTranscriptProgram.run_finishField] using same

/-- A native receipt already present in a replayable past is fixed on the
entire posterior fiber, including its parent transcript metadata. -/
theorem transcript_on_fiber {P : Type} {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world other : World) (phase : FieldPhase)
    (observed : (NativeTranscript.finishField world phase).run.2.Sublist (past world).run.2)
    (fiber : (past other).run = (past world).run) :
    (NativeTranscript.finishField other phase).run.1 = (NativeTranscript.finishField world phase).run.1 := by
  have truthful := replay.truthful other
  rw [fiber] at truthful
  exact congrArg Prod.fst (transcript_replay phase world other _ observed truthful)
/-- Arbitrary split reads covering the receipt suffice; no synthetic full
read or finalization observation is inserted into the history. -/
theorem known_of_split (history : List Observation) (phase : FieldPhase) (cut : ℕ) (within : cut ≤ 64)
    (first second : Input) (firstLength : first.length = cut) (secondLength : second.length = 64-cut)
    (firstRead : .output (input phase) 0 first ∈ history)
    (secondRead : .output (input phase) cut second ∈ history) : Known history phase := by
  intro position
  by_cases left : position.val < cut
  · apply Finset.mem_biUnion.mpr
    refine ⟨.output (input phase) 0 first,List.mem_toFinset.mpr firstRead,?_⟩
    apply (NativeShakeProjection.output_coordinate _ _ _ _).mpr
    exact ⟨rfl,by omega,by omega⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨.output (input phase) cut second,List.mem_toFinset.mpr secondRead,?_⟩
    apply (NativeShakeProjection.output_coordinate _ _ _ _).mpr
    have bounded := position.isLt
    exact ⟨rfl,by omega,by omega⟩

/-- Complete receipt knowledge assembled in any earlier observations fixes
its parent on the whole replay fiber. No cached coordinate is refreshed. -/
theorem transcript_on_fiber_of_known {P : Type} {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world other : World) (phase : FieldPhase)
    (known : Known (past world).run.2 phase)
    (fiber : (past other).run = (past world).run) :
    (NativeTranscript.finishField other phase).run.1 = (NativeTranscript.finishField world phase).run.1 := by
  have truthful := replay.truthful other
  rw [fiber] at truthful
  have same := ObservationReplay.same_of_agrees world other _ (replay.truthful world) truthful
  have bytes : InputIndexedOracle.bytes other (input phase) 0 64 = InputIndexedOracle.bytes world (input phase) 0 64 := by
    apply congrArg List.ofFn
    funext position
    exact same _ (by simpa only [Nat.zero_add] using known position)
  simp only [NativeTranscript.finishField,NativeTranscript.receipt,NativeTranscript.query,ObservationReplay.run_bind,
    WriterT.run_mk,WriterT.run_pure]
  rw [show NativeTranscript.utf8 "HasteBoots consumed field bytes v1" ++ phase.consumed = input phase from rfl,bytes]

end
end FormalProof4FHE.HasteBoots.NativeFieldReceipt
