module
public import FormalProof4FHE.HasteBoots.EqualityCollectorTrace
public import FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
@[expose] public section

/-! Original initialized equality collectors retain their raw read logs,
including all rejected candidates. A completed positive-dimensional point
therefore supplies an actual first stream exposure in any enclosing log. -/
namespace FormalProof4FHE.HasteBoots.EqualityCollectorLogs
open InputIndexedOracle (Input World)
open NativeTranscript (Observation FieldPhase)
open NativeLookupEquality (Machine Draw pointLabel)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open EqualityCollectorTrace (start)
noncomputable section

def Source (n : ℕ) (field : NativeFieldVector.State) (world : World) (history : List Observation) : Prop :=
  ∃ fuel, (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial (start field) (n*3)) world).1 = field ∧
    (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial (start field) (n*3)) world).2.Sublist history

theorem mono {n : ℕ} {field : NativeFieldVector.State} {world : World} {before after : List Observation}
    (source : Source n field world before) (included : before.Sublist after) : Source n field world after := by
  obtain ⟨fuel,state,logs⟩ := source
  exact ⟨fuel,state,logs.trans included⟩

def Traced {n : ℕ} (machine : Machine n Goldilocks3) (world : World) (history : List Observation) : Prop :=
  (∀ field, machine.active = some field → Source n field world history) ∧
    ∀ draw ∈ machine.draws, Source n draw.coefficients world history ∧ draw.coefficients.remaining = 0

theorem begin_source (n : ℕ) (transcript : NativeTranscript.Transcript) (world : World) (history : List Observation) :
    Source n (TypedFieldVector.beginExecute goldilocksModulus 3 7 n transcript pointLabel).1 world history :=
  ⟨0,rfl,List.nil_sublist _⟩

theorem collect_source (n fuel : ℕ) (field : NativeFieldVector.State) (world : World) (history : List Observation)
    (source : Source n field world history) :
    Source n (NativeFieldVector.execute goldilocksModulus fuel field world).1 world
      (history++(NativeFieldVector.execute goldilocksModulus fuel field world).2) := by
  obtain ⟨prior,old,logged⟩ := source
  have header := NativeFieldVector.header_preserved goldilocksModulus fuel field world
  have startEq : start (NativeFieldVector.execute goldilocksModulus fuel field world).1 = start field := by
    unfold start
    rw [header.1]
  refine ⟨prior+fuel,?_,?_⟩
  · rw [startEq,NativeFieldVector.execute_add]
    dsimp only
    rw [old]
  · rw [startEq,NativeFieldVector.execute_add]
    dsimp only
    rw [old]
    exact List.Sublist.append logged (List.Sublist.refl _)

theorem drive_source (n fuel : ℕ) (field : NativeFieldVector.State) (world : World) (history : List Observation)
    (source : Source n field world history) :
    Source n (NativeFieldVector.stateOf (NativeFieldVector.driveExecute goldilocksModulus fuel field world).1) world
      (history++(NativeFieldVector.driveExecute goldilocksModulus fuel field world).2) := by
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  exact mono (collect_source n fuel field world history source) (by
    rw [← List.append_assoc]
    exact List.sublist_append_left _ _)

theorem tick {n : ℕ} (machine : Machine n Goldilocks3) (world : World) (history : List Observation)
    (traced : Traced machine world history) :
    Traced (NativeLookupEquality.tickExecute goldilocksBasis 7 machine world).1 world
      (history++(NativeLookupEquality.tickExecute goldilocksBasis 7 machine world).2) := by
  by_cases done : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,done,ite_true,List.append_nil] using traced
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,done,ite_false,active,Traced]
      refine ⟨?_,?_⟩
      · intro field same
        cases Option.some.inj same
        exact begin_source n machine.transcript world _
      · intro draw member
        exact ⟨mono (traced.2 draw member).1 (List.sublist_append_left _ _),(traced.2 draw member).2⟩
    | some field =>
      have collected := drive_source n 1 field world history (traced.1 field active)
      have status := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
      change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at status
      cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
      | suspended next =>
        rw [result] at collected
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Traced]
        refine ⟨?_,?_⟩
        · intro field same
          cases Option.some.inj same
          exact collected
        · intro draw member
          exact ⟨mono (traced.2 draw member).1 (List.sublist_append_left _ _),(traced.2 draw member).2⟩
      | finished coefficients transcript =>
        rw [result] at collected status
        simp only [NativeLookupEquality.tickExecute,done,ite_false,active,result,Traced]
        refine ⟨by simp,?_⟩
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact ⟨mono (traced.2 draw old).1 (List.sublist_append_left _ _),(traced.2 draw old).2⟩
        · cases List.mem_singleton.mp added
          exact ⟨collected,status⟩

theorem execute {n : ℕ} (fuel : ℕ) (machine : Machine n Goldilocks3) (world : World) (history : List Observation)
    (traced : Traced machine world history) :
    Traced (NativeLookupEquality.execute goldilocksBasis 7 fuel machine world).1 world
      (history++(NativeLookupEquality.execute goldilocksBasis 7 fuel machine world).2) := by
  induction fuel generalizing machine history with
  | zero => simpa only [NativeLookupEquality.execute,List.append_nil] using traced
  | succ fuel ih =>
    simpa only [NativeLookupEquality.execute,List.append_assoc] using
      ih _ _ (tick machine world history traced)

theorem initialized (n fuel : ℕ) (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) :
    Traced (NativeLookupEquality.execute goldilocksBasis 7 fuel (NativeLookupEquality.initial n transcript roots fits) world).1 world
      (NativeLookupEquality.execute goldilocksBasis 7 fuel (NativeLookupEquality.initial n transcript roots fits) world).2 := by
  simpa only [List.nil_append] using execute fuel _ world []
    (show Traced (NativeLookupEquality.initial n transcript roots fits) world [] from
      ⟨by simp [NativeLookupEquality.initial],by simp [NativeLookupEquality.initial]⟩)

theorem request (n fuel : ℕ) (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) :
    Traced (OracleProgram.run (NativeLookupEquality.request goldilocksBasis 7 n fuel transcript roots fits) world).run.1 world
      (OracleProgram.run (NativeLookupEquality.request goldilocksBasis 7 n fuel transcript roots fits) world).run.2 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  exact initialized n fuel transcript roots fits world

/-- Completion in positive dimension entails a real raw read; a receipt alone
is not treated as exposing the coefficient stream. -/
theorem source_first {A : Type} {n : ℕ} (field : NativeFieldVector.State) (world : World)
    (program : OracleProgram.Program A) (source : Source n field world (OracleProgram.run program world).run.2)
    (complete : field.remaining = 0) (positive : 0 < n) :
    Nonempty (ProgramFirstStreamRead.First program world field.phase.pending.input) := by
  obtain ⟨fuel,state,logs⟩ := source
  cases fuel with
  | zero =>
    have remaining := congrArg NativeFieldVector.State.remaining state
    change n*3 = field.remaining at remaining
    omega
  | succ fuel =>
    have pending : n*3 ≠ 0 := by omega
    have member : Observation.output field.phase.pending.input 0
        (InputIndexedOracle.bytes world field.phase.pending.input 0 (CanonicalByteSampler.byteCount goldilocksModulus)) ∈
        (NativeFieldVector.execute goldilocksModulus (fuel+1) (NativeFieldVector.initial (start field) (n*3)) world).2 := by
      simp only [NativeFieldVector.execute,NativeFieldVector.initial,pending,ite_false]
      apply List.mem_append_left
      simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk]
      split_ifs <;> simp_all only [EqualityCollectorTrace.start, List.length_nil, List.nil_append, ite_true, ite_false, List.append_nil, List.mem_singleton]
    apply ProgramFirstStreamRead.of_output program world _ 0 _ _ (logs.subset member)
    rw [← List.length_pos_iff,InputIndexedOracle.bytes_length]
    decide +kernel

end
end FormalProof4FHE.HasteBoots.EqualityCollectorLogs
