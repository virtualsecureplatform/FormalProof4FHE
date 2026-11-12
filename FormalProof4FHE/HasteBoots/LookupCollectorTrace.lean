module
public import FormalProof4FHE.HasteBoots.EqualityCollectorInputCongruence
public import FormalProof4FHE.HasteBoots.LookupProducedEndpoints
@[expose] public section

/-! Every original lookup compression and offset draw comes from its own
initialized three-coordinate collector. Rejected offsets, partial collectors
and native finalization retain the original raw read logs. -/
namespace FormalProof4FHE.HasteBoots.LookupCollectorTrace
open InputIndexedOracle (Input World)
open NativeTranscript (Observation FieldPhase Transcript)
open NativeLookupChallenge (Machine)
open NativeFields (goldilocksModulus)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
noncomputable section

def start (field : NativeFieldVector.State) : FieldPhase := ⟨field.phase.pending,field.phase.label,[]⟩

def Source (field : NativeFieldVector.State) (world : World) (history : List Observation) : Prop :=
  ∃ fuel, (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial (start field) 3) world).1 = field ∧
    (NativeFieldVector.execute goldilocksModulus fuel (NativeFieldVector.initial (start field) 3) world).2.Sublist history

theorem mono {field : NativeFieldVector.State} {world : World} {before after : List Observation}
    (source : Source field world before) (included : before.Sublist after) : Source field world after := by
  obtain ⟨fuel,state,logs⟩ := source
  exact ⟨fuel,state,logs.trans included⟩

def Traced (machine : Machine Goldilocks3) (world : World) (history : List Observation) : Prop :=
  (match machine.control with
    | .compression field | .reciprocal _ _ _ field => Source field world history
    | .finished _ _ _ _ _ => True) ∧
  ∀ draw ∈ machine.draws, Source draw.coefficients world history ∧ draw.coefficients.remaining = 0

theorem traced_mono (machine : Machine Goldilocks3) (world : World) (before after : List Observation)
    (traced : Traced machine world before) (included : before.Sublist after) : Traced machine world after := by
  constructor
  · cases control : machine.control with
    | finished y r weights table transcript => exact True.intro
    | compression field =>
      exact mono (by simpa only [control] using traced.1) included
    | reciprocal y weights table field =>
      exact mono (by simpa only [control] using traced.1) included
  · exact fun draw member => ⟨mono (traced.2 draw member).1 included,(traced.2 draw member).2⟩

theorem begin_source (transcript : Transcript) (label : Input) (world : World) (history : List Observation) :
    Source (TypedFieldRequest.beginExecute goldilocksModulus 3 7 transcript label).1 world history :=
  ⟨0,rfl,List.nil_sublist _⟩

theorem collect_source (fuel : ℕ) (field : NativeFieldVector.State) (world : World) (history : List Observation)
    (source : Source field world history) :
    Source (NativeFieldVector.execute goldilocksModulus fuel field world).1 world
      (history++(NativeFieldVector.execute goldilocksModulus fuel field world).2) := by
  obtain ⟨prior,old,logged⟩ := source
  have header := NativeFieldVector.header_preserved goldilocksModulus fuel field world
  have startEq : start (NativeFieldVector.execute goldilocksModulus fuel field world).1 = start field := by
    unfold start
    rw [header.1,header.2]
  refine ⟨prior+fuel,?_,?_⟩
  · rw [startEq,NativeFieldVector.execute_add]
    dsimp only
    rw [old]
  · rw [startEq,NativeFieldVector.execute_add]
    dsimp only
    rw [old]
    exact List.Sublist.append logged (List.Sublist.refl _)

theorem drive_source (fuel : ℕ) (field : NativeFieldVector.State) (world : World) (history : List Observation)
    (source : Source field world history) :
    Source (NativeFieldVector.stateOf (NativeFieldVector.driveExecute goldilocksModulus fuel field world).1) world
      (history++(NativeFieldVector.driveExecute goldilocksModulus fuel field world).2) := by
  simp only [NativeFieldVector.driveExecute,NativeFieldVector.finish_state]
  exact mono (collect_source fuel field world history source) (by
    rw [← List.append_assoc]
    exact List.sublist_append_left _ _)

theorem tick (width : ℕ) (rows : List (List NativeFields.Goldilocks)) (machine : Machine Goldilocks3)
    (world : World) (history : List Observation) (traced : Traced machine world history) :
    Traced (NativeLookupChallenge.tickExecute goldilocksBasis 7 width rows machine world).1 world
      (history++(NativeLookupChallenge.tickExecute goldilocksBasis 7 width rows machine world).2) := by
  have old (later : List Observation) : ∀ draw ∈ machine.draws,
      Source draw.coefficients world (history++later) ∧ draw.coefficients.remaining = 0 := by
    intro draw member
    exact ⟨mono (traced.2 draw member).1 (List.sublist_append_left _ _),(traced.2 draw member).2⟩
  cases control : machine.control with
  | finished y r weights table transcript =>
    simpa only [NativeLookupChallenge.tickExecute,control,List.append_nil] using traced
  | compression field =>
    have source : Source field world history := by simpa only [Traced,control] using traced.1
    have collected := drive_source 1 field world history source
    have status := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
    change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at status
    cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended next =>
      rw [result] at collected
      simpa only [Traced,NativeLookupChallenge.tickExecute,control,result,NativeFieldVector.stateOf] using And.intro collected (old _)
    | finished coefficients transcript =>
      rw [result] at collected status
      simp only [Traced,NativeLookupChallenge.tickExecute,control,result]
      refine ⟨begin_source _ _ world _,?_⟩
      intro draw member
      rcases List.mem_append.mp member with earlier | added
      · exact old _ draw earlier
      · cases List.mem_singleton.mp added
        exact ⟨mono collected (by rw [← List.append_assoc]; exact List.sublist_append_left _ _),status⟩
  | reciprocal y weights table field =>
    have source : Source field world history := by simpa only [Traced,control] using traced.1
    have collected := drive_source 1 field world history source
    have status := NativeFieldVector.finish_status world (NativeFieldVector.execute goldilocksModulus 1 field world).1
    change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 at status
    cases result : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended next =>
      rw [result] at collected
      simpa only [Traced,NativeLookupChallenge.tickExecute,control,result,NativeFieldVector.stateOf] using And.intro collected (old _)
    | finished coefficients transcript =>
      rw [result] at collected status
      cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue goldilocksBasis coefficients.values) with
      | true =>
        simp only [Traced,NativeLookupChallenge.tickExecute,control,result,allowed,ite_true]
        refine ⟨True.intro,?_⟩
        intro draw member
        rcases List.mem_append.mp member with earlier | added
        · exact old _ draw earlier
        · cases List.mem_singleton.mp added
          exact ⟨collected,status⟩
      | false =>
        simp only [Traced,NativeLookupChallenge.tickExecute,control,result,allowed,Bool.false_eq_true,ite_false]
        refine ⟨begin_source _ _ world _,?_⟩
        intro draw member
        rcases List.mem_append.mp member with earlier | added
        · exact old _ draw earlier
        · cases List.mem_singleton.mp added
          exact ⟨mono collected (by rw [← List.append_assoc]; exact List.sublist_append_left _ _),status⟩

theorem execute (width fuel : ℕ) (rows : List (List NativeFields.Goldilocks)) (machine : Machine Goldilocks3)
    (world : World) (history : List Observation) (traced : Traced machine world history) :
    Traced (NativeLookupChallenge.execute goldilocksBasis 7 width rows fuel machine world).1 world
      (history++(NativeLookupChallenge.execute goldilocksBasis 7 width rows fuel machine world).2) := by
  induction fuel generalizing machine history with
  | zero => simpa only [NativeLookupChallenge.execute,List.append_nil] using traced
  | succ fuel ih =>
    simpa only [NativeLookupChallenge.execute,List.append_assoc] using ih _ _ (tick width rows machine world history traced)

theorem initialized (width fuel : ℕ) (rows : List (List NativeFields.Goldilocks)) (transcript : Transcript) (world : World) :
    Traced (NativeLookupChallenge.execute goldilocksBasis 7 width rows fuel
      (NativeLookupChallenge.initialExecute goldilocksModulus 3 7 transcript).1 world).1 world
      ((NativeLookupChallenge.initialExecute (K := Goldilocks3) goldilocksModulus 3 7 transcript).2++
        (NativeLookupChallenge.execute goldilocksBasis 7 width rows fuel
          (NativeLookupChallenge.initialExecute goldilocksModulus 3 7 transcript).1 world).2) := by
  apply execute
  exact ⟨begin_source _ _ world _,by simp [NativeLookupChallenge.initialExecute]⟩

theorem request (width fuel : ℕ) (rows : List (List NativeFields.Goldilocks)) (transcript : Transcript) (world : World) :
    Traced (OracleProgram.run (NativeLookupChallenge.request goldilocksBasis 7 width fuel rows transcript) world).run.1 world
      (OracleProgram.run (NativeLookupChallenge.request goldilocksBasis 7 width fuel rows transcript) world).run.2 := by
  rw [NativeLookupChallenge.run_request]
  exact initialized width fuel rows transcript world

/-- A completed scalar has a genuine positive raw read, even when the
containing adversary queried that stream before the native job began. -/
theorem source_first {A : Type} (field : NativeFieldVector.State) (world : World)
    (program : OracleProgram.Program A) (source : Source field world (OracleProgram.run program world).run.2)
    (complete : field.remaining = 0) :
    Nonempty (ProgramFirstStreamRead.First program world field.phase.pending.input) := by
  obtain ⟨fuel,state,logs⟩ := source
  cases fuel with
  | zero =>
    have remaining := congrArg NativeFieldVector.State.remaining state
    change 3 = field.remaining at remaining
    omega
  | succ fuel =>
    have member : Observation.output field.phase.pending.input 0
        (InputIndexedOracle.bytes world field.phase.pending.input 0 (CanonicalByteSampler.byteCount goldilocksModulus)) ∈
        (NativeFieldVector.execute goldilocksModulus (fuel+1) (NativeFieldVector.initial (start field) 3) world).2 := by
      simp only [NativeFieldVector.execute,NativeFieldVector.initial,OfNat.ofNat_ne_zero,ite_false]
      apply List.mem_append_left
      simp only [CanonicalTranscriptSampler.executePrefix,NativeTranscript.drawField,WriterT.run_mk]
      split_ifs <;> simp_all only [start,List.length_nil,List.nil_append,ite_true,ite_false,List.append_nil,List.mem_singleton]
    apply ProgramFirstStreamRead.of_output program world _ 0 _ _ (logs.subset member)
    rw [← List.length_pos_iff,InputIndexedOracle.bytes_length]
    decide +kernel

end
end FormalProof4FHE.HasteBoots.LookupCollectorTrace
