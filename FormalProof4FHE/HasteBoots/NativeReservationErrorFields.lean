module
public import FormalProof4FHE.HasteBoots.NativeResidentVec
public import FormalProof4FHE.HasteBoots.NativeIncomingReference
public import FormalProof4FHE.HasteBoots.NativeAllocatorExecution
@[expose] public section

/-! Checked reads of the retained reservation-error representation. The first
word is the layout alignment, with zero selecting capacity overflow. Only the
allocation-error variant reads the size word. Resident local construction and
native Rust type, stack and lifetime correspondence remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeReservationErrorFields
open NativeReferenceMachine (State)
open NativeRawVecFields (Result)
open NativeWord64Memory (Word)

inductive Kind where
  | capacityOverflow
  | allocationError (size alignment : Word)
  deriving DecidableEq

def wordAccess (world : State) (index offset : Nat) : Result Word :=
  match NativeReferenceMachine.execute world (.access index offset (.read 8 8)) with
  | none => .invalid world
  | some next => match next.outputs[0]? >>= NativeWord64Memory.decode with
    | none => .invalid next
    | some value => .value value next

def afterAlignment (world : State) (index : Nat) (alignment : Word) : Result Kind :=
  if alignment = 0 then .value .capacityOverflow world
  else match wordAccess world index 8 with
    | .invalid next => .invalid next
    | .value size next =>
      if (NativeAllocatorExecution.request size alignment).Valid then .value (.allocationError size alignment) next
      else .invalid next

def read (world : State) (index : Nat) : Result Kind :=
  match NativeRawVecFields.select world index with
  | none => .invalid world
  | some _ => match wordAccess world index 0 with
    | .invalid next => .invalid next
    | .value alignment next => afterAlignment next index alignment

theorem wordAccess_complete (world next : State) (index offset : Nat) (value : Word)
    (executed : NativeReferenceMachine.execute world (.access index offset (.read 8 8)) = some next)
    (decoded : (next.outputs[0]? >>= NativeWord64Memory.decode) = some value) :
    wordAccess world index offset = .value value next := by
  simp only [wordAccess,executed,decoded]

theorem wordAccess_success (world next : State) (index offset : Nat) (value : Word)
    (loaded : wordAccess world index offset = .value value next) :
    NativeReferenceMachine.execute world (.access index offset (.read 8 8)) = some next ∧
      (next.outputs[0]? >>= NativeWord64Memory.decode) = some value := by
  cases executed : NativeReferenceMachine.execute world (.access index offset (.read 8 8)) with
  | none => simp only [wordAccess,executed] at loaded; cases loaded
  | some changed =>
    cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simp only [wordAccess,executed,decoded] at loaded; cases loaded
    | some word =>
      simp only [wordAccess,executed,decoded] at loaded
      cases loaded
      exact ⟨rfl,decoded⟩

theorem wordAccess_observation (world next : State) (index offset : Nat) (value : Word)
    (loaded : wordAccess world index offset = .value value next) :
    ∃ reference lease slot,
      world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      NativeByteRange.pointerAt lease.pointer offset = some slot ∧
      NativeWord64Memory.load world.pointers.heap.memory slot = some value := by
  obtain ⟨executed,decoded⟩ := wordAccess_success world next index offset value loaded
  exact NativeResidentVec.access_word_observation world next index offset value executed decoded

theorem overflow_no_tail (world : State) (index : Nat) :
    afterAlignment world index 0 = .value .capacityOverflow world := by
  simp [afterAlignment]

theorem overflow_complete (world next : State) (index : Nat) (reference : NativeReferenceMachine.Reference)
    (selected : NativeRawVecFields.select world index = some reference)
    (loaded : wordAccess world index 0 = .value 0 next) :
    read world index = .value .capacityOverflow next := by
  simp only [read,selected,loaded,overflow_no_tail]

theorem allocation_complete (world middle next : State) (index : Nat)
    (reference : NativeReferenceMachine.Reference) (size alignment : Word)
    (selected : NativeRawVecFields.select world index = some reference)
    (loadedAlignment : wordAccess world index 0 = .value alignment middle)
    (nonzero : alignment ≠ 0) (loadedSize : wordAccess middle index 8 = .value size next)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    read world index = .value (.allocationError size alignment) next := by
  simp only [read,selected,loadedAlignment,afterAlignment,ite_eq_right nonzero,loadedSize,ite_eq_left valid]

theorem wordAccess_preserves (property : State → Prop)
    (step : ∀ before after index offset,
      NativeReferenceMachine.execute before (.access index offset (.read 8 8)) = some after → property before → property after)
    (world : State) (index offset : Nat) (initial : property world) :
    property (wordAccess world index offset).world := by
  cases executed : NativeReferenceMachine.execute world (.access index offset (.read 8 8)) with
  | none => simpa only [wordAccess,executed,Result.world] using initial
  | some next =>
    have kept := step world next index offset executed initial
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode <;>
      simpa only [wordAccess,executed,decoded,Result.world] using kept

theorem afterAlignment_preserves (property : State → Prop)
    (step : ∀ before after index offset,
      NativeReferenceMachine.execute before (.access index offset (.read 8 8)) = some after → property before → property after)
    (world : State) (index : Nat) (alignment : Word) (initial : property world) :
    property (afterAlignment world index alignment).world := by
  by_cases zero : alignment = 0
  · simpa only [afterAlignment,ite_eq_left zero,Result.world] using initial
  · have kept := wordAccess_preserves property step world index 8 initial
    cases loaded : wordAccess world index 8 with
    | invalid next => simpa only [afterAlignment,ite_eq_right zero,loaded,Result.world] using kept
    | value size next =>
      simp only [loaded,Result.world] at kept
      simp only [afterAlignment,ite_eq_right zero,loaded]
      split <;> exact kept

theorem read_preserves (property : State → Prop)
    (step : ∀ before after index offset,
      NativeReferenceMachine.execute before (.access index offset (.read 8 8)) = some after → property before → property after)
    (world : State) (index : Nat) (initial : property world) : property (read world index).world := by
  cases selected : NativeRawVecFields.select world index with
  | none => simpa only [read,selected,Result.world] using initial
  | some reference =>
    have kept := wordAccess_preserves property step world index 0 initial
    cases loaded : wordAccess world index 0 with
    | invalid next => simpa only [read,selected,loaded,Result.world] using kept
    | value alignment next =>
      simp only [loaded,Result.world] at kept
      simpa only [read,selected,loaded] using afterAlignment_preserves property step next index alignment kept

theorem read_projects (world : State) (index : Nat) : NativeReferenceMachine.Runs world (read world index).world :=
  read_preserves (NativeReferenceMachine.Runs world)
    (fun _ _ _ _ actual prior => .step prior _ actual) world index (.refl world)

theorem read_heap (world : State) (index : Nat) : (read world index).world.pointers.heap = world.pointers.heap :=
  read_preserves (fun next => next.pointers.heap = world.pointers.heap)
    (fun before after index offset actual prior =>
      (NativeHeapFrame.execute_heap before after (.access index offset (.read 8 8)) rfl actual).trans prior) world index rfl

theorem read_incoming (world : State) (index : Nat) : NativeIncomingReference.Preserves world (read world index).world :=
  read_preserves (NativeIncomingReference.Preserves world)
    (fun before after index offset actual prior => prior.trans
      (NativeIncomingReference.step before after (.access index offset (.read 8 8)) actual rfl)) world index (.refl world)

theorem read_reachable (world : State) (index : Nat) (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (read world index).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (read_projects world index)

theorem read_wellFormed (world : State) (index : Nat) (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (read world index).world :=
  NativeSliceLLBC.reference_runs_wellFormed _ _ valid (read_projects world index)

theorem overflow_success (world next : State) (index : Nat)
    (loaded : read world index = .value .capacityOverflow next) :
    ∃ reference, NativeRawVecFields.select world index = some reference ∧
      wordAccess world index 0 = .value 0 next := by
  cases selected : NativeRawVecFields.select world index with
  | none => simp only [read,selected] at loaded; cases loaded
  | some reference =>
    cases first : wordAccess world index 0 with
    | invalid changed => simp only [read,selected,first] at loaded; cases loaded
    | value alignment changed =>
      simp only [read,selected,first,afterAlignment] at loaded
      split at loaded
      next zero =>
        subst alignment
        cases loaded
        exact ⟨reference,rfl,rfl⟩
      next nonzero =>
        cases second : wordAccess changed index 8 with
        | invalid final => simp only [second] at loaded; cases loaded
        | value size final =>
          simp only [second] at loaded
          split at loaded <;> cases loaded

theorem allocation_success (world next : State) (index : Nat) (size alignment : Word)
    (loaded : read world index = .value (.allocationError size alignment) next) :
    ∃ reference middle, NativeRawVecFields.select world index = some reference ∧
      wordAccess world index 0 = .value alignment middle ∧ alignment ≠ 0 ∧
      wordAccess middle index 8 = .value size next ∧ (NativeAllocatorExecution.request size alignment).Valid := by
  cases selected : NativeRawVecFields.select world index with
  | none => simp only [read,selected] at loaded; cases loaded
  | some reference =>
    cases first : wordAccess world index 0 with
    | invalid changed => simp only [read,selected,first] at loaded; cases loaded
    | value align changed =>
      simp only [read,selected,first,afterAlignment] at loaded
      split at loaded
      next zero => cases loaded
      next nonzero =>
        cases second : wordAccess changed index 8 with
        | invalid final => simp only [second] at loaded; cases loaded
        | value count final =>
          simp only [second] at loaded
          split at loaded
          next valid =>
            cases loaded
            exact ⟨reference,changed,rfl,rfl,nonzero,second,valid⟩
          next => cases loaded

theorem malformed_layout (world middle next : State) (index : Nat)
    (reference : NativeReferenceMachine.Reference) (size alignment : Word)
    (selected : NativeRawVecFields.select world index = some reference)
    (loadedAlignment : wordAccess world index 0 = .value alignment middle)
    (nonzero : alignment ≠ 0) (loadedSize : wordAccess middle index 8 = .value size next)
    (invalid : ¬ (NativeAllocatorExecution.request size alignment).Valid) :
    read world index = .invalid next := by
  simp only [read,selected,loadedAlignment,afterAlignment,ite_eq_right nonzero,loadedSize,ite_eq_right invalid]

end FormalProof4FHE.HasteBoots.NativeReservationErrorFields
