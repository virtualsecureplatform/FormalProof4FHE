module

public import FormalProof4FHE.HasteBoots.NativeHashPrefix
public import FormalProof4FHE.HasteBoots.NativeSharedLookupParent

@[expose] public section

/-! All actual parent-preparation branches are hash-only. In particular the
full original registry is processed before any child/outer lookup challenge. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix

open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open NativeHashPrefix (HashOnly bind_hashOnly)

variable {C : Type}

theorem context (row : RowDescription C) (parameters : Parameters C) :
    HashOnly (NativeBrakedownContext.context row parameters) := by
  unfold NativeBrakedownContext.context
  cases NativeBrakedownContext.input row parameters with
  | none => trivial
  | some input => intro answer; trivial

theorem contexts (row : RowDescription C) (sources : List (Oracle C)) : HashOnly (NativeSharedLookupParent.contexts row sources) := by
  induction sources with
  | nil => trivial
  | cons source tail ih =>
    apply bind_hashOnly _ _ (context row source.parameters)
    intro digest
    cases digest with
    | none => trivial
    | some digest => exact bind_hashOnly _ _ ih (fun _ => True.intro)

theorem frame (row : RowDescription C) (helper : Parameters C) (selected : List (Oracle C))
    (parent : Transcript) (request : Request) : HashOnly (NativeSharedLookupParent.frame row helper selected parent request) := by
  apply bind_hashOnly _ _ (contexts row selected)
  intro sources
  cases sources with
  | none => trivial
  | some sources =>
    apply bind_hashOnly _ _ (context row helper)
    intro digest
    cases digest with
    | none => trivial
    | some digest => dsimp only; split <;> trivial

theorem step (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (request : Request) :
    HashOnly (NativeSharedLookupParent.step row registry helper state parent request) := by
  unfold NativeSharedLookupParent.step
  cases NativeSharedLookupParent.gather registry request.toModel.terminal.sourceSlots with
  | none => trivial
  | some selected =>
    dsimp only
    cases NativeLookupBindGeometry.bind request.toModel.columns request.toModel.terminal.logicalLength helper.geometry (selected.map Oracle.geometry) with
    | none => trivial
    | some geometry =>
      dsimp only
      apply bind_hashOnly _ _ (frame row helper selected parent request)
      intro framed
      cases framed with
      | none => trivial
      | some next =>
        dsimp only
        split
        · cases NativeSharedLookupPreflight.addRepetitions state.repetitions request.toModel.repetitions <;> trivial
        · trivial

theorem loop (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (state : NativeSharedLookupPreflight.State) (parent : Transcript) (requests : List Request) :
    HashOnly (NativeSharedLookupParent.loop row registry helper state parent requests) := by
  induction requests generalizing state parent with
  | nil => trivial
  | cons request tail ih =>
    apply bind_hashOnly _ _ (step row registry helper state parent request)
    rintro ⟨next,following⟩
    cases following with
    | none => trivial
    | some state => exact ih state next

theorem preflight (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) :
    HashOnly (NativeSharedLookupParent.preflight row registry helper parent requests) := by
  unfold NativeSharedLookupParent.preflight
  split
  · exact bind_hashOnly _ _ (loop row registry helper _ _ requests.val) (fun _ => True.intro)
  · trivial

theorem register (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (parent : Transcript) :
    HashOnly (NativeSharedLookupParent.register row registry parent) := by
  unfold NativeSharedLookupParent.register
  split
  · trivial
  · apply bind_hashOnly _ _ (contexts row registry.val)
    intro sources
    cases sources with
    | none => trivial
    | some sources => dsimp only; split <;> trivial

theorem prepare (row : RowDescription C) (registry : NativePrefixCodec.Vector (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : NativePrefixCodec.Vector Request) :
    HashOnly (NativeSharedLookupParent.prepare row registry helper parent requests) := by
  apply bind_hashOnly _ _ (preflight row registry.val helper parent requests)
  rintro ⟨next,geometry⟩
  cases geometry with
  | none => trivial
  | some geometry => exact bind_hashOnly _ _ (register row registry next) (fun registered => by cases registered <;> trivial)

end FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix
