module

public import FormalProof4FHE.HasteBoots.NativeParentStateExecution
public import FormalProof4FHE.HasteBoots.CausalSeedExposure
@[expose] public section

/-! Coverage for helper contexts from earlier observed native parent requests.
All state is replayed from the same empty initialization; actual seed quotes
remain associated after arbitrary truthful partial reads. Earlier quoted-seed
prequeries are linked to the existing first-exposure event. This does not yet
prove exhaustive native protocol coverage, receipt entropy, or source availability. -/
namespace FormalProof4FHE.HasteBoots.NativeParentCoverage
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeParentRootFreeze (Ledger)
open OracleSpec OracleComp
noncomputable section

def observationInput : Observation → Input
  | .start input => input
  | .output input _ _ => input
  | .hash input _ => input

theorem record_parents (state : Ledger × NativeShakeCache.Cache) (entry : Observation) :
    (NativeParentHistory.record state entry).1.parents =
      (NativeParentLedger.discover state.1 state.2 (observationInput entry)).parents := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values =>
    simp only [NativeParentHistory.record,observationInput]
    split <;> rfl

theorem parseParent_decode (input : Input) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent input = some frames) :
    TranscriptFrame.decodeAll input = some frames := by
  unfold NativeParentInputView.parseParent at parsed
  cases decoded : TranscriptFrame.decodeAll input with
  | none => simp [decoded] at parsed
  | some values =>
    simp only [decoded,Option.bind_some] at parsed
    split at parsed
    · exact congrArg some (Option.some.inj parsed)
    · simp at parsed

theorem binding_helper (input : Input) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent input = some frames) (binding : NativeCanonicalLookupWire.Binding)
    (bound : (⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ : TranscriptFrame.Frame) ∈ frames) :
    binding.helper ∈ NativeParentLedger.helpers input :=
  NativeParentLedger.helpers_frame input frames (parseParent_decode input frames parsed) _ bound binding.helper
    (NativeParentInputView.frameHelper_complete binding)

/-- Every observed recognized parent input declares its direct native helper contexts. -/
theorem record_declaration (state : Ledger × NativeShakeCache.Cache) (entry : Observation)
    (frames : List TranscriptFrame.Frame) (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (context : Digest) (helper : context ∈ NativeParentLedger.helpers (observationInput entry)) :
    ∃ parent ∈ (NativeParentHistory.record state entry).1.parents,
      parent.input = observationInput entry ∧ context ∈ parent.helpers := by
  refine ⟨⟨observationInput entry,NativeParentLedger.resolve state.1 state.2 (observationInput entry),
    NativeParentLedger.contexts state.1 state.2 (observationInput entry)⟩,?_,rfl,?_⟩
  · rw [record_parents]
    exact NativeParentLedger.discover_entry state.1 state.2 _ frames parsed
  · exact List.mem_append_left _ helper

/-- Later raw activity retains the declaration, including after partial seed reads and hashes. -/
theorem fold_declaration (state : Ledger × NativeShakeCache.Cache) (before later : List Observation)
    (entry : Observation) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (context : Digest) (helper : context ∈ NativeParentLedger.helpers (observationInput entry)) :
    ∃ parent ∈ ((before++[entry]++later).foldl NativeParentHistory.record state).1.parents,
      parent.input = observationInput entry ∧ context ∈ parent.helpers := by
  obtain ⟨parent,present,input,helpers⟩ := record_declaration (before.foldl NativeParentHistory.record state)
    entry frames parsed context helper
  refine ⟨parent,?_,input,helpers⟩
  simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using
    (NativeParentHistory.fold_keeps_parents (NativeParentHistory.record (before.foldl NativeParentHistory.record state) entry) later).subset present

/-- A real declared parent is resolved with the actual history-owned cache, without requiring a complete seed read. -/
theorem resolve_declared_helper (before later : List Observation) (entry : Observation)
    (frames : List TranscriptFrame.Frame) (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (context : Digest) (helper : context ∈ NativeParentLedger.helpers (observationInput entry))
    (world : World) (truthful : ObservationReplay.Agrees world (before++[entry]++later))
    (input : Input) (quoted : NativeChildSeedView.quote input =
      some (InputIndexedOracle.block world (observationInput entry) 0 64))
    (root : Digest) (committed : root ∈ NativeParentLedger.roots input) :
    let state := (before++[entry]++later).foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
    (context,root) ∈ NativeParentLedger.resolve state.1 state.2 input := by
  let state := (before++[entry]++later).foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
  obtain ⟨parent,present,same,helpers⟩ := fold_declaration (NativeParentLedger.empty,NativeShakeCache.empty)
    before later entry frames parsed context helper
  have cache : state.2 = NativeShakeKernel.observed (before++[entry]++later) world := by
    rw [NativeParentHistory.fold_cache]
    exact NativeShakeProjection.fold_observed _ world truthful
  change (context,root) ∈ NativeParentLedger.resolve state.1 state.2 input
  rw [cache]
  exact NativeParentLedger.resolve_actual_helper state.1 _ world input parent present
    (by simpa only [same] using quoted) context root helpers committed

/-- Every supported continuation of this read retains a checkpoint for a helper of an earlier declared parent. -/
theorem declared_helper_snapshot {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (before later : List Observation) (entry : Observation)
    (frames : List TranscriptFrame.Frame) (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (context : Digest) (helper : context ∈ NativeParentLedger.helpers (observationInput entry))
    (world : World) (truthful : ObservationReplay.Agrees world (before++[entry]++later))
    (input : Input) (quoted : NativeChildSeedView.quote input =
      some (InputIndexedOracle.block world (observationInput entry) 0 64))
    (root : Digest) (committed : root ∈ NativeParentLedger.roots input)
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A) :
    let initial := (before++[entry]++later).foldl (NativeParentStateExecution.record enc dummy shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute enc dummy shape initial.1.1
        (.read input offset count next) initial.1.2 initial.2),
      ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ⟨context,⟨root,log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  let initial := (before++[entry]++later).foldl (NativeParentStateExecution.record enc dummy shape)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
  dsimp only
  intro result possible
  apply NativeParentStateExecution.resolved_snapshot enc dummy shape initial.1.1 input offset count next initial.1.2 initial.2
    (NativeParentStateExecution.fold_covered enc dummy shape _ _ (NativeParentStateExecution.empty_covered shape))
    positive (context,root) _ result possible
  have resolved := resolve_declared_helper before later entry frames parsed context helper world truthful input quoted root committed
  simpa only [initial,NativeParentStateExecution.fold_parent] using resolved

/-- A quoted-seed prequery in the actual prior log supplies a target for the first-exposure event. -/
theorem prior_quote_target (log : List Observation) (entry : Observation) (present : entry ∈ log)
    (seed : Digest) (quoted : NativeChildSeedView.candidate entry = some seed) :
    seed ∈ NativeChildSeedView.guesses log := by
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨entry,present,quoted⟩

/-- This is the same new-exposure event whose exact history-conditional probability is already proved. -/
theorem prior_quote_event {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (world : World) (input : Input)
    (selected : CausalSeedExposure.firstRead step history = some input)
    (entry : Observation) (present : entry ∈ history.2)
    (quoted : NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)) :
    CausalSeedExposure.event step history world := by
  simp only [CausalSeedExposure.event,selected]
  exact prior_quote_target history.2 entry present _ quoted

end
end FormalProof4FHE.HasteBoots.NativeParentCoverage
