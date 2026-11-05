module

public import FormalProof4FHE.HasteBoots.NativeParentCoverage
@[expose] public section

/-! Chronological inheritance of complete context/root source keys through
observed native parent requests. Soundness uses the same truthful raw history
and its owned partial byte cache. These are registration guarantees; native
first-original aliases, trusted parameters and Merkle availability remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeSourceLineage
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeParentRootFreeze (Ledger)
open NativeCanonicalLookupWire (Source)
open NativeParentCoverage (observationInput)
open OracleSpec OracleComp
noncomputable section

inductive Known (world : World) : List Observation → Input → Source → Prop
  | direct (before : List Observation) (entry : Observation) (frames : List TranscriptFrame.Frame)
      (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
      (key : Source) (source : key ∈ NativeParentLedger.direct (observationInput entry)) :
      Known world (before++[entry]) (observationInput entry) key
  | inherit (before : List Observation) (entry : Observation) (frames : List TranscriptFrame.Frame)
      (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
      (parentInput : Input) (key : Source) (earlier : Known world before parentInput key)
      (quoted : NativeChildSeedView.quote (observationInput entry) = some (InputIndexedOracle.block world parentInput 0 64)) :
      Known world (before++[entry]) (observationInput entry) key
  | later (before later : List Observation) (input : Input) (key : Source)
      (earlier : Known world before input key) : Known world (before++later) input key

theorem record_source (state : Ledger × NativeShakeCache.Cache) (entry : Observation)
    (frames : List TranscriptFrame.Frame) (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (key : Source) (resolved : key ∈ NativeParentLedger.resolve state.1 state.2 (observationInput entry)) :
    ∃ parent ∈ (NativeParentHistory.record state entry).1.parents,
      parent.input = observationInput entry ∧ key ∈ parent.sources := by
  refine ⟨⟨observationInput entry,NativeParentLedger.resolve state.1 state.2 (observationInput entry),
    NativeParentLedger.contexts state.1 state.2 (observationInput entry)⟩,?_,rfl,resolved⟩
  rw [NativeParentCoverage.record_parents]
  exact NativeParentLedger.discover_entry state.1 state.2 _ frames parsed

theorem actual_source (state : Ledger) (log : List Observation) (world : World) (input : Input)
    (parent : NativeParentLedger.Parent) (present : parent ∈ state.parents)
    (key : Source) (source : key ∈ parent.sources)
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent.input 0 64)) :
    key ∈ NativeParentLedger.resolve state (NativeShakeKernel.observed log world) input :=
  NativeParentLedger.resolve_source state _ input parent
    (NativeParentLedger.active_member state _ input _ quoted parent present
      (NativeParentInputView.compatible_observed log world parent.input)) key source

theorem Known.sound {world : World} {log : List Observation} {input : Input} {key : Source}
    (known : Known world log input key) (truthful : ObservationReplay.Agrees world log) :
    ∃ parent ∈ (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1.parents,
      parent.input = input ∧ key ∈ parent.sources := by
  induction known with
  | direct before entry frames parsed key source =>
    let state := before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using
      record_source state entry frames parsed key (List.mem_append_left _ source)
  | inherit before entry frames parsed parentInput key earlier quoted ih =>
    let state := before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
    have beforeTruth := ((ObservationReplay.agrees_append world before [entry]).mp truthful).1
    obtain ⟨parent,present,same,source⟩ := ih beforeTruth
    have cache : state.2 = NativeShakeKernel.observed before world := by
      rw [NativeParentHistory.fold_cache]
      exact NativeShakeProjection.fold_observed _ world beforeTruth
    have resolved : key ∈ NativeParentLedger.resolve state.1 state.2 (observationInput entry) := by
      rw [cache]
      exact actual_source state.1 before world _ parent present key source (by simpa only [same] using quoted)
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using record_source state entry frames parsed key resolved
  | later before later input key earlier ih =>
    obtain ⟨parent,present,same,source⟩ := ih (((ObservationReplay.agrees_append world before later).mp truthful).1)
    refine ⟨parent,?_,same,source⟩
    rw [List.foldl_append]
    exact (NativeParentHistory.fold_keeps_parents _ later).subset present

theorem resolve_known_source {world : World} {log : List Observation} {parentInput : Input} {key : Source}
    (known : Known world log parentInput key) (truthful : ObservationReplay.Agrees world log)
    (input : Input) (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parentInput 0 64)) :
    let state := log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
    key ∈ NativeParentLedger.resolve state.1 state.2 input := by
  let state := log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
  obtain ⟨parent,present,same,source⟩ := known.sound truthful
  have cache : state.2 = NativeShakeKernel.observed log world := by
    rw [NativeParentHistory.fold_cache]
    exact NativeShakeProjection.fold_observed _ world truthful
  change key ∈ NativeParentLedger.resolve state.1 state.2 input
  rw [cache]
  exact actual_source state.1 log world input parent present key source (by simpa only [same] using quoted)
theorem binding_source (input : Input) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent input = some frames) (binding : NativeCanonicalLookupWire.Binding)
    (bound : (⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ : TranscriptFrame.Frame) ∈ frames)
    (key : Source) (source : key ∈ binding.sources.val) : key ∈ NativeParentLedger.direct input := by
  unfold NativeParentLedger.direct NativeRootInputView.raw
  rw [NativeParentCoverage.parseParent_decode input frames parsed]
  exact (NativeRootInputView.recognized_sources frames _ bound binding.sources.val
    (NativeRootInputView.binding_complete binding)).subset source

theorem known_source_snapshot {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) {world : World} {log : List Observation} {parentInput : Input} {key : Source}
    (known : Known world log parentInput key) (truthful : ObservationReplay.Agrees world log)
    (input : Input) (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parentInput 0 64))
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A) :
    let initial := log.foldl (NativeParentStateExecution.record enc dummy shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute enc dummy shape initial.1.1
        (.read input offset count next) initial.1.2 initial.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest, ⟨key.1,⟨key.2,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  let initial := log.foldl (NativeParentStateExecution.record enc dummy shape)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
  dsimp only
  intro result possible
  apply NativeParentStateExecution.resolved_snapshot enc dummy shape initial.1.1 input offset count next initial.1.2 initial.2
    (NativeParentStateExecution.fold_covered enc dummy shape _ _ (NativeParentStateExecution.empty_covered shape))
    positive key _ result possible
  have resolved := resolve_known_source known truthful input quoted
  simpa only [initial,NativeParentStateExecution.fold_parent] using resolved

end
end FormalProof4FHE.HasteBoots.NativeSourceLineage
