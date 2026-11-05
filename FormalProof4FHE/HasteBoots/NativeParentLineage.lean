module

public import FormalProof4FHE.HasteBoots.NativeParentCoverage
@[expose] public section

/-! Chronological helper-context inheritance through finite native parent
request chains. Every certificate consists of observed requests and actual
logical seed links. Soundness derives metadata from the same truthful history.
This certifies registration before the current read, not retrospective
coverage of earlier orphans, authenticated lineage, or source availability. -/
namespace FormalProof4FHE.HasteBoots.NativeParentLineage
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeParentRootFreeze (Ledger)
open OracleSpec OracleComp
open NativeParentCoverage (observationInput)
noncomputable section

/-- A chronological chain of observed parent requests, not a supplied parent table. -/
inductive Known (world : World) : List Observation → Input → Digest → Prop
  | direct (before : List Observation) (entry : Observation) (frames : List TranscriptFrame.Frame)
      (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
      (context : Digest) (helper : context ∈ NativeParentLedger.helpers (observationInput entry)) :
      Known world (before++[entry]) (observationInput entry) context
  | inherit (before : List Observation) (entry : Observation) (frames : List TranscriptFrame.Frame)
      (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
      (parentInput : Input) (context : Digest) (earlier : Known world before parentInput context)
      (quoted : NativeChildSeedView.quote (observationInput entry) = some (InputIndexedOracle.block world parentInput 0 64)) :
      Known world (before++[entry]) (observationInput entry) context
  | later (before later : List Observation) (input : Input) (context : Digest)
      (earlier : Known world before input context) : Known world (before++later) input context

/-- Newly stored parent metadata includes inherited compatible contexts. -/
theorem record_context (state : Ledger × NativeShakeCache.Cache) (entry : Observation)
    (frames : List TranscriptFrame.Frame) (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (context : Digest) (inherited : context ∈ NativeParentLedger.contexts state.1 state.2 (observationInput entry)) :
    ∃ parent ∈ (NativeParentHistory.record state entry).1.parents,
      parent.input = observationInput entry ∧ context ∈ parent.helpers := by
  refine ⟨⟨observationInput entry,NativeParentLedger.resolve state.1 state.2 (observationInput entry),
    NativeParentLedger.contexts state.1 state.2 (observationInput entry)⟩,?_,rfl,inherited⟩
  rw [NativeParentCoverage.record_parents]
  exact NativeParentLedger.discover_entry state.1 state.2 _ frames parsed

theorem actual_context (state : Ledger) (log : List Observation) (world : World) (input : Input)
    (parent : NativeParentLedger.Parent) (present : parent ∈ state.parents)
    (context : Digest) (helper : context ∈ parent.helpers)
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent.input 0 64)) :
    context ∈ NativeParentLedger.contexts state (NativeShakeKernel.observed log world) input := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨parent,NativeParentLedger.active_member state _ input _ quoted parent present
    (NativeParentInputView.compatible_observed log world parent.input),helper⟩

/-- Every finite chronological ancestry chain occurs in the real history-reconstructed table. -/
theorem Known.sound {world : World} {log : List Observation} {input : Input} {context : Digest}
    (known : Known world log input context) (truthful : ObservationReplay.Agrees world log) :
    ∃ parent ∈ (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1.parents,
      parent.input = input ∧ context ∈ parent.helpers := by
  induction known with
  | direct before entry frames parsed context helper =>
    simpa only [List.append_nil] using NativeParentCoverage.fold_declaration
      (NativeParentLedger.empty,NativeShakeCache.empty) before [] entry frames parsed context helper
  | inherit before entry frames parsed parentInput context earlier quoted ih =>
    let state := before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
    have beforeTruth := ((ObservationReplay.agrees_append world before [entry]).mp truthful).1
    obtain ⟨parent,present,same,helper⟩ := ih beforeTruth
    have cache : state.2 = NativeShakeKernel.observed before world := by
      rw [NativeParentHistory.fold_cache]
      exact NativeShakeProjection.fold_observed _ world beforeTruth
    have inherited : context ∈ NativeParentLedger.contexts state.1 state.2 (observationInput entry) := by
      rw [cache]
      exact actual_context state.1 before world _ parent present context helper (by simpa only [same] using quoted)
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using record_context state entry frames parsed context inherited
  | later before later input context earlier ih =>
    obtain ⟨parent,present,same,helper⟩ := ih (((ObservationReplay.agrees_append world before later).mp truthful).1)
    refine ⟨parent,?_,same,helper⟩
    rw [List.foldl_append]
    exact (NativeParentHistory.fold_keeps_parents _ later).subset present

theorem resolve_known_helper {world : World} {log : List Observation} {parentInput : Input} {context : Digest}
    (known : Known world log parentInput context) (truthful : ObservationReplay.Agrees world log)
    (input : Input) (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parentInput 0 64))
    (root : Digest) (committed : root ∈ NativeParentLedger.roots input) :
    let state := log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
    (context,root) ∈ NativeParentLedger.resolve state.1 state.2 input := by
  let state := log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)
  obtain ⟨parent,present,same,helper⟩ := known.sound truthful
  have cache : state.2 = NativeShakeKernel.observed log world := by
    rw [NativeParentHistory.fold_cache]
    exact NativeShakeProjection.fold_observed _ world truthful
  change (context,root) ∈ NativeParentLedger.resolve state.1 state.2 input
  rw [cache]
  exact NativeParentLedger.resolve_actual_helper state.1 log world input parent present
    (by simpa only [same] using quoted) context root helper committed

/-- Descendant helper roots have actual retained snapshots after any supported nonempty read. -/
theorem known_helper_snapshot {Payload A : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) {world : World} {log : List Observation} {parentInput : Input} {context : Digest}
    (known : Known world log parentInput context) (truthful : ObservationReplay.Agrees world log)
    (input : Input) (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parentInput 0 64))
    (root : Digest) (committed : root ∈ NativeParentLedger.roots input)
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A) :
    let initial := log.foldl (NativeParentStateExecution.record enc dummy shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute enc dummy shape initial.1.1
        (.read input offset count next) initial.1.2 initial.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest, ⟨context,⟨root,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  let initial := log.foldl (NativeParentStateExecution.record enc dummy shape)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
  dsimp only
  intro result possible
  apply NativeParentStateExecution.resolved_snapshot enc dummy shape initial.1.1 input offset count next initial.1.2 initial.2
    (NativeParentStateExecution.fold_covered enc dummy shape _ _ (NativeParentStateExecution.empty_covered shape))
    positive (context,root) _ result possible
  have resolved := resolve_known_helper known truthful input quoted root committed
  simpa only [initial,NativeParentStateExecution.fold_parent] using resolved
end
end FormalProof4FHE.HasteBoots.NativeParentLineage
