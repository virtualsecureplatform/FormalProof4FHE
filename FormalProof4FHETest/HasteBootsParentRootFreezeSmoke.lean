module
import all FormalProof4FHE.HasteBoots.NativeParentRootFreeze
import all Init.Data.String.Defs
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleSpec OracleComp
namespace HasteBootsParentRootFreezeSmoke
noncomputable section

def context : Digest := fun _ => 0
def root : Digest := fun _ => 41
def seed : Digest := fun _ => 9
def parent : NativeParentLedger.Parent := ⟨[7],[],[context]⟩
def other : NativeParentLedger.Parent := ⟨[8],[],[root]⟩
def ledger : NativeParentLedger.State := ⟨[parent,other],∅⟩
def childFrames := NativeChildSeedView.seededFrames context [] [] seed ++
  [⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode [root] (by decide)⟩]
def child : Input := TranscriptFrame.encodeMany childFrames

private theorem child_valid : ∀ frame ∈ childFrames, TranscriptFrame.Valid frame := by
  intro frame present
  rcases List.mem_append.mp present with header | tail
  · exact NativeChildSeedView.seededFrames_valid context [] [] seed (by decide) (by decide) frame header
  · simp only [List.mem_singleton] at tail
    subst frame
    constructor <;> decide +kernel

private theorem quoted : NativeChildSeedView.quote child = some seed :=
  NativeChildSeedView.quote_complete context [] [] seed _ child_valid

private theorem committed : root ∈ NativeParentLedger.roots child :=
  NativeParentLedger.roots_frame child childFrames
    (TranscriptFrame.decodeAll_encodeMany childFrames child_valid) _
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) [root]
    (NativeParentInputView.helperRoots_complete [root] (by decide)) root (by simp)

example : parent ∈ NativeParentLedger.active ledger NativeShakeCache.empty child :=
  NativeParentLedger.active_member ledger _ child seed quoted parent (by simp [ledger])
    (NativeParentInputView.compatible_empty _ _)
example : other ∈ NativeParentLedger.active ledger NativeShakeCache.empty child :=
  NativeParentLedger.active_member ledger _ child seed quoted other (by simp [ledger])
    (NativeParentInputView.compatible_empty _ _)
example : (context,root) ∈ NativeParentLedger.resolve ledger NativeShakeCache.empty child :=
  NativeParentLedger.resolve_helper ledger _ child parent
    (NativeParentLedger.active_member ledger _ child seed quoted parent (by simp [ledger])
      (NativeParentInputView.compatible_empty _ _)) context root (by simp [parent]) committed
example : (root,root) ∈ NativeParentLedger.resolve ledger NativeShakeCache.empty child :=
  NativeParentLedger.resolve_helper ledger _ child other
    (NativeParentLedger.active_member ledger _ child seed quoted other (by simp [ledger])
      (NativeParentInputView.compatible_empty _ _)) root root (by simp [other]) committed

/-- One unknown byte must not exclude any of its 256 possible values. -/
def partiallyKnown (last : InputIndexedOracle.Byte) : NativeShakeCache.Cache := fun key =>
  if key.1 = parent.input ∧ key.2 < 63 then some 9 else if key = (parent.input,63) then some last else none
example (last : InputIndexedOracle.Byte) : NativeParentInputView.compatible (partiallyKnown last) parent.input
    (fun position => if position.val < 63 then 9 else last) := by
  intro position value known
  by_cases early : position.val < 63
  · simpa [partiallyKnown,early] using known.symm
  · have atLast : position.val = 63 := by omega
    simpa [partiallyKnown,early,atLast] using known.symm

example (log : List NativeTranscript.Observation) (world : World) :
    NativeParentInputView.compatible (NativeShakeKernel.observed log world) parent.input
      (InputIndexedOracle.block world parent.input 0 64) := NativeParentInputView.compatible_observed log world _

example (cache : NativeShakeCache.Cache) (input : Input) :
    (NativeParentLedger.discover ledger cache input).frozen = ∅ := NativeParentLedger.discover_frozen _ _ _
example (cache : NativeShakeCache.Cache) (input : Input) (key : NativeCanonicalLookupWire.Source) :
    key ∉ (NativeParentLedger.discover NativeParentLedger.empty cache input).frozen := by
  rw [NativeParentLedger.discover_frozen]
  exact Finset.notMem_empty key
example (cache : NativeShakeCache.Cache) (input : Input) :
    ledger.parents.Sublist (NativeParentLedger.prepare ledger cache input).next.parents := NativeParentLedger.prepare_parents _ _ _
example (cache : NativeShakeCache.Cache) (input later : Input) (key : NativeCanonicalLookupWire.Source)
    (present : key ∈ NativeParentLedger.resolve ledger cache input) :
    key ∉ (NativeParentLedger.prepare (NativeParentLedger.prepare ledger cache input).next cache later).requests :=
  NativeParentLedger.prepare_no_repeat _ _ _ key (NativeParentLedger.prepare_remembers _ _ _ key present)

example (cache : NativeShakeCache.Cache) :
    NativeParentRootFreeze.project <$> simulateQ NativeDirectRootFreeze.erase
      ((NativeParentRootFreeze.compile ledger (.read child 63 1 (fun _ => .pure ()))).run cache) =
      (NativeLazyProgram.compile (Cfg := Digest) (.read child 63 1 (fun _ => .pure ()))).run cache :=
  NativeParentRootFreeze.erase_compile ledger _ cache

example (program : OracleProgram.Program Unit) : NativeParentRootFreeze.compile ledger program = (do
    let first ← NativeParentRootFreeze.compile ledger (NativeProgramPrefix.take 3 program)
    let second ← NativeParentRootFreeze.compile first.2 (NativeProgramPrefix.resume first.1.1)
    pure ((second.1.1,first.1.2++second.1.2),second.2)) := NativeParentRootFreeze.compile_resume ledger 3 program

example (binding : NativeCanonicalLookupWire.Binding) :
    NativeParentInputView.frameHelper ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ =
      some binding.helper := NativeParentInputView.frameHelper_complete binding
example : NativeParentInputView.helperRoots
    ⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode [root] (by decide)⟩ = some [root] :=
  NativeParentInputView.helperRoots_complete [root] (by decide)
example (state : NativeTranscript.Transcript) (before : List TranscriptFrame.Frame)
    (bytes : state.input = TranscriptFrame.encodeMany before) (label context : Input)
    (valid : ∀ frame ∈ before++[⟨6,label,context⟩,
      ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩], TranscriptFrame.Valid frame) :
    NativeParentInputView.parseParent (NativeTranscript.requestInput (NativeTranscript.absorb state 6 label context)
      (NativeTranscript.utf8 "classical child seed") 64) =
      some (before++[⟨6,label,context⟩,
        ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]) :=
  NativeParentInputView.parseParent_request state before bytes label context valid

def shape (_ : Digest) : BinaryTree.Skeleton := .leaf

/-- A helper without its context in the raw child input is associated through the old parent table. -/
example (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : (((Unit × List NativeTranscript.Observation) × NativeParentLedger.State) × NativeShakeCache.Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape ledger
      (.read child 0 1 (fun _ => .pure ())) NativeShakeCache.empty state)) :
    ⟨context,⟨root,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  apply NativeParentRootFreeze.read_snapshot _ _ _ _ _ _ _ _ _ _ (by decide) (context,root) _ result possible
  apply (NativeParentLedger.prepare_mem _ _ _ _).mpr
  refine ⟨?_,by simp [ledger]⟩
  exact NativeParentLedger.resolve_helper ledger _ child parent
    (NativeParentLedger.active_member ledger _ child seed quoted parent (by simp [ledger])
      (NativeParentInputView.compatible_empty _ _)) context root (by simp [parent]) committed

example (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape ledger
      (.read child 0 0 (fun _ => .pure ())) cache state =
    NativeParentRootFreeze.prependExecution (.output child 0 []) <$>
      NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape
        (NativeParentLedger.discover ledger cache child) (.pure ()) cache state :=
  NativeParentRootFreeze.execute_zero _ _ _ _ _ _ _ _ _

example (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun result => (NativeParentRootFreeze.project result.1,result.2.hash.cache)) <$>
      NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape ledger
        (.hash child (fun answer => .pure answer)) cache state =
    Prod.map id (fun final => final.hash.cache) <$>
      NativeLazyStateExecution.execute NativeGoldColumnAuthentication.encoding context shape
        (.hash child (fun answer => .pure answer)) cache state :=
  NativeParentRootFreeze.execute_erasure _ _ _ _ _ _ _

end
end HasteBootsParentRootFreezeSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.frameHelper_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.frameHelper_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.helperRoots_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.helperRoots_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.compatible_empty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.compatible_empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.compatible_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.compatible_observed

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.isSeedFrames_native' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.isSeedFrames_native

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.parseParent_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.parseParent_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.parent_request_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.parent_request_frames

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentInputView.parseParent_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentInputView.parseParent_request

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.discover_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.discover_frozen

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_mem

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_frozen

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_keeps

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_remembers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_remembers

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_no_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_no_repeat

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.active_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.active_member

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.resolve_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.resolve_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.resolve_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.resolve_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.resolve_actual_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.resolve_actual_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.discover_parents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.discover_parents

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_parents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.prepare_parents

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.discover_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.discover_entry

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.helpers_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.helpers_frame

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.roots_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.roots_frame

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLedger.discover_no_backdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLedger.discover_no_backdate

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.project_prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.project_prepend

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.erase_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.erase_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.canonical_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.canonical_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_erasure

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_pure

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.execute_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.compile_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.compile_bind

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.compile_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.compile_resume

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.read_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.read_snapshot

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentRootFreeze.actual_helper_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentRootFreeze.actual_helper_snapshot
