module
import all FormalProof4FHE.HasteBoots.NativeParentCoverage
import all Init.Data.String.Defs
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeParentRootFreeze (Ledger)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsParentStateSmoke
noncomputable section

def context : Digest := fun _ => 0
def seed : Digest := fun _ => 9
def root : Digest := fun _ => 41
def shape (_ : Digest) : BinaryTree.Skeleton := .leaf
def config : NativeLookupRequestWire.Config := ⟨⟨1,by decide⟩,⟨[],by decide⟩,⟨1,by decide⟩⟩
def binding : NativeCanonicalLookupWire.Binding := ⟨config,context,⟨[],by decide⟩⟩
def bindingFrame : TranscriptFrame.Frame := ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩
def parentFrames : List TranscriptFrame.Frame := [bindingFrame,⟨6,[],[]⟩,
  ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]
def parentInput : Input := TranscriptFrame.encodeMany parentFrames

def childFrames : List TranscriptFrame.Frame := NativeChildSeedView.seededFrames context [] [] seed ++
  [⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode [root] (by decide)⟩]
def child : Input := TranscriptFrame.encodeMany childFrames
private theorem parent_valid : ∀ frame ∈ parentFrames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [parentFrames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> constructor <;> decide +kernel
private theorem parent_parsed : NativeParentInputView.parseParent parentInput = some parentFrames :=
  NativeParentInputView.parseParent_complete [bindingFrame] [] [] parent_valid
private theorem helper : context ∈ NativeParentLedger.helpers parentInput :=
  NativeParentCoverage.binding_helper parentInput parentFrames parent_parsed binding (by simp [parentFrames,bindingFrame])
private theorem child_valid : ∀ frame ∈ childFrames, TranscriptFrame.Valid frame := by
  intro frame member
  rcases List.mem_append.mp member with header | tail
  · exact NativeChildSeedView.seededFrames_valid context [] [] seed (by decide) (by decide) frame header
  · obtain rfl := List.mem_singleton.mp tail
    constructor <;> decide +kernel
private theorem quoted : NativeChildSeedView.quote child = some seed :=
  NativeChildSeedView.quote_complete context [] [] seed _ child_valid
private theorem committed : root ∈ NativeParentLedger.roots child :=
  NativeParentLedger.roots_frame child childFrames (TranscriptFrame.decodeAll_encodeMany childFrames child_valid)
    _ (List.mem_append_right _ (by simp)) [root] (NativeParentInputView.helperRoots_complete [root] (by decide)) root (by simp)

def world : World := fun _ => 9
def later : List NativeTranscript.Observation := [.output parentInput 0 (List.replicate 63 9),.hash [255] (List.replicate 64 9)]
def history : List NativeTranscript.Observation := [.start parentInput]++later
private theorem truthful : ObservationReplay.Agrees world history := by
  intro entry member
  simp only [history,later,List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · trivial
  · simp [ObservationReplay.Matches,world,InputIndexedOracle.bytes,InputIndexedOracle.shake,InputIndexedOracle.block]
  · simp [ObservationReplay.Matches,world,InputIndexedOracle.sha512]
private theorem actual_quote : NativeChildSeedView.quote child = some (InputIndexedOracle.block world parentInput 0 64) := by
  exact quoted

example : TranscriptFrame.decodeAll parentInput = some parentFrames := NativeParentCoverage.parseParent_decode _ _ parent_parsed
example : context ∈ NativeParentLedger.helpers parentInput := helper
example : ∃ parent ∈ (NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty) (.start parentInput)).1.parents,
    parent.input = parentInput ∧ context ∈ parent.helpers :=
  NativeParentCoverage.record_declaration _ (.start parentInput) parentFrames parent_parsed context helper
example : ∃ parent ∈ (NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty) (.output parentInput 63 [9])).1.parents,
    parent.input = parentInput ∧ context ∈ parent.helpers :=
  NativeParentCoverage.record_declaration _ (.output parentInput 63 [9]) parentFrames parent_parsed context helper
example : ∃ parent ∈ (NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty) (.hash parentInput (List.replicate 64 9))).1.parents,
    parent.input = parentInput ∧ context ∈ parent.helpers :=
  NativeParentCoverage.record_declaration _ (.hash parentInput (List.replicate 64 9)) parentFrames parent_parsed context helper
example : ∃ parent ∈ (history.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1.parents,
    parent.input = parentInput ∧ context ∈ parent.helpers :=
  NativeParentCoverage.fold_declaration _ [] later (.start parentInput) parentFrames parent_parsed context helper
example : (context,root) ∈ NativeParentLedger.resolve
    (history.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
    (history.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 child :=
  NativeParentCoverage.resolve_declared_helper [] later (.start parentInput) parentFrames parent_parsed context helper
    world truthful child actual_quote root committed

example (initial : Ledger × NativeShakeCache.Cache) :
    (history.foldl NativeParentHistory.record initial).2 = history.foldl NativeShakeHistory.record initial.2 := NativeParentHistory.fold_cache _ _
example (initial : Ledger × NativeShakeCache.Cache) : initial.1.frozen ⊆ (history.foldl NativeParentHistory.record initial).1.frozen :=
  NativeParentHistory.fold_keeps_frozen _ _
example (initial : Ledger × NativeShakeCache.Cache) : initial.1.parents.Sublist (history.foldl NativeParentHistory.record initial).1.parents :=
  NativeParentHistory.fold_keeps_parents _ _
example (initial : Ledger × NativeShakeCache.Cache) :
    history.foldl NativeParentHistory.record initial = later.foldl NativeParentHistory.record
      (NativeParentHistory.record initial (.start parentInput)) := by
  simp only [history,List.foldl_append,List.foldl_cons,List.foldl_nil]

example : NativeParentStateExecution.Covered
    (history.foldl (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)) :=
  NativeParentStateExecution.fold_covered _ _ _ _ _ (NativeParentStateExecution.empty_covered shape)
example : (history.foldl (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)).2.hash = JointHashCache.project history := by
  rw [NativeParentStateExecution.fold_hash]
  rfl

example :
    let initial := history.foldl (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape initial.1.1
      (.read child 0 1 (fun _ => .pure ())) initial.1.2 initial.2),
      ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ⟨context,⟨root,log⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  NativeParentCoverage.declared_helper_snapshot _ _ _ [] later (.start parentInput) parentFrames parent_parsed context helper
    world truthful child actual_quote root committed 0 1 (by decide) (fun _ => .pure ())

def program : OracleProgram.Program Unit := .start parentInput
  (.read parentInput 0 1 (fun _ => .hash [255] (fun _ => .read child 0 1 (fun _ => .pure ()))))
example : NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape NativeParentLedger.empty program
    NativeShakeCache.empty (CheckpointExecution.empty shape) =
    NativeParentStateExecution.reconstruct NativeGoldColumnAuthentication.encoding context shape NativeParentLedger.empty
      NativeShakeCache.empty (CheckpointExecution.empty shape) <$>
      NativeLazyExecution.execute NativeGoldColumnAuthentication.encoding context shape program NativeShakeCache.empty
        (CheckpointExecution.empty shape) := NativeParentStateExecution.execute_records _ _ _ _ _ _ _
example (event : (((Unit × List NativeTranscript.Observation) × Ledger) × NativeShakeCache.Cache) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    InputIndexedOracle.law {world | event (NativeParentStateExecution.reconstruct NativeGoldColumnAuthentication.encoding context shape
      NativeParentLedger.empty NativeShakeCache.empty (CheckpointExecution.empty shape) (OracleProgram.run program world).run)} =
      Pr{let result ← (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape NativeParentLedger.empty program
        NativeShakeCache.empty (CheckpointExecution.empty shape))}[event result] := NativeParentStateExecution.from_empty _ _ _ _ _

example (cache : NativeShakeCache.Cache) (result : Input × NativeShakeCache.Cache)
    (possible : result ∈ support (NativeShakeReadLaw.sample parentInput 63 1 cache)) : result.1.length = 1 :=
  (NativeParentStateExecution.sample_records parentInput 63 1 cache result possible).1
example : NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape) (.output parentInput 0 []) =
    ((NativeParentLedger.discover NativeParentLedger.empty NativeShakeCache.empty parentInput,NativeShakeCache.empty),CheckpointExecution.empty shape) := rfl

example : seed ∈ NativeChildSeedView.guesses [.output child 0 [0]] :=
  NativeParentCoverage.prior_quote_target _ (.output child 0 [0]) (by simp) seed
    (by simpa only [NativeChildSeedView.candidate,ite_eq_right (by decide : ([0] : Input) ≠ [])] using quoted)
example : seed ∈ NativeChildSeedView.guesses [.hash child (List.replicate 64 0)] :=
  NativeParentCoverage.prior_quote_target _ (.hash child (List.replicate 64 0)) (by simp) seed quoted

def prelude : OracleProgram.Program Unit := .start parentInput (.read parentInput 0 63 (fun _ => .pure ()))
example (event : (((Unit × List NativeTranscript.Observation) × Ledger) × NativeShakeCache.Cache) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    let initial := (OracleProgram.run prelude world).run.2.foldl
      (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    (InputIndexedOracle.law[|{other | (OracleProgram.run prelude other).run = (OracleProgram.run prelude world).run}])
      {other | event (NativeParentStateExecution.reconstruct NativeGoldColumnAuthentication.encoding context shape
        initial.1.1 initial.1.2 initial.2 (OracleProgram.run program other).run)} =
      Pr{let result ← (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape initial.1.1
        program initial.1.2 initial.2)}[event result] :=
  NativeParentStateExecution.after_prelude_law program (OracleProgram.run_replay prelude) world _ _ _ event

def cached : NativeShakeCache.Cache := fun _ => some 9
private theorem sample_cached : NativeShakeReadLaw.sample parentInput 63 1 cached = pure ([9],cached) := by
  simp [NativeShakeReadLaw.sample,NativeShakeKernel.step,NativeShakeKernel.answer,NativeShakeKernel.install,cached]

example : (fun result => (result.1.1.1.2,result.2.hash.log)) <$>
    NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape NativeParentLedger.empty
      (.read parentInput 63 1 (fun _ => .pure ())) cached (CheckpointExecution.empty shape) =
      pure ([NativeTranscript.Observation.output parentInput 63 [9]],[]) := by
  rw [NativeParentRootFreeze.execute_read _ _ _ _ _ _ _ _ _ _ (by decide),sample_cached,pure_bind,
    NativeParentRootFreeze.execute_pure,pure_bind,map_pure]
  simp only [NativeParentRootFreeze.prependExecution,NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,RecordRoots.hash_eq,CheckpointExecution.empty,CachedHashHandler.empty]

example (event : ((((OracleProgram.Program Unit ⊕ Unit) × List NativeTranscript.Observation) × Ledger) × NativeShakeCache.Cache) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (InputIndexedOracle.law[|{other | (OracleProgram.run prelude other).run = (OracleProgram.run prelude world).run}])
      {other | event (NativeParentStateExecution.reconstruct NativeGoldColumnAuthentication.encoding context shape
        NativeParentLedger.empty (NativeShakeKernel.observed (OracleProgram.run prelude world).run.2 world)
        ((OracleProgram.run prelude world).run.2.foldl
          (NativeLazyStateExecution.record NativeGoldColumnAuthentication.encoding context shape) (CheckpointExecution.empty shape))
        (OracleProgram.runPrefix 2 program other).run)} =
      Pr{let result ← (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape NativeParentLedger.empty
        (NativeProgramPrefix.take 2 program) (NativeShakeKernel.observed (OracleProgram.run prelude world).run.2 world)
        ((OracleProgram.run prelude world).run.2.foldl
          (NativeLazyStateExecution.record NativeGoldColumnAuthentication.encoding context shape) (CheckpointExecution.empty shape)))}[event result] := by
  apply NativeParentStateExecution.prefix_law _ _ (OracleProgram.run_replay prelude) world _ _ _ _ _ _ event
  exact NativeLazyStateExecution.fold_project _ _ _ [] _ _ rfl

end
end HasteBootsParentStateSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.read_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.read_record

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.compile_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.compile_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.simulated_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.simulated_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.record_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.record_append

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.record_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.record_cache

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.fold_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.fold_cache

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.record_keeps_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.record_keeps_frozen

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.fold_keeps_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.fold_keeps_frozen

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.record_keeps_parents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.record_keeps_parents

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentHistory.fold_keeps_parents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentHistory.fold_keeps_parents

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_start

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.sample_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.sample_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.sample_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.sample_record

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_records_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_records_support

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.project_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.project_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_records

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.record_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.record_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.fold_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.fold_hash

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.fold_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.fold_parent

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.state_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.state_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.from_empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.after_prelude_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.after_prelude_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.record_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.record_covered

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.fold_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.fold_covered

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.empty_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.empty_covered

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_covered

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.execute_bind

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.prefix_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.prefix_law

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentStateExecution.resolved_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentStateExecution.resolved_snapshot

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.record_parents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.record_parents

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.parseParent_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.parseParent_decode

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.binding_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.binding_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.record_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.record_declaration

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.fold_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.fold_declaration

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.resolve_declared_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.resolve_declared_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.declared_helper_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.declared_helper_snapshot

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.prior_quote_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.prior_quote_target

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentCoverage.prior_quote_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentCoverage.prior_quote_event
