module
import all FormalProof4FHE.HasteBoots.NativeForkAncestry
import all FormalProof4FHE.HasteBoots.NativeProgramComposition
import all FormalProof4FHETest.HasteBootsSourceExposureCoverageSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (Program run bind)
open OracleSpec OracleComp
open HasteBootsParentStateSmoke (context root)
open HasteBootsSourceExposureCoverageSmoke (binding bindingFrame sources)
namespace HasteBootsForkAncestrySmoke
noncomputable section

def parent := NativeCanonicalLookupWire.bind (NativeTranscript.new [] context) binding
def before : List TranscriptFrame.Frame :=
  [⟨0,utf8 "protocol",utf8 "HasteBoots framed SHAKE256 v1"⟩,
   ⟨0,utf8 "application",[]⟩,⟨0,utf8 "trusted profile",List.ofFn context⟩,bindingFrame]
def packet : NativeLookupMultiplicityWire.Packet := ⟨⟨[],by decide⟩,by decide⟩
private theorem framed : parent.input = TranscriptFrame.encodeMany before := by
  simp only [parent,before,NativeCanonicalLookupWire.bind_input,NativeTranscript.new,NativeTranscript.absorb,
    TranscriptFrame.encodeMany,bindingFrame,List.nil_append,List.append_nil,List.append_assoc]
private theorem valid : ∀ frame ∈ before, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [before,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel
private theorem groupedFits : (NativeLookupMultiplicityWire.grouped packet).length < TranscriptFrame.lengthLimit := by decide +kernel
private theorem flatFits : (NativeLookupMultiplicityWire.flattened packet).length < TranscriptFrame.lengthLimit := by decide +kernel

def prelude : Program Input := .read [255] 0 2 .pure
def start := NativeSharedLookupChild.start parent packet
def startedProgram := bind prelude (fun _ => start)
def nested (pair : NativeSharedLookupChild.State × Transcript) := NativeTranscriptProgram.forkChild pair.2 [7] []
def finalRead (pair : Transcript × Transcript) := NativeTranscriptProgram.challengeBytes pair.2 [] 1
def program := bind prelude (fun _ => bind start (fun pair => bind (nested pair) finalRead))
def log (world : World) := (run program world).run.2
def started (world : World) := (NativeSharedLookupChild.startExecute world parent packet).1
def nestedResult (world : World) := (run (nested (started world)) world).run.1
def producer := NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare parent packet)
  NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
def nestedProducer (world : World) := NativeForkAncestry.seedInput (started world).2 [7] []
def leafInput (world : World) := NativeTranscript.requestInput (nestedResult world).2 [] 1

private theorem start_observed (world : World) : (run start world).run.2.Sublist (log world) :=
  NativeForkAncestry.segment_log world prelude (fun _ => start) (fun _ pair => bind (nested pair) finalRead)
private theorem nested_observed (world : World) : (run (nested (started world)) world).run.2.Sublist (log world) := by
  have segment := NativeForkAncestry.segment_log world startedProgram nested (fun _ => finalRead)
  simpa only [startedProgram,OracleProgram.run_bind,ObservationReplay.run_bind,prelude,OracleProgram.run,
    program,log,start,NativeSharedLookupChild.run_start,started,NativeProgramComposition.bind_assoc] using segment

private theorem source_realized (world : World) (key : NativeCanonicalLookupWire.Source) (member : key ∈ sources.val) :
    ∃ index, NativeSeedAncestry.Realized world (log world) producer index (.source key) :=
  NativeForkAncestry.start_source world (log world) parent before packet framed valid groupedFits flatFits
    (start_observed world) binding (by simp [before,bindingFrame]) key member
private theorem helper_realized (world : World) :
    ∃ index, NativeSeedAncestry.Realized world (log world) producer index (.helper context) :=
  NativeForkAncestry.start_helper world (log world) parent before packet framed valid groupedFits flatFits
    (start_observed world) binding (by simp [before,bindingFrame])

example (world : World) : ∃ fuel, (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run =
    (.inr (run program world).run.1,log world) := OracleProgramMachine.complete program world
example (world : World) (fuel : ℕ) :
    (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2.IsPrefix (log world) :=
  OracleProgramMachine.log_prefix_run fuel program world
example (world : World) : (log world).length = 12 := rfl
example (world : World) : (log world).head? = some (.output [255] 0 (InputIndexedOracle.bytes world [255] 0 2)) := rfl
example (world : World) : ∃ index, NativeSeedAncestry.Realized world (log world) producer index (.source (context,root)) :=
  source_realized world (context,root) (by simp [sources])
example (world : World) : ∃ index, NativeSeedAncestry.Realized world (log world) producer index (.source (root,root)) :=
  source_realized world (root,root) (by simp [sources])
example (world : World) : ∃ index, NativeSeedAncestry.Realized world (log world) producer index (.helper context) := helper_realized world
example (world : World) : NativeChildSeedView.HasHeader (started world).2 parent.profile
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext (InputIndexedOracle.block world producer 0 64) :=
  NativeForkAncestry.start_header world parent packet

private theorem inherited (world : World) (fact : NativeSeedAncestry.Fact)
    (realized : ∃ index, NativeSeedAncestry.Realized world (log world) producer index fact) :
    ∃ index, NativeSeedAncestry.Realized world (log world) (nestedProducer world) index fact := by
  obtain ⟨index,previous⟩ := realized
  exact NativeForkAncestry.fork_inherit previous (started world).2 [7] [] (by decide) (by decide)
    parent.profile NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
    (NativeForkAncestry.start_header world parent packet) (nested_observed world)
example (world : World) :
    ∃ index, NativeSeedAncestry.Realized world (log world) (nestedProducer world) index (.source (context,root)) :=
  inherited world _ (source_realized world (context,root) (by simp [sources]))
example (world : World) :
    ∃ index, NativeSeedAncestry.Realized world (log world) (nestedProducer world) index (.helper context) :=
  inherited world _ (helper_realized world)
private theorem leaf_quote (world : World) : NativeChildSeedView.quote (leafInput world) =
    some (InputIndexedOracle.block world (nestedProducer world) 0 64) := by
  apply (NativeChildSeedView.forkChild_header world (started world).2 [7] [] (by decide) (by decide)).request [] 1 (by decide)
private theorem leaf_position (world : World) : (log world)[11]? =
    some (.output (leafInput world) 0 (InputIndexedOracle.bytes world (leafInput world) 0 1)) := rfl

example (world : World) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    NativeSeedAncestry.Known world ((log world).take 11) (nestedProducer world) (.source (context,root)) := by
  obtain ⟨index,realized⟩ := inherited world _ (source_realized world (context,root) (by simp [sources]))
  apply NativeForkAncestry.program_before_quote program world safe realized 11 _ (leaf_position world)
  simp only [NativeChildSeedView.candidate,show InputIndexedOracle.bytes world (leafInput world) 0 1 ≠ [] by simp [InputIndexedOracle.bytes],ite_false]
  exact leaf_quote world


private theorem before_known (world : World) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (fact : NativeSeedAncestry.Fact)
    (realized : ∃ index, NativeSeedAncestry.Realized world (log world) producer index fact) :
    NativeSeedAncestry.Known world ((log world).take 11) (nestedProducer world) fact := by
  obtain ⟨index,realized⟩ := inherited world fact realized
  apply NativeForkAncestry.program_before_quote program world safe realized 11 _ (leaf_position world)
  simp only [NativeChildSeedView.candidate,show InputIndexedOracle.bytes world (leafInput world) 0 1 ≠ [] by simp [InputIndexedOracle.bytes],ite_false]
  exact leaf_quote world

example (world : World) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    NativeSeedAncestry.Known world ((log world).take 11) (nestedProducer world) (.helper context) :=
  before_known world safe _ (helper_realized world)

private theorem source_resolved (world : World) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (key : NativeCanonicalLookupWire.Source) (member : key ∈ sources.val) :
    let before := (log world).take 11
    key ∈ NativeParentLedger.resolve
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 (leafInput world) := by
  have known := before_known world safe (.source key) (source_realized world key member)
  have truthful : ObservationReplay.Agrees world ((log world).take 11) := by
    intro entry present
    exact (OracleProgram.run_replay program).truthful world entry ((List.take_sublist _ _).subset present)
  exact NativeSeedAncestry.known_resolves world _ (nestedProducer world) (.source key) known truthful
    (leafInput world) (leaf_quote world) key (by simp [NativeSeedAncestry.Keys])

example (world : World) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    let before := (log world).take 11
    (context,root) ∈ NativeParentLedger.resolve
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 (leafInput world) :=
  source_resolved world safe _ (by simp [sources])
example (world : World) (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    let before := (log world).take 11
    (root,root) ∈ NativeParentLedger.resolve
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 (leafInput world) :=
  source_resolved world safe _ (by simp [sources])

example (world : World) (fact : NativeSeedAncestry.Fact) :
    ¬∃ index, NativeSeedAncestry.Realized world [.start producer] producer index fact := by
  rintro ⟨index,realized⟩
  have first := realized.first
  simp [OracleFirstExposure.locate,ObservationReplay.coordinates] at first


example {Payload B : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (world : World)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) (next : Input → Program B) :
    let before := (log world).take 11
    let state := before.foldl (NativeParentStateExecution.record enc dummy shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute enc dummy shape state.1.1
        (.read (leafInput world) 0 1 next) state.1.2 state.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest,
        ⟨context,⟨root,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  have known := before_known world safe (.source (context,root))
    (source_realized world (context,root) (by simp [sources]))
  have truthful : ObservationReplay.Agrees world ((log world).take 11) := by
    intro entry present
    exact (OracleProgram.run_replay program).truthful world entry ((List.take_sublist _ _).subset present)
  exact NativeSourceLineage.known_source_snapshot enc dummy shape known truthful
    (leafInput world) (leaf_quote world) 0 1 (by decide) next

end
end HasteBootsForkAncestrySmoke

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgramMachine.take_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgramMachine.take_program

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgramMachine.take_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgramMachine.take_run

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgramMachine.prefix_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgramMachine.prefix_complete

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgramMachine.complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgramMachine.complete

/-- info: 'FormalProof4FHE.HasteBoots.OracleProgramMachine.log_prefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.OracleProgramMachine.log_prefix_run

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.seedFrames_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.seedFrames_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.seedInput_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.seedInput_parsed

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.fork_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.fork_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.fork_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.fork_direct

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.fork_inherit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.fork_inherit

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.segment_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.segment_log

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.start_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.start_fork

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.prepare_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.prepare_frames

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.prepareFrames_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.prepareFrames_valid

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.start_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.start_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.start_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.start_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.identity_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.identity_header

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.start_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.start_header

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.program_chronological' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.program_chronological

/-- info: 'FormalProof4FHE.HasteBoots.NativeForkAncestry.program_before_quote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeForkAncestry.program_before_quote
