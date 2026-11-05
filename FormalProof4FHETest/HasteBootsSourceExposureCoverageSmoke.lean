module
import all FormalProof4FHE.HasteBoots.NativeSourceLineage
import all FormalProof4FHE.HasteBoots.CausalExposureCoverage
import all FormalProof4FHETest.HasteBootsLifetimeLineageSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open HasteBootsParentStateSmoke (config context root seed shape world child quoted)
open HasteBootsLifetimeLineageSmoke (descendantInput descendantFrames descendant_valid descendant_parsed descendant_quote)
namespace HasteBootsSourceExposureCoverageSmoke
noncomputable section

def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[(context,root),(context,root),(root,root)],by decide⟩
def binding : NativeCanonicalLookupWire.Binding := ⟨config,context,sources⟩
def bindingFrame : TranscriptFrame.Frame := ⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩
def frames : List TranscriptFrame.Frame := [bindingFrame,⟨6,[],[]⟩,
  ⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]
def parentInput := TranscriptFrame.encodeMany frames
private theorem valid : ∀ frame ∈ frames, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [frames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> constructor <;> decide +kernel
private theorem parsed : NativeParentInputView.parseParent parentInput = some frames :=
  NativeParentInputView.parseParent_complete [bindingFrame] [] [] valid
private theorem direct_source (key : NativeCanonicalLookupWire.Source) (present : key ∈ sources.val) :
    key ∈ NativeParentLedger.direct parentInput :=
  NativeSourceLineage.binding_source parentInput frames parsed binding (by simp [frames,bindingFrame]) key present

private theorem block_world (input : Input) : InputIndexedOracle.block world input 0 64 = seed := rfl
private theorem descendant_actual_quote (input : Input) : NativeChildSeedView.quote descendantInput =
    some (InputIndexedOracle.block world input 0 64) := by
  rw [block_world]
  simpa only [block_world] using descendant_quote
private theorem child_actual_quote (input : Input) : NativeChildSeedView.quote child =
    some (InputIndexedOracle.block world input 0 64) := by
  rw [block_world]
  exact quoted

def log : List NativeTranscript.Observation := [.start parentInput]++[.start descendantInput]
private theorem known (key : NativeCanonicalLookupWire.Source) (present : key ∈ sources.val) :
    NativeSourceLineage.Known world log descendantInput key :=
  NativeSourceLineage.Known.inherit [.start parentInput] (.start descendantInput) descendantFrames descendant_parsed
    parentInput key (NativeSourceLineage.Known.direct [] (.start parentInput) frames parsed key (direct_source key present)) (descendant_actual_quote parentInput)
private theorem truthful : ObservationReplay.Agrees world log := by
  intro entry member
  simp only [log,List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> trivial

example : (context,root) ∈ NativeParentLedger.direct parentInput := direct_source _ (by simp [sources])
example : (root,root) ∈ NativeParentLedger.direct parentInput := direct_source _ (by simp [sources])
example : NativeParentLedger.direct descendantInput = [] := by
  rw [NativeParentLedger.direct,NativeRootInputView.raw,descendantInput,TranscriptFrame.decodeAll_encodeMany _ descendant_valid]
  decide +kernel
example : NativeSourceLineage.Known world log descendantInput (context,root) := known (context,root) (by simp [sources])
example : NativeSourceLineage.Known world log descendantInput (root,root) := known (root,root) (by simp [sources])
example : ∃ parent ∈ (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1.parents,
    parent.input = descendantInput ∧ (context,root) ∈ parent.sources := (known (context,root) (by simp [sources])).sound truthful
example : (context,root) ∈ NativeParentLedger.resolve
    (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
    (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 child :=
  NativeSourceLineage.resolve_known_source (known (context,root) (by simp [sources])) truthful child (child_actual_quote descendantInput)
example :
    let initial := log.foldl (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape initial.1.1
      (.read child 0 1 (fun _ => .pure ())) initial.1.2 initial.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest, ⟨context,⟨root,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  NativeSourceLineage.known_source_snapshot _ _ _ (known (context,root) (by simp [sources])) truthful child (child_actual_quote descendantInput) 0 1 (by decide) (fun _ => .pure ())

-- Starts, empty reads, reads outside the seed block, and SHA-512 activity do not create a seed exposure.
def step (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 0 then .start child 1 else
  if state = 1 then .read child 0 1 (fun _ => 2) else
  if state = 2 then .read [7,9] 0 0 (fun _ => 3) else
  if state = 3 then .read [7,9] 64 1 (fun _ => 4) else
  if state = 4 then .hash [7,9] (fun _ => 5) else
  if state = 5 then .read [7,9] 63 1 (fun _ => 6) else .done ()
private theorem first : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step 6 0) world).run.2
    (OracleFirstExposure.seedCoordinates [7,9]) = some 5 := by decide +kernel
private theorem present : NativeTranscript.Observation.output child 0 [9] ∈
    (OracleProgram.run (OracleMachine.take step 5 0) world).run.2 := by decide +kernel
private theorem candidate : NativeChildSeedView.candidate (.output child 0 [9]) =
    some (InputIndexedOracle.block world [7,9] 0 64) := by
  rw [block_world]
  simpa only [NativeChildSeedView.candidate,ite_eq_right (by decide : ([9] : Input) ≠ [])] using quoted

example : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step 5 0) world).run.2
    (OracleFirstExposure.seedCoordinates [7,9]) = none := by decide +kernel
example : CausalSeedExposure.firstRead step (OracleProgram.run (OracleMachine.take step 5 0) world).run = some [7,9] :=
  CausalExposureCoverage.selected_at_first_exposure step 6 5 0 world [7,9] first
example : ∃ time, CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step time 0) world).run world :=
  CausalExposureCoverage.prior_quote_lifetime step 6 5 0 world [7,9] first (.output child 0 [9]) present candidate
example : CausalExposureCoverage.SeedPrequery step 0 world := ⟨6,5,[7,9],.output child 0 [9],first,present,candidate⟩
example : MeasurableSet {world | CausalExposureCoverage.SeedPrequery step 0 world} := CausalExposureCoverage.seedPrequery_measurable step 0
example : InputIndexedOracle.law {world | CausalExposureCoverage.SeedPrequery step 0 world} ≤
    ∫⁻ world, CausalExposureLifetime.totalCharge (fun _ => (pure () : NativeTranscript.Execution Unit)) (fun _ => 0) step world
      ∂InputIndexedOracle.law := CausalExposureCoverage.seedPrequery_probability step 0

private theorem prequeryAfter : CausalExposureCoverage.SeedPrequeryAfter HasteBootsLifetimeLineageSmoke.past id
    HasteBootsLifetimeLineageSmoke.step world := by
  refine ⟨0,[7,9],.output child 0 [9],?_,?_,?_,candidate⟩ <;> decide +kernel
example : ∃ time, CausalSeedExposure.event HasteBootsLifetimeLineageSmoke.step
    (CausalExposureLifetime.history HasteBootsLifetimeLineageSmoke.past id HasteBootsLifetimeLineageSmoke.step time world).run world :=
  CausalExposureCoverage.seedPrequeryAfter_lifetime _ _ _ _ prequeryAfter
example : MeasurableSet {world | CausalExposureCoverage.SeedPrequeryAfter HasteBootsLifetimeLineageSmoke.past id
    HasteBootsLifetimeLineageSmoke.step world} :=
  CausalExposureCoverage.seedPrequeryAfter_measurable (OracleProgram.run_replay HasteBootsLifetimeLineageSmoke.prelude) id _
example (inherited : Set World) :
    (InputIndexedOracle.law[|{other | (HasteBootsLifetimeLineageSmoke.past other).run = (HasteBootsLifetimeLineageSmoke.past world).run}])
      (inherited ∪ {other | CausalExposureCoverage.SeedPrequeryAfter HasteBootsLifetimeLineageSmoke.past id HasteBootsLifetimeLineageSmoke.step other}) ≤
    (InputIndexedOracle.law[|{other | (HasteBootsLifetimeLineageSmoke.past other).run = (HasteBootsLifetimeLineageSmoke.past world).run}]) inherited +
      ∫⁻ other, CausalExposureLifetime.totalCharge HasteBootsLifetimeLineageSmoke.past id HasteBootsLifetimeLineageSmoke.step other
        ∂InputIndexedOracle.law[|{other | (HasteBootsLifetimeLineageSmoke.past other).run = (HasteBootsLifetimeLineageSmoke.past world).run}] :=
  CausalExposureCoverage.conditional_seedPrequeryAfter (OracleProgram.run_replay HasteBootsLifetimeLineageSmoke.prelude) id _ world inherited
end
end HasteBootsSourceExposureCoverageSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceLineage.record_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceLineage.record_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceLineage.actual_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceLineage.actual_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceLineage.Known.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceLineage.Known.sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceLineage.resolve_known_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceLineage.resolve_known_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceLineage.binding_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceLineage.binding_source

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceLineage.known_source_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceLineage.known_source_snapshot

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.read_hits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.read_hits

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.take_zero_log' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.take_zero_log

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.firstRead_of_next_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.firstRead_of_next_hit

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.locate_take_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.locate_take_succ

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.selected_at_first_exposure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.selected_at_first_exposure

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.prior_quote_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.prior_quote_lifetime

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_lifetime

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_probability

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_lifetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_lifetime

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.conditional_seedPrequeryAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.conditional_seedPrequeryAfter

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_iff

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequery_measurable

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_iff

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_measurable

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureCoverage.seedPrequeryAfter_probability
