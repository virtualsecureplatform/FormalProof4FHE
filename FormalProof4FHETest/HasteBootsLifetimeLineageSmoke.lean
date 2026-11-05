module
import all FormalProof4FHE.HasteBoots.CausalExposureLifetime
import all FormalProof4FHE.HasteBoots.NativeParentLineage
import all FormalProof4FHETest.HasteBootsParentStateSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open HasteBootsParentStateSmoke (context seed root shape binding parentFrames parentInput parent_parsed helper child childFrames child_valid quoted committed world later truthful)
namespace HasteBootsLifetimeLineageSmoke
noncomputable section

def descendantFrames : List TranscriptFrame.Frame := NativeChildSeedView.seededFrames context [] [] seed ++
  [⟨6,[],[]⟩,⟨2,NativeTranscript.utf8 "classical child seed",TranscriptFrame.littleEndian 8 64⟩]
def descendantInput := TranscriptFrame.encodeMany descendantFrames
private theorem descendant_valid : ∀ frame ∈ descendantFrames, TranscriptFrame.Valid frame := by
  intro frame member
  rcases List.mem_append.mp member with header | tail
  · exact NativeChildSeedView.seededFrames_valid context [] [] seed (by decide) (by decide) frame header
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at tail
    rcases tail with rfl | rfl <;> constructor <;> decide +kernel
private theorem descendant_parsed : NativeParentInputView.parseParent descendantInput = some descendantFrames :=
  NativeParentInputView.parseParent_complete (NativeChildSeedView.seededFrames context [] [] seed) [] [] descendant_valid
private theorem descendant_quote : NativeChildSeedView.quote descendantInput = some (InputIndexedOracle.block world parentInput 0 64) :=
  NativeChildSeedView.quote_complete context [] [] seed _ descendant_valid

def ancestryLog : List NativeTranscript.Observation := [.start parentInput]++[.start descendantInput]
private theorem knownParent : NativeParentLineage.Known world [.start parentInput] parentInput context :=
  NativeParentLineage.Known.direct [] (.start parentInput) parentFrames parent_parsed context helper
private theorem knownDescendant : NativeParentLineage.Known world ancestryLog descendantInput context :=
  NativeParentLineage.Known.inherit [.start parentInput] (.start descendantInput) descendantFrames descendant_parsed
    parentInput context knownParent descendant_quote
private theorem ancestry_truthful : ObservationReplay.Agrees world ancestryLog := by
  intro entry member
  simp only [ancestryLog,List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> trivial

example : NativeParentLedger.helpers descendantInput = [] := by
  rw [NativeParentLedger.helpers,NativeParentLedger.frames,descendantInput,TranscriptFrame.decodeAll_encodeMany _ descendant_valid]
  decide +kernel
example : NativeParentLineage.Known world ancestryLog descendantInput context := knownDescendant
example : ∃ parent ∈ (ancestryLog.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1.parents,
    parent.input = descendantInput ∧ context ∈ parent.helpers := knownDescendant.sound ancestry_truthful
example : NativeParentLineage.Known world (ancestryLog++later) descendantInput context :=
  NativeParentLineage.Known.later ancestryLog later descendantInput context knownDescendant
example (truthfulLater : ObservationReplay.Agrees world (ancestryLog++later)) :
    ∃ parent ∈ ((ancestryLog++later).foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1.parents,
      parent.input = descendantInput ∧ context ∈ parent.helpers :=
  (NativeParentLineage.Known.later ancestryLog later descendantInput context knownDescendant).sound truthfulLater
example : (context,root) ∈ NativeParentLedger.resolve
    (ancestryLog.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
    (ancestryLog.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 child :=
  NativeParentLineage.resolve_known_helper knownDescendant ancestry_truthful child quoted root committed
example :
    let initial := ancestryLog.foldl (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape initial.1.1
      (.read child 0 1 (fun _ => .pure ())) initial.1.2 initial.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest, ⟨context,⟨root,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  NativeParentLineage.known_helper_snapshot _ _ _ knownDescendant ancestry_truthful child quoted root committed 0 1 (by decide) (fun _ => .pure ())

-- The prelude returns the actual local state and retains its earlier child query.
def prelude : OracleProgram.Program ℕ := .read child 0 1 (fun _ => .pure 3)
def past (world : World) := OracleProgram.run prelude world
def step (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 3 then .read [7,9] 63 1 (fun _ => 4) else .done ()

def packet (fuel : ℕ) (world : World) := (CausalExposureLifetime.history past id step fuel world).run
example : ObservationReplay.Replayable (CausalExposureLifetime.history past id step 7) :=
  CausalExposureLifetime.history_replay (OracleProgram.run_replay prelude) id step 7
example : ObservationReplay.Replayable (CausalExposureLifetime.retained past id step 7) :=
  CausalExposureLifetime.retained_replay (OracleProgram.run_replay prelude) id step 7
example (fuel : ℕ) : CausalExposureLifetime.project (CausalExposureLifetime.retained past id step fuel world).run = packet fuel world :=
  CausalExposureLifetime.retained_history past id step fuel world
example : CausalSeedExposure.firstRead step (packet 0 world) = some [7,9] := by decide +kernel
private theorem packet_zero : packet 0 world = (.inl 3,[NativeTranscript.Observation.output child 0 [9]]) := rfl
private theorem packet_done (fuel : ℕ) : (packet (fuel+1) world).1 = .inr () := by
  cases fuel <;> rfl
private theorem risk_zero : CausalSeedExposure.risk step (packet 0 world) = 1/(2 : ENNReal)^512 := by
  have selected : CausalSeedExposure.firstRead step (packet 0 world) = some [7,9] := by decide +kernel
  have count : (NativeChildSeedView.guesses (packet 0 world).2).card = 1 := by
    rw [packet_zero]
    simp [NativeChildSeedView.guesses,NativeChildSeedView.candidate,quoted]
  simp only [CausalSeedExposure.risk,selected,count,Nat.cast_one]
private theorem risk_done (fuel : ℕ) : CausalSeedExposure.risk step (packet (fuel+1) world) = 0 := by
  simp [CausalSeedExposure.risk,CausalSeedExposure.firstRead,CausalSeedExposure.request,packet_done]
example : CausalSeedExposure.risk step (packet 0 world) = 1/(2 : ENNReal)^512 := risk_zero
example (fuel : ℕ) : CausalSeedExposure.risk step (packet (fuel+1) world) = 0 := risk_done fuel
example : CausalExposureLifetime.totalCharge past id step world = 1/(2 : ENNReal)^512 := by
  change (∑' fuel : ℕ, CausalSeedExposure.risk step (packet fuel world)) = _
  have zero (fuel : ℕ) (different : fuel ≠ 0) : CausalSeedExposure.risk step (packet fuel world) = 0 := by
    cases fuel with
    | zero => contradiction
    | succ fuel => exact risk_done fuel
  rw [tsum_eq_single 0 (fun fuel different => zero fuel different)]
  exact risk_zero
example (inherited : Set World) : InputIndexedOracle.law
    (inherited ∪ {world | ∃ fuel, CausalSeedExposure.event step (packet fuel world) world}) ≤
    InputIndexedOracle.law inherited + ∫⁻ world, CausalExposureLifetime.totalCharge past id step world ∂InputIndexedOracle.law :=
  CausalExposureLifetime.lifetime_le_totalCharge (OracleProgram.run_replay prelude) id step inherited
example (inherited : Set World) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      (inherited ∪ {other | ∃ fuel, CausalSeedExposure.event step (packet fuel other) other}) ≤
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}]) inherited +
      ∫⁻ other, CausalExposureLifetime.totalCharge past id step other ∂InputIndexedOracle.law[|{other | (past other).run = (past world).run}] :=
  CausalExposureLifetime.conditional_lifetime_le (OracleProgram.run_replay prelude) id step world inherited
example : Measurable (CausalExposureLifetime.totalCharge past id step) :=
  CausalExposureLifetime.totalCharge_measurable (OracleProgram.run_replay prelude) id step
example : MeasurableSet {world | ∃ fuel, CausalSeedExposure.event step (packet fuel world) world} :=
  CausalExposureLifetime.lifetime_measurable (OracleProgram.run_replay prelude) id step
end
end HasteBootsLifetimeLineageSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.history_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.history_replay

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.lifetime_le

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.totalCharge_lintegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.totalCharge_lintegral

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.lifetime_le_totalCharge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.lifetime_le_totalCharge

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.history_run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.history_run

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.retained_history' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.retained_history

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.retained_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.retained_replay

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.retained_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.retained_event

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.conditional_step_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.conditional_step_event

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.conditional_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.conditional_lifetime_le

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.totalCharge_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.totalCharge_measurable

/-- info: 'FormalProof4FHE.HasteBoots.CausalExposureLifetime.lifetime_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalExposureLifetime.lifetime_measurable

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLineage.record_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLineage.record_context

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLineage.actual_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLineage.actual_context

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLineage.Known.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLineage.Known.sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLineage.resolve_known_helper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLineage.resolve_known_helper

/-- info: 'FormalProof4FHE.HasteBoots.NativeParentLineage.known_helper_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeParentLineage.known_helper_snapshot
