module
import all FormalProof4FHE.HasteBoots.NativeSeedAncestry
import all FormalProof4FHETest.HasteBootsSourceExposureCoverageSmoke
import all FormalProof4FHETest.HasteBootsLifetimeLineageSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp
open HasteBootsParentStateSmoke (context seed root shape)
open HasteBootsSourceExposureCoverageSmoke (parentInput frames parsed binding bindingFrame valid)
open HasteBootsLifetimeLineageSmoke (descendantInput descendantFrames descendant_valid descendant_parsed)
namespace HasteBootsRealizedAncestrySmoke
noncomputable section

def seed17 : Digest := fun _ => 17
def seed23 : Digest := fun _ => 23
def helperRoot : Digest := fun _ => 61
def leafFrames : List TranscriptFrame.Frame := NativeChildSeedView.seededFrames context [1] [] seed17 ++
  [⟨1,NativeLookupEquality.rootsLabel,NativeRootMessage.encode [helperRoot] (by decide)⟩]
def leafInput := TranscriptFrame.encodeMany leafFrames
private theorem leaf_valid : ∀ frame ∈ leafFrames, TranscriptFrame.Valid frame := by
  intro frame member
  rcases List.mem_append.mp member with header | tail
  · exact NativeChildSeedView.seededFrames_valid context [1] [] seed17 (by decide) (by decide) frame header
  · obtain rfl := List.mem_singleton.mp tail
    constructor <;> decide +kernel
private theorem leaf_quote : NativeChildSeedView.quote leafInput = some seed17 :=
  NativeChildSeedView.quote_complete context [1] [] seed17 _ leaf_valid
private theorem descendant_quote : NativeChildSeedView.quote descendantInput = some seed :=
  NativeChildSeedView.quote_complete context [] [] seed _ descendant_valid
private theorem parent_quote : NativeChildSeedView.quote parentInput = none := by
  rw [NativeChildSeedView.quote,NativeParentCoverage.parseParent_decode parentInput frames parsed]
  rfl
private theorem parent_ne_descendant : parentInput ≠ descendantInput := by decide +kernel
private theorem parent_ne_leaf : parentInput ≠ leafInput := by decide +kernel
private theorem descendant_ne_leaf : descendantInput ≠ leafInput := by decide +kernel

def modelWorld : World := fun coordinate => match coordinate with
  | .inl (input,_) => if input = descendantInput then 17 else if input = leafInput then 23 else 9
  | .inr _ => 0
private theorem parent_block : InputIndexedOracle.block modelWorld parentInput 0 64 = seed := by
  funext position
  simp only [InputIndexedOracle.block,InputIndexedOracle.shake,modelWorld,
    ite_eq_right parent_ne_descendant,ite_eq_right parent_ne_leaf]
  rfl
private theorem descendant_block : InputIndexedOracle.block modelWorld descendantInput 0 64 = seed17 := by
  funext position
  simp only [InputIndexedOracle.block,InputIndexedOracle.shake,modelWorld]
  rfl
private theorem leaf_block : InputIndexedOracle.block modelWorld leafInput 0 64 = seed23 := by
  funext position
  simp only [InputIndexedOracle.block,InputIndexedOracle.shake,modelWorld,
    ite_eq_right descendant_ne_leaf.symm]
  rfl
attribute [irreducible] modelWorld

private theorem seed17_ne_seed : seed17 ≠ seed := by
  intro equal
  exact (by decide : (17 : Byte) ≠ 9) (congrFun equal 0)

def step (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 0 then .read parentInput 0 64 (fun _ => 1) else
  if state = 1 then .read descendantInput 0 1 (fun _ => 2) else
  if state = 2 then .hash [255] (fun _ => 3) else
  if state = 3 then .read leafInput 64 1 (fun _ => 4) else .done ()
def packet (fuel : ℕ) := (OracleProgram.run (OracleMachine.take step fuel 0) modelWorld).run
def log := (packet 4).2
def parentValues := InputIndexedOracle.bytes modelWorld parentInput 0 64
def descendantValues := InputIndexedOracle.bytes modelWorld descendantInput 0 1
def leafValues := InputIndexedOracle.bytes modelWorld leafInput 64 1
private theorem log_eq : log = [.output parentInput 0 parentValues,.output descendantInput 0 descendantValues,
    .hash [255] (List.ofFn (InputIndexedOracle.sha512 modelWorld [255])),.output leafInput 64 leafValues] := rfl
private theorem packet1 : packet 1 = (.inl 1,[.output parentInput 0 parentValues]) := rfl
private theorem value2 : (packet 2).1 = .inl 2 := rfl
private theorem value3 : (packet 3).1 = .inl 3 := rfl
private theorem done_value (extra : ℕ) : (packet (extra+4)).1 = .inr () := by
  cases extra <;> rfl
private theorem fresh_descendant : OracleFirstExposure.locate [.output parentInput 0 parentValues]
    (OracleFirstExposure.seedCoordinates descendantInput) = none := by
  apply (OracleFirstExposure.locate_none _ _).mpr
  simp only [ObservationReplay.footprint,List.toFinset_cons,List.toFinset_nil,Finset.biUnion_insert,
    Finset.biUnion_empty,Finset.union_empty]
  apply Finset.disjoint_left.mpr
  intro coordinate observed relevant
  obtain ⟨index,_,rfl⟩ := Finset.mem_image.mp observed
  obtain ⟨position,_,equal⟩ := Finset.mem_image.mp relevant
  have same : descendantInput = parentInput ∧ position.val = 0+index := by
    simpa [CachedOracleResponse.shakeCoordinates] using equal
  exact parent_ne_descendant same.1.symm
private theorem selected0 : CausalSeedExposure.firstRead step (packet 0) = some parentInput := rfl
private theorem selected1 : CausalSeedExposure.firstRead step (packet 1) = some descendantInput := by
  rw [packet1]
  simp [CausalSeedExposure.firstRead,CausalSeedExposure.request,step,fresh_descendant]
private theorem selected2 : CausalSeedExposure.firstRead step (packet 2) = none := by
  simp [CausalSeedExposure.firstRead,CausalSeedExposure.request,value2,step]
private theorem selected3 : CausalSeedExposure.firstRead step (packet 3) = none := by
  simp [CausalSeedExposure.firstRead,CausalSeedExposure.request,value3,step]
private theorem selected_done (extra : ℕ) : CausalSeedExposure.firstRead step (packet (extra+4)) = none := by
  simp [CausalSeedExposure.firstRead,CausalSeedExposure.request,done_value]
private theorem guesses0 : NativeChildSeedView.guesses (packet 0).2 = ∅ := rfl
private theorem guesses1 : NativeChildSeedView.guesses (packet 1).2 = ∅ := by
  rw [packet1]
  simp [NativeChildSeedView.guesses,NativeChildSeedView.candidate,parent_quote]
attribute [local irreducible] CausalSeedExposure.firstRead

private theorem no_prior {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (world : World) (empty : NativeChildSeedView.guesses history.2 = ∅) :
    ¬CausalSeedExposure.event step history world := by
  cases selected : CausalSeedExposure.firstRead step history with
  | none => simp only [CausalSeedExposure.event,selected,not_false_eq_true]
  | some input =>
    rw [CausalSeedExposure.event,selected,empty]
    exact Finset.notMem_empty _
private theorem no_pending {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (world : World) (input : Input) (seed : Digest)
    (selected : CausalSeedExposure.firstRead step history = some input) (quoted : NativeChildSeedView.quote input = some seed)
    (different : InputIndexedOracle.block world input 0 64 ≠ seed) : ¬PendingSeedQuote.event step history world := by
  simpa only [PendingSeedQuote.event,selected,quoted] using different
private theorem safe : ¬SeedQuoteOrder.Bad step 0 modelWorld := by
  rintro ⟨time,bad⟩
  change CausalSeedExposure.event step (packet time) modelWorld ∨ PendingSeedQuote.event step (packet time) modelWorld at bad
  by_cases small : time < 4
  · interval_cases time
    · rcases bad with old | pending
      · exact no_prior step (packet 0) modelWorld guesses0 old
      · simp only [PendingSeedQuote.event,selected0,parent_quote] at pending
    · rcases bad with old | pending
      · exact no_prior step (packet 1) modelWorld guesses1 old
      · apply no_pending step (packet 1) modelWorld descendantInput seed selected1 descendant_quote _ pending
        rw [descendant_block]
        exact seed17_ne_seed
    · rcases bad with old | pending
      · simp only [CausalSeedExposure.event,selected2] at old
      · simp only [PendingSeedQuote.event,selected2] at pending
    · rcases bad with old | pending
      · simp only [CausalSeedExposure.event,selected3] at old
      · simp only [PendingSeedQuote.event,selected3] at pending
  · have size : time = (time-4)+4 := by omega
    rw [size] at bad
    rcases bad with old | pending
    · simp only [CausalSeedExposure.event,selected_done] at old
    · simp only [PendingSeedQuote.event,selected_done] at pending

private theorem parent_nonempty : parentValues ≠ [] := by
  apply List.ne_nil_of_length_pos
  change 0 < (InputIndexedOracle.bytes modelWorld parentInput 0 64).length
  rw [InputIndexedOracle.bytes_length]
  decide
private theorem descendant_nonempty : descendantValues ≠ [] := by
  apply List.ne_nil_of_length_pos
  change 0 < (InputIndexedOracle.bytes modelWorld descendantInput 0 1).length
  rw [InputIndexedOracle.bytes_length]
  decide
private theorem leaf_nonempty : leafValues ≠ [] := by
  apply List.ne_nil_of_length_pos
  change 0 < (InputIndexedOracle.bytes modelWorld leafInput 64 1).length
  rw [InputIndexedOracle.bytes_length]
  decide
private theorem descendant_quote_actual : NativeChildSeedView.quote descendantInput = some (InputIndexedOracle.block modelWorld parentInput 0 64) := by
  rw [parent_block]
  exact descendant_quote
private theorem leaf_quote_actual : NativeChildSeedView.quote leafInput = some (InputIndexedOracle.block modelWorld descendantInput 0 64) := by
  rw [descendant_block]
  exact leaf_quote
private theorem realized (fact : NativeSeedAncestry.Fact) (direct : NativeSeedAncestry.Direct parentInput fact) :
    ∃ index, NativeSeedAncestry.Realized modelWorld log descendantInput index fact := by
  obtain ⟨index,parent⟩ := NativeSeedAncestry.direct_of_read modelWorld log parentInput frames parsed fact direct
    0 parentValues parent_nonempty (by decide) (by rw [log_eq]; exact List.mem_cons_self)
  exact NativeSeedAncestry.inherit_of_read parent descendantInput descendantFrames descendant_parsed descendant_quote_actual
    0 descendantValues descendant_nonempty (by decide) (by rw [log_eq]; apply List.mem_cons_of_mem; exact List.mem_cons_self)
private theorem direct_helper : NativeSeedAncestry.Direct parentInput (.helper context) :=
  NativeParentCoverage.binding_helper parentInput frames parsed binding (by simp [frames,bindingFrame])
private theorem helper_member : (context,helperRoot) ∈ NativeSeedAncestry.Keys leafInput (.helper context) := by
  apply List.mem_map.mpr
  refine ⟨helperRoot,?_,rfl⟩
  exact NativeParentLedger.roots_frame leafInput leafFrames (TranscriptFrame.decodeAll_encodeMany leafFrames leaf_valid)
    _ (List.mem_append_right _ (by simp)) [helperRoot] (NativeParentInputView.helperRoots_complete [helperRoot] (by decide)) helperRoot (by simp)
private theorem positioned : log[3]? = some (.output leafInput 64 leafValues) := by
  rw [log_eq]
  rfl

example : ¬SeedQuoteOrder.Bad step 0 modelWorld := safe
example : InputIndexedOracle.block modelWorld parentInput 0 64 ≠ InputIndexedOracle.block modelWorld descendantInput 0 64 := by
  rw [parent_block,descendant_block]
  exact seed17_ne_seed.symm
example : InputIndexedOracle.block modelWorld leafInput 0 64 = seed23 := leaf_block
example : ∃ index, NativeSeedAncestry.Realized modelWorld log descendantInput index (.helper context) := realized _ direct_helper
example : ∃ index, NativeSeedAncestry.Realized modelWorld log descendantInput index (.source (context,root)) :=
  realized _ (HasteBootsSourceExposureCoverageSmoke.direct_source _ (by simp [HasteBootsSourceExposureCoverageSmoke.sources]))
example : NativeSeedAncestry.Known modelWorld (log.take 3) descendantInput (.helper context) := by
  obtain ⟨index,ancestry⟩ := realized _ direct_helper
  exact ancestry.before_quote step 4 0 modelWorld safe 3 (.output leafInput 64 leafValues) positioned
    (by simp only [NativeChildSeedView.candidate,ite_eq_right leaf_nonempty,leaf_quote_actual])
example : (context,helperRoot) ∈ NativeParentLedger.resolve
    ((log.take 3).foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
    ((log.take 3).foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 leafInput := by
  obtain ⟨index,ancestry⟩ := realized _ direct_helper
  exact ancestry.before_read_resolves step 4 0 modelWorld safe 3 leafInput 64 leafValues leaf_nonempty positioned leaf_quote_actual
    (context,helperRoot) helper_member
example :
    let state := (log.take 3).foldl (NativeParentStateExecution.record NativeGoldColumnAuthentication.encoding context shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute NativeGoldColumnAuthentication.encoding context shape state.1.1
      (.read leafInput 64 1 (fun _ => .pure ())) state.1.2 state.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest, ⟨context,⟨helperRoot,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  obtain ⟨index,ancestry⟩ := realized _ direct_helper
  exact ancestry.before_read_snapshot NativeGoldColumnAuthentication.encoding context shape step 4 0 modelWorld safe
    3 leafInput 64 leafValues leaf_nonempty positioned leaf_quote_actual (context,helperRoot) helper_member 1 (by decide) (fun _ => .pure ())
end
end HasteBootsRealizedAncestrySmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_direct

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_inherit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_inherit

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.first

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.hit_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.hit_input

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.chronological' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.chronological

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.before_quote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.before_quote

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.known_resolves

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.before_read_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.before_read_resolves

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.before_read_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.Realized.before_read_snapshot

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.first_of_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.first_of_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.direct_of_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.direct_of_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeSeedAncestry.inherit_of_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSeedAncestry.inherit_of_read
