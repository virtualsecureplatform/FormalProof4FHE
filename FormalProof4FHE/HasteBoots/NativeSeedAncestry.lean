module

public import FormalProof4FHE.HasteBoots.SeedQuoteOrder
public import FormalProof4FHE.HasteBoots.NativeSourceLineage
public import FormalProof4FHE.HasteBoots.NativeParentLineage
@[expose] public section

/-! Actual producer exposures and semantic source/helper ancestry do not
assume chronological order. Outside the prior/pending quote-risk ledger,
chronological metadata and retained pre-read snapshots are derived for the
same whole-machine history. Native accepted runs must establish the semantic
certificates. Availability, receipt order, partial-seed arithmetic losses and
physical attacker-work coupling remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeSeedAncestry
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeTranscript (Observation)
open NativeParentCoverage (observationInput)
open OracleSpec OracleComp
noncomputable section

inductive Fact where
  | source (key : Source)
  | helper (context : Digest)

def Direct (input : Input) : Fact → Prop
  | .source key => key ∈ NativeParentLedger.direct input
  | .helper context => context ∈ NativeParentLedger.helpers input

def Known (world : World) (log : List Observation) (input : Input) : Fact → Prop
  | .source key => NativeSourceLineage.Known world log input key
  | .helper context => NativeParentLineage.Known world log input context

theorem known_direct (world : World) (before : List Observation) (entry : Observation) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames)
    (fact : Fact) (direct : Direct (observationInput entry) fact) :
    Known world (before++[entry]) (observationInput entry) fact := by
  cases fact with
  | source key => exact NativeSourceLineage.Known.direct before entry frames parsed key direct
  | helper context => exact NativeParentLineage.Known.direct before entry frames parsed context direct

theorem known_inherit (world : World) (before : List Observation) (entry : Observation) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent (observationInput entry) = some frames) (parent : Input) (fact : Fact)
    (known : Known world before parent fact)
    (quoted : NativeChildSeedView.quote (observationInput entry) = some (InputIndexedOracle.block world parent 0 64)) :
    Known world (before++[entry]) (observationInput entry) fact := by
  cases fact with
  | source key => exact NativeSourceLineage.Known.inherit before entry frames parsed parent key known quoted
  | helper context => exact NativeParentLineage.Known.inherit before entry frames parsed parent context known quoted

theorem known_prefix (world : World) (before later : List Observation) (input : Input) (fact : Fact)
    (known : Known world before input fact) (ordered : before.IsPrefix later) : Known world later input fact := by
  obtain ⟨suffix,rfl⟩ := ordered
  cases fact with
  | source key => exact NativeSourceLineage.Known.later before suffix input key known
  | helper context => exact NativeParentLineage.Known.later before suffix input context known

/-- Producer metadata and actual exposure positions, without an assumed chronological parent order. -/
inductive Realized (world : World) (log : List Observation) : Input → ℕ → Fact → Prop
  | direct (input : Input) (index : ℕ) (frames : List TranscriptFrame.Frame)
      (parsed : NativeParentInputView.parseParent input = some frames) (fact : Fact) (direct : Direct input fact)
      (first : OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates input) = some index) :
      Realized world log input index fact
  | inherit (input : Input) (index : ℕ) (frames : List TranscriptFrame.Frame)
      (parsed : NativeParentInputView.parseParent input = some frames) (parent : Input) (parentIndex : ℕ) (fact : Fact)
      (previous : Realized world log parent parentIndex fact)
      (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
      (first : OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates input) = some index) :
      Realized world log input index fact

theorem Realized.first {world : World} {log : List Observation} {input : Input} {index : ℕ} {fact : Fact}
    (realized : Realized world log input index fact) :
    OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates input) = some index := by
  cases realized <;> assumption

theorem hit_input (entry : Observation) (input : Input)
    (hit : ¬Disjoint (ObservationReplay.coordinates entry) (OracleFirstExposure.seedCoordinates input)) :
    observationInput entry = input := by
  cases entry with
  | start key => simp [ObservationReplay.coordinates] at hit
  | hash key digest =>
    exfalso
    apply hit
    apply Finset.disjoint_left.mpr
    intro coordinate observed relevant
    obtain ⟨index,_,rfl⟩ := Finset.mem_image.mp observed
    obtain ⟨position,_,equal⟩ := Finset.mem_image.mp relevant
    cases equal
  | output key offset values =>
    obtain ⟨coordinate,observed,relevant⟩ := Finset.not_disjoint_iff.mp hit
    obtain ⟨index,_,rfl⟩ := Finset.mem_image.mp observed
    obtain ⟨position,_,equal⟩ := Finset.mem_image.mp relevant
    have same : input = key ∧ position.val = offset+index := by simpa [CachedOracleResponse.shakeCoordinates] using equal
    exact same.1.symm

/-- The risk ledger proves chronology; it is not a premise of the realization certificate. -/
theorem Realized.chronological {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (safe : ¬SeedQuoteOrder.Bad step initial world) {input : Input} {index : ℕ} {fact : Fact}
    (realized : Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 input index fact) :
    Known world ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take (index+1)) input fact := by
  induction realized with
  | direct input index frames parsed fact direct first =>
    obtain ⟨before,entry,after,split,length,_,hit⟩ := (OracleFirstExposure.locate_some _ _ index).mp first
    have same := hit_input entry input hit
    have known := known_direct world before entry frames (by rw [same]; exact parsed) fact (by rw [same]; exact direct)
    rw [same] at known
    have cut : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take (index+1) = before++[entry] := by
      rw [split,← length]
      simp [List.take_append]
    rw [cut]
    exact known
  | inherit input index frames parsed parent parentIndex fact previous quoted first ih =>
    have order : parentIndex < index := by
      by_contra notEarlier
      exact safe (SeedQuoteOrder.early_edge_bad step fuel initial world input parent index parentIndex
        first previous.first quoted (by omega))
    have known := known_prefix world _ _ parent fact ih (List.take_prefix_take_left (by omega : parentIndex+1 ≤ index))
    obtain ⟨before,entry,after,split,length,_,hit⟩ := (OracleFirstExposure.locate_some _ _ index).mp first
    have beforeEq : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take index = before := by
      rw [split,← length,List.take_left]
    rw [beforeEq] at known
    have same := hit_input entry input hit
    have inherited := known_inherit world before entry frames (by rw [same]; exact parsed) parent fact known
      (by rw [same]; exact quoted)
    rw [same] at inherited
    have cut : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take (index+1) = before++[entry] := by
      rw [split,← length]
      simp [List.take_append]
    rw [cut]
    exact inherited

/-- Every source/helper producer fact is available before any later raw observation quoting its seed. -/
theorem Realized.before_quote {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (safe : ¬SeedQuoteOrder.Bad step initial world) {input : Input} {index : ℕ} {fact : Fact}
    (realized : Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 input index fact)
    (position : ℕ) (entry : Observation)
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some entry)
    (quoted : NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)) :
    Known world ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position) input fact := by
  have earlier := SeedQuoteOrder.observation_order step fuel initial world safe input index position entry realized.first positioned quoted
  exact known_prefix world _ _ input fact (realized.chronological step fuel initial world safe)
    (List.take_prefix_take_left (by omega))
def Keys (input : Input) : Fact → List Source
  | .source key => [key]
  | .helper context => (NativeParentLedger.roots input).map (context,·)

theorem known_resolves (world : World) (log : List Observation) (parent : Input) (fact : Fact)
    (known : Known world log parent fact) (truthful : ObservationReplay.Agrees world log)
    (input : Input) (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (key : Source) (member : key ∈ Keys input fact) :
    key ∈ NativeParentLedger.resolve
      (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
      (log.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 input := by
  cases fact with
  | source source =>
    have same : key = source := List.mem_singleton.mp member
    subst key
    exact NativeSourceLineage.resolve_known_source known truthful input quoted
  | helper context =>
    obtain ⟨root,present,rfl⟩ := List.mem_map.mp member
    exact NativeParentLineage.resolve_known_helper known truthful input quoted root present

theorem Realized.before_read_resolves {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (safe : ¬SeedQuoteOrder.Bad step initial world) {parent : Input} {parentIndex : ℕ} {fact : Fact}
    (realized : Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 parent parentIndex fact)
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (nonempty : values ≠ [])
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some (.output input offset values))
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (key : Source) (member : key ∈ Keys input fact) :
    let before := (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position
    key ∈ NativeParentLedger.resolve
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).1
      (before.foldl NativeParentHistory.record (NativeParentLedger.empty,NativeShakeCache.empty)).2 input := by
  have candidate : NativeChildSeedView.candidate (.output input offset values) =
      some (InputIndexedOracle.block world parent 0 64) := by
    simp only [NativeChildSeedView.candidate,ite_eq_right nonempty,quoted]
  have known := realized.before_quote step fuel initial world safe position _ positioned candidate
  have truthful : ObservationReplay.Agrees world ((OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position) := by
    intro entry present
    exact (OracleProgram.run_replay _).truthful world entry ((List.take_sublist _ _).subset present)
  exact known_resolves world _ parent fact known truthful input quoted key member

/-- Actual pre-read snapshots follow from realized ancestry and the bounded seed-order exceptions. -/
theorem Realized.before_read_snapshot {Payload S A B : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (safe : ¬SeedQuoteOrder.Bad step initial world) {parent : Input} {parentIndex : ℕ} {fact : Fact}
    (realized : Realized world (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 parent parentIndex fact)
    (position : ℕ) (input : Input) (offset : ℕ) (values : Input) (nonempty : values ≠ [])
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[position]? = some (.output input offset values))
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (key : Source) (member : key ∈ Keys input fact) (count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program B) :
    let before := (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position
    let state := before.foldl (NativeParentStateExecution.record enc dummy shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    ∀ result ∈ support (NativeParentRootFreeze.execute enc dummy shape state.1.1
        (.read input offset count next) state.1.2 state.2),
      ∃ hashes : MerkleTreeExtractor.QueryLog Input Digest, ⟨key.1,⟨key.2,hashes⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  let before := (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2.take position
  let state := before.foldl (NativeParentStateExecution.record enc dummy shape)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
  dsimp only
  intro result possible
  apply NativeParentStateExecution.resolved_snapshot enc dummy shape state.1.1 input offset count next state.1.2 state.2
    (NativeParentStateExecution.fold_covered enc dummy shape _ _ (NativeParentStateExecution.empty_covered shape))
    positive key _ result possible
  have resolved := realized.before_read_resolves step fuel initial world safe position input offset values nonempty positioned quoted key member
  simpa only [state,NativeParentStateExecution.fold_parent] using resolved

theorem first_of_read (log : List Observation) (input : Input) (offset : ℕ) (values : Input)
    (nonempty : values ≠ []) (small : offset < 64) (present : Observation.output input offset values ∈ log) :
    ∃ index, OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates input) = some index := by
  have member : (.inl (input,offset) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.footprint log := by
    apply Finset.mem_biUnion.mpr
    refine ⟨.output input offset values,List.mem_toFinset.mpr present,?_⟩
    exact Finset.mem_image.mpr ⟨0,by simpa only [Finset.mem_range,List.length_pos_iff] using nonempty,by simp⟩
  have relevant : (.inl (input,offset) : InputIndexedOracle.Coordinate) ∈ OracleFirstExposure.seedCoordinates input := by
    exact Finset.mem_image.mpr ⟨⟨offset,small⟩,Finset.mem_univ _,by simp [CachedOracleResponse.shakeCoordinates]⟩
  cases found : OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates input) with
  | some index => exact ⟨index,rfl⟩
  | none => exact False.elim (Finset.disjoint_left.mp ((OracleFirstExposure.locate_none _ _).mp found) member relevant)

theorem direct_of_read (world : World) (log : List Observation) (input : Input) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent input = some frames) (fact : Fact) (direct : Direct input fact)
    (offset : ℕ) (values : Input) (nonempty : values ≠ []) (small : offset < 64)
    (present : Observation.output input offset values ∈ log) : ∃ index, Realized world log input index fact := by
  obtain ⟨index,first⟩ := first_of_read log input offset values nonempty small present
  exact ⟨index,Realized.direct input index frames parsed fact direct first⟩

theorem inherit_of_read {world : World} {log : List Observation} {parent : Input} {parentIndex : ℕ} {fact : Fact}
    (previous : Realized world log parent parentIndex fact) (input : Input) (frames : List TranscriptFrame.Frame)
    (parsed : NativeParentInputView.parseParent input = some frames)
    (quoted : NativeChildSeedView.quote input = some (InputIndexedOracle.block world parent 0 64))
    (offset : ℕ) (values : Input) (nonempty : values ≠ []) (small : offset < 64)
    (present : Observation.output input offset values ∈ log) : ∃ index, Realized world log input index fact := by
  obtain ⟨index,first⟩ := first_of_read log input offset values nonempty small present
  exact ⟨index,Realized.inherit input index frames parsed parent parentIndex fact previous quoted first⟩

end
end FormalProof4FHE.HasteBoots.NativeSeedAncestry
