module

public import FormalProof4FHE.HasteBoots.CausalExposureLifetime
@[expose] public section

/-! The first logical seed hit in an actual machine log selects the causally
pending raw read. Earlier matching quotes therefore enter the existing
lifetime risk event. No future-selected-input guessing bound is postulated;
partial-seed and receipt exceptions and attacker-work coupling remain open. -/
namespace FormalProof4FHE.HasteBoots.CausalExposureCoverage
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation Execution)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

theorem read_hits (world : World) (input target : Input) (offset count : ℕ)
    (hit : ¬Disjoint (ObservationReplay.coordinates (.output input offset (InputIndexedOracle.bytes world input offset count)))
      (OracleFirstExposure.seedCoordinates target)) : input = target ∧ offset < 64 ∧ 0 < count := by
  obtain ⟨coordinate,observed,relevant⟩ := Finset.not_disjoint_iff.mp hit
  obtain ⟨index,bounded,rfl⟩ := Finset.mem_image.mp observed
  obtain ⟨position,_,equal⟩ := Finset.mem_image.mp relevant
  have same : target = input ∧ position.val = offset+index := by
    simpa [CachedOracleResponse.shakeCoordinates] using equal
  have range : index < count := by
    simpa [InputIndexedOracle.bytes_length] using bounded
  exact ⟨same.1.symm,by omega,by omega⟩

theorem take_zero_log {S A : Type} (step : S → OracleMachine.Command S A) (state : S) (world : World) :
    (OracleProgram.run (OracleMachine.take step 0 state) world).run.2 = [] := by
  cases selected : step state <;> rw [OracleMachine.take,selected] <;> rfl

theorem firstRead_of_next_hit {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List Observation) (world : World) (input : Input)
    (fresh : OracleFirstExposure.locate history.2 (OracleFirstExposure.seedCoordinates input) = none)
    (hit : OracleFirstExposure.locate
      (OracleProgram.run (OracleMachine.resume step 1 history.1) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some 0) :
    CausalSeedExposure.firstRead step history = some input := by
  rcases history with ⟨current,log⟩
  cases current with
  | inr value =>
    change OracleFirstExposure.locate [] _ = some 0 at hit
    cases hit
  | inl state =>
    cases selected : step state with
    | done value =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change OracleFirstExposure.locate [] _ = some 0 at hit
      cases hit
    | start key next =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change OracleFirstExposure.locate (.start key :: (OracleProgram.run (OracleMachine.take step 0 next) world).run.2) _ = _ at hit
      simp [take_zero_log,OracleFirstExposure.locate,ObservationReplay.coordinates] at hit
    | hash key next =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change OracleFirstExposure.locate (.hash key (List.ofFn (InputIndexedOracle.sha512 world key)) ::
        (OracleProgram.run (OracleMachine.take step 0 (next (InputIndexedOracle.sha512 world key))) world).run.2) _ = _ at hit
      have apart : Disjoint (ObservationReplay.coordinates (.hash key (List.ofFn (InputIndexedOracle.sha512 world key))))
          (OracleFirstExposure.seedCoordinates input) := by
        apply Finset.disjoint_left.mpr
        intro coordinate observed relevant
        obtain ⟨index,_,rfl⟩ := Finset.mem_image.mp observed
        obtain ⟨position,_,equal⟩ := Finset.mem_image.mp relevant
        cases equal
      rw [take_zero_log,OracleFirstExposure.locate,ite_eq_left apart] at hit
      cases hit
    | read key offset count next =>
      rw [OracleMachine.resume,OracleMachine.take,selected] at hit
      change OracleFirstExposure.locate (.output key offset (InputIndexedOracle.bytes world key offset count) ::
        (OracleProgram.run (OracleMachine.take step 0 (next (InputIndexedOracle.bytes world key offset count))) world).run.2) _ = _ at hit
      rw [take_zero_log] at hit
      have intersect : ¬Disjoint (ObservationReplay.coordinates (.output key offset (InputIndexedOracle.bytes world key offset count)))
          (OracleFirstExposure.seedCoordinates input) := by
        by_contra apart
        simp [OracleFirstExposure.locate,apart] at hit
      obtain ⟨rfl,offsetSmall,positive⟩ := read_hits world key input offset count intersect
      simp [CausalSeedExposure.firstRead,CausalSeedExposure.request,selected,positive,offsetSmall,fresh]

theorem locate_take_succ (log : List Observation) (relevant : Finset InputIndexedOracle.Coordinate) (index : ℕ)
    (found : OracleFirstExposure.locate log relevant = some index) :
    OracleFirstExposure.locate (log.take (index+1)) relevant = some index := by
  obtain ⟨before,entry,after,split,length,earlier,hit⟩ := (OracleFirstExposure.locate_some log relevant index).mp found
  apply (OracleFirstExposure.locate_some _ relevant index).mpr
  refine ⟨before,entry,[],?_,length,earlier,hit⟩
  rw [split,← length]
  simp [List.take_append]
theorem selected_at_first_exposure {S A : Type} (step : S → OracleMachine.Command S A)
    (fuel index : ℕ) (initial : S) (world : World) (input : Input)
    (first : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some index) :
    CausalSeedExposure.firstRead step (OracleProgram.run (OracleMachine.take step index initial) world).run = some input := by
  have bounded : index+1 ≤ fuel := by
    have indexLt := OracleFirstExposure.locate_lt _ _ index first
    have lengthLe := OracleMachineExposure.log_length_le step fuel initial world
    omega
  have fresh := (OracleFirstExposure.seed_none _ input).mpr
    (OracleMachineExposure.pre_exposure_fresh step fuel index initial world input first)
  have length : (OracleProgram.run (OracleMachine.take step index initial) world).run.2.length = index := by
    rw [OracleMachineExposure.log_take step index fuel (by omega) initial world,List.length_take]
    have indexLt := OracleFirstExposure.locate_lt _ _ index first
    exact Nat.min_eq_left (by omega)
  have next := locate_take_succ (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2 _ index first
  rw [← OracleMachineExposure.log_take step (index+1) fuel bounded initial world] at next
  rw [OracleMachine.take_resume step index 1 initial,OracleProgram.run_bind,ObservationReplay.run_bind] at next
  change OracleFirstExposure.locate
    ((OracleProgram.run (OracleMachine.take step index initial) world).run.2 ++
      (OracleProgram.run (OracleMachine.resume step 1 (OracleProgram.run (OracleMachine.take step index initial) world).run.1) world).run.2)
    (OracleFirstExposure.seedCoordinates input) = some index at next
  rw [OracleFirstExposure.locate_append,fresh] at next
  obtain ⟨position,found,equal⟩ := Option.map_eq_some_iff.mp next
  have zero : position = 0 := by rw [length] at equal; omega
  rw [zero] at found
  exact firstRead_of_next_hit step _ world input fresh found

/-- Any earlier matching raw child quote is included in the causally selected lifetime event. -/
theorem prior_quote_lifetime {S A : Type} (step : S → OracleMachine.Command S A)
    (fuel index : ℕ) (initial : S) (world : World) (input : Input)
    (first : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some index)
    (entry : Observation) (present : entry ∈ (OracleProgram.run (OracleMachine.take step index initial) world).run.2)
    (quoted : NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)) :
    ∃ time, CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step time initial) world).run world := by
  refine ⟨index,?_⟩
  simp only [CausalSeedExposure.event,selected_at_first_exposure step fuel index initial world input first]
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨entry,present,quoted⟩

/-- An earlier raw quote matches a seed before its first logical exposure in the actual machine log. -/
def SeedPrequery {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) (world : World) : Prop :=
  ∃ fuel index input entry,
    OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some index ∧
    entry ∈ (OracleProgram.run (OracleMachine.take step index initial) world).run.2 ∧
    NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)

theorem seedPrequery_lifetime {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) (world : World)
    (cold : SeedPrequery step initial world) :
    ∃ time, CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step time initial) world).run world := by
  obtain ⟨fuel,index,input,entry,first,present,quoted⟩ := cold
  exact prior_quote_lifetime step fuel index initial world input first entry present quoted

theorem seedPrequery_probability {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) :
    law {world | SeedPrequery step initial world} ≤
      ∫⁻ world, CausalExposureLifetime.totalCharge (fun _ => (pure () : Execution Unit)) (fun _ => initial) step world ∂law := by
  have bound := CausalExposureLifetime.lifetime_le_totalCharge (past := fun _ => (pure () : Execution Unit))
    (ObservationReplay.pure_replay ()) (fun _ => initial) step ∅
  simp only [Set.empty_union,measure_empty,zero_add] at bound
  apply (measure_mono _).trans bound
  intro world cold
  obtain ⟨time,event⟩ := seedPrequery_lifetime step initial world cold
  refine ⟨time,?_⟩
  simpa only [CausalExposureLifetime.history,pure_bind] using event

/-- Prelude-aware witness: a full seed quote precedes the causally pending first seed hit. -/
def SeedPrequeryAfter {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel input entry,
    let history := (CausalExposureLifetime.history past initial step fuel world).run
    OracleFirstExposure.locate history.2 (OracleFirstExposure.seedCoordinates input) = none ∧
    OracleFirstExposure.locate (OracleProgram.run (OracleMachine.resume step 1 history.1) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some 0 ∧
    entry ∈ history.2 ∧ NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)

theorem seedPrequeryAfter_lifetime {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) (cold : SeedPrequeryAfter past initial step world) :
    ∃ time, CausalSeedExposure.event step (CausalExposureLifetime.history past initial step time world).run world := by
  obtain ⟨time,input,entry,fresh,hit,present,quoted⟩ := cold
  refine ⟨time,?_⟩
  simp only [CausalSeedExposure.event,firstRead_of_next_hit step _ world input fresh hit]
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,present,quoted⟩)

theorem conditional_seedPrequeryAfter {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) (inherited : Set World) :
    (law[|{other | (past other).run = (past world).run}])
      (inherited ∪ {other | SeedPrequeryAfter past initial step other}) ≤
    (law[|{other | (past other).run = (past world).run}]) inherited +
      ∫⁻ other, CausalExposureLifetime.totalCharge past initial step other ∂law[|{other | (past other).run = (past world).run}] := by
  apply (measure_mono _).trans (CausalExposureLifetime.conditional_lifetime_le replay initial step world inherited)
  intro other member
  rcases member with old | cold
  · exact Or.inl old
  · exact Or.inr (seedPrequeryAfter_lifetime past initial step other cold)
theorem seedPrequery_iff {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) (world : World) :
    SeedPrequery step initial world ↔ ∃ fuel index input,
      OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
        (OracleFirstExposure.seedCoordinates input) = some index ∧
      CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step index initial) world).run world := by
  constructor
  · rintro ⟨fuel,index,input,entry,first,present,quoted⟩
    refine ⟨fuel,index,input,first,?_⟩
    simp only [CausalSeedExposure.event,selected_at_first_exposure step fuel index initial world input first]
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,present,quoted⟩)
  · rintro ⟨fuel,index,input,first,event⟩
    simp only [CausalSeedExposure.event,selected_at_first_exposure step fuel index initial world input first] at event
    obtain ⟨entry,present,quoted⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp event)
    exact ⟨fuel,index,input,entry,first,present,quoted⟩

theorem seedPrequery_measurable {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) :
    MeasurableSet {world | SeedPrequery step initial world} := by
  have union : {world | SeedPrequery step initial world} = ⋃ fuel : ℕ, ⋃ index : ℕ, ⋃ input : Input,
      {world | OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
        (OracleFirstExposure.seedCoordinates input) = some index} ∩
      {world | CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step index initial) world).run world} := by
    ext world
    simp only [Set.mem_ofPred_eq,seedPrequery_iff,Set.mem_iUnion,Set.mem_inter_iff]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => MeasurableSet.iUnion (fun index => MeasurableSet.iUnion (fun input =>
    (OracleExecutionLaw.event_measurable (OracleProgram.run_replay _) (fun packet =>
      OracleFirstExposure.locate packet.2 (OracleFirstExposure.seedCoordinates input) = some index)).inter
        (CausalSeedExposure.event_measurable step (OracleProgram.run_replay _)))))

theorem seedPrequeryAfter_iff {P S A : Type} (past : World → Execution P) (initial : P → S)
    (step : S → OracleMachine.Command S A) (world : World) :
    SeedPrequeryAfter past initial step world ↔ ∃ fuel input,
      let history := (CausalExposureLifetime.history past initial step fuel world).run
      OracleFirstExposure.locate history.2 (OracleFirstExposure.seedCoordinates input) = none ∧
      OracleFirstExposure.locate (OracleProgram.run (OracleMachine.resume step 1 history.1) world).run.2
        (OracleFirstExposure.seedCoordinates input) = some 0 ∧ CausalSeedExposure.event step history world := by
  constructor
  · rintro ⟨fuel,input,entry,fresh,hit,present,quoted⟩
    refine ⟨fuel,input,fresh,hit,?_⟩
    simp only [CausalSeedExposure.event,firstRead_of_next_hit step _ world input fresh hit]
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,present,quoted⟩)
  · rintro ⟨fuel,input,fresh,hit,event⟩
    simp only [CausalSeedExposure.event,firstRead_of_next_hit step _ world input fresh hit] at event
    obtain ⟨entry,present,quoted⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp event)
    exact ⟨fuel,input,entry,fresh,hit,present,quoted⟩

theorem seedPrequeryAfter_measurable {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) :
    MeasurableSet {world | SeedPrequeryAfter past initial step world} := by
  have union : {world | SeedPrequeryAfter past initial step world} = ⋃ fuel : ℕ, ⋃ input : Input,
      {world | OracleFirstExposure.locate (CausalExposureLifetime.history past initial step fuel world).run.2
        (OracleFirstExposure.seedCoordinates input) = none} ∩
      {world | OracleFirstExposure.locate (OracleProgram.run (OracleMachine.resume step 1
        (CausalExposureLifetime.history past initial step fuel world).run.1) world).run.2
        (OracleFirstExposure.seedCoordinates input) = some 0} ∩
      {world | CausalSeedExposure.event step (CausalExposureLifetime.history past initial step fuel world).run world} := by
    ext world
    simp only [Set.mem_ofPred_eq,seedPrequeryAfter_iff,Set.mem_iUnion,Set.mem_inter_iff,and_assoc]
  rw [union]
  apply MeasurableSet.iUnion
  intro fuel
  apply MeasurableSet.iUnion
  intro input
  have rp := CausalExposureLifetime.history_replay replay initial step fuel
  exact ((OracleExecutionLaw.event_measurable rp (fun packet => OracleFirstExposure.locate packet.2
    (OracleFirstExposure.seedCoordinates input) = none)).inter
    (OracleHistoryCharge.continuation_measurable rp
      (fun history world => OracleProgram.run (OracleMachine.resume step 1 history.1) world)
      (fun _ => OracleProgram.run_replay _) (fun packet => OracleFirstExposure.locate packet.2
        (OracleFirstExposure.seedCoordinates input) = some 0))).inter (CausalSeedExposure.event_measurable step rp)

theorem seedPrequeryAfter_probability {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (step : S → OracleMachine.Command S A) (inherited : Set World) :
    law (inherited ∪ {other | SeedPrequeryAfter past initial step other}) ≤
      law inherited + ∫⁻ other, CausalExposureLifetime.totalCharge past initial step other ∂law := by
  apply (measure_mono _).trans (CausalExposureLifetime.lifetime_le_totalCharge replay initial step inherited)
  intro other member
  rcases member with old | cold
  · exact Or.inl old
  · exact Or.inr (seedPrequeryAfter_lifetime past initial step other cold)

end
end FormalProof4FHE.HasteBoots.CausalExposureCoverage
