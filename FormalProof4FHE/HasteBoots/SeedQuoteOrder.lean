module

public import FormalProof4FHE.HasteBoots.PendingSeedQuote
@[expose] public section

/-! Outside the prior/pending seed-quote risk ledger, every quoted raw
observation follows its seed producer. Finite closed dependency graphs,
including repeated inputs and self-links, imply an actual ledger event.
This gives seed-dependency order, not full native stage admissibility,
receipt entropy or a physical attacker-work bound. -/
namespace FormalProof4FHE.HasteBoots.SeedQuoteOrder
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation Execution)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def Bad {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) (world : World) : Prop :=
  ∃ time, CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step time initial) world).run world ∨
    PendingSeedQuote.event step (OracleProgram.run (OracleMachine.take step time initial) world).run world

/-- A positive seed hit carries exactly the quote in that complete input. -/
theorem hit_candidate (entry : Observation) (input : Input)
    (hit : ¬Disjoint (ObservationReplay.coordinates entry) (OracleFirstExposure.seedCoordinates input)) :
    NativeChildSeedView.candidate entry = NativeChildSeedView.quote input := by
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
    obtain ⟨index,bounded,rfl⟩ := Finset.mem_image.mp observed
    obtain ⟨position,_,equal⟩ := Finset.mem_image.mp relevant
    have same : input = key ∧ position.val = offset+index := by
      simpa [CachedOracleResponse.shakeCoordinates] using equal
    have nonempty : values ≠ [] := by
      intro empty
      simp [empty] at bounded
    rw [← same.1]
    simp only [NativeChildSeedView.candidate,ite_eq_right nonempty]

theorem first_entry_hit (log : List Observation) (relevant : Finset InputIndexedOracle.Coordinate) (index : ℕ)
    (entry : Observation) (first : OracleFirstExposure.locate log relevant = some index) (positioned : log[index]? = some entry) :
    ¬Disjoint (ObservationReplay.coordinates entry) relevant := by
  obtain ⟨before,head,after,split,length,_,hit⟩ := (OracleFirstExposure.locate_some log relevant index).mp first
  rw [split,← length,List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero] at positioned
  exact Option.some.inj positioned ▸ hit

theorem entry_mem_take (log : List Observation) (entry : Observation) (index bound : ℕ)
    (positioned : log[index]? = some entry) (smaller : index < bound) : entry ∈ log.take bound := by
  apply List.mem_iff_getElem?.mpr
  exact ⟨index,by rw [List.getElem?_take_of_lt smaller]; exact positioned⟩

/-- A quoted observation cannot precede or coincide with its parent's first seed exposure outside the risk ledger. -/
theorem early_observation_bad {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (input : Input) (firstIndex index : ℕ) (entry : Observation)
    (first : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some firstIndex)
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[index]? = some entry)
    (quoted : NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64))
    (early : index ≤ firstIndex) : Bad step initial world := by
  have selected := CausalExposureCoverage.selected_at_first_exposure step fuel firstIndex initial world input first
  rcases Nat.lt_or_eq_of_le early with smaller | same
  · have present := entry_mem_take _ entry index firstIndex positioned smaller
    have bounded : firstIndex ≤ fuel := by
      have lt := OracleFirstExposure.locate_lt _ _ firstIndex first
      have length := OracleMachineExposure.log_length_le step fuel initial world
      omega
    rw [← OracleMachineExposure.log_take step firstIndex fuel bounded initial world] at present
    refine ⟨firstIndex,Or.inl ?_⟩
    simp only [CausalSeedExposure.event,selected]
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨entry,present,quoted⟩)
  · have hit := first_entry_hit _ _ firstIndex entry first (by simpa only [same] using positioned)
    have selfQuote := (hit_candidate entry input hit).symm.trans quoted
    refine ⟨firstIndex,Or.inr ?_⟩
    simp only [PendingSeedQuote.event,selected,selfQuote]

theorem observation_order {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (safe : ¬Bad step initial world) (input : Input) (firstIndex index : ℕ) (entry : Observation)
    (first : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates input) = some firstIndex)
    (positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[index]? = some entry)
    (quoted : NativeChildSeedView.candidate entry = some (InputIndexedOracle.block world input 0 64)) : firstIndex < index := by
  by_contra notLater
  exact safe (early_observation_bad step fuel initial world input firstIndex index entry first positioned quoted (by omega))

theorem early_edge_bad {S A : Type} (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (child parent : Input) (childIndex parentIndex : ℕ)
    (childFirst : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates child) = some childIndex)
    (parentFirst : OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates parent) = some parentIndex)
    (quoted : NativeChildSeedView.quote child = some (InputIndexedOracle.block world parent 0 64))
    (early : childIndex ≤ parentIndex) : Bad step initial world := by
  obtain ⟨before,entry,after,split,length,_,hit⟩ := (OracleFirstExposure.locate_some _ _ childIndex).mp childFirst
  have positioned : (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2[childIndex]? = some entry := by
    rw [split,← length,List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero]
  exact early_observation_bad step fuel initial world parent parentIndex childIndex entry parentFirst positioned
    ((hit_candidate entry child hit).trans quoted) early

/-- Every finite closed seed-quote dependency graph has an actual prior/pending exposure exception. -/
theorem closed_graph_bad {V S A : Type} [Fintype V] [Nonempty V]
    (step : S → OracleMachine.Command S A) (fuel : ℕ) (initial : S) (world : World)
    (input : V → Input) (parent : V → V) (firstIndex : V → ℕ)
    (first : ∀ vertex, OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step fuel initial) world).run.2
      (OracleFirstExposure.seedCoordinates (input vertex)) = some (firstIndex vertex))
    (quoted : ∀ vertex, NativeChildSeedView.quote (input vertex) =
      some (InputIndexedOracle.block world (input (parent vertex)) 0 64)) : Bad step initial world := by
  obtain ⟨vertex,_,minimal⟩ := Finset.exists_min_image Finset.univ firstIndex Finset.univ_nonempty
  exact early_edge_bad step fuel initial world (input vertex) (input (parent vertex)) (firstIndex vertex) (firstIndex (parent vertex))
    (first vertex) (first (parent vertex)) (quoted vertex) (minimal (parent vertex) (Finset.mem_univ _))
theorem bad_measurable {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) :
    MeasurableSet {world | Bad step initial world} := by
  have union : {world | Bad step initial world} = ⋃ time : ℕ,
      {world | CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step time initial) world).run world} ∪
      {world | PendingSeedQuote.event step (OracleProgram.run (OracleMachine.take step time initial) world).run world} := by
    ext world
    simp [Bad]
  rw [union]
  exact MeasurableSet.iUnion (fun time => (CausalSeedExposure.event_measurable step (OracleProgram.run_replay _)).union
    (PendingSeedQuote.event_measurable step (OracleProgram.run_replay _)))

theorem bad_probability {S A : Type} (step : S → OracleMachine.Command S A) (initial : S) :
    law {world | Bad step initial world} ≤
      (∫⁻ world, CausalExposureLifetime.totalCharge (fun _ => (pure () : Execution Unit)) (fun _ => initial) step world ∂law) +
      ∫⁻ world, PendingSeedQuote.totalCharge (fun _ => (pure () : Execution Unit)) (fun _ => initial) step world ∂law := by
  have bound := PendingSeedQuote.combined_lifetime_le (past := fun _ => (pure () : Execution Unit))
    (ObservationReplay.pure_replay ()) (fun _ => initial) step ∅
  simpa only [Set.empty_union,measure_empty,zero_add,CausalExposureLifetime.history,pure_bind,Bad] using bound
end
end FormalProof4FHE.HasteBoots.SeedQuoteOrder
