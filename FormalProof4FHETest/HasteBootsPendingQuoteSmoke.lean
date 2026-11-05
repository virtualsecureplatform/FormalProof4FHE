module
import all FormalProof4FHE.HasteBoots.SeedQuoteOrder
import all FormalProof4FHETest.HasteBootsParentStateSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open HasteBootsParentStateSmoke (child seed quoted world)
namespace HasteBootsPendingQuoteSmoke
noncomputable section

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read child 0 1 (fun _ => ())
def packet (fuel : ℕ) := (OracleProgram.run (OracleMachine.take step fuel ()) world).run
private theorem value (fuel : ℕ) : (packet fuel).1 = .inl () := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih
private theorem selected : CausalSeedExposure.firstRead step (packet 0) = some child := rfl
private theorem hit : ¬Disjoint (ObservationReplay.coordinates (.output child 0 [9])) (OracleFirstExposure.seedCoordinates child) := by
  apply Finset.not_disjoint_iff.mpr
  refine ⟨.inl (child,0),?_,?_⟩
  · exact Finset.mem_image.mpr ⟨0,by simp,by simp⟩
  · exact Finset.mem_image.mpr ⟨⟨0,by decide⟩,Finset.mem_univ _,by simp [CachedOracleResponse.shakeCoordinates]⟩
private theorem first : OracleFirstExposure.locate (packet 1).2 (OracleFirstExposure.seedCoordinates child) = some 0 := by
  exact (OracleFirstExposure.locate_some _ _ 0).mpr ⟨[],.output child 0 [9],[],rfl,rfl,by simp [ObservationReplay.footprint],hit⟩
private theorem located (fuel : ℕ) : OracleFirstExposure.locate (packet (fuel+1)).2 (OracleFirstExposure.seedCoordinates child) = some 0 := by
  obtain ⟨suffix,append⟩ := OracleMachine.log_prefix step 1 (fuel+1) (by omega) () world
  change OracleFirstExposure.locate (OracleProgram.run (OracleMachine.take step (fuel+1) ()) world).run.2 (OracleFirstExposure.seedCoordinates child) = some 0
  rw [← append]
  exact OracleFirstExposure.locate_preserved _ _ _ _ first
private theorem selected_after (fuel : ℕ) : CausalSeedExposure.firstRead step (packet (fuel+1)) = none := by
  simp [CausalSeedExposure.firstRead,CausalSeedExposure.request,value,step,located]
private theorem rate : PendingSeedQuote.risk step (packet 0) = 1/(2 : ENNReal)^512 := by
  simp only [PendingSeedQuote.risk,selected,quoted]
private theorem no_later_rate (fuel : ℕ) : PendingSeedQuote.risk step (packet (fuel+1)) = 0 := by
  simp only [PendingSeedQuote.risk,selected_after]

private theorem guesses0 : NativeChildSeedView.guesses (packet 0).2 = ∅ := rfl
example : ¬CausalSeedExposure.event step (packet 0) world := by
  rw [CausalSeedExposure.event,selected,guesses0]
  exact Finset.notMem_empty _
example : PendingSeedQuote.event step (packet 0) world := by
  simp only [PendingSeedQuote.event,selected,quoted]
  rfl
example : PendingSeedQuote.risk step (packet 0) = 1/(2 : ENNReal)^512 := rate
example (fuel : ℕ) : PendingSeedQuote.risk step (packet (fuel+1)) = 0 := no_later_rate fuel
example : (InputIndexedOracle.law[|{other | (OracleProgram.run (OracleMachine.take step 0 ()) other).run =
    (OracleProgram.run (OracleMachine.take step 0 ()) world).run}])
      {other | PendingSeedQuote.event step (OracleProgram.run (OracleMachine.take step 0 ()) other).run other} =
      1/(2 : ENNReal)^512 := by
  rw [PendingSeedQuote.conditional_event step (OracleProgram.run_replay _) world]
  exact rate
example : PendingSeedQuote.totalCharge (fun _ => (pure () : NativeTranscript.Execution Unit)) id step world =
    1/(2 : ENNReal)^512 := by
  change (∑' fuel : ℕ, PendingSeedQuote.risk step (packet fuel)) = _
  have zero (fuel : ℕ) (different : fuel ≠ 0) : PendingSeedQuote.risk step (packet fuel) = 0 := by
    cases fuel with
    | zero => contradiction
    | succ fuel => exact no_later_rate fuel
  rw [tsum_eq_single 0 (fun fuel different => zero fuel different)]
  exact rate
example : SeedQuoteOrder.Bad step () world :=
  SeedQuoteOrder.closed_graph_bad (V := Unit) step 1 () world (fun _ => child) id (fun _ => 0) (fun _ => first)
    (fun _ => by change NativeChildSeedView.quote child = some seed; exact quoted)
example : MeasurableSet {world | SeedQuoteOrder.Bad step () world} := SeedQuoteOrder.bad_measurable step ()
example : InputIndexedOracle.law {world | SeedQuoteOrder.Bad step () world} ≤
    (∫⁻ world, CausalExposureLifetime.totalCharge (fun _ => (pure () : NativeTranscript.Execution Unit)) id step world ∂InputIndexedOracle.law) +
      ∫⁻ world, PendingSeedQuote.totalCharge (fun _ => (pure () : NativeTranscript.Execution Unit)) id step world ∂InputIndexedOracle.law :=
  SeedQuoteOrder.bad_probability step ()
example : PendingSeedQuote.risk (fun _ : Unit => (OracleMachine.Command.read child 0 0 (fun _ => ()) : OracleMachine.Command Unit Unit))
    (.inl (),[]) = 0 := rfl
example : PendingSeedQuote.risk (fun _ : Unit => (OracleMachine.Command.read child 64 1 (fun _ => ()) : OracleMachine.Command Unit Unit))
    (.inl (),[]) = 0 := rfl
example : PendingSeedQuote.risk (fun _ : Unit => (OracleMachine.Command.hash child (fun _ => ()) : OracleMachine.Command Unit Unit))
    (.inl (),[]) = 0 := rfl
end
end HasteBootsPendingQuoteSmoke

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_event

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.event_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.event_measurable

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.averaged_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.averaged_event

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.lifetime_le

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.totalCharge_lintegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.totalCharge_lintegral

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.lifetime_le_totalCharge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.lifetime_le_totalCharge

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.retained_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.retained_event

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_step_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_step_event

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_lifetime_le

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.totalCharge_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.totalCharge_measurable

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.lifetime_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.lifetime_measurable

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.combined_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.combined_lifetime_le

/-- info: 'FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_combined_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PendingSeedQuote.conditional_combined_lifetime_le

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.hit_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.hit_candidate

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.first_entry_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.first_entry_hit

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.entry_mem_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.entry_mem_take

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.early_observation_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.early_observation_bad

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.observation_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.observation_order

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.early_edge_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.early_edge_bad

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.closed_graph_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.closed_graph_bad

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.bad_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.bad_measurable

/-- info: 'FormalProof4FHE.HasteBoots.SeedQuoteOrder.bad_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.SeedQuoteOrder.bad_probability
