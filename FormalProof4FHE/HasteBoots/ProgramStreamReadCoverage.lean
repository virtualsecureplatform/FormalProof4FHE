module
public import FormalProof4FHE.HasteBoots.AdaptiveBatchFieldLifetime
@[expose] public section

/-! Causal lineage on a clean program is exact raw observation lineage.
The first selected read retains its real continuation and offset. -/
namespace FormalProof4FHE.HasteBoots.ProgramStreamReadCoverage
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
open NativeTranscript (Observation)
noncomputable section

theorem packet {A : Type} (program : Program A) (world : World) (position : ℕ) :
    (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step position world).run =
      (runPrefix position program world).run := by
  rw [CausalExposureLifetime.history_run]
  change (run (OracleMachine.take OracleProgramMachine.step position program) world).run = _
  rw [OracleProgramMachine.take_run]

theorem first {A : Type} (program : Program A) (world : World) (position : ℕ) (input : Input)
    (selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run = some input) :
    ∃ found : ProgramFirstStreamRead.First program world input, found.position = position := by
  unfold CausalStreamExposure.firstRead at selected
  cases active : (runPrefix position program world).run.1 with
  | inr value => simp only [active,CausalSeedExposure.request] at selected; contradiction
  | inl state =>
    cases state with
    | pure value => simp only [active,CausalSeedExposure.request,OracleProgramMachine.step] at selected; contradiction
    | start key next => simp only [active,CausalSeedExposure.request,OracleProgramMachine.step] at selected; contradiction
    | hash key next => simp only [active,CausalSeedExposure.request,OracleProgramMachine.step] at selected; contradiction
    | read key offset count next =>
      simp only [active,CausalSeedExposure.request,OracleProgramMachine.step] at selected
      split at selected
      next eligible =>
        have equal := Option.some.inj selected
        subst input
        exact ⟨⟨position,offset,count,next,active,ReceiptProgramObservation.history program world position,
          eligible.2,eligible.1,FirstReadFiber.output_of_active program world position key offset count next active⟩,rfl⟩
      next => contradiction

theorem prefix_coverage {A : Type} (program : Program A) (world : World) (fuel : ℕ) (input : Input)
    (seen : CausalStreamExposure.seen (runPrefix fuel program world).run.2 input = true) :
    ∃ position < fuel,
      CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run = some input ∧
      ∃ offset values after, values ≠ [] ∧
        (runPrefix fuel program world).run.2 = (runPrefix position program world).run.2 ++ .output input offset values :: after := by
  have touched : CausalStreamExposure.seen
      (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step fuel world).run.2 input = true := by
    rw [packet]
    exact seen
  rcases CausalStreamLineage.coverage (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step fuel world input touched with
    inherited | ⟨position,inside,selected,_,offset,values,after,positive,split⟩
  · cases inherited
  · simp only [packet] at selected split
    exact ⟨position,inside,selected,offset,values,after,positive,split⟩

theorem coverage {A : Type} (program : Program A) (world : World) (input : Input)
    (seen : CausalStreamExposure.seen (run program world).run.2 input = true) :
    ∃ position < (run program world).run.2.length,
      CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run = some input ∧
      ∃ offset values after, values ≠ [] ∧
        (run program world).run.2 = (runPrefix position program world).run.2 ++ .output input offset values :: after := by
  have touched : CausalStreamExposure.seen
      (runPrefix (run program world).run.2.length program world).run.2 input = true := by
    rw [ProgramObservationClock.complete_length]
    exact seen
  obtain ⟨position,inside,selected,offset,values,after,positive,split⟩ := prefix_coverage program world _ input touched
  rw [ProgramObservationClock.complete_length] at split
  exact ⟨position,inside,selected,offset,values,after,positive,split⟩

end
end FormalProof4FHE.HasteBoots.ProgramStreamReadCoverage
