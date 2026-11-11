module
public import FormalProof4FHE.HasteBoots.AllocatedIdentityOpeningLifetime
@[expose] public section

/-! Completed-program witnesses enter the same unbounded causal lifetime at
an actual path-dependent completion depth. No uniform fuel cap is supplied. -/
namespace FormalProof4FHE.HasteBoots.ProgramOpeningLifetime
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
open NativeRootMessage (Digest)
noncomputable section

theorem history_log {A : Type} (program : Program A) (fuel : ℕ) (world : World) :
    (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step fuel world).run.2 =
      (runPrefix fuel program world).run.2 := by
  rw [CausalExposureLifetime.history_run]
  change (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2 = _
  rw [OracleProgramMachine.take_run]

theorem completed_log {A : Type} (program : Program A) (world : World) :
    ∃ fuel, (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step fuel world).run.2 =
      (run program world).run.2 := by
  obtain ⟨fuel,finished⟩ := OracleProgramMachine.prefix_complete program world
  exact ⟨fuel,(history_log program fuel world).trans (congrArg Prod.snd finished)⟩

theorem helper {A Memory : Type} (program : Program A) (world : World) (dummy : Digest)
    (target : NativeGoldPcsExecution.Context) (radius : ℕ)
    (occurred : Nonempty (SingleOpeningLifetimeSoundness.Witness Memory dummy target radius world (run program world).run.2)) :
    SingleOpeningLifetimeSoundness.Failure Memory dummy target radius (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  obtain ⟨fuel,logEq⟩ := completed_log program world
  exact ⟨fuel,logEq.symm ▸ occurred⟩

theorem batch {A Memory : Type} (program : Program A) (world : World) (dummy : Digest)
    (target : NativeGoldBatchPcsProgram.Context) (old reference : CacheBackedCodeOrigin.Origin target) (radius : ℕ)
    (occurred : Nonempty (CacheBackedBatchLifetimeSoundness.Witness Memory dummy target old radius world (run program world).run.2)) :
    CacheBackedBatchLifetimeSoundness.Failure Memory dummy target reference radius (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  obtain ⟨witness⟩ := occurred
  obtain ⟨fuel,logEq⟩ := completed_log program world
  refine ⟨fuel,?_⟩
  rw [logEq]
  exact ⟨CacheBackedBatchLifetimeSoundness.ofNative reference (CacheBackedBatchLifetimeSoundness.toNative witness)⟩

theorem root_bad {A : Type} (program : Program A) (world : World) (dummy : Digest)
    (bad : NativeRootFamilyLifetime.Bad dummy (run program world).run.2) :
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  obtain ⟨fuel,logEq⟩ := completed_log program world
  exact ⟨fuel,logEq.symm ▸ bad⟩

end
end FormalProof4FHE.HasteBoots.ProgramOpeningLifetime
