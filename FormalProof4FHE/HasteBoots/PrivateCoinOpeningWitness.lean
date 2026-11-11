module
public import FormalProof4FHE.HasteBoots.InstructionLogRealization
public import FormalProof4FHE.HasteBoots.PrivateCoinByteNativeCoverage
@[expose] public section

/-! Original program-prefix PCS witnesses occur on exact actual instruction
logs. Only the equal log index is transported; native witness data are kept. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinOpeningWitness
open InputIndexedOracle (Input World)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction initialise take)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
open PrivateCoinByteLineage (history)
noncomputable section

theorem helper (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest) (ctx : NativeGoldPcsExecution.Context) (radius : ℕ)
    (failed : SingleOpeningLifetimeSoundness.Failure Memory dummy ctx radius
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) :
    ∃ index ≤ fuel, Nonempty (SingleOpeningLifetimeSoundness.Witness Memory dummy ctx radius world
      (history code publicData privateData tape index world).run.2) := by
  obtain ⟨position,⟨witness⟩⟩ := failed
  obtain ⟨index,inside,same⟩ := InstructionLogRealization.pcs_prefix code publicData tape (initialise code privateData) fuel position world
  have logEq : (history code publicData privateData tape index world).run.2 =
      (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel))
        id OracleProgramMachine.step position world).run.2 := by
    rw [PrivateCoinByteLineage.history_run]
    exact same
  exact ⟨index,inside,⟨logEq.symm ▸ witness⟩⟩

theorem source (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context) (radius : ℕ)
    (failed : NativeGoldBatchLifetimeSoundness.Failure Memory dummy ctx radius
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) :
    ∃ index ≤ fuel, Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world
      (history code publicData privateData tape index world).run.2) := by
  obtain ⟨position,⟨witness⟩⟩ := failed
  obtain ⟨index,inside,same⟩ := InstructionLogRealization.pcs_prefix code publicData tape (initialise code privateData) fuel position world
  have logEq : (history code publicData privateData tape index world).run.2 =
      (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel))
        id OracleProgramMachine.step position world).run.2 := by
    rw [PrivateCoinByteLineage.history_run]
    exact same
  exact ⟨index,inside,⟨logEq.symm ▸ witness⟩⟩

theorem cached_source (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (origin : CacheBackedCodeOrigin.Origin ctx) (radius : ℕ)
    (failed : CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin radius
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) :
    ∃ index ≤ fuel, Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world
      (history code publicData privateData tape index world).run.2) :=
  source Memory code publicData privateData tape fuel world dummy ctx radius
    ((CacheBackedBatchLifetimeSoundness.failure_iff Memory dummy ctx origin radius _ id OracleProgramMachine.step world).mp failed)

theorem family {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest)
    (helperCtx : NativeGoldPcsExecution.Context) (sourceCtx : I → NativeGoldBatchPcsProgram.Context)
    (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (sourceCtx i)) (helperRadius : ℕ) (sourceRadius : I → ℕ)
    (failed : OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helperCtx sourceCtx sourceOrigin helperRadius sourceRadius
      (privateProgram code publicData tape privateData fuel) OracleProgramMachine.step world) :
    ∃ index ≤ fuel,
      Nonempty (SingleOpeningLifetimeSoundness.Witness HelperMemory dummy helperCtx helperRadius world (history code publicData privateData tape index world).run.2) ∨
      ∃ i, Nonempty (NativeGoldBatchLifetimeSoundness.Witness SourceMemory dummy (sourceCtx i) (sourceRadius i) world (history code publicData privateData tape index world).run.2) := by
  rcases failed with single | ⟨i,batch⟩
  · obtain ⟨index,inside,witness⟩ := helper HelperMemory code publicData privateData tape fuel world dummy helperCtx helperRadius single
    exact ⟨index,inside,Or.inl witness⟩
  · obtain ⟨index,inside,witness⟩ := cached_source SourceMemory code publicData privateData tape fuel world dummy (sourceCtx i) (sourceOrigin i) (sourceRadius i) batch
    exact ⟨index,inside,Or.inr ⟨i,witness⟩⟩

end
end FormalProof4FHE.HasteBoots.PrivateCoinOpeningWitness
