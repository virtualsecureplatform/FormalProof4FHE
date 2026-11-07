module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineHistory
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
@[expose] public section

/-! The existing one-world root-family collision/source accounting over the
closed interpreter's actual instruction prefixes. Local steps do not reset
caches, manufacture starts, or become observation indices. Hazard charges
remain explicit; their coupling to physical attacker work is not assumed. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineRootLifetime
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleProgram (Program run bind)
open ClosedByteMachine (Instruction State take)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeRootFamilyLifetime (Bad)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def program (prelude : Program State) (code : List Instruction) (publicData : Input) (fuel : ℕ) : Program State :=
  bind prelude (take code publicData fuel)

def prefixCharge (dummy : Digest) (prelude : Program State) (code : List Instruction) (publicData : Input) (fuel : ℕ) :=
  ExpectedHazard.charge
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
    (CheckpointCollision.loss unifSpec shape)
    ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program prelude code publicData fuel)).run NativeShakeCache.empty)
    (CheckpointExecution.empty shape)

theorem log_prefix (prelude : Program State) (code : List Instruction) (publicData : Input)
    (first later : ℕ) (bounded : first ≤ later) (world : World) :
    (run (program prelude code publicData first) world).run.2.IsPrefix
      (run (program prelude code publicData later) world).run.2 := by
  simpa only [program,OracleProgram.run_bind,ClosedByteMachineHistory.history] using
    ClosedByteMachineHistory.history_prefix (run prelude) code publicData first later bounded world

theorem prefixCharge_monotone (dummy : Digest) (prelude : Program State) (code : List Instruction) (publicData : Input) :
    Monotone (prefixCharge dummy prelude code publicData) := by
  intro first later bounded
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  have same : program prelude code publicData (first+extra) =
      bind (program prelude code publicData first) (take code publicData extra) := by
    simp only [program,NativeProgramComposition.bind_assoc]
    apply congrArg (bind prelude)
    funext state
    exact ClosedByteMachine.take_resume code publicData first extra state
  unfold prefixCharge
  rw [same]
  exact NativeRootFamilyLifetime.charge_bind dummy NativeParentLedger.empty NativeShakeCache.empty
    (CheckpointExecution.empty shape) _ _

theorem bad_monotone (dummy : Digest) (prelude : Program State) (code : List Instruction) (publicData : Input) :
    Monotone (fun fuel : ℕ => {world | Bad dummy (run (program prelude code publicData fuel) world).run.2}) := by
  intro first later bounded world failed
  exact NativeRootFamilyAudit.bad_persistent dummy world _ _ ((OracleProgram.run_replay _).truthful world)
    (log_prefix prelude code publicData first later bounded world) failed

/-- An unbounded execution of the closed interpreter uses the same global
hash/source ledger at every instruction prefix, including the whole prelude. -/
theorem lifetime_bad_le_charge (dummy : Digest) (prelude : Program State) (code : List Instruction) (publicData : Input) :
    InputIndexedOracle.law {world | ∃ fuel, Bad dummy (run (program prelude code publicData fuel) world).run.2} ≤
      ⨆ fuel : ℕ, prefixCharge dummy prelude code publicData fuel := by
  have union : {world | ∃ fuel, Bad dummy (run (program prelude code publicData fuel) world).run.2} =
      ⋃ fuel : ℕ, {world | Bad dummy (run (program prelude code publicData fuel) world).run.2} := by
    ext world
    simp
  rw [union,(bad_monotone dummy prelude code publicData).measure_iUnion]
  exact iSup_mono (fun fuel => NativeRootFamilyAudit.bad_le_charge dummy (program prelude code publicData fuel))
end
end FormalProof4FHE.HasteBoots.ClosedByteMachineRootLifetime
