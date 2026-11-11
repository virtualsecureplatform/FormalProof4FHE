module
public import FormalProof4FHE.HasteBoots.AcceptedBatchAdaptiveCoverage
@[expose] public section

/-! The original source witnesses enter adaptive field candidates without
changing parameters, profiles, original indices or constructor provenance. -/
namespace FormalProof4FHE.HasteBoots.OriginalSourceAdaptiveCoverage
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
open NativeGoldBatchPcsProgram (Context)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Hazards {A : Type} (program : Program A) (world : World) (dummy : Digest) (ctx : Context)
    (origin : CacheBackedCodeOrigin.Origin ctx) (role : NativeBrakedownCalibration.Role) : Prop :=
  NativeRootFamilyLifetime.Bad dummy (run program world).run.2 ∨
  (∃ position, NativeEarlyReceiptBound.event ctx.parent.profile OracleProgramMachine.step (runPrefix position program world).run world) ∨
  (∃ position, AdaptiveBatchFieldKernel.Occurs program position ctx.parent.profile dummy world) ∨
  ∃ position, NativeGoldBatchProfileColumnExposure.event dummy ctx (origin.primitiveAt ctx rfl) ctx.parent.profile OracleProgramMachine.step
    (runPrefix position program world).run (NativeBrakedownCalibration.radius .goldilocks role) world

theorem witness_covered {A Memory : Type} (program : Program A) (world : World) (dummy : Digest)
    (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx) (role : NativeBrakedownCalibration.Role)
    (admitted : NativeGoldBatchCalibration.Matches ctx role)
    (witness : NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx (NativeBrakedownCalibration.radius .goldilocks role)
      world (run program world).run.2) :
    Hazards program world dummy ctx origin role := by
  let candidateOrigin : CacheBackedCodeOrigin.Origin witness.candidate :=
    ⟨origin.request,origin.config,origin.reachable,origin.result,origin.finished,origin.retainedAt witness.candidate witness.sameParameters⟩
  have compatible : NativeGoldBatchCalibration.Matches witness.candidate role := by
    constructor
    · rw [witness.sameParameters]; exact admitted.width
    · rw [witness.sameParameters]; exact admitted.height
    · rw [witness.sameParameters]; exact admitted.message
    · rw [witness.sameParameters]; exact admitted.queries
  have covered := AcceptedBatchAdaptiveCoverage.accepted_coverage program world dummy witness.candidate witness.work candidateOrigin role compatible
    witness.choose witness.verifierFuel witness.memory witness.decoded witness.parsed witness.responseFits witness.accepted witness.falseClaim
  rcases covered with different | ⟨position,early⟩ | ⟨position,field⟩ | ⟨position,column⟩
  · left
    have audit := NativeRootFamilyAudit.disagreement_implies_bad dummy world _ ((OracleProgram.run_replay program).truthful world)
    have decisions : (fun first second : Digest => Fintype.decidablePiFintype first second) =
        (inferInstance : DecidableEq Digest) := Subsingleton.elim _ _
    rw [decisions] at audit
    exact audit different
  · right; left
    rw [witness.sameProfile] at early
    exact ⟨position,early⟩
  · right; right; left
    rw [witness.sameProfile] at field
    exact ⟨position,field⟩
  · right; right; right
    rw [witness.sameProfile] at column
    exact ⟨position,(NativeGoldBatchEventContext.profile_column_event dummy witness.candidate ctx witness.sameParameters
      (candidateOrigin.primitiveAt _ rfl) (origin.primitiveAt ctx rfl) (NativeBrakedownCalibration.radius .goldilocks role)
      ctx.parent.profile OracleProgramMachine.step _ world).mp column⟩

theorem original_covered (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest)
    (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx) (role : NativeBrakedownCalibration.Role)
    (admitted : NativeGoldBatchCalibration.Matches ctx role)
    (failed : CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin (NativeBrakedownCalibration.radius .goldilocks role)
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) :
    ∃ index ≤ fuel, Hazards (privateProgram code publicData tape privateData index) world dummy ctx origin role := by
  obtain ⟨index,inside,⟨witness⟩⟩ := PrivateCoinOpeningWitness.cached_source Memory code publicData privateData tape fuel world dummy ctx origin _ failed
  have actual : NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx (NativeBrakedownCalibration.radius .goldilocks role)
      world (run (privateProgram code publicData tape privateData index) world).run.2 := by
    simpa only [PrivateCoinByteLineage.history_run,PrivateCoinByteLineage.packet,privateProgram] using witness
  exact ⟨index,inside,witness_covered _ world dummy ctx origin role admitted actual⟩

end
end FormalProof4FHE.HasteBoots.OriginalSourceAdaptiveCoverage
