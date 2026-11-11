module
public import FormalProof4FHE.HasteBoots.PrivateCoinOpeningWitness
public import FormalProof4FHE.HasteBoots.PrivateCoinByteReceiptWork
@[expose] public section

/-! Original source-family PCS failures enter the actual runtime instruction
hazards with the same full parameters/profile and original constructor.
The shared hash alternative is excluded once, outside all source events. -/
namespace FormalProof4FHE.HasteBoots.OriginalBatchInstructionCoverage
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open PrivateCoinByteLineage (history)
open PrivateCoinByteRequest (command)
open NativeGoldBatchPcsProgram (Context)
open MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Hazards (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (tape : Tape)
    (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx) (radius : ℕ) (world : World) : Prop :=
  (∃ index, NativeEarlyReceiptBound.event ctx.parent.profile (command code publicData tape)
    (history code publicData privateData tape index world).run world) ∨
  (∃ index, NativeGoldBatchFieldProximity.event dummy ctx (origin.primitiveAt ctx rfl) radius ctx.parent.profile (command code publicData tape)
    (history code publicData privateData tape index world).run world) ∨
  ∃ index, NativeGoldBatchProfileColumnExposure.event dummy ctx (origin.primitiveAt ctx rfl) ctx.parent.profile (command code publicData tape)
    (history code publicData privateData tape index world).run radius world

theorem witness_covered (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (index : ℕ) (world : World) (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (safe : ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel (tape,world))
    (witness : NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world
      (history code publicData privateData tape index world).run.2) :
    Hazards code publicData privateData tape dummy ctx origin radius world := by
  have built : NativeGoldBlockCode.build origin.tables origin.request.message origin.request.block origin.request.blowup =
      .ok witness.candidate.parameters.code := by
    rw [witness.sameParameters]
    exact origin.constructedAt ctx rfl
  have candidateWidth : 3 ≤ witness.candidate.parameters.width.val := by rw [witness.sameParameters]; exact width
  have covered := PrivateCoinByteNativeCoverage.accepted_coverage code publicData privateData tape index world dummy witness.candidate witness.work
    origin.tables origin.request.message origin.request.block origin.request.blowup built witness.primitive
    witness.choose witness.verifierFuel witness.memory witness.decoded witness.parsed witness.responseFits witness.accepted
    witness.capacity radius candidateWidth witness.falseClaim
  rcases covered with different | ⟨earlier,_,early⟩ | ⟨earlier,_,field⟩ | ⟨earlier,_,column⟩
  · have audit := NativeRootFamilyAudit.disagreement_implies_bad dummy world _
      ((PrivateCoinByteLineage.history_replay code publicData privateData tape index).truthful world)
    have decisions : (fun first second : Digest => Fintype.decidablePiFintype first second) =
        (inferInstance : DecidableEq Digest) := Subsingleton.elim _ _
    rw [decisions] at audit
    have bad := audit different
    apply False.elim
    apply safe
    refine ⟨index,?_⟩
    rw [PrivateCoinByteLineage.history_run] at bad
    exact bad
  · left
    rw [witness.sameProfile] at early
    exact ⟨earlier,early⟩
  · right; left
    rw [witness.sameProfile] at field
    exact ⟨earlier,(NativeGoldBatchEventContext.field_event dummy witness.candidate ctx witness.sameParameters witness.primitive
      (origin.primitiveAt ctx rfl) radius ctx.parent.profile (command code publicData tape) _ world).mp field⟩
  · right; right
    rw [witness.sameProfile] at column
    exact ⟨earlier,(NativeGoldBatchEventContext.profile_column_event dummy witness.candidate ctx witness.sameParameters witness.primitive
      (origin.primitiveAt ctx rfl) radius ctx.parent.profile (command code publicData tape) _ world).mp column⟩

theorem covered (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (safe : ¬∃ horizon, PrivateCoinSharedHash.Root code publicData privateData dummy horizon (tape,world))
    (failed : CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin radius
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) :
    Hazards code publicData privateData tape dummy ctx origin radius world := by
  obtain ⟨index,_,⟨witness⟩⟩ := PrivateCoinOpeningWitness.cached_source Memory code publicData privateData tape fuel world dummy ctx origin radius failed
  exact witness_covered Memory code publicData privateData tape index world dummy ctx origin radius width safe witness

theorem calibrated_bound (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (role : NativeBrakedownCalibration.Role) (compatible : NativeGoldBatchCalibration.Matches ctx role)
    (width : 3 ≤ ctx.parameters.width.val) :
    law {world | (∃ fuel, CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin (NativeBrakedownCalibration.radius .goldilocks role)
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel (tape,world)} ≤
      ((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have included : {world | (∃ fuel, CacheBackedBatchLifetimeSoundness.Failure Memory dummy ctx origin (NativeBrakedownCalibration.radius .goldilocks role)
      (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData tape privateData fuel)) id OracleProgramMachine.step world) ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel (tape,world)} ⊆
      {world | ∃ index, PrivateCoinByteGoldRisk.event code publicData tape dummy ctx (origin.primitiveAt ctx rfl) role ctx.parent.profile
        (PrivateCoinByteFixed.history code publicData tape privateData index world).run world ∨
        NativeEarlyReceiptBound.event ctx.parent.profile (command code publicData tape)
          (PrivateCoinByteFixed.history code publicData tape privateData index world).run world} := by
    rintro world ⟨⟨fuel,failed⟩,safe⟩
    rcases covered Memory code publicData privateData tape fuel world dummy ctx origin _ width safe failed with ⟨index,early⟩ | ⟨index,field⟩ | ⟨index,column⟩
    · exact ⟨index,Or.inr early⟩
    · exact ⟨index,Or.inl (Or.inl field)⟩
    · exact ⟨index,Or.inl (Or.inr column)⟩
  exact (measure_mono included).trans (PrivateCoinByteReceiptWork.gold_exposure_lifetime_le_work code publicData tape dummy ctx
    origin.tables origin.request.message origin.request.block origin.request.blowup (origin.constructedAt ctx rfl)
    (origin.primitiveAt ctx rfl) role compatible ctx.parent.profile privateData)

end
end FormalProof4FHE.HasteBoots.OriginalBatchInstructionCoverage
