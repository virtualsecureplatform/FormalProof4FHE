module
public import FormalProof4FHE.HasteBoots.NativeGoldExecutableExtraction
public import FormalProof4FHE.HasteBoots.ClosedByteMachineNativeSoundness
@[expose] public section
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineExecutableSoundness
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeBrakedownCalibration (Role radius)
open ClosedByteMachine (Instruction Tape)
open ClosedByteMachineGoldRisk (history)
open NativeTranscript (Observation)
open MeasureTheory
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-! The accepted native failure event with executable extraction. All original
query finishing claims, acceptance/log premises and scheduler memory remain.
The result prices declared interpreter work; it is not a physical PBS theorem. -/
structure Witness (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ) (world : World) (log : List Observation) where
  candidate : Context
  sameParameters : candidate.parameters = ctx.parameters
  sameProfile : candidate.parent.profile = ctx.parent.profile
  primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue candidate.parameters.code.domainRoot) (2^(logSize candidate.parameters.code+1))
  capacity : candidate.parameters.code.messageLength.val ≤ candidate.parameters.code.messageBlocks.val*candidate.parameters.code.blockWidth.val
  choose : Scheduler Memory
  verifierFuel : ℕ
  memory : Memory
  work : Prepared
  decoded : NativeGoldBatchChallengeLink.View
  parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded
  responseFits : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit
  accepted : NativeGoldBatchAnySourceRisk.Accepted world log candidate choose verifierFuel memory work
  falseClaim : NativeGoldExecutableExtraction.FalseClaim dummy candidate work decoded log capacity radius

def Failure (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role) (world : World) : Prop :=
  ∃ fuel, Nonempty (Witness Memory dummy ctx (radius .goldilocks role) world (history code publicData privateData fuel world).run.2)

def toAnalysis {Memory : Type} {dummy : Digest} {ctx : Context} {radius : ℕ} {world : World} {log : List Observation}
    (witness : Witness Memory dummy ctx radius world log)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok witness.candidate.parameters.code)
    (uniqueRadius : 2*radius < 2^(logSize witness.candidate.parameters.code)-witness.candidate.parameters.code.messageBlocks.val+1) :
    NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world log where
  candidate := witness.candidate
  sameParameters := witness.sameParameters
  sameProfile := witness.sameProfile
  primitive := witness.primitive
  capacity := witness.capacity
  choose := witness.choose
  verifierFuel := witness.verifierFuel
  memory := witness.memory
  work := witness.work
  decoded := witness.decoded
  parsed := witness.parsed
  responseFits := witness.responseFits
  accepted := witness.accepted
  falseClaim := (NativeGoldExecutableExtraction.falseClaim_iff_analysis dummy witness.candidate tables message block blowup
    constructed witness.primitive witness.work witness.decoded log witness.capacity radius uniqueRadius).mp witness.falseClaim

def ofAnalysis {Memory : Type} {dummy : Digest} {ctx : Context} {radius : ℕ} {world : World} {log : List Observation}
    (witness : NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world log)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok witness.candidate.parameters.code)
    (uniqueRadius : 2*radius < 2^(logSize witness.candidate.parameters.code)-witness.candidate.parameters.code.messageBlocks.val+1) :
    Witness Memory dummy ctx radius world log where
  candidate := witness.candidate
  sameParameters := witness.sameParameters
  sameProfile := witness.sameProfile
  primitive := witness.primitive
  capacity := witness.capacity
  choose := witness.choose
  verifierFuel := witness.verifierFuel
  memory := witness.memory
  work := witness.work
  decoded := witness.decoded
  parsed := witness.parsed
  responseFits := witness.responseFits
  accepted := witness.accepted
  falseClaim := (NativeGoldExecutableExtraction.falseClaim_iff_analysis dummy witness.candidate tables message block blowup
    constructed witness.primitive witness.work witness.decoded log witness.capacity radius uniqueRadius).mpr witness.falseClaim

theorem failure_iff_analysis (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (compatible : NativeGoldBatchCalibration.Matches ctx role) (world : World) :
    Failure Memory code publicData privateData dummy ctx role world ↔
      ClosedByteMachineNativeSoundness.Failure Memory code publicData privateData dummy ctx role world := by
  have uniqueRadius : 2 * radius .goldilocks role < 2^(logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1 := by
    rw [compatible.height,compatible.message]
    cases role <;> decide +kernel
  constructor
  · rintro ⟨fuel,⟨witness⟩⟩
    have built : NativeGoldBlockCode.build tables message block blowup = .ok witness.candidate.parameters.code := by
      rwa [witness.sameParameters]
    have unique : 2 * radius .goldilocks role < 2^(logSize witness.candidate.parameters.code)-witness.candidate.parameters.code.messageBlocks.val+1 := by
      rwa [witness.sameParameters]
    exact ⟨fuel,⟨toAnalysis witness tables message block blowup built unique⟩⟩
  · rintro ⟨fuel,⟨witness⟩⟩
    have built : NativeGoldBlockCode.build tables message block blowup = .ok witness.candidate.parameters.code := by
      rwa [witness.sameParameters]
    have unique : 2 * radius .goldilocks role < 2^(logSize witness.candidate.parameters.code)-witness.candidate.parameters.code.messageBlocks.val+1 := by
      rwa [witness.sameParameters]
    exact ⟨fuel,⟨ofAnalysis witness tables message block blowup built unique⟩⟩

theorem failure_set_eq_analysis (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (compatible : NativeGoldBatchCalibration.Matches ctx role) :
    {world | Failure Memory code publicData privateData dummy ctx role world} =
      {world | ClosedByteMachineNativeSoundness.Failure Memory code publicData privateData dummy ctx role world} := by
  ext world
  exact failure_iff_analysis Memory code publicData privateData dummy ctx role tables message block blowup constructed compatible world

theorem failure_measurable (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (compatible : NativeGoldBatchCalibration.Matches ctx role) :
    MeasurableSet {world | Failure Memory code publicData privateData dummy ctx role world} := by
  rw [failure_set_eq_analysis Memory code publicData privateData dummy ctx role tables message block blowup constructed compatible]
  exact ClosedByteMachineNativeSoundness.failure_measurable Memory code publicData privateData dummy ctx role

theorem lifetime_le_work (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (compatible : NativeGoldBatchCalibration.Matches ctx role) :
    law {world | Failure Memory code publicData privateData dummy ctx role world} ≤
      ClosedByteMachineGoldAllRisk.rate*ClosedByteMachineWork.expectedWork code publicData privateData := by
  rw [failure_set_eq_analysis Memory code publicData privateData dummy ctx role tables message block blowup constructed compatible]
  exact ClosedByteMachineNativeSoundness.lifetime_le_work Memory code publicData privateData dummy ctx role tables message block blowup
    constructed primitive compatible

theorem scaled_lifetime_le_work (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (compatible : NativeGoldBatchCalibration.Matches ctx role) :
    (2 : ENNReal)^128 * law {world | Failure Memory code publicData privateData dummy ctx role world} ≤
      (9/4096 : ENNReal)*ClosedByteMachineWork.expectedWork code publicData privateData := by
  rw [failure_set_eq_analysis Memory code publicData privateData dummy ctx role tables message block blowup constructed compatible]
  exact ClosedByteMachineNativeSoundness.scaled_lifetime_le_work Memory code publicData privateData dummy ctx role tables message block blowup
    constructed primitive compatible

end FormalProof4FHE.HasteBoots.ClosedByteMachineExecutableSoundness
