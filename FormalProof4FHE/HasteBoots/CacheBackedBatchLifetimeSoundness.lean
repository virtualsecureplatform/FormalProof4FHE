module
public import FormalProof4FHE.HasteBoots.CacheBackedCodeOrigin
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSoundness
@[expose] public section

/-! Native lifetime false analysis claims with constructor/root/capacity facts
derived from retained completed backend execution. The witness stores actual
acceptance and claim data, not independent code-security certificates. Prelude
work stays in the native exposure charges. Application/physical refinement is
still separate. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedBatchLifetimeSoundness
open CacheBackedCodeOrigin (Origin)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open InputIndexedOracle (World law)
open CausalExposureLifetime (history)
open OracleProgram (Program run)
open MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Witness (Memory : Type) (dummy : Digest) (ctx : Context) (origin : Origin ctx)
    (radius : ℕ) (world : World) (log : List Observation) where
  candidate : Context
  sameParameters : candidate.parameters = ctx.parameters
  sameProfile : candidate.parent.profile = ctx.parent.profile
  choose : Scheduler Memory
  verifierFuel : ℕ
  memory : Memory
  work : Prepared
  decoded : NativeGoldBatchChallengeLink.View
  parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded
  responseFits : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit
  accepted : NativeGoldBatchAnySourceRisk.Accepted world log candidate choose verifierFuel memory work
  falseClaim : NativeGoldBatchCausalCoverage.FalseClaim dummy candidate (origin.primitiveAt candidate sameParameters)
    work decoded log (origin.capacityAt candidate sameParameters) radius

def toNative {Memory : Type} {dummy : Digest} {ctx : Context} {origin : Origin ctx} {radius : ℕ}
    {world : World} {log : List Observation} (witness : Witness Memory dummy ctx origin radius world log) :
    NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world log where
  candidate := witness.candidate
  sameParameters := witness.sameParameters
  sameProfile := witness.sameProfile
  primitive := origin.primitiveAt witness.candidate witness.sameParameters
  capacity := origin.capacityAt witness.candidate witness.sameParameters
  choose := witness.choose
  verifierFuel := witness.verifierFuel
  memory := witness.memory
  work := witness.work
  decoded := witness.decoded
  parsed := witness.parsed
  responseFits := witness.responseFits
  accepted := witness.accepted
  falseClaim := witness.falseClaim

def ofNative {Memory : Type} {dummy : Digest} {ctx : Context} (origin : Origin ctx) {radius : ℕ}
    {world : World} {log : List Observation} (witness : NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius world log) :
    Witness Memory dummy ctx origin radius world log where
  candidate := witness.candidate
  sameParameters := witness.sameParameters
  sameProfile := witness.sameProfile
  choose := witness.choose
  verifierFuel := witness.verifierFuel
  memory := witness.memory
  work := witness.work
  decoded := witness.decoded
  parsed := witness.parsed
  responseFits := witness.responseFits
  accepted := witness.accepted
  falseClaim := witness.falseClaim

def Failure {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (origin : Origin ctx) (radius : ℕ)
    (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, Nonempty (Witness Memory dummy ctx origin radius world (history past initial step fuel world).run.2)

/-- Deriving code facts changes neither the witnessed native calls nor the
false-claim event, in either direction. -/
theorem failure_iff {P S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (origin : Origin ctx) (radius : ℕ)
    (past : World → Execution P) (initial : P → S) (step : S → OracleMachine.Command S A) (world : World) :
    Failure Memory dummy ctx origin radius past initial step world ↔
      NativeGoldBatchLifetimeSoundness.Failure Memory dummy ctx radius past initial step world := by
  constructor
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨toNative witness⟩⟩
  · rintro ⟨fuel,⟨witness⟩⟩
    exact ⟨fuel,⟨ofNative origin witness⟩⟩

/-- The complete native prelude is rebased into the same causal machine.
Constructor/root, capacity, field-size and code-distance facts are derived;
only public width and the numerical radius condition remain. -/
theorem prelude_bound {S A : Type} (Memory : Type) (dummy : Digest) (ctx : Context) (origin : Origin ctx)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (prelude : Program S) (step : S → OracleMachine.Command S A)
    (small : 3 * radius < ctx.parameters.code.blocks.val - ctx.parameters.code.messageBlocks.val + 1) :
    law {world | Failure Memory dummy ctx origin radius (run prelude) id step world} ≤
      (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure prelude) (OracleMachinePrelude.prepend step) fuel) +
        NativeGoldBatchLifetimeSoundness.exposureCharge (NativeGoldBatchLifetimeSoundness.clean prelude) id dummy ctx
          (origin.primitiveAt ctx rfl) radius (OracleMachinePrelude.prepend step) := by
  have nativeSmall : 3 * radius < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx (origin.primitiveAt ctx rfl))
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
      Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) := by
    rw [origin.distanceAt ctx rfl]
    exact small
  have bound := NativeGoldBatchLifetimeSoundness.prelude_bound Memory dummy ctx (origin.primitiveAt ctx rfl)
    origin.tables origin.request.message origin.request.block origin.request.blowup (origin.constructedAt ctx rfl)
    radius width prelude step (origin.radius_fits radius small) nativeSmall
  simpa only [failure_iff] using bound

end
end FormalProof4FHE.HasteBoots.CacheBackedBatchLifetimeSoundness
