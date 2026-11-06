module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
import all FormalProof4FHETest.HasteBootsCausalCoverageSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open OracleProgram (Program run)
namespace HasteBootsLifetimeSoundnessSmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (ctx world root primitive usize)
open HasteBootsNativeFinishingSmoke (work choose)
open HasteBootsFirstFieldSourceSmoke (decoded parsed)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
local instance : NeZero ctx.parameters.code.blockWidth.val := ⟨by decide +kernel⟩

-- Roots, parent bytes, openings and native collection budgets may vary.
def other : NativeGoldBatchPcsProgram.Context :=
  {ctx with
    root := fun _ => 1
    parent := {ctx.parent with input := [99]}
    opening := {ctx.opening with columns := ⟨[],by decide⟩}
    fieldFuel := 0}
example {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) (oracle : World) :
    NativeGoldBatchFieldProximity.event root other primitive 0 root step packet oracle ↔
      NativeGoldBatchFieldProximity.event root ctx primitive 0 root step packet oracle :=
  NativeGoldBatchEventContext.field_event root other ctx rfl primitive primitive 0 root step packet oracle
example {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) (oracle : World) :
    NativeGoldBatchConcreteColumnExposure.event root other primitive root step packet 0 oracle ↔
      NativeGoldBatchConcreteColumnExposure.event root ctx primitive root step packet 0 oracle :=
  NativeGoldBatchEventContext.column_event root other ctx rfl primitive primitive 0 root step packet oracle

section Prelude
open HasteBootsCausalCoverageSmoke (key step)
def before : Program ℕ := .read key 999 1 (fun _ => .hash [77] (fun _ => .pure 0))
def machine := OracleMachinePrelude.prepend step
def full (fuel : ℕ) := CausalExposureLifetime.history (NativeGoldBatchLifetimeSoundness.clean before) id machine fuel world
example : CausalStreamExposure.firstRead machine (full 0).run = some key := by decide +kernel
-- After the prelude, its earlier partial read prevents another first-read charge.
example : CausalStreamExposure.firstRead machine (full 5).run = none := by decide +kernel
example (fuel : ℕ) :
    (run (OracleMachine.take machine ((run before world).run.2.length+fuel) before) world).run.2 =
      (run before world).run.2 ++ (run (OracleMachine.take step fuel (run before world).run.1) world).run.2 :=
  OracleMachinePrelude.prelude_log step before fuel world
end Prelude

abbrev capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val := by decide +kernel
def nativePrelude := NativeGoldBatchPcsProgram.program ctx choose 6 ()
def stopped (_ : NativeGoldBatchPcsProgram.Outcome Unit) : OracleMachine.Command (NativeGoldBatchPcsProgram.Outcome Unit) Unit := .done ()
def oldHistory := CausalExposureLifetime.history (run nativePrelude) id stopped 0 world

theorem accepted : NativeGoldBatchAnySourceRisk.Accepted world oldHistory.run.2 ctx choose 6 () work :=
  HasteBootsCausalCoverageSmoke.nativeAccepted

def witness (falseClaim : NativeGoldBatchCausalCoverage.FalseClaim root ctx primitive work decoded oldHistory.run.2 capacity 0) :
    NativeGoldBatchLifetimeSoundness.Witness Unit root ctx 0 world oldHistory.run.2 where
  candidate := ctx
  sameParameters := rfl
  sameProfile := rfl
  primitive := primitive
  capacity := capacity
  choose := choose
  verifierFuel := 6
  memory := ()
  work := work
  decoded := decoded
  parsed := parsed
  responseFits := by decide +kernel
  accepted := accepted
  falseClaim := falseClaim

-- Actual native verification in the old prelude is retained by clean rebasing.
example (falseClaim : NativeGoldBatchCausalCoverage.FalseClaim root ctx primitive work decoded oldHistory.run.2 capacity 0) :
    NativeGoldBatchLifetimeSoundness.Failure Unit root ctx 0 (NativeGoldBatchLifetimeSoundness.clean nativePrelude) id
      (OracleMachinePrelude.prepend stopped) world :=
  NativeGoldBatchLifetimeSoundness.failure_rebase Unit root ctx 0 nativePrelude stopped world ⟨0,⟨witness falseClaim⟩⟩

example : {oracle | NativeGoldBatchLifetimeSoundness.Inherited Unit root ctx 0
    (NativeGoldBatchLifetimeSoundness.clean nativePrelude) id (OracleMachinePrelude.prepend stopped) oracle} = ∅ :=
  NativeGoldBatchLifetimeSoundness.inherited_clean Unit root ctx 0 nativePrelude (OracleMachinePrelude.prepend stopped)

-- All future batches/schedulers with these public parameters share this bound.
example : law {oracle | NativeGoldBatchLifetimeSoundness.Failure Unit root ctx 0 (run nativePrelude) id stopped oracle} ≤
    (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge root (.pure nativePrelude) (OracleMachinePrelude.prepend stopped) fuel) +
      NativeGoldBatchLifetimeSoundness.exposureCharge (NativeGoldBatchLifetimeSoundness.clean nativePrelude) id root ctx primitive 0
        (OracleMachinePrelude.prepend stopped) :=
  NativeGoldBatchLifetimeSoundness.prelude_bound Unit root ctx primitive ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchMeaningSmoke.constructed 0 (by decide +kernel) nativePrelude stopped Fintype.card_pos
    (by rw [BlockCode.minDist _ _ _ (by decide +kernel)]; decide +kernel)
example (other : World) (agrees : ObservationReplay.Agrees other oldHistory.run.2)
    (falseClaim : NativeGoldBatchCausalCoverage.FalseClaim root ctx primitive work decoded oldHistory.run.2 capacity 0) :
    Nonempty (NativeGoldBatchLifetimeSoundness.Witness Unit root ctx 0 other oldHistory.run.2) :=
  NativeGoldBatchLifetimeMeasurable.witness_replay Unit root ctx 0 world other oldHistory.run.2 agrees (witness falseClaim)

example {P S A : Type} (Memory : Type) {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (initial : P → S) (step : S → OracleMachine.Command S A) :
    MeasurableSet {oracle | NativeGoldBatchLifetimeSoundness.Failure Memory root ctx 0 past initial step oracle} :=
  NativeGoldBatchLifetimeMeasurable.failure_measurable Memory root ctx 0 replay initial step

end
end HasteBootsLifetimeSoundnessSmoke
