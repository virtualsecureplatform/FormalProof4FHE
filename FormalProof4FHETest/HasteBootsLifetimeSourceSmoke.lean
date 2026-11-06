module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSourceRisk
import all FormalProof4FHETest.HasteBootsObservedSourceSmoke
open FormalProof4FHE.HasteBoots
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open OracleSpec OracleComp
namespace HasteBootsLifetimeSourceSmoke
noncomputable section
open HasteBootsBatchExposureSmoke (input)
def dummy : Digest := fun _ => 0
def world : World := fun _ => 0
def prelude : OracleProgram.Program ℕ := .read input 7 1 (fun _ => .pure 0)
-- The machine never finishes. After two hashes it repeatedly reads one cached byte.
def step (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 0 then .hash [1] (fun _ => state+1)
  else if state = 1 then .hash [2] (fun _ => state+1)
  else .read input 7 1 (fun _ => state+1)
def history (fuel : ℕ) := (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2
def state (fuel : ℕ) := NativeRootFamilyHistory.reconstruct NativeGoldColumnAuthentication.encoding dummy (history fuel)

example : (run (NativeRootFamilyLifetime.program prelude step 0) world).run.1 = .inl 0 := by decide +kernel
example : (run (NativeRootFamilyLifetime.program prelude step 12) world).run.1 = .inl 12 := by decide +kernel
example : (history 0).length = 1 := by decide +kernel
example : history 2 = [.output input 7 [0],.hash [1] (List.replicate 64 0),.hash [2] (List.replicate 64 0)] := by decide +kernel
example : (JointHashCache.project (history 12)).keys.card = 2 := by decide +kernel
example : (state 12).1.2 (input,7) = some 0 := by decide +kernel
example : (state 12).2.checkpoints.checkpoints.length = 64 := by decide +kernel
example : ((state 12).2.checkpoints.checkpoints.all (fun checkpoint => checkpoint.2.cumulativeLog.isEmpty)) = true := by decide +kernel

theorem collision_at_two : CacheHasCollision (JointHashCache.project (history 2)).cache := by
  exact ⟨[1],[2],dummy,dummy,by decide +kernel,by decide +kernel,by decide +kernel,HEq.rfl⟩

theorem bad_at_two : NativeRootFamilyLifetime.Bad dummy (history 2) := by
  apply Or.inr
  rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
  exact collision_at_two

example (fuel : ℕ) (bounded : 2 ≤ fuel) : NativeRootFamilyLifetime.Bad dummy (history fuel) :=
  NativeRootFamilyAudit.bad_persistent dummy world _ _ ((OracleProgram.run_replay _).truthful world)
    (NativeRootFamilyLifetime.log_prefix prelude step 2 fuel bounded world) bad_at_two

example : MeasurableSet {world | NativeGoldBatchLifetimeSourceRisk.Failure Unit dummy prelude step world} :=
  NativeGoldBatchLifetimeSourceRisk.failure_measurable Unit dummy prelude step
-- The source tag follows the actual context hash, including a changed oracle world.
def actualContext (oracle : World) := HasteBootsBatchPcsSmoke.Accepted.context.map (fun ctx =>
  (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) oracle).run.1)
example : actualContext HasteBootsBatchPcsSmoke.Accepted.world = some (some HasteBootsSourceGroupsSmoke.nativeDigest) := by decide +kernel
example : actualContext world = some (some dummy) := by decide +kernel
example : actualContext world ≠ actualContext HasteBootsBatchPcsSmoke.Accepted.world := by decide +kernel

end
end HasteBootsLifetimeSourceSmoke
