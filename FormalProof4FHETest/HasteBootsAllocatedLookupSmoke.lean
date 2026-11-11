module
import all FormalProof4FHE.HasteBoots.AllocatedLookupContext
import all FormalProof4FHE.HasteBoots.AllocatedLookupPublicOwnership
import all FormalProof4FHETest.HasteBootsHelperPublicSourceSmoke

namespace FormalProof4FHE.HasteBoots.AllocatedLookupSmoke
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open OracleProgram (run)
noncomputable section

def references : Vector Reference := ⟨[⟨1,fun _ => 0⟩,⟨0,fun _ => 1⟩,⟨1,fun _ => 0⟩],by decide⟩
def badReferences : Vector Reference := ⟨[⟨2,fun _ => 0⟩],by decide⟩

/-- info: true -/
#guard_msgs in
#eval match HelperPublicSourceSmoke.entries with
  | some (first::rest) =>
    match AllocatedLookupContext.assemble (first::rest) 0 references (HelperPublicSourceSmoke.executableTemplate first) with
    | some ctx => ctx.helper.queries.val == 544 && ctx.registry.val.map (fun oracle : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => oracle.parameters.queries.val) == [600,544,600] &&
        ctx.registry.val.map (fun oracle : NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored => (oracle.root 0).val) == [0,1,0] && ctx.fieldFuel == 18 && ctx.workerFuel == 6
    | none => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match HelperPublicSourceSmoke.entries with
  | some (first::rest) =>
    (AllocatedLookupContext.assemble (first::rest) 2 references (HelperPublicSourceSmoke.executableTemplate first)).isNone
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match HelperPublicSourceSmoke.entries with
  | some (first::rest) =>
    (AllocatedLookupContext.assemble (first::rest) 0 badReferences (HelperPublicSourceSmoke.executableTemplate first)).isNone
  | _ => false

/-- The original statement/proof, parent and fuels survive both projections. -/
example (entry : Entry) : (AllocatedLookupContext.assemble [entry] 0 ⟨[],by decide⟩ HasteBootsCallerAvailabilitySmoke.ctx).map
      (fun ctx => (ctx.requests,ctx.proof,ctx.parent,ctx.fieldFuel,ctx.workerFuel)) =
    some (HasteBootsCallerAvailabilitySmoke.ctx.requests,HasteBootsCallerAvailabilitySmoke.ctx.proof,
      HasteBootsCallerAvailabilitySmoke.ctx.parent,HasteBootsCallerAvailabilitySmoke.ctx.fieldFuel,HasteBootsCallerAvailabilitySmoke.ctx.workerFuel) := rfl

/-- Failed assembly cannot invoke either scheduler, including arbitrary
schedulers that would issue prequeries if called. -/
example (chooseHelper : NativeGoldPcsProgram.Scheduler Unit) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Unit)
    (world : InputIndexedOracle.World) :
    (run (AllocatedLookupExecution.program [] 0 ⟨[],by decide⟩ HasteBootsCallerAvailabilitySmoke.ctx chooseHelper chooseBatch ()) world).run =
      (.unavailable,[]) :=
  AllocatedLookupExecution.unavailable [] 0 ⟨[],by decide⟩ HasteBootsCallerAvailabilitySmoke.ctx chooseHelper chooseBatch () world
    (AllocatedLookupContext.missing_helper [] 0 _ _ rfl)

/-- A source-reference failure has the same empty observation behavior even
when the helper handle itself exists. -/
example (entry : Entry) (chooseHelper : NativeGoldPcsProgram.Scheduler Unit) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Unit)
    (world : InputIndexedOracle.World) :
    (run (AllocatedLookupExecution.program [entry] 0 badReferences HasteBootsCallerAvailabilitySmoke.ctx chooseHelper chooseBatch ()) world).run =
      (.unavailable,[]) :=
  AllocatedLookupExecution.unavailable [entry] 0 badReferences HasteBootsCallerAvailabilitySmoke.ctx chooseHelper chooseBatch () world
    (AllocatedLookupContext.missing_registry [entry] 0 badReferences _ rfl)

/-- Empty registry validation remains the original native prior outcome;
assembly success does not manufacture verifier acceptance. -/
example (entry : Entry) (world : InputIndexedOracle.World) :
    (run (AllocatedLookupExecution.program [entry] 0 ⟨[],by decide⟩ HasteBootsCallerAvailabilitySmoke.ctx
      HasteBootsCausalPcsSmoke.probe HasteBootsCallerAvailabilitySmoke.batchProbe ()) world).run.1 =
      .verification {HasteBootsCallerAvailabilitySmoke.ctx with registry := ⟨[],by decide⟩,helper := entry.initialized.parameters}
        ⟨(.prior (none,none),none),.prior⟩ := rfl

example (entry : Entry) (world : InputIndexedOracle.World) :
    (run (AllocatedLookupExecution.program [entry] 0 ⟨[],by decide⟩ HasteBootsCallerAvailabilitySmoke.ctx
      HasteBootsCausalPcsSmoke.probe HasteBootsCallerAvailabilitySmoke.batchProbe ()) world).run.2 = [] := rfl

end
end FormalProof4FHE.HasteBoots.AllocatedLookupSmoke
