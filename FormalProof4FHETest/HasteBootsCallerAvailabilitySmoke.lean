module
import all FormalProof4FHE.HasteBoots.NativeCallerLookupLifetimeAvailability
import all FormalProof4FHETest.HasteBootsCausalPcsSmoke
import all FormalProof4FHETest.HasteBootsLifetimeSourceSmoke
open FormalProof4FHE.HasteBoots
open OracleProgram (run)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
namespace HasteBootsCallerAvailabilitySmoke
noncomputable section
open HasteBootsCausalPcsSmoke (emptyProof probe)

def proof : NativeSharedLookupProofData.Proof NativeGoldPcsOpening.Opening (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening) :=
  ⟨emptyProof.multiplicities,emptyProof.roots,emptyProof.algebra,emptyProof.sources,emptyProof.helpers,⟨[],by decide⟩,emptyProof.helperOpenings⟩
def ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening) :=
  ⟨NativePcsClaimSmoke.blockTables,⟨[],by decide⟩,NativePcsClaimSmoke.retainedParameters,NativePcsClaimSmoke.parent,
    ⟨[],by decide⟩,proof,18,18,18,18,6⟩
def batchProbe : NativeGoldBatchPcsProgram.Scheduler Unit := fun _ _ _ => .hash [254] (fun _ => .pure (none,()))

theorem prior (world : World) :
    (run (NativeGoldLookupVerification.program ctx probe batchProbe ()) world).run.1.phase = .prior := rfl

example (world : World) : (run (NativeGoldLookupVerification.program ctx probe batchProbe ()) world).run.2 = [] := rfl

-- Neither scheduler runs before the original empty-registry gate. There can
-- be no receipt-source failure in any containing history, regardless of its world.
example (dummy : Digest) (history : List NativeTranscript.Observation) (world : World) :
    ¬NativeCallerLookupAvailability.Failure dummy ctx probe batchProbe () history world := by
  rintro ⟨prepared,progress,result,receipt,executed,_⟩
  rw [prior world] at executed
  contradiction

example (dummy : Digest) : MeasurableSet {world |
    NativeCallerLookupAvailability.Failure dummy ctx probe batchProbe ()
      (run (NativeGoldLookupVerification.program ctx probe batchProbe ()) world).run.2 world} :=
  NativeCallerLookupAvailability.failure_measurable dummy ctx probe batchProbe ()

open HasteBootsLifetimeSourceSmoke (dummy prelude step)
example : MeasurableSet {world |
    NativeCallerLookupLifetimeAvailability.LifetimeFailure Unit dummy prelude step world} :=
  NativeCallerLookupLifetimeAvailability.lifetime_failure_measurable Unit dummy prelude step

example : InputIndexedOracle.law {world |
    NativeCallerLookupLifetimeAvailability.LifetimeFailure Unit dummy prelude step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy prelude step fuel :=
  NativeCallerLookupLifetimeAvailability.lifetime_failure_le_charge Unit dummy prelude step

-- The surrounding causal machine can retain its residual state at long prefixes.
example : (run (NativeRootFamilyLifetime.program prelude step 37) HasteBootsLifetimeSourceSmoke.world).run.1 = .inl 37 := by decide +kernel
end
end HasteBootsCallerAvailabilitySmoke
