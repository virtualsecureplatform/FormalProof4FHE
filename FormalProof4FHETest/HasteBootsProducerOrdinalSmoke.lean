module
import all FormalProof4FHE.HasteBoots.OriginalLookupFactorSamples
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke
import all FormalProof4FHETest.HasteBootsLookupNativeTerminalSmoke

namespace FormalProof4FHE.HasteBoots.ProducerOrdinalSmoke
open HasteBootsSamplerAncestrySmoke (basis child worldOne actions batch)
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

/-- A zero-repetition request does not renumber later original ordinals. -/
example : LookupScheduleKeys.keys ![2,0,3] = [(0,0),(0,1),(2,0),(2,1),(2,2)] := by decide +kernel

/-- Keys remain unique when requests have many repetitions or none. -/
example : (LookupScheduleKeys.keys ![2,0,3]).Nodup := LookupScheduleKeys.keys_nodup _

/-- The actual batch uses two identical request payloads. Address keys,
not challenge values or table equality, identify its second record. -/
example (entry : NativeLookupBatch.Completed 17 (ZMod 17)) (member : entry ∈ batch.completed)
    (address : LookupScheduleKeys.jobKey entry.job = (1,0)) : batch.completed[1]? = some entry := by
  apply LookupScheduleKeys.get_of_key batch.completed (fun entry => LookupScheduleKeys.jobKey entry.job)
    (by decide +kernel) 1 entry member
  rw [address]
  decide +kernel

/-- Literal raw production supplies both endpoint getters and exact decoders
without a caller-provided sampled-value or successful-decoder certificate. -/
example : ∃ first last : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3,
    LookupNativeTerminalSmoke.selection.draws.head? = some first ∧
    LookupNativeTerminalSmoke.selection.draws.getLast? = some last ∧
    NativeGoldLookupProducer.decode first.coefficients.values = some LookupNativeTerminalSmoke.output.y ∧
    NativeGoldLookupProducer.decode last.coefficients.values = some LookupNativeTerminalSmoke.output.r :=
  LookupProducedEndpoints.draws 2 [] _ _ LookupNativeTerminalSmoke.produced

/-- An absent repetition cannot be recovered as a fabricated position. -/
example : (2,3) ∉ LookupScheduleKeys.keys ![2,0,3] := by decide +kernel

end
end FormalProof4FHE.HasteBoots.ProducerOrdinalSmoke
