module
import all FormalProof4FHE.HasteBoots.AdaptiveBatchFieldLifetime
import all FormalProof4FHETest.HasteBootsFieldInputSmoke
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke

namespace HasteBootsAdaptiveBatchFieldSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
noncomputable section

-- The parsed immediate batch binding names its context before parameter fixation.
theorem names_context : HasteBootsFieldInputSmoke.view.data.context ∈
    ContextDigestTargets.fromInput HasteBootsFieldInputSmoke.fieldInput :=
  BatchFieldContextName.context _ _ HasteBootsFieldInputSmoke.decoded

-- A zero-length earlier read and a same-key hash do not move the first
-- positive read. Its next prefix adds only the actual far-offset output.
theorem next_observation :
    (runPrefix 4 FactorFiberSmoke.program HasteBootsSamplerAncestrySmoke.worldZero).run.2 =
      (runPrefix 3 FactorFiberSmoke.program HasteBootsSamplerAncestrySmoke.worldZero).run.2 ++
        [NativeTranscript.Observation.output FactorFiberSmoke.input 999 [0]] :=
  ContextAtFirstRead.next_log FactorFiberSmoke.first

-- A completed packet cannot incur another field charge.
theorem completed_score (history : List NativeTranscript.Observation) :
    AdaptiveBatchFieldKernel.score (((.inr ()) : Program Unit ⊕ Unit),history) = 0 := rfl

end
end HasteBootsAdaptiveBatchFieldSmoke
