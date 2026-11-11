module
import all FormalProof4FHE.HasteBoots.CanonicalAllocatedJobWork
import all FormalProof4FHETest.HasteBootsBatchOrderedSmoke

namespace HasteBootsCanonicalRadiusSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsBatchMeaningSmoke (usize)
open HasteBootsBatchOrderedSmoke (ctx)
noncomputable section

-- Two genuine constructors on the same domain may require different
-- decoding radii because their original message dimensions differ.
def larger : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored :=
  {ctx.parameters with code := {ctx.parameters.code with messageLength := usize 16, messageBlocks := usize 4}}

theorem larger_constructed : NativeGoldBlockCode.build ctx.tables (usize 16) (usize 4) (usize 2) = .ok larger.code := by decide +kernel

theorem same_domain : ctx.parameters.code.blocks = larger.code.blocks := rfl

theorem different_radii : ParameterDecodingRadius.ofParameters ctx.parameters = 10 ∧
    ParameterDecodingRadius.ofParameters larger = 9 := by decide +kernel

-- The actual calibrated source/helper roles do not share one radius.
theorem role_radii_differ : NativeBrakedownCalibration.radius .goldilocks .source ≠
    NativeBrakedownCalibration.radius .goldilocks .helper := by decide +kernel

-- Changing a query quota does not select another source decoder.
theorem quota_keeps_radius : ParameterDecodingRadius.ofParameters {ctx.parameters with queries := usize 544} =
    ParameterDecodingRadius.ofParameters ctx.parameters := rfl

end
end HasteBootsCanonicalRadiusSmoke
