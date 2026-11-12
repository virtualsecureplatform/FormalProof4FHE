module
import all FormalProof4FHE.HasteBoots.EqualityFactorCandidate
import all FormalProof4FHETest.HasteBootsEqualityFamilySmoke

namespace HasteBootsEqualityFactorSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsSamplerAncestrySmoke (child)
open HasteBootsGoldEqualityPointSmoke (equality)
open HasteBootsEqualityFamilySmoke (originalRoots decoyChild repeatedRoots repeated)
noncomputable section

def before (state : NativeTranscript.Transcript) := (TranscriptFrame.decodeAll state.input).getD []

theorem first_original_boundary : HelperRootsBoundary.parse
    (equality.draws[0]'(by decide +kernel)).coefficients.phase.pending.input = some (originalRoots,before child) := by decide +kernel

/-- A completed earlier equality receipt is excluded from the recovered
lookup transcript; the second reader has the same original boundary. -/
theorem second_original_boundary : HelperRootsBoundary.parse
    (equality.draws[1]'(by decide +kernel)).coefficients.phase.pending.input = some (originalRoots,before child) := by decide +kernel

theorem latest_binder_boundary : HelperRootsBoundary.parse
    (repeated.draws[1]'(by decide +kernel)).coefficients.phase.pending.input = some (repeatedRoots,before decoyChild) := by decide +kernel

def bound := NativeLookupEquality.bindRoots child originalRoots.val originalRoots.property

theorem malformed_latest_rejected : HelperRootsBoundary.parse
    (NativeTranscript.appendBytes bound NativeLookupEquality.rootsLabel []).input = none := by decide +kernel

/-- Same label with the receipt kind is not a new roots binder. -/
theorem receipt_kind_not_binder : HelperRootsBoundary.parse
    (NativeTranscript.absorb bound 5 NativeLookupEquality.rootsLabel []).input = some (originalRoots,before child) := by decide +kernel

end
end HasteBootsEqualityFactorSmoke
