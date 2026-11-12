module
import all FormalProof4FHE.HasteBoots.EqualityFamilyCandidate
import all FormalProof4FHETest.HasteBootsGoldEqualityPointSmoke

namespace HasteBootsEqualityFamilySmoke
open FormalProof4FHE.HasteBoots
open NativeExtensionFields (goldilocksBasis)
open NativePrefixCodec (Vector)
open NativeRootMessage (Digest)
open HasteBootsSamplerAncestrySmoke (child worldZero roots)
open HasteBootsGoldEqualityPointSmoke (equality)
noncomputable section

def originalRoots : Vector Digest := ⟨roots,by decide +kernel⟩

theorem first_reader_roots : HelperRootsView.parse
    (equality.draws[0]'(by decide +kernel)).coefficients.phase.pending.input = some originalRoots := by decide +kernel

theorem second_reader_roots : HelperRootsView.parse
    (equality.draws[1]'(by decide +kernel)).coefficients.phase.pending.input = some originalRoots := by decide +kernel

/-- An earlier roots frame is tolerated; the current ordered binder wins. -/
def decoyChild := NativeLookupEquality.bindRoots child [fun _ => 9] (by decide +kernel)
def repeatedRoots : Vector Digest := ⟨[fun _ => 7,fun _ => 7],by decide +kernel⟩
def repeated := (NativeLookupEquality.execute goldilocksBasis 7 4
  (NativeLookupEquality.initial 0 decoyChild repeatedRoots.val repeatedRoots.property) worldZero).1

theorem repeated_jobs_preserved : repeated.draws.length = 2 ∧ repeated.remaining = 0 := by decide +kernel

theorem decoy_does_not_replace_roots : HelperRootsView.parse
    (repeated.draws[1]'(by decide +kernel)).coefficients.phase.pending.input = some repeatedRoots := by decide +kernel

theorem duplicate_roots_still_named : (fun _ => 7 : Digest) ∈ NativeParentLedger.roots
    (repeated.draws[1]'(by decide +kernel)).coefficients.phase.pending.input :=
  EqualityInputFamilyView.parsed_root _ repeatedRoots decoy_does_not_replace_roots _ (by simp [repeatedRoots])

end
end HasteBootsEqualityFamilySmoke
