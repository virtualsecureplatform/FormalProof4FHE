module
import all FormalProof4FHE.HasteBoots.NativeGoldHelperFraming
import all FormalProof4FHETest.HasteBootsCausalPcsSmoke
open FormalProof4FHE.HasteBoots
open NativeTranscriptFraming (Framed)
namespace HasteBootsHelperFramingSmoke
noncomputable section
open HasteBootsCausalPcsSmoke
open NativePcsClaimSmoke (parent blockTables retainedParameters)

local instance (call : NativeSharedLookupHelpers.Call NativeGoldPcsOpening.Opening) :
    Decidable (NativeGoldHelperFraming.CallFits call) := by
  unfold NativeGoldHelperFraming.CallFits
  infer_instance

theorem calls_fit : NativeGoldHelperFraming.Domain calls := by
  intro call member
  have fits : calls.all (fun call => decide (NativeGoldHelperFraming.CallFits call)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp fits call member)

theorem parent_framed : Framed parent := by
  rw [NativeTranscriptFraming.framed_iff_decode]
  decide +kernel

example : Framed (helpers 6 false).1.progress.lastAccepted :=
  NativeGoldHelperFraming.loop_framed blockTables retainedParameters 18 (select false) 6 calls ⟨parent,(),[]⟩
    NativePcsClaimSmoke.Canonical.world parent_framed calls_fit

example : Framed (helpers 5 false).1.progress.lastAccepted :=
  NativeGoldHelperFraming.loop_framed blockTables retainedParameters 18 (select false) 5 calls ⟨parent,(),[]⟩
    NativePcsClaimSmoke.Canonical.world parent_framed calls_fit

example : Framed (helpers 6 true).1.progress.lastAccepted :=
  NativeGoldHelperFraming.loop_framed blockTables retainedParameters 18 (select true) 6 calls ⟨parent,(),[]⟩
    NativePcsClaimSmoke.Canonical.world parent_framed calls_fit

example : Framed repeated.1.progress.lastAccepted := by
  apply NativeGoldHelperFraming.loop_framed blockTables retainedParameters 18 (select false) 6 (calls ++ calls) ⟨parent,(),[]⟩
    NativePcsClaimSmoke.Canonical.world parent_framed
  intro call member
  rcases List.mem_append.mp member with first | second
  · exact calls_fit call first
  · exact calls_fit call second

example : NativeGoldHelperFraming.Domain [] := by intro call member; contradiction
end
end HasteBootsHelperFramingSmoke
