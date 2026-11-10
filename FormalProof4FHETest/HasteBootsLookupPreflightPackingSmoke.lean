module
import FormalProof4FHE.HasteBoots.LookupPreflightPCSGeometry
open FormalProof4FHE.HasteBoots
namespace HasteBootsLookupPreflightPackingSmoke
open NativeUsizeMessage (Usize)
def usize (n : ℕ) : Usize := ⟨n % 2^64, Nat.mod_lt _ (by decide +kernel)⟩
def source : NativeLookupBindGeometry.Parameters := ⟨usize 1,usize 4⟩
def helper (width : ℕ) : NativeLookupBindGeometry.Parameters := ⟨usize 3,usize width⟩
def requests : List NativeSharedLookupStatement.Request :=
  [⟨2,[[0,0]],1,⟨[0,1],usize 5⟩⟩,⟨1,[[0]],3,⟨[1],usize 8⟩⟩]

-- Compact and full-width helpers are both legal at the same original source
-- geometry, with request-specific active lengths and repetition counts.
example : (NativeSharedLookupPreflight.preflight [source,source] (helper 3) requests).map
    (LookupPreflightPacking.packing (helper 3)) = some ⟨1,0,2,1⟩ := by decide +kernel
example : (NativeSharedLookupPreflight.preflight [source,source] (helper 4) requests).map
    (LookupPreflightPacking.packing (helper 4)) = some ⟨1,1,2,1⟩ := by decide +kernel
example : (NativeSharedLookupPreflight.preflight [source,source] (helper 3) requests).map
    (fun output => output.repetitions.val) = some 4 := by decide +kernel

-- Neither an undersized helper nor a changed source shape is admitted.
example : (NativeSharedLookupPreflight.preflight [source,source] (helper 2) requests).isNone = true := by decide +kernel
example : (NativeSharedLookupPreflight.preflight [source,⟨usize 2,usize 4⟩] (helper 3) requests).isNone = true := by decide +kernel
example : (NativeSharedLookupPreflight.preflight [source,source] ⟨usize 2,usize 3⟩ requests).isNone = true := by decide +kernel
end HasteBootsLookupPreflightPackingSmoke
