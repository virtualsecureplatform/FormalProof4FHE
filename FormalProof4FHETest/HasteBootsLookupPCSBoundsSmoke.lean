module
import all Batteries.Data.Except
import all Init.Data.String.Defs
import all FormalProof4FHE.HasteBoots.NativeTranscript
import FormalProof4FHE.HasteBoots.LookupPCSLayoutBounds
open FormalProof4FHE.HasteBoots
namespace HasteBootsLookupPCSBoundsSmoke
open NativeGoldBlockCode (Stored Tables description)
noncomputable section
def usize (n : ℕ) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide +kernel)⟩
def tables : Tables where
  generate log := decide (log = 5)
  initTable log := decide (log = 5)
  load log := if log = 5 then some ⟨549755813888,by decide +kernel⟩ else none

def code (width blocks : ℕ) : Stored :=
  ⟨usize 8,usize width,usize blocks,usize 32,NativeBrakedownContext.modulus,usize 549755813888⟩
def source : NativeBrakedownContext.Parameters Stored := ⟨usize 3,usize 4,usize 0,usize 1,code 4 2⟩
def helper : NativeBrakedownContext.Parameters Stored := ⟨usize 5,usize 3,usize 2,usize 1,code 3 4⟩
def sourceGeometry := NativeBrakedownParameters.geometry description source (by decide +kernel)
def helperGeometry := NativeBrakedownParameters.geometry description helper (by decide +kernel)
theorem source_built : NativeBrakedownParameters.build description source = some sourceGeometry :=
  NativeBrakedownParameters.build_complete description source (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem helper_built : NativeBrakedownParameters.build description helper = some helperGeometry :=
  NativeBrakedownParameters.build_complete description helper (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- Equal row message lengths require different padded coefficient counts at
-- source width four and compact helper width three. Both constructors run.
example : LookupPCSCodeCapacity.Spec source sourceGeometry :=
  LookupPCSCodeCapacity.code_spec tables (usize 8) (usize 2) source (by decide +kernel) sourceGeometry source_built
example : LookupPCSCodeCapacity.Spec helper helperGeometry :=
  LookupPCSCodeCapacity.code_spec tables (usize 8) (usize 2) helper (by decide +kernel) helperGeometry helper_built
example : source.code.messageBlocks.val = 2 ∧ helper.code.messageBlocks.val = 4 := by decide +kernel
example : ¬(8 ≤ source.code.messageBlocks.val * helper.width.val) := by decide +kernel
end
end HasteBootsLookupPCSBoundsSmoke
