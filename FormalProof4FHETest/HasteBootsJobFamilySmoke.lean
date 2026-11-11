module
import all FormalProof4FHE.HasteBoots.JobFamilyPosteriorMismatch
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke

namespace FormalProof4FHE.HasteBoots.JobFamilySmoke
open NativeLookupRequestWire (Request)
open NativePrefixCodec (Vector)
open NativeFields (Goldilocks)
open MatrixFold (Cube)
open HasteBootsRegistryAncestrySmoke (usize)
noncomputable section

def row : NativeLookupRequestWire.Row := ⟨[usize 0,usize 0,usize 0],by decide⟩
def firstRequest : Request := ⟨⟨usize 1,⟨[row],by decide⟩,usize 2⟩,⟨[usize 2,usize 1,usize 2],by decide⟩⟩
def secondRequest : Request := ⟨⟨usize 1,⟨[row],by decide⟩,usize 1⟩,⟨[usize 1,usize 0,usize 1],by decide⟩⟩
def requests : Vector Request := ⟨[firstRequest,secondRequest],by decide⟩

/-- Native tags retain request ordinal, repetition and the whole original
address sequence; repeated producer jobs are not deduplicated. -/
theorem original_tags : (OriginalJobOrdinal.requestTags requests).map
    (fun tag => (tag.ordinal.val,tag.repetition,tag.request.terminal.sourceSlots)) =
      [(0,0,[2,1,2]),(0,1,[2,1,2]),(1,0,[1,0,1])] := rfl

def slots : LookupOriginalSlots.Slots 3 firstRequest.toModel := ⟨![⟨2,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],rfl⟩

theorem original_addresses (candidate : LookupOriginalSlots.Slots 3 firstRequest.toModel)
    (leftColumn rightColumn : Fin firstRequest.toModel.columns) (ordinal : leftColumn.val = rightColumn.val) :
    (slots.slot leftColumn).val = (candidate.slot rightColumn).val :=
  OriginalJobOrdinal.slot_ordinal rfl rfl slots candidate leftColumn rightColumn ordinal

/-- Distinct original slots have distinct nonzero fourth-lane values. -/
def table (slot : Fin 3) : Cube 2 → Fin (3+1) → Goldilocks :=
  fun _ lane => if lane.val = 3 then slot.val+1 else 0

def sourceFamily (selector : LookupOriginalSlots.Slots 3 firstRequest.toModel) :
    Fin firstRequest.toModel.columns → Cube 2 → Fin (3+1) → Goldilocks := fun column => table (selector.slot column)

/-- Lifting corresponding columns retains repeated addresses and the entire
packed function, including its nonzero fourth lane. -/
theorem complete_sources (candidate : LookupOriginalSlots.Slots 3 firstRequest.toModel) :
    HEq (sourceFamily slots) (sourceFamily candidate) := by
  apply PackedFamilyReindex.family _ _ rfl rfl rfl
  intro leftColumn rightColumn ordinal
  have address : slots.slot leftColumn = candidate.slot rightColumn := Fin.ext (original_addresses candidate leftColumn rightColumn ordinal)
  change HEq (table (slots.slot leftColumn)) (table (candidate.slot rightColumn))
  rw [address]

theorem nonzero_padding : sourceFamily slots ⟨0,by decide⟩ (false,false,()) ⟨3,by decide⟩ = 3 ∧
    sourceFamily slots ⟨1,by decide⟩ (false,false,()) ⟨3,by decide⟩ = 2 ∧
    sourceFamily slots ⟨2,by decide⟩ = sourceFamily slots ⟨0,by decide⟩ := by
  refine ⟨?_,?_,rfl⟩ <;> decide +kernel

/-- Dependent row casts preserve the complete fourth-lane value. -/
theorem source_reindex :
    HEq (fun cell : Cube (1+1) => table ⟨2,by decide⟩ (cast (congrArg Cube (show 2 = 1+1 from rfl).symm) cell))
      (fun cell : Cube (2+0) => table ⟨2,by decide⟩ (cast (congrArg Cube (show 2 = 2+0 from rfl).symm) cell)) :=
  PackedFamilyReindex.table _ _ rfl rfl rfl rfl HEq.rfl

/-- The helper uses full scalar rows and three lanes while the sources use
two row bits and four lanes; the high helper bit is retained. -/
def helper : Cube (NativeScalarQueryShape.laneBits 4+2) → Fin 3 → Goldilocks :=
  fun cell _ => if cell.2.2.2.1 then 13 else 0

theorem helper_reindex :
    HEq (fun cell : Cube (2+2) => helper (cast (congrArg Cube (show NativeScalarQueryShape.laneBits 4+2 = 2+2 from rfl).symm) cell))
      (fun cell : Cube 4 => helper (cast (congrArg Cube (show NativeScalarQueryShape.laneBits 4+2 = 4 from rfl).symm) cell)) :=
  PackedFamilyReindex.table (leftPadding := 0) (rightPadding := 0) helper helper rfl rfl rfl rfl HEq.rfl

theorem helper_high_bit : helper (false,false,false,true,()) ⟨0,by decide⟩ = 13 := by decide +kernel

end
end FormalProof4FHE.HasteBoots.JobFamilySmoke
