module
import all FormalProof4FHE.HasteBoots.AllocatedLookupTables
import all FormalProof4FHETest.HasteBootsAllocatedLookupSmoke
import all FormalProof4FHETest.HasteBootsScalarFinishAncestrySmoke

namespace FormalProof4FHE.HasteBoots.LookupExecutionSmoke
open NativePrefixCodec (Vector)
open NativeFieldRepresentation (GoldWord)
open HasteBootsScalarFinishAncestrySmoke (usize)
noncomputable section

def wire : NativeLookupRequestWire.Request :=
  ⟨⟨usize 3,⟨[⟨[usize 0,usize 0,usize 0],by decide⟩],by decide⟩,usize 1⟩,⟨[usize 1,usize 0,usize 1],by decide⟩⟩
def request := wire.toModel
local instance : NeZero request.columns := ⟨by decide +kernel⟩
def requests : Vector NativeLookupRequestWire.Request := ⟨[wire],by decide⟩
def source : NativeLookupBindGeometry.Parameters := ⟨usize 0,usize 4⟩
def registry := [source,source,source]
def helper : NativeLookupBindGeometry.Parameters := ⟨usize 2,usize 3⟩
def preflight? := NativeSharedLookupPreflight.preflight registry helper [request]
theorem preflightPresent : preflight?.isSome = true := by decide +kernel
def geometry := preflight?.get preflightPresent
theorem preflight : NativeSharedLookupPreflight.preflight registry helper [request] = some geometry := (Option.some_get preflightPresent).symm

def slots : LookupOriginalSlots.Slots registry.length request := Classical.choice
  (LookupOriginalSlots.recover registry helper [request] geometry preflight request List.mem_cons_self)

/-- Repeated original addresses are retained, while the third registry slot
is unused. The typed addresses follow from operational preflight recovery. -/
theorem addresses : (slots.slot 0).val = 1 ∧ (slots.slot 1).val = 0 ∧ (slots.slot 2).val = 1 := by
  have ordered : List.ofFn (fun i : Fin 3 => (slots.slot i).val) = [1,0,1] := slots.ordered
  have valuesEq : [(slots.slot 0).val,(slots.slot 1).val,(slots.slot 2).val] = [1,0,1] := by
    simp only [List.ofFn_succ,List.ofFn_zero] at ordered
    exact ordered
  have first := List.cons.inj valuesEq
  have second := List.cons.inj first.2
  have third := List.cons.inj second.2
  exact ⟨first.1,second.1,third.1⟩

theorem aliases : slots.slot 0 = slots.slot 2 := Fin.ext (addresses.1.trans addresses.2.2.symm)

def values : List (List GoldWord) := [List.replicate 4 (usize 10),List.replicate 4 (usize 20),List.replicate 4 (usize 30)]
def copies : List (List GoldWord) := [List.replicate 4 (usize 20),List.replicate 4 (usize 10),List.replicate 4 (usize 20)]
def inputs (column : Fin 3) (_ : Fin 4) : GoldWord := ![usize 20,usize 10,usize 20] column

theorem gathered : NativeSharedLookupGuard.gather values request.terminal.sourceSlots = some copies := by decide +kernel

theorem original_rows (column : Fin 3) : values[(slots.slot column).val]? = some (List.ofFn (inputs column)) :=
  slots.opening values copies inputs (by decide +kernel) (NativeSharedLookupGuard.gather_related values _ copies gathered) column

theorem all_used (column : Fin 3) : NativeSharedSourceClaims.used requests (slots.slot column) = true :=
  slots.used requests (by change request ∈ [request]; exact List.mem_cons_self) column

/-- Helper width three stays independent of source packing width four. -/
example : geometry.geometry.1.val = 2 ∧ geometry.geometry.2.val = 4 ∧ helper.width.val = 3 := by decide +kernel

/-- A malformed original address is rejected before any source is gathered. -/
example : NativeSharedLookupPreflight.preflight registry helper
    [{request with terminal := ⟨[1,3,1],usize 3⟩}] = none := by decide +kernel

/-- Even an unused registry entry must satisfy native uniformity. -/
example : NativeSharedLookupPreflight.preflight [source,source,⟨usize 1,usize 4⟩] helper [request] = none := by decide +kernel

/-- Raw count mismatch is an actual preflight rejection. -/
example : NativeSharedLookupPreflight.preflight registry helper [{request with columns := 2}] = none := by decide +kernel

end
end FormalProof4FHE.HasteBoots.LookupExecutionSmoke
