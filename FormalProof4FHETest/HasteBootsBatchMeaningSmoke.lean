module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchLinearEquations
import all FormalProof4FHE.HasteBoots.NTTRootCheck
import all FormalProof4FHETest.HasteBootsBatchPcsSmoke
open FormalProof4FHE.HasteBoots
open NativeFieldRepresentation (GoldWord goldValue)
open NativeGoldBlockCode (build logSize)
open OracleProgram (run)
namespace HasteBootsBatchMeaningSmoke
noncomputable section

def usize (n : ℕ) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide)⟩
def zeros (n : ℕ) (fits : n < 2^64) : NativeLookupRequestWire.Row := ⟨List.replicate n 0,by simpa using fits⟩
def code : NativeGoldBlockCode.Stored := ⟨usize 2,usize 4,usize 1,usize 32,NativeBrakedownContext.modulus,usize 549755813888⟩
def matrix : NativeGoldPcsWire.Matrix := ⟨usize 3,zeros 9 (by decide)⟩
def query : NativeGoldPcsWire.Query := ⟨[(matrix,matrix),(matrix,matrix)],by decide⟩
def identity : NativeGoldPcsWire.Matrix := ⟨usize 3,⟨[1,0,0,0,1,0,0,0,1],by decide⟩⟩
def secondQuery : NativeGoldPcsWire.Query := ⟨[(matrix,matrix),(identity,identity)],by decide⟩
def root : NativeRootMessage.Digest := fun _ => 0
def ctx : NativeGoldBatchPcsProgram.Context :=
  ⟨NativePcsClaimSmoke.blockTables,⟨usize 2,usize 3,usize 1,usize 1,code⟩,
    NativeTranscript.new [] root,root,⟨[query,secondQuery],by decide⟩,⟨[zeros 3 (by decide),zeros 3 (by decide)],by decide⟩,
    ⟨zeros 6 (by decide),⟨[zeros 6 (by decide)],by decide⟩,
      ⟨[⟨zeros 24 (by decide),⟨List.replicate 6 root,by decide⟩⟩],by decide⟩⟩,18⟩
def world : InputIndexedOracle.World := fun _ => 0

theorem constructed : build ctx.tables (usize 2) (usize 4) (usize 2) = .ok ctx.parameters.code := by decide +kernel

theorem primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)) := by
  apply NTTRootCheck.primitive_of_half_power 5 _ NativeFields.goldilocks_odd
  decide +kernel

def prepared? : NativeGoldBatchPcsProgram.PrefixOutcome → Option NativeGoldBatchPcsProgram.Prepared
  | .prepared work => some work
  | _ => none

theorem prepared_get (outcome : NativeGoldBatchPcsProgram.PrefixOutcome) (known : (prepared? outcome).isSome = true) :
    outcome = .prepared ((prepared? outcome).get known) := by
  cases outcome with
  | prior previous => contradiction
  | encodingUnavailable => contradiction
  | pairingUnavailable => contradiction
  | prepared actual => rfl

def result := (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1
theorem present : (prepared? result).isSome = true := by decide +kernel
def work : NativeGoldBatchPcsProgram.Prepared := (prepared? result).get present

theorem prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work := by
  exact prepared_get result present

-- This actual prefix has three test rows and four code coordinates.
example : work.width = 3 ∧ work.geometry.blockWidth = 4 := by decide +kernel
example : work.evaluations.length = 1 ∧ work.groups.length = 1 ∧ work.binding.queries.val.length = 2 := by decide +kernel
example : work.test.length = 3*(32*4) := by decide +kernel
example : work.sample.draws = [0] ∧ work.sample.indices = [0] := by decide +kernel

example (lane : Fin work.width) : NativeGoldBatchResponseMeaning.Lane ctx work work.test lane.val ∈
    BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :=
  (NativeGoldBatchResponseMeaning.prepared_test ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed primitive lane.val lane.isLt).2

example (response : NativeGoldBatchColumnWorker.Response) (member : response ∈ work.groups) (lane : Fin work.width) :
    NativeGoldBatchResponseMeaning.Lane ctx work response.2 lane.val ∈
      BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :=
  NativeGoldBatchResponseMeaning.prepared_groups ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed primitive response member lane.val lane.isLt

example : work.geometry.blocks = 32 ∧ work.geometry.stride = 128 ∧ work.geometry.height = 5 := by
  have layout := NativeGoldBatchResponseMeaning.prepared_layout ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed
  exact ⟨layout.1,layout.2.2.1,layout.2.2.2⟩
theorem checked_groups : work.groups.all (fun response => NativeGoldColumnChecks.check work.geometry work.width work.random response.1
    work.test response.2 (zeros 24 (by decide)).val 0) = true := by decide +kernel

theorem zero_projection : (fun coordinate => NativeGoldColumnChecks.view (zeros 24 (by decide)).val coordinate) =
    (fun _ => (0 : NativeFields.Goldilocks)) := by
  funext coordinate
  simp only [NativeGoldColumnChecks.view,zeros,List.getElem?_replicate]
  split <;> rfl

theorem zero_equations : NativeGoldBatchRawAvailability.Equations
    (NativeGoldBatchRawAvailability.view work ([] : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request (fun _ : Unit => 0))))
    (fun _ => 0) 0 := by
  intro response member
  have equal := (NativeGoldColumnChecks.check_iff _ _ _ _ _ _ _ _).mp (List.all_eq_true.mp checked_groups response member)
  have zero_at (coordinate : ℕ) : NativeGoldColumnChecks.view (zeros 24 (by decide)).val coordinate = 0 := congrFun zero_projection coordinate
  simpa +instances only [NativeGoldRawAvailability.Equations,NativeGoldBatchRawAvailability.view,zero_at] using equal

example : ∀ response ∈ work.groups, ∀ lane : Fin work.width,
    StructuredOpening.combine (NativeGoldBatchLinearEquations.Weights work work.random lane)
      (NativeGoldBatchLinearEquations.Word ctx work (fun _ _ => 0)) ⟨0,by decide⟩ =
      NativeGoldBatchResponseMeaning.Lane ctx work work.test lane.val ⟨0,by decide⟩ ∧
    StructuredOpening.combine (NativeGoldBatchLinearEquations.Weights work response.1 lane)
      (NativeGoldBatchLinearEquations.Word ctx work (fun _ _ => 0)) ⟨0,by decide⟩ =
      NativeGoldBatchResponseMeaning.Lane ctx work response.2 lane.val ⟨0,by decide⟩ :=
  NativeGoldBatchLinearEquations.column_equations ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed _ _ _ zero_equations

-- A changed returned coordinate fails at the shared sampled column.
example : NativeGoldBatchColumnWorker.check work.geometry work.width work.random (1 :: work.test.drop 1)
    (zeros 24 (by decide)).val work.groups 0 = false := by decide +kernel

namespace Captured
-- Nonzero response bytes and the program inputs come from the existing native fixture.
def ctx := HasteBootsBatchPcsSmoke.Accepted.context.get (by decide +kernel)
def world := HasteBootsBatchPcsSmoke.Accepted.world
def result := (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1
theorem present : (prepared? result).isSome = true := by decide +kernel
def work : NativeGoldBatchPcsProgram.Prepared := (prepared? result).get present

theorem prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work := by
  exact prepared_get result present

theorem constructed : build ctx.tables (usize 2) (usize 2) (usize 2) = .ok ctx.parameters.code := by decide +kernel

theorem primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)) := by
  apply NTTRootCheck.primitive_of_half_power 5 _ NativeFields.goldilocks_odd
  decide +kernel

example : work.test.any (fun value => decide (goldValue value ≠ 0)) = true := by decide +kernel
example : work.width = 1 ∧ ctx.parameters.code.blockWidth.val = 2 := by decide +kernel
example (lane : Fin work.width) : NativeGoldBatchResponseMeaning.Lane ctx work work.test lane.val ∈
    BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :=
  (NativeGoldBatchResponseMeaning.prepared_test ctx world work prepared ctx.tables (usize 2) (usize 2) (usize 2) constructed primitive lane.val lane.isLt).2
end Captured

end
end HasteBootsBatchMeaningSmoke
