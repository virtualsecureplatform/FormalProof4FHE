module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchOpeningView
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke
open FormalProof4FHE.HasteBoots
open OracleProgram (run)
open NativeGoldBatchLinearEquations (Weights Word)
open NativeGoldBatchResponseMeaning (Lane)
namespace HasteBootsBatchOrderedSmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (usize zeros root prepared? prepared_get)

def ctx : NativeGoldBatchPcsProgram.Context :=
  {HasteBootsBatchMeaningSmoke.ctx with
    parameters := {HasteBootsBatchMeaningSmoke.ctx.parameters with queries := usize 3}
    opening := {HasteBootsBatchMeaningSmoke.ctx.opening with columns :=
      ⟨List.replicate 2 ⟨zeros 24 (by decide),⟨List.replicate 6 root,by decide⟩⟩,by decide⟩}}

def world : InputIndexedOracle.World
  | .inr _ => 0
  | .inl (input,offset) =>
    match (TranscriptFrame.decodeAll input).bind List.getLast? with
    | some frame => if frame.kind = 2 ∧ frame.label = NativeGoldBatchColumns.label then
        if offset % 8 = 0 then if offset / 8 = 1 then 1 else 7 else 0
      else 0
    | none => 0

def result := (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1
theorem present : (prepared? result).isSome = true := by decide +kernel
def work : NativeGoldBatchPcsProgram.Prepared := (prepared? result).get present

theorem prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work :=
  prepared_get result present

theorem constructed : NativeGoldBlockCode.build ctx.tables (usize 2) (usize 4) (usize 2) = .ok ctx.parameters.code := by decide +kernel

example : work.sample.draws = [7,1,7] := by decide +kernel
example : work.sample.indices = [1,7] := by decide +kernel
example : work.jobs.map NativeGoldColumnWorker.Job.index = [1,7] := by decide +kernel
example : work.jobs.length = 2 ∧ work.sample.draws.length = 3 := by decide +kernel
example : work.groups.length = 1 ∧ work.binding.queries.val.length = 2 := by decide +kernel

def draw : Fin ctx.parameters.queries.val → Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)) := ![7,1,7]
theorem typed : NativeGoldPcsDraws.typed (NativeGoldBlockCode.logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw := by decide +kernel
theorem ordered : (List.ofFn draw).map Fin.val = work.sample.draws := NativeGoldPcsDraws.typed_values _ _ _ _ typed

def requests := (NativeGoldBatchFamilyRequests.prepare root work).get (by decide +kernel)
theorem computed : NativeGoldBatchFamilyRequests.prepare root work = some requests := by
  exact (Option.some_get _).symm

example (index : Fin ctx.parameters.queries.val) : ∃ entry ∈ requests, entry.2.position.val = (draw index).val :=
  NativeGoldBatchDraws.draw_request ctx world work prepared root requests computed draw ordered index

-- Every native coordinate check at the two transported columns passes.
theorem checked : requests.all (fun entry => NativeGoldBatchColumnWorker.check work.geometry work.width work.random work.test
    entry.2.payload.val work.groups entry.2.position.val) = true := by decide +kernel

theorem payloads : requests.all (fun entry => decide (entry.2.payload.val = (zeros 24 (by decide)).val)) = true := by decide +kernel

theorem bounds : requests.all (fun entry => decide (entry.2.position.val < 2^(NativeGoldBlockCode.logSize ctx.parameters.code))) = true := by decide +kernel

theorem equations (entry : NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request NativeMerkleShapeFamily.height) (member : entry ∈ requests) :
    NativeGoldBatchRawAvailability.Equations (NativeGoldBatchRawAvailability.view work requests) (fun _ => 0) entry.2.position.val := by
  intro response responseMember
  have native := NativeGoldBatchColumnWorker.check_each _ _ _ _ _ _ _ (List.all_eq_true.mp checked entry member) response responseMember
  have equal := (NativeGoldColumnChecks.check_iff _ _ _ _ _ _ _ _).mp native
  rw [of_decide_eq_true (List.all_eq_true.mp payloads entry member)] at equal
  have zero_at (coordinate : ℕ) : NativeGoldColumnChecks.view (zeros 24 (by decide)).val coordinate = 0 :=
    congrFun HasteBootsBatchMeaningSmoke.zero_projection coordinate
  simpa +instances only [NativeGoldRawAvailability.Equations,NativeGoldBatchRawAvailability.view,zero_at] using equal

theorem all_agree : (∀ lane : Fin work.width, ColumnOpening.Agrees
    (StructuredOpening.combine (Weights work work.random lane) (Word ctx work (fun _ _ => 0))) (Lane ctx work work.test lane.val) draw) ∧
    ∀ response ∈ work.groups, ∀ lane : Fin work.width, ColumnOpening.Agrees
      (StructuredOpening.combine (Weights work response.1 lane) (Word ctx work (fun _ _ => 0))) (Lane ctx work response.2 lane.val) draw := by
  apply NativeGoldBatchOrderedChecks.requests_agree ctx world work prepared root requests computed draw ordered (fun _ _ => 0)
  intro entry member
  have bounded := of_decide_eq_true (List.all_eq_true.mp bounds entry member)
  exact ⟨bounded,NativeGoldBatchLinearEquations.column_equations ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed
    requests (fun _ _ => 0) ⟨entry.2.position.val,bounded⟩ (equations entry member)⟩
example : Fintype.card (NativeGoldBatchOpeningView.Test work) = 3 := by decide +kernel

example (test : NativeGoldBatchOpeningView.Test work) : NativeGoldBatchOpeningView.claim ctx work test ∈
    BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx HasteBootsBatchMeaningSmoke.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :=
  (NativeGoldBatchOpeningView.responses_coded ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed
    HasteBootsBatchMeaningSmoke.primitive).2 test

example (test : NativeGoldBatchOpeningView.Test work) : ColumnOpening.Agrees
    (StructuredOpening.combine (NativeGoldBatchOpeningView.weights work test) (Word ctx work (fun _ _ => 0)))
    (NativeGoldBatchOpeningView.claim ctx work test) draw :=
  all_agree.2 (work.groups.get test.1) (List.get_mem _ _) test.2

end
end HasteBootsBatchOrderedSmoke
