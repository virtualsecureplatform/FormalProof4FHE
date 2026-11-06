module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFinishingMeaning
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke
open FormalProof4FHE.HasteBoots
open NativeFieldRepresentation (GoldWord goldValue)
open OracleProgram (run)
namespace HasteBootsNativeFinishingSmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (ctx world usize constructed primitive)

abbrev Packet := Sigma (fun work : NativeGoldBatchPcsProgram.Prepared => NativeGoldBatchPcsProgram.Completion Unit work.jobs.length)
def completed? : NativeGoldBatchPcsProgram.Outcome Unit → Option Packet
  | .completed work completion => some ⟨work,completion⟩
  | _ => none

theorem completed_spec (outcome : NativeGoldBatchPcsProgram.Outcome Unit) (known : (completed? outcome).isSome = true) :
    outcome = .completed ((completed? outcome).get known).1 ((completed? outcome).get known).2 := by
  cases outcome with
  | prior previous => contradiction
  | completed work completion => rfl

def parent? : NativeGoldBatchPcsProgram.Status → Option NativeTranscript.Transcript
  | .accepted parent => some parent
  | _ => none

theorem parent_spec (status : NativeGoldBatchPcsProgram.Status) (known : (parent? status).isSome = true) :
    status = .accepted ((parent? status).get known) := by
  cases status with
  | accepted parent => rfl
  | columns => contradiction
  | claim reason => contradiction
  | suspended => contradiction

def choose := HasteBootsBatchPcsSmoke.choose false
def result := (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.1
def packet : Packet := (completed? result).get (by decide +kernel)
def work := packet.1
def completion := packet.2
def parent := (parent? completion.status).get (by decide +kernel)

theorem executed : (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.1 = .completed work completion := completed_spec _ _
theorem accepted : completion.status = .accepted parent := parent_spec _ _

example : work.width = 3 ∧ ctx.parameters.code.blockWidth.val = 4 ∧ work.binding.queries.val.length = 2 ∧ work.evaluations.length = 1 := by decide +kernel

example (index : Fin work.binding.queries.val.length) :
    ∃ (claimed : NativeLookupRequestWire.Row) (group : Fin work.evaluations.length)
      (size : (work.binding.queries.val.get index).models.length = ctx.parameters.numVariables.val)
      (shape : (NativeGoldBlockCode.encoding ctx.parameters.code work.planRoot).messageLength = 2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)),
      group.val = (NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val ∧
      work.binding.values.val[index.val]? = some claimed ∧
      claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishEncoded
        (NTTButterfly.domain (NativeGoldBlockCode.logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) primitive)
        (NativeGoldBlockCodeMeaning.constructor_dimensions ctx.tables (usize 2) (usize 4) (usize 2) ctx.parameters.code constructed).2.2.1
        (NativeGoldSuffixFinishing.encodedRight ctx.parameters (work.binding.queries.val.get index) (NativeGoldBlockCode.encoding ctx.parameters.code work.planRoot) size shape)
        (fun lane => NativeGoldResponseMeaning.laneWord (NativeGoldBlockCode.encoding ctx.parameters.code work.planRoot) (work.evaluations.get group) lane.val)) := by
  obtain ⟨response,claimed,group,size,shape,groupEq,_,claimRead,value⟩ := NativeGoldBatchFinishingMeaning.accepted_value ctx choose 6 () world work completion executed parent accepted
    ctx.tables (usize 2) (usize 4) (usize 2) constructed primitive index
  exact ⟨claimed,group,size,shape,groupEq,claimRead,value⟩

-- Lazy representatives are normalized only after the original lane/chunk is fixed.
def code := NativeGoldBlockCode.encoding ctx.parameters.code work.planRoot
local instance : NeZero code.blockWidth := ⟨by decide +kernel⟩
def raw : List GoldWord := [usize (NativeFields.goldilocksModulus+1),2,usize NativeFields.goldilocksModulus,5,7,8]
def encoded : List GoldWord := (NativeGoldRowEncoding.encodeResponses code 3 raw).get (by decide +kernel)
theorem encoded_spec : NativeGoldRowEncoding.encodeResponses code 3 raw = some encoded := (Option.some_get _).symm
example : raw[0]?.map goldValue = some 1 ∧ raw[2]?.map goldValue = some 0 := by decide +kernel
example : NativeGoldRowMeaning.coefficients code 1 ((raw.drop 0).take 2) 0 0 = 1 ∧
    NativeGoldRowMeaning.coefficients code 1 ((raw.drop 0).take 2) 0 1 = 2 ∧
    NativeGoldRowMeaning.coefficients code 1 ((raw.drop 0).take 2) 0 2 = 0 ∧
    NativeGoldRowMeaning.coefficients code 1 ((raw.drop 0).take 2) 0 3 = 0 := by decide +kernel

def claimed : NativeLookupRequestWire.Row := ⟨[3,5,15],by decide⟩
theorem verified : NativeGoldPcsClaim.verify ctx.parameters HasteBootsBatchMeaningSmoke.secondQuery raw claimed = .ok () := by decide +kernel

theorem query_valid : NativeGoldMatrixWeights.QueryValid ctx.parameters.width.val HasteBootsBatchMeaningSmoke.secondQuery.models := by
  intro pair member
  have checks : HasteBootsBatchMeaningSmoke.secondQuery.models.all (fun pair => NativeGoldMatrix.validate pair.zero ctx.parameters.width.val &&
    NativeGoldMatrix.validate pair.one ctx.parameters.width.val) = true := by decide +kernel
  exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp checks pair member)

example : claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishEncoded
    (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive) (by decide : code.messageLength ≤ 1*code.blockWidth)
    (NativeGoldSuffixFinishing.encodedRight ctx.parameters HasteBootsBatchMeaningSmoke.secondQuery code (by decide) (by decide))
    (fun lane => NativeGoldResponseMeaning.laneWord code encoded lane.val)) :=
  NativeGoldSuffixFinishing.claim_encoded ctx.parameters HasteBootsBatchMeaningSmoke.secondQuery raw encoded claimed query_valid verified code 1 encoded_spec
    (by decide) (by decide) primitive (by decide) (by decide)
-- Shared left-prefix responses do not collapse distinct original right queries.
example : NativeGoldPcsClaim.verify ctx.parameters HasteBootsBatchMeaningSmoke.query raw claimed = .error .claim := by decide +kernel

def binding : NativeGoldBatchBinding.Bound := {work.binding with values := ⟨[HasteBootsBatchMeaningSmoke.zeros 3 (by decide),claimed],by decide⟩}
def opening : NativeGoldBatchOpening.Opening := {ctx.opening with evaluations := ⟨[⟨raw,by decide⟩],by decide⟩}
example : NativeGoldBatchPcsProgram.finish ctx.parameters binding opening = .ok () := by decide +kernel
example : NativeGoldBatchPcsProgram.finish ctx.parameters
    {binding with values := ⟨[HasteBootsBatchMeaningSmoke.zeros 3 (by decide),HasteBootsBatchMeaningSmoke.zeros 3 (by decide)],by decide⟩}
    opening = .error (.claim .claim) := by decide +kernel

end
end HasteBootsNativeFinishingSmoke
