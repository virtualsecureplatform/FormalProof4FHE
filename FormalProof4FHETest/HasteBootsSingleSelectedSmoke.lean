module
import all FormalProof4FHE.HasteBoots.SingleOpeningFieldProximityCoverage
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleSelectedSmoke
noncomputable section
open InputIndexedOracle (World)
open OracleProgram (run)
open HasteBootsBatchMeaningSmoke (usize zeros root)

/-- The fixture reuses raw code data but executes the original single protocol. -/
def ctx : NativeGoldPcsExecution.Context :=
  ⟨HasteBootsBatchMeaningSmoke.ctx.tables,
    {HasteBootsBatchMeaningSmoke.ctx.parameters with queries := usize 3},⟨[],root⟩,root,
    HasteBootsBatchMeaningSmoke.query,zeros 3 (by decide),
    ⟨zeros 6 (by decide),zeros 6 (by decide),
      ⟨List.replicate 2 ⟨zeros 24 (by decide),⟨List.replicate 6 root,by decide⟩⟩,by decide⟩⟩,18⟩

def world : World
  | .inr _ => 0
  | .inl (input,offset) =>
    match (TranscriptFrame.decodeAll input).bind List.getLast? with
    | some frame => if frame.kind = 2 ∧ frame.label = NativeGoldPcsColumns.label then
        if offset % 8 = 0 then if offset / 8 = 1 then 1 else 7 else 0
      else 0
    | none => 0

def prepared? : NativeGoldPcsWorkers.Outcome → Option NativeGoldPcsWorkers.Prepared
  | .prepared work => some work
  | _ => none

def result := (run ctx.prefix world).run.1
theorem present : (prepared? result).isSome = true := by decide +kernel
def work := (prepared? result).get present

theorem prepared : (run ctx.prefix world).run.1 = .prepared work := by
  have known := present
  cases equal : result with
  | «prefix» previous => simp only [equal,prepared?,Option.isSome_none,Bool.false_eq_true] at known
  | pairingUnavailable => simp only [equal,prepared?,Option.isSome_none,Bool.false_eq_true] at known
  | prepared actual => change result = _; simp only [work,equal,prepared?,Option.get_some]

example : work.geometry.rows = 6 ∧ work.geometry.randomCount.val = 18 ∧ work.width = 3 ∧ work.geometry.blockWidth = 4 := by decide +kernel
example : work.jobs.map NativeGoldColumnWorker.Job.index = [1,7] := by decide +kernel

/-- Original ordered draws retain repetitions although native workers deduplicate. -/
def sampleView (outcome : NativeGoldPcsColumns.Outcome) : Option (List ℕ × List ℕ) :=
  match outcome with
  | .columns _ _ _ sample => some (sample.draws,sample.indices)
  | _ => none

example : sampleView (run (NativeGoldPcsColumns.protocol NativeGoldBlockCode.description ctx.parameters ctx.transcript ctx.root ctx.query
    ctx.claimed ctx.opening ctx.fieldFuel) world).run.1 = some ([7,1,7],[1,7]) := by decide +kernel

/-- Actual native preparation derives completion and all eighteen values. -/
example : ∃ sample, ∃ receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample,
    receipt.state.remaining = 0 ∧ receipt.state.values.length = 18 := by
  obtain ⟨sample,⟨receipt⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation ctx world work prepared
  have exactValues := NativePrimeRequest.finished_gold_exact ctx.fieldFuel receipt.bound .vector NativeGoldPcsPrelude.randomLabel
    work.geometry.randomCount world receipt.state receipt.next receipt.field
  exact ⟨sample,receipt,SingleOpeningFieldProximityCoverage.complete receipt,
    exactValues.1.trans (by decide +kernel)⟩

/-- One missing coefficient suspends the actual native preparation. -/
example : (prepared? (run ({ctx with fieldFuel := 17}.prefix) world).run.1).isNone = true := by decide +kernel

/-- The real sampler receipt yields a complete linked native nonce. -/
example : ∃ sample, ∃ receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample,
    ∃ decoded : SingleOpeningChallengeLink.View,
      SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded ∧
      decoded.field.count.val = 18 ∧ decoded.column.index.count.val = 3 ∧ decoded.receipt.length = 80 := by
  obtain ⟨sample,⟨receipt⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation ctx world work prepared
  obtain ⟨context,_,parsed,_,_⟩ := SingleOpeningPreparedChallenge.prepared_link receipt prepared [] rfl (by simp)
    (by decide +kernel) (by decide +kernel)
  refine ⟨sample,receipt,SingleOpeningPreparedChallenge.recovered receipt [] context,parsed,?_,?_,?_⟩
  · change work.geometry.randomCount.val = 18
    decide +kernel
  · change ctx.parameters.queries.val = 3
    decide +kernel
  · exact NativeTranscript.receipt_length world receipt.state.phase.consumed

end

end FormalProof4FHE.HasteBoots.SingleSelectedSmoke
