module
public import FormalProof4FHE.HasteBoots.CausalStoredSourceRecovery
@[expose] public section

/-! Measured Gold public-source extraction from the source selected before an
original stream's first positive read. Root and dummy are stored bytes; the
entire mixed-history recovery/selection cost is included. Trusted context and
capacity production, original field-input parsing, application ownership and
physical/native backend refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.CausalStoredGoldExtraction
open InputIndexedOracle (Input Byte)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize)
open StoredSourceVectorReadCost (Source)
open StoredGoldPublicSource (Log viewLog)
open SolverOperationCost (Run)

def sourceBound (ctx : Context) (log : Log) (radius : ℕ) : ℕ :=
  let n := 2^(logSize ctx.parameters.code)
  let left := 2^ctx.parameters.leftVariables.val
  let packing := ctx.parameters.width.val
  let m := ctx.parameters.code.messageBlocks.val
  let b := ctx.parameters.code.blockWidth.val
  let size := ctx.parameters.code.messageLength.val
  NativeGoldPublicSource.materializeBound ctx (viewLog log)+
    DenseCommonSource.operationBound n (left*packing) m b radius+
    (left*packing)*(7*size+2)+left*(size*(5*packing+2)+2)+n*(2*logSize ctx.parameters.code+9)+6

def run (history : List Observation) (input : Input) (key : Source) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  let recovered := CausalStoredSourceRecovery.run history input key
  match recovered.value with
  | none => Run.mk none (recovered.cost+2)
  | some log =>
    let root := StoredDigestView.fromVector key.2
    let extracted := StoredGoldPublicSource.extract dummy root.value ctx log radius capacity
    Run.mk (some extracted.value) (recovered.cost+root.cost+extracted.cost+3)

theorem run_value (history : List Observation) (input : Input) (key : Source) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run history input key dummy ctx radius capacity).value =
      (CausalFirstStreamPrefix.recover input history).map (fun before =>
        (NativeGoldPublicSource.extractWithCost dummy.get key.2.get ctx
          (ExecutableSourceSelection.select (ExecutableSourceHistory.reconstruct before)
            (StoredSourceVectorReadCost.sourceView key)) radius capacity).value) := by
  have selected := CausalStoredSourceRecovery.run_value history input key
  cases found : (CausalStoredSourceRecovery.run history input key).value with
  | none =>
    rw [found,Option.map_none] at selected
    have absent : CausalFirstStreamPrefix.recover input history = none := by
      exact Option.map_eq_none_iff.mp selected.symm
    simp only [run,found,absent,Option.map_none]
  | some log =>
    rw [found,Option.map_some] at selected
    obtain ⟨before,recovered,same⟩ := Option.map_eq_some_iff.mp selected.symm
    simp only [run,found,recovered,Option.map_some,StoredGoldPublicSource.extract_eq,
      StoredDigestView.view_fromVector]
    rw [← same]

theorem run_cost (history : List Observation) (input : Input) (key : Source) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run history input key dummy ctx radius capacity).cost ≤
      (6*input.length+16)*history.length+
      StoredSourceSnapshotBudget.stepBound (ClosedByteMachineRootBudget.inputWork history)
        history.length (StoredShakeHistory.bytes history)*history.length+
      5308*ClosedByteMachineRootBudget.inputWork history^2+141+
      ((CausalStoredSourceRecovery.run history input key).value.map (fun log => sourceBound ctx log radius)).getD 0 := by
  have recovered := CausalStoredSourceRecovery.run_cost history input key
  simp only [run]
  split
  · rename_i absent
    simp only [absent,Option.map_none,Option.getD_none]
    omega
  · rename_i log found
    have extracted := StoredGoldPublicSource.extract_cost dummy (StoredDigestView.fromVector key.2).value ctx log radius capacity
    simp only [found,Option.map_some,Option.getD_some]
    dsimp only [sourceBound,StoredDigestView.fromVector] at extracted ⊢
    omega

theorem run_unseen (history : List Observation) (input : Input) (key : Source) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (unseen : CausalStreamExposure.seen history input = false) :
    (run history input key dummy ctx radius capacity).value = none := by
  rw [run_value,(CausalFirstStreamPrefix.recover_none input history).mpr unseen]
  rfl
end FormalProof4FHE.HasteBoots.CausalStoredGoldExtraction
