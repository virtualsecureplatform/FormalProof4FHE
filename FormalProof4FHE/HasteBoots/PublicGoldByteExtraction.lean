module
public import FormalProof4FHE.HasteBoots.StoredGoldPublicSource
public import FormalProof4FHE.HasteBoots.PublicSourceByteInputs
@[expose] public section

/-! Fail-closed public-source extraction from supplied byte snapshots. Strict
root/dummy/hash-output decoding is part of the measured run, including rejection.
The caller supplies a context and dimension values and an already framed snapshot;
complete-history selection and physical/backend refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.PublicGoldByteExtraction
open InputIndexedOracle (Input)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize)
open PublicSourceByteInputs (ByteLog Inputs)
open SolverOperationCost (Run)

def sourceBound (ctx : Context) (inputs : Inputs) (radius : ℕ) : ℕ :=
  let n := 2^(logSize ctx.parameters.code)
  let left := 2^ctx.parameters.leftVariables.val
  let packing := ctx.parameters.width.val
  let m := ctx.parameters.code.messageBlocks.val
  let b := ctx.parameters.code.blockWidth.val
  let size := ctx.parameters.code.messageLength.val
  NativeGoldPublicSource.materializeBound ctx (StoredGoldPublicSource.viewLog inputs.hashes)+
    DenseCommonSource.operationBound n (left*packing) m b radius+
    (left*packing)*(7*size+2)+left*(size*(5*packing+2)+2)+n*(2*logSize ctx.parameters.code+9)+6

def run (dummy root : Input) (ctx : Context) (entries : ByteLog) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  let prepared := PublicSourceByteInputs.read dummy root entries
  match prepared.value with
  | none => Run.mk none (prepared.cost+2)
  | some inputs =>
    let result := StoredGoldPublicSource.extract inputs.dummy inputs.root ctx inputs.hashes radius capacity
    Run.mk (some result.value) (prepared.cost+result.cost+3)

theorem run_value (dummy root : Input) (ctx : Context) (entries : ByteLog) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run dummy root ctx entries radius capacity).value =
      (PublicSourceByteInputs.read dummy root entries).value.map (fun inputs =>
        (NativeGoldPublicSource.extractWithCost inputs.dummy.get (StoredDigestView.view inputs.root)
          ctx (StoredGoldPublicSource.viewLog inputs.hashes) radius capacity).value) := by
  cases found : (PublicSourceByteInputs.read dummy root entries).value <;>
    simp only [run,found,Option.map_none,Option.map_some,StoredGoldPublicSource.extract_eq]

theorem run_cost (dummy root : Input) (ctx : Context) (entries : ByteLog) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run dummy root ctx entries radius capacity).cost ≤ 589*entries.length+1052+
      ((PublicSourceByteInputs.read dummy root entries).value.map (fun inputs => sourceBound ctx inputs radius)).getD 0 := by
  have parsed := PublicSourceByteInputs.read_cost dummy root entries
  cases found : (PublicSourceByteInputs.read dummy root entries).value with
  | none =>
    simp only [run,found,Option.map_none,Option.getD_none]
    omega
  | some inputs =>
    have extracted := StoredGoldPublicSource.extract_cost inputs.dummy inputs.root ctx inputs.hashes radius capacity
    simp only [run,found,Option.map_some,Option.getD_some]
    dsimp only [sourceBound]
    omega

theorem run_reject (dummy root : Input) (ctx : Context) (entries : ByteLog) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (rejected : (PublicSourceByteInputs.read dummy root entries).value = none) :
    (run dummy root ctx entries radius capacity).value = none ∧
      (run dummy root ctx entries radius capacity).cost ≤ 589*entries.length+1051 := by
  have parsed := PublicSourceByteInputs.read_cost dummy root entries
  simp only [run,rejected]
  exact ⟨trivial,by omega⟩

theorem run_encode (inputs : Inputs) (ctx : Context) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    (run inputs.dummy.toList inputs.root.val ctx (PublicSourceByteInputs.encodeLog inputs.hashes) radius capacity).value =
      some (StoredGoldPublicSource.extract inputs.dummy inputs.root ctx inputs.hashes radius capacity).value := by
  simp only [run,PublicSourceByteInputs.read_encode]
end FormalProof4FHE.HasteBoots.PublicGoldByteExtraction
