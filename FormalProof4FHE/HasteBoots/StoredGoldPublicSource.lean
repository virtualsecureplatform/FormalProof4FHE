module
public import FormalProof4FHE.HasteBoots.NativeGoldPublicSource
@[expose] public section

/-! Concrete stored-byte entry points for public source extraction. Functional
views occur only in compatibility statements and analysis bounds, never in the
executed materializer/extractor. Runtime size production, complete-history
selection and physical/compiler/backend refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldPublicSource
open InputIndexedOracle (Input Byte)
open PreparedMerklePayloads (StoredDigest)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize)
open SolverOperationCost (Run)

abbrev Log := List (Input × StoredDigest)
def viewLog (log : Log) : ExecutableMerkleAvailability.Log :=
  log.map (fun entry => ⟨entry.1,StoredDigestView.view entry.2⟩)

theorem store_viewLog (log : Log) :
    (viewLog log).map (fun entry => (entry.1,PreparedMerklePayloads.store entry.2)) = log := by
  simp only [viewLog,List.map_map,Function.comp_def,StoredDigestView.store_view]
  exact List.map_id log

def materialize (dummy : Vector Byte 64) (root : StoredDigest) (ctx : Context) (log : Log) :=
  let height := (Fin.ofNat 64 (logSize ctx.parameters.code)).val
  let raw := CostedMerkleWord.prepareWord height dummy log root
  let result := RawGoldColumnCost.columns (2^(logSize ctx.parameters.code))
    (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)
    ctx.parameters.code.blockWidth.val raw.value
  Run.mk result.value (raw.cost+result.cost+2)

theorem materialize_eq (dummy : Vector Byte 64) (root : StoredDigest) (ctx : Context) (log : Log) :
    materialize dummy root ctx log = NativeGoldPublicSource.materializeWithCost
      dummy.get (StoredDigestView.view root) ctx (viewLog log) := by
  have vector : Vector.ofFn dummy.get = dummy := by ext i; simp [Vector.get]
  simp only [materialize,NativeGoldPublicSource.materializeWithCost,store_viewLog,
    StoredDigestView.store_view,vector]

theorem materialize_cost (dummy : Vector Byte 64) (root : StoredDigest) (ctx : Context) (log : Log) :
    (materialize dummy root ctx log).cost ≤ NativeGoldPublicSource.materializeBound ctx (viewLog log) := by
  rw [materialize_eq]
  exact NativeGoldPublicSource.materializeWithCost_cost _ _ _ _

def extract (dummy : Vector Byte 64) (root : StoredDigest) (ctx : Context) (log : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :=
  let prepared := materialize dummy root ctx log
  let result := NativeGoldExecutableExtraction.extractPreparedWithCost ctx radius capacity prepared.value
  Run.mk result.value (prepared.cost+result.cost+1)

theorem extract_eq (dummy : Vector Byte 64) (root : StoredDigest) (ctx : Context) (log : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    extract dummy root ctx log radius capacity = NativeGoldPublicSource.extractWithCost
      dummy.get (StoredDigestView.view root) ctx (viewLog log) radius capacity := by
  simp only [extract,materialize_eq,NativeGoldPublicSource.extractWithCost]

theorem extract_cost (dummy : Vector Byte 64) (root : StoredDigest) (ctx : Context) (log : Log) (radius : ℕ)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) :
    let n := 2^(logSize ctx.parameters.code)
    let left := 2^ctx.parameters.leftVariables.val
    let packing := ctx.parameters.width.val
    let m := ctx.parameters.code.messageBlocks.val
    let b := ctx.parameters.code.blockWidth.val
    let size := ctx.parameters.code.messageLength.val
    (extract dummy root ctx log radius capacity).cost ≤ NativeGoldPublicSource.materializeBound ctx (viewLog log)+
      DenseCommonSource.operationBound n (left*packing) m b radius+
      (left*packing)*(7*size+2)+left*(size*(5*packing+2)+2)+n*(2*logSize ctx.parameters.code+9)+6 := by
  rw [extract_eq]
  exact NativeGoldPublicSource.extractWithCost_cost _ _ _ _ _ _
end FormalProof4FHE.HasteBoots.StoredGoldPublicSource
