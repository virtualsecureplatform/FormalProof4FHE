module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
public import FormalProof4FHE.HasteBoots.NativeGoldRawRequests
@[expose] public section

/-! Actual checked batch prefixes supply typed raw column positions and paths.
No primitive-root correctness or encoder mathematics is assumed. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchPaths
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (description)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_paths (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ∀ job ∈ work.jobs, job.index < 2^work.geometry.height ∧ job.column.path.val.length = work.geometry.height+1 := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,attached,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,drawn,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have initial := NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening
    ctx.fieldFuel world geometry binding (.finished state next) prelude
  have checked := (NativeGoldBatchOpening.check_iff _ _ _ _).mp initial.2.2.1
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters geometry initial.1
  have sizes := NativeBrakedownParameters.computed_sizes description ctx.parameters geometry initial.1
  have height : geometry.height = NativeBrakedownParameters.height geometry.blocks := by
    rw [sizes.2.2.2.2.2.2.2.1,sizes.2.1]
  have positive : 0 < geometry.blocks := by
    rw [sizes.2.1]
    exact Nat.pos_of_ne_zero spec.code.2.2.2.1
  have cover : geometry.blocks ≤ 2^geometry.height := by
    rw [height]
    exact NativeBrakedownParameters.leaves_cover geometry.blocks positive
  have sampled := NativeIndexRequest.accepted_shape _ _ _ _ world sample drawn
  have paired := NativeGoldPcsWorkers.attach_spec sample.indices ctx.opening.columns.val jobs attached
  intro job member
  have indexMember : job.index ∈ sample.indices := by rw [← paired.1]; exact List.mem_map.mpr ⟨job,member,rfl⟩
  have drawMember : job.index ∈ sample.draws := by rw [sampled.2.1] at indexMember; exact (NativeIndexRequest.mem_distinct _ _).mp indexMember
  have bounded : job.index < geometry.blocks := by
    rw [sizes.2.1]
    exact sampled.2.2.2.2.1 job.index drawMember
  have columnMember : job.column ∈ ctx.opening.columns.val := by rw [← paired.2]; exact List.mem_map.mpr ⟨job,member,rfl⟩
  exact ⟨bounded.trans_le cover,(checked.columns job.column columnMember).2⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchPaths
