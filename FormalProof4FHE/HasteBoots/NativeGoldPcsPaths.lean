module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers

@[expose] public section

/-! Typed Merkle positions/path lengths follow from the actual checked prefix,
independently of primitive-root correctness and the encoder's mathematics. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsPaths

open NativeGoldBlockCode (Tables Stored description)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (run)

theorem prepared_paths (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work) :
    ∀ job ∈ work.jobs, job.index < 2^work.geometry.height ∧ job.column.path.val.length = work.geometry.height+1 := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,attached,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin tables parameters transcript root query values opening fuel world work success
  have original := (NativeGoldPcsEncoding.encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,prior,_,_,_⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample original
  obtain ⟨parametersRead,shape,_,_,_⟩ := NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) prior
  have checked := (NativeGoldPcsOpening.check_iff geometry parameters.queries opening).mp shape
  have spec := NativeBrakedownParameters.build_spec description parameters geometry parametersRead
  have sizes := NativeBrakedownParameters.computed_sizes description parameters geometry parametersRead
  have height : geometry.height = NativeBrakedownParameters.height geometry.blocks := by
    rw [sizes.2.2.2.2.2.2.2.1,sizes.2.1]
  have positive : 0 < geometry.blocks := by
    rw [sizes.2.1]
    exact Nat.pos_of_ne_zero spec.code.2.2.2.1
  have cover : geometry.blocks ≤ 2^geometry.height := by
    rw [height]
    exact NativeBrakedownParameters.leaves_cover geometry.blocks positive
  obtain ⟨_,_,_,_,_,_,_,bounded,_⟩ := NativeGoldPcsColumnsShape.columns_shape description parameters transcript root query values opening fuel world geometry state weights sample original
  have paired := NativeGoldPcsWorkers.attach_spec sample.indices opening.columns.val jobs attached
  intro job member
  have indexMember : job.index ∈ sample.indices := by rw [← paired.1]; exact List.mem_map.mpr ⟨job,member,rfl⟩
  have columnMember : job.column ∈ opening.columns.val := by rw [← paired.2]; exact List.mem_map.mpr ⟨job,member,rfl⟩
  exact ⟨(bounded job.index indexMember).trans_le cover,(checked.columns job.column columnMember).2⟩

end FormalProof4FHE.HasteBoots.NativeGoldPcsPaths
