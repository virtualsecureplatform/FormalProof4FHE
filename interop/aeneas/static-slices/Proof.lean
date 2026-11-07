/-! Kernel checks for static result data and ordinary borrowed input behavior.
These are compiler regression statements, not native PCS refinement. -/
namespace HasteBootsStaticSlicesProof
open Aeneas Aeneas.Std Result
open hasteboots_static_slices

theorem domain_exact {C : Type} (row : Row C) (code : C) : domain row code = row.domain code := rfl

theorem dimensions_exact {C : Type} (row : Row C) (code : C) :
    dimensions row code = (do let width ← row.width code; let blocks ← row.blocks code; .ok (width,blocks)) := rfl

theorem metadata_exact {C : Type} (row : Row C) (code : C) :
    metadata row code = (do
      let width ← row.width code
      let blocks ← row.blocks code
      let bytes ← row.domain code
      .ok (width,blocks,bytes)) := rfl

theorem copy_exact {C : Type} (row : Row C) (code : C) :
    copy_domain row code = (do let bytes ← row.domain code; .ok (bytes,bytes)) := rfl

theorem after_local_exact {C : Type} (row : Row C) (code : C) :
    after_local row code = (do let bytes ← row.domain code; let width ← row.width code; .ok (bytes,width)) := rfl

theorem borrow_identity (input : Slice U8) : preserve_borrow input = .ok input := rfl

theorem metadata_success {C : Type} (row : Row C) (code : C) (width blocks : Usize) (bytes : Slice U8)
    (executed : metadata row code = .ok (width,blocks,bytes)) :
    row.width code = .ok width ∧ row.blocks code = .ok blocks ∧ row.domain code = .ok bytes := by
  cases first : row.width code <;> cases second : row.blocks code <;> cases third : row.domain code <;>
    simp_all [metadata,Bind.bind,Aeneas.Std.bind]

theorem metadata_width_error {C : Type} (row : Row C) (code : C) (error : Error)
    (failed : row.width code = .fail error) : metadata row code = .fail error := by
  simp only [metadata,failed,bind_tc_fail]

end HasteBootsStaticSlicesProof
