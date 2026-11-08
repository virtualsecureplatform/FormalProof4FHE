/-! Associated-type equality controls. Recursive interfaces remain unproved. -/
namespace HasteBootsAssociatedTypesProof
open Aeneas Aeneas.Std Result
open hasteboots_associated_control

theorem convert_exact {F Root : Type} (field : Field F Root) (root : Root) :
    convert field root = field.from_root root := rfl

theorem constrained_exact {F : Type} (field : Field F U64) (root : U64) :
    constrained field root = field.from_root root := rfl

theorem chain_exact {F G Root : Type} (first : Field F Root) (second : Field G F) (root : Root) :
    chain first second root = (do let value ← first.from_root root; second.from_root value) := rfl

theorem chain_success {F G Root : Type} (first : Field F Root) (second : Field G F) (root : Root) (output : G)
    (executed : chain first second root = .ok output) :
    ∃ value, first.from_root root = .ok value ∧ second.from_root value = .ok output := by
  unfold chain at executed
  cases selected : first.from_root root with
  | fail error => simp only [selected,bind_tc_fail] at executed; cases executed
  | div => simp only [selected,bind_tc_div] at executed; cases executed
  | ok value =>
    simp only [selected,bind_tc_ok] at executed
    exact ⟨value,rfl,executed⟩

theorem constrained_failure {F : Type} (field : Field F U64) (root : U64) (error : Error)
    (failed : field.from_root root = .fail error) : constrained field root = .fail error := failed

end HasteBootsAssociatedTypesProof
