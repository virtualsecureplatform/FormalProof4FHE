module
import FormalProof4FHE.HasteBoots.MixedWidthSharedLookupTerminalSoundness
import Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
open PackedSumcheckSubclaim
namespace HasteBootsMixedWidthTerminalSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17
def basis : Module.Basis (Fin 1) F F := Module.Basis.singleton _ _

theorem zero_decode (columns : ℕ) :
    LookupPairTerminal.decodeSources basis (padding := 1) (c := 1) (row := 0) rfl (fun _ => 0) columns
      (fun _ _ => 0) = some (fun _ => 0) := by
  have parsed : PaddedExtension.element (padding := 1) basis (0 : Fin 2 → F) = some 0 := by
    simpa only [map_zero] using PaddedExtension.element_encode (padding := 1) basis (0 : F)
  have projected : (ExtensionLookupTerminal.sourceQuery basis (padding := 1) (c := 1) (row := 0) rfl
      (fun _ : Fin (1 + 0) => (0 : F))).finish (0 : Fin 2 → F) = 0 := Matrix.mulVec_zero _
  induction columns with
  | zero =>
    change some (Fin.elim0 : Fin 0 → F) = some (fun _ => 0)
    congr 1
    funext index
    exact Fin.elim0 index
  | succ columns ih =>
    change (PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis (padding := 1) (c := 1) (row := 0) rfl
      (fun _ => 0)).finish (0 : Fin 2 → F))).bind (fun first : F =>
        (LookupPairTerminal.decodeSources basis (padding := 1) (c := 1) (row := 0) rfl (fun _ => 0) columns (fun _ _ => 0)).bind
          (fun rest => some (Fin.cons first rest))) = some (fun _ : Fin (columns+1) => (0 : F))
    rw [projected,parsed,ih]
    simp only [Option.bind_some]
    congr 1
    funext index
    exact Fin.cases rfl (fun _ => rfl) index

theorem zero_check (columns : ℕ) :
    LookupPairTerminal.check basis (padding := 1) (c := 1) (row := 0) rfl (fun _ => 0) (fun _ => 0)
      1 0 2 le_rfl (fun _ : Fin columns => fun _ => 0) 1 0 = true := by
  rw [LookupPairTerminal.check,zero_decode]
  simp only [decide_eq_true_eq]
  have full : NativePrefixMask.evaluatePrefix (fun _ : Fin (1 + 0) => (0 : F)) 2 le_rfl = 1 :=
    NativePrefixMask.prefix_full _
  norm_num [ExtensionLookupIdentity.terminal,full,ExtensionLookupIdentity.equality]

theorem wrong_helper_check (columns : ℕ) :
    LookupPairTerminal.check basis (padding := 1) (c := 1) (row := 0) rfl (fun _ => 0) (fun _ => 0)
      1 0 2 le_rfl (fun _ : Fin columns => fun _ => 0) 2 0 = false := by
  rw [LookupPairTerminal.check,zero_decode]
  have full : NativePrefixMask.evaluatePrefix (fun _ : Fin (1 + 0) => (0 : F)) 2 le_rfl = 1 :=
    NativePrefixMask.prefix_full _
  norm_num [ExtensionLookupIdentity.terminal,full,ExtensionLookupIdentity.equality]

end
end HasteBootsMixedWidthTerminalSmoke
