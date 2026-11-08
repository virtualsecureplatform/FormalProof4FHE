module
import FormalProof4FHE.HasteBoots.NativeVariantValues

namespace FormalProof4FHETest.HasteBootsVariantValuesSmoke
open FormalProof4FHE.HasteBoots
open NativeVariantValues

private def unit : NativeRecordValues.Value := .scalar .unit
private def pointer : NativeRecordValues.Value := .scalar (.raw ⟨⟨64, some ⟨9,3⟩⟩, none⟩)
private def schema : Schema := ⟨10, [⟨0, .scalar .unit⟩,
  ⟨1, .pair .nonnull (.pair (.scalar .usize) (.scalar .unit))⟩]⟩
private def payload : NativeRecordValues.Value := .pair pointer (.pair (.scalar (.usize 8)) unit)
private def present : Value := ⟨10, 1, payload⟩
private def movedValue : Value := ⟨10, 1, .pair .uninit (.pair (.scalar (.usize 8)) unit)⟩

example : pack schema 0 unit = some ⟨10, 0, unit⟩ := by decide
example : pack schema 1 payload = some present := by decide
example : pack schema 2 payload = none := by decide
example : pack schema 0 payload = none := by decide
example : pack schema 1 movedValue.payload = none := by decide
example : pack schema 1 (.pair (.scalar (.raw ⟨⟨0,none⟩,none⟩)) (.pair (.scalar (.usize 8)) unit)) = none := by decide
example : discriminant schema present = some 1 := by decide
example : discriminant schema {present with tag := 11} = none := by decide
example : discriminant schema {present with variant := 2} = none := by decide
example : project schema present 0 [.left] = none := by decide
example : project schema present 1 [.left] = some pointer := by decide
example : project schema present 1 [.unwrap 10] = none := by decide
example : take schema present 1 [.left] = some (pointer, movedValue) := by decide
example : project schema movedValue 1 [.left] = none := by decide
example : project schema movedValue 1 [.right,.left] = some (.scalar (.usize 8)) := by decide
example : project schema movedValue 1 [] = none := by decide
example : discriminant schema movedValue = some 1 := by decide
example : take schema movedValue 1 [.left] = none := by decide
-- Signed logical discriminants are neither variant indices nor stored words.
example : discriminant ⟨10, [⟨-7, .scalar .unit⟩]⟩ ⟨10, 0, unit⟩ = some (-7) := by decide

end FormalProof4FHETest.HasteBootsVariantValuesSmoke
