namespace HasteBootsRawVecOption.Smoke
open FormalProof4FHE.HasteBoots
open NativeVariantValues

private def unit : NativeRecordValues.Value := .scalar .unit
private def pointer : NativeRecordValues.Value := .scalar (.raw ⟨⟨64, some ⟨9,3⟩⟩, none⟩)
private def layout : NativeRecordValues.Value := .record 9 (.pair (.scalar (.usize 8))
  (.pair (.record 11 (.pair (.enumeration 12 8) unit)) unit))
private def payload : NativeRecordValues.Value := .pair
  (.pair (.record 7 (.pair pointer unit)) (.pair layout unit)) unit
private def movedPayload : NativeRecordValues.Value := .pair
  (.pair (.record 7 (.pair .uninit unit)) (.pair layout unit)) unit
private def pointerPath : NativeRecordValues.Path := [.left,.left,.unwrap 7,.left]
private def layoutPath : NativeRecordValues.Path := [.left,.right,.left]

example : pack schema 1 payload = some (someValue payload) := by decide
example : project schema (someValue payload) 1 pointerPath = some pointer := by decide
example : project schema (someValue payload) 0 pointerPath = none := by decide
example : take schema (someValue payload) 1 pointerPath = some (pointer, someValue movedPayload) := by decide
example : project schema (someValue movedPayload) 1 pointerPath = none := by decide
example : project schema (someValue movedPayload) 1 layoutPath = some layout := by decide
example : project schema (someValue movedPayload) 1 [] = none := by decide
example : discriminant schema (someValue movedPayload) = some 1 := by decide
example : pack schema 1 movedPayload = none := by decide
example : discriminant schema ⟨11,1,payload⟩ = none := by decide

end HasteBootsRawVecOption.Smoke
