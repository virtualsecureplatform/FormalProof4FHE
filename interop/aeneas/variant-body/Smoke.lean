namespace HasteBootsVariantBody.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def world := NativeReferenceMachine.empty
private def raw : NativeSliceLLBC.Raw := ⟨⟨64,some ⟨9,3⟩⟩,none⟩
private def layoutInput (size alignment : NativeWord64Memory.Word) : Input :=
  .record 3 (.pair (.scalar (.usize size)) (.pair
    (.record 6 (.pair (.enumeration 9 alignment) .unit)) .unit))
private def noneInput : Input := .record 4 (.choice false .unit)
private def someInput : Input := .record 4 (.choice true (.pair
  (.pair (.record 2 (.pair (.scalar (.rawRegister 0)) .unit)) (.pair (layoutInput 8 8) .unit)) .unit))
private def registered : NativeReferenceMachine.State :=
  {world with pointers := {world.pointers with registers := [raw.storage]}}

example : invoke f2 world [] = .returned noneValue world := by decide
example : invoke f3 world [noneInput,layoutInput 16 8] = .returned (layoutValue 16 8) world := by decide
example : invoke f3 registered [someInput,layoutInput 16 8] = .returned (layoutValue 8 8) registered := by decide
example : invoke f1 registered [.record 2 (.pair (.scalar (.rawRegister 0)) .unit),layoutInput 8 8] =
    .returned (someValue raw 8 8) registered := by decide
example : invoke f3 world [someInput,layoutInput 16 8] = .invalid world := by decide
example : invoke f3 world [noneInput,layoutInput 16 3] = .invalid world := by decide
example : invoke f3 world [.record 4 (.choice true .unit),layoutInput 16 8] = .invalid world := by decide
example : invoke f3 world [.record 5 (.choice false .unit),layoutInput 16 8] = .invalid world := by decide

end HasteBootsVariantBody.Smoke
