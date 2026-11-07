namespace HasteBootsConstructorTypingProof
open Aeneas Aeneas.Std Result
open hasteboots_constructor_typing

theorem parent_fields {P T : Type} (selfCopy : core.marker.Copy P)
    (valueCopy : core.marker.Copy T) (same : P → Result P)
    (other : P → T → Result T) :
    (Pair.mk selfCopy valueCopy same other).coremarkerCopyInst = selfCopy ∧
    (Pair.mk selfCopy valueCopy same other).coremarkerCopyInst1 = valueCopy :=
  ⟨rfl, rfl⟩

theorem both_calls {P T : Type} (copy : core.marker.Copy T)
    (inst : Pair P T) (pair : P) (value : T) :
    both copy inst pair value = (do
      let p ← inst.same pair
      let t ← inst.other pair value
      ok (p, t)) := rfl

theorem propagate_exact (value : core.result.Result Usize Usize) :
    propagate value = ok value := by
  cases value <;> rfl

end HasteBootsConstructorTypingProof
