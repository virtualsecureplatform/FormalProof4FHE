module
public import FormalProof4FHE.HasteBoots.DependentStageContinuation
@[expose] public section

/-! Recover actual predecessor support through a reached-or-skipped dependent
continuation, without replaying or expanding the predecessor experiment. -/
namespace FormalProof4FHE.HasteBoots.DependentStageSupport
noncomputable section
variable {Before Memory State : Type} {Result : Memory → Type}

theorem predecessor_supported_bind (select : Before → Option Memory) (start : Before → State)
    (child : (memory : Memory) → State → ProbComp (Result memory))
    (prior : ProbComp Before) (outcome : Before × Option (Sigma Result))
    (supported : outcome ∈ support (prior >>= DependentStageContinuation.program select start child)) :
    outcome.1 ∈ support prior := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨earlier,later⟩ := Set.mem_iUnion.mp present
  have same := DependentStageContinuation.predecessor select start child before outcome later
  simpa only [same] using earlier

end
end FormalProof4FHE.HasteBoots.DependentStageSupport
