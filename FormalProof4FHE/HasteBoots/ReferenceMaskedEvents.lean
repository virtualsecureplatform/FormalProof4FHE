module
public import FormalProof4FHE.HasteBoots.MaskedOracleBound
@[expose] public section

/-! The four original reference events obey their thresholded score bounds
on the appropriate original or completed replay fibers. -/
namespace FormalProof4FHE.HasteBoots.ReferenceMaskedEvents
open InputIndexedOracle (World law)
open NativeTranscript (Execution Observation)
open MeasureTheory ProbabilityTheory
noncomputable section
open scoped Classical

def small {S A : Type} (threshold : ℕ) (packet : (S ⊕ A) × List Observation) : Prop :=
  packet.2.length < threshold ∧ ClosedByteMachineRootBudget.inputWork packet.2 < threshold

variable {S A : Type} (step : S → OracleMachine.Command S A)
  {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (threshold : ℕ)
include replay

theorem parent_bound :
    law {world | small threshold (past world).run ∧ ParentSeedCollisionRisk.event step (past world).run world} ≤
      ∫⁻ world, (if small threshold (past world).run then ParentSeedCollisionRisk.risk step (past world).run else 0) ∂law := by
  have bounded := MaskedOracleBound.bound (ParentSeedCompletion.replay replay) (fun packet => packet.1.1)
    (small threshold) {world | ParentSeedCollisionRisk.event step (past world).run world} (ParentSeedCollisionRisk.risk step)
    (fun world => ParentSeedCollisionRisk.retained_bound step replay world)
  exact bounded

theorem context_bound :
    law {world | small threshold (past world).run ∧ ContextTargetRisk.event step (past world).run world} ≤
      ∫⁻ world, (if small threshold (past world).run then ContextTargetRisk.risk step (past world).run else 0) ∂law := by
  exact MaskedOracleBound.bound replay id (small threshold)
    {world | ContextTargetRisk.event step (past world).run world} (ContextTargetRisk.risk step)
    (fun world => le_of_eq (ContextTargetRisk.conditional_event step replay world))

theorem fresh_bound :
    law {world | small threshold (past world).run ∧ FreshReceiptTargetRisk.event step (past world).run world} ≤
      ∫⁻ world, (if small threshold (past world).run then FreshReceiptTargetRisk.risk step (past world).run else 0) ∂law := by
  exact MaskedOracleBound.bound replay id (small threshold)
    {world | FreshReceiptTargetRisk.event step (past world).run world} (FreshReceiptTargetRisk.risk step)
    (fun world => le_of_eq (FreshReceiptTargetRisk.conditional_event step replay world))

theorem collision_bound :
    law {world | small threshold (past world).run ∧ ReceiptCollisionRisk.event step (past world).run world} ≤
      ∫⁻ world, (if small threshold (past world).run then ReceiptCollisionRisk.risk step (past world).run else 0) ∂law := by
  have bounded := MaskedOracleBound.bound (ReceiptCandidateCompletion.replay replay) (fun packet => packet.1.1)
    (small threshold) {world | ReceiptCollisionRisk.event step (past world).run world} (ReceiptCollisionRisk.risk step)
    (fun world => ReceiptCollisionRisk.retained_bound step replay world)
  exact bounded

def event (packet : (S ⊕ A) × List Observation) (world : World) : Prop :=
  ParentSeedCollisionRisk.event step packet world ∨ ContextTargetRisk.event step packet world ∨
    FreshReceiptTargetRisk.event step packet world ∨ ReceiptCollisionRisk.event step packet world

theorem bound : law {world | small threshold (past world).run ∧ event step (past world).run world} ≤
    ∫⁻ world, ReferenceRiskBudget.lowRisk step threshold (past world).run ∂law := by
  let p := fun packet => if small threshold packet then ParentSeedCollisionRisk.risk step packet else 0
  let c := fun packet => if small threshold packet then ContextTargetRisk.risk step packet else 0
  let f := fun packet => if small threshold packet then FreshReceiptTargetRisk.risk step packet else 0
  let r := fun packet => if small threshold packet then ReceiptCollisionRisk.risk step packet else 0
  have mp := OracleExecutionLaw.score_measurable replay p
  have mc := OracleExecutionLaw.score_measurable replay c
  have mf := OracleExecutionLaw.score_measurable replay f
  have equal : {world | small threshold (past world).run ∧ event step (past world).run world} =
      {world | small threshold (past world).run ∧ ParentSeedCollisionRisk.event step (past world).run world} ∪
      ({world | small threshold (past world).run ∧ ContextTargetRisk.event step (past world).run world} ∪
      ({world | small threshold (past world).run ∧ FreshReceiptTargetRisk.event step (past world).run world} ∪
      {world | small threshold (past world).run ∧ ReceiptCollisionRisk.event step (past world).run world})) := by
    ext world
    simp only [event,Set.mem_ofPred_eq,Set.mem_union,and_or_left]
  rw [equal]
  calc
    _ ≤ (∫⁻ world, p (past world).run ∂law) + ((∫⁻ world, c (past world).run ∂law) +
        ((∫⁻ world, f (past world).run ∂law) + ∫⁻ world, r (past world).run ∂law)) :=
      (measure_union_le _ _).trans (add_le_add (parent_bound step replay threshold)
        ((measure_union_le _ _).trans (add_le_add (context_bound step replay threshold)
          ((measure_union_le _ _).trans (add_le_add (fresh_bound step replay threshold) (collision_bound step replay threshold))))))
    _ = ∫⁻ world, p (past world).run + (c (past world).run + (f (past world).run + r (past world).run)) ∂law := by
      rw [lintegral_add_left mp,lintegral_add_left mc,lintegral_add_left mf]
    _ = _ := by
      apply lintegral_congr
      intro world
      dsimp only [p,c,f,r]
      unfold ReferenceRiskBudget.lowRisk ReferenceRiskBudget.risk small
      split_ifs <;> simp only [add_zero,add_assoc]

end
end FormalProof4FHE.HasteBoots.ReferenceMaskedEvents
