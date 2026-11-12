module
public import FormalProof4FHE.HasteBoots.LookupCompressionReceipt
public import FormalProof4FHE.HasteBoots.LookupReciprocalStatement
public import FormalProof4FHE.HasteBoots.QuotedReceiptCoverage
public import FormalProof4FHE.HasteBoots.LookupBatchReceiptLogs
public import FormalProof4FHE.HasteBoots.LookupProducerConsumed
@[expose] public section

/-! An original accepted-offset candidate fixes its own produced y from the
earlier compression receipt on the existing parent/receipt-completed fiber.
The existing lifetime receipt events cover all quoted keys and collisions. -/
namespace FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation
open InputIndexedOracle (World)
open NativeExtensionFields (Goldilocks3)
open NativeFields (goldilocksModulus)
open OracleProgram (Program run runPrefix)
noncomputable section

structure Candidate {A : Type} (program : Program A) (position : ℕ) (world : World)
    extends LookupMultiplicityFixation.Candidate program position world where
  last : source.job.view.producer.selection.draws.getLast? = some source.draw
  receipts : LookupReceiptLogs.Reads world source.job.view.producer.selection.draws (run program world).run.2

theorem compression {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) :
    ∃ first : NativeLookupChallenge.Draw Goldilocks3,
      candidate.source.job.view.producer.selection.draws.head? = some first ∧
      NativeGoldLookupProducer.decode first.coefficients.values = some (candidate.source.origin.ready.jobs.get candidate.source.index).output.y ∧
      LookupCompressionReceipt.latest candidate.source.draw.coefficients.phase.pending.input = some (ReceiptFrameView.frame world first.coefficients.phase) := by
  obtain ⟨first,last,firstAt,lastAt,decoded,quoted⟩ := LookupCompressionReceipt.last candidate.source.origin candidate.source.job
  have same := Option.some.inj (lastAt.symm.trans candidate.last)
  rw [same] at quoted
  exact ⟨first,firstAt,decoded,quoted⟩

theorem y_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : NativeRootMessage.Digest)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    NativeFieldWire.goldExtensionValue (left.source.origin.ready.jobs.get left.source.index).output.y =
      NativeFieldWire.goldExtensionValue (right.source.origin.ready.jobs.get right.source.index).output.y := by
  obtain ⟨leftFirst,leftAt,leftDecoded,leftQuoted⟩ := compression left
  obtain ⟨rightFirst,rightAt,rightDecoded,rightQuoted⟩ := compression right
  have leftMember := List.mem_of_mem_head? (by rw [leftAt]; rfl)
  have rightMember := List.mem_of_mem_head? (by rw [rightAt]; rfl)
  have leftIn := LookupCompressionReceipt.member _ _ leftQuoted
  have rightIn := LookupCompressionReceipt.member _ _ rightQuoted
  have leftOutput := (left.receipts leftFirst leftMember).subset (LookupReceiptLogs.output_member world leftFirst.coefficients.phase)
  have rightOutput := (right.receipts rightFirst rightMember).subset (LookupReceiptLogs.output_member other rightFirst.coefficients.phase)
  have leftNamed := QuotedReceiptCoverage.named program world _ leftFirst.coefficients.phase left.source.first leftIn leftOutput good.receipt
  have rightNamed := QuotedReceiptCoverage.named program other _ rightFirst.coefficients.phase right.source.first rightIn rightOutput (fun bad => safe (Or.inl bad))
  rw [left.source.first_position] at leftNamed
  rw [right.source.first_position] at rightNamed
  have receipts := congrArg LookupCompressionReceipt.latest input
  rw [leftQuoted,rightQuoted] at receipts
  have messages := congrArg TranscriptFrame.Frame.message (Option.some.inj receipts)
  have leftTrace := (LookupProducerConsumed.producer left.source.origin left.source.job).2 leftFirst leftMember
  have rightTrace := (LookupProducerConsumed.producer right.source.origin right.source.job).2 rightFirst rightMember
  have coefficients := ReceiptDigestFixation.coefficients_on_fiber (OracleProgram.prefix_replay position program) world other goldilocksModulus
    (by decide +kernel) leftFirst.coefficients rightFirst.coefficients leftTrace rightTrace leftNamed rightNamed
    (ParentFactorFiber.receipt_packet (OracleProgram.prefix_replay position program) world other same)
    (ReceiptDigestFixation.receipt_digest_equal _ _ _ _ messages)
  rcases coefficients with coefficients | collision
  · rw [coefficients] at rightDecoded
    exact congrArg NativeFieldWire.goldExtensionValue (Option.some.inj (leftDecoded.symm.trans rightDecoded))
  · exact False.elim (good.collision (ProgramReceiptCollision.prefix_covers program world position collision))

theorem test_fixed {A : Type} (program : Program A) (position : ℕ) (world other : World)
    (left : Candidate program position world) (right : Candidate program position other) (dummy : NativeRootMessage.Digest)
    (input : left.source.draw.coefficients.phase.pending.input = right.source.draw.coefficients.phase.pending.input)
    (ordinal : left.source.index.val = right.source.index.val)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run)
    (good : JobReferenceFixation.Good program position world dummy) (safe : ¬JobReferenceFixation.CounterBad program other) :
    LookupReciprocalStatement.test left.toCandidate dummy
        (NativeFieldWire.goldExtensionValue (left.source.origin.ready.jobs.get left.source.index).output.y) =
      LookupReciprocalStatement.test right.toCandidate dummy
        (NativeFieldWire.goldExtensionValue (right.source.origin.ready.jobs.get right.source.index).output.y) := by
  exact LookupReciprocalStatement.test_fixed program position world other left.toCandidate right.toCandidate dummy _ _
    (y_fixed program position world other left right dummy input same good safe) input ordinal same good safe

end
end FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation
