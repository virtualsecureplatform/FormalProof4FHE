module
import all FormalProof4FHE.HasteBoots.NativeRecordHeapBounds

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.count' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.count

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.no_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.no_growth

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.unchanged

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.refl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.refl

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.ofFrame' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.ofFrame

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.mono

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.suffix

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.deallocationBudget' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.deallocationBudget

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.canContinue' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.canContinue

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.deallocate_not_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.deallocate_not_normal

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.eval_normal_canContinue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.eval_normal_canContinue

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.deallocate_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.deallocate_loss

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.eval_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.eval_loss

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.resumeCall_heap_projects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.resumeCall_heap_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.resumeScope_heap_projects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.resumeScope_heap_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget.total' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget.total

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget.limit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget.limit

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget.limit_le_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.HeapBudget.limit_le_total

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordDropCalls.heapBudget' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordDropCalls.heapBudget

