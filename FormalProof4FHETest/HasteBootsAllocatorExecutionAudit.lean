module
import FormalProof4FHE.HasteBoots.NativeAllocatorLLBC

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.run

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.allocation_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.allocation_step

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.uninitialized_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.uninitialized_result

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.initialized_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.initialized_result

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.zero_write_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.zero_write_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.zero_write_loaded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.zero_write_loaded

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.run_projects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.run_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.run_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.run_reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.eval

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.eval_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.eval_call

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.legacy_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.legacy_done

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.eval_projects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.eval_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.invoke_projects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.invoke_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.invoke_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.invoke_reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.Body.allocate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorLLBC.Body.allocate

/-- info: 'FormalProof4FHE.HasteBoots.NativeAllocatorExecution.Symbol.allocate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeAllocatorExecution.Symbol.allocate

