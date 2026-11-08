module
import all FormalProof4FHE.HasteBoots.NativePointerMachine

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.origin' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.origin

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.State' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.State

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.empty

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.push' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.push

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.setHeap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.setHeap

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.execute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.execute

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.run

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Issued' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Issued

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Authentic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Authentic

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.WellFormed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.WellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Runs

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.empty_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.empty_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.register_authentic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.register_authentic

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.push_wellFormed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.push_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.setHeap_wellFormed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.setHeap_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.store_generation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.store_generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.write_generation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.write_generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.raw_copy_generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.raw_copy_generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.copy_generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.copy_generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.free_generation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.free_generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.store_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.store_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.write_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.write_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.copy_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.copy_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.free_wellFormed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.free_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.allocate_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.allocate_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.load_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.load_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.historyAfter' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.historyAfter

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.execute_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.execute_invariants

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.execute_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.execute_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.run_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.run_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.run_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.run_reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.issued_generation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.issued_generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.fresh_not_issued' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.fresh_not_issued

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_register_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_register_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_stored_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_stored_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.unissued_register_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.unissued_register_impossible

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.runs_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.runs_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.runs_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.runs_reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_event_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_event_allocation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_origin_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_origin_allocation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_origin_allocator_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_origin_allocator_result

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_register_allocator_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_register_allocator_result

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_stored_allocator_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_stored_allocator_result

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_unique_generations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.reachable_unique_generations

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.run_register_allocator_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.run_register_allocator_result

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.run_stored_allocator_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.run_stored_allocator_result

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.mk' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.mk

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.base' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.base

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.layout' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.layout

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.generation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Allocation.generation

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.State.mk' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.State.mk

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.State.heap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.State.heap

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.State.registers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.State.registers

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.State.history' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.State.history

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.allocate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.allocate

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.fromAddress' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.fromAddress

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.withAddress' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.withAddress

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.load' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.load

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.store' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.store

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.writeBytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.writeBytes

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.copy' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.copy

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.copyNonoverlapping' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.copyNonoverlapping

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Op.free' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Op.free

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Reachable.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Reachable.empty

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Reachable.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Reachable.step

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Runs.refl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Runs.refl

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerMachine.Runs.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerMachine.Runs.step
