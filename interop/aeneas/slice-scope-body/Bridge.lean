namespace HasteBootsSliceScopeBody
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC NativeReferenceCleanup
open NativeReferenceMachine (State)
open NativeWord64Memory (Word)

theorem shared_scope_closed (world current : State) (reachable : NativeReferenceMachine.Reachable world)
    (index : Nat) (length : Word) (returned : invoke f0 world [.rawRegister index, .usize length] = .returned .unit current) :
    ∃ next, invokeUnit f0 world [.rawRegister index, .usize length] = .returned .unit next ∧
      withoutLeases next = withoutLeases current ∧
      (∀ lease, lease ∈ next.leases ↔ lease ∈ current.leases ∧ lease.tag < world.nextTag) :=
  invokeUnit_success f0 world current reachable _ returned

theorem mutable_scope_closed (world current : State) (reachable : NativeReferenceMachine.Reachable world)
    (index : Nat) (length : Word) (returned : invoke f1 world [.rawRegister index, .usize length] = .returned .unit current) :
    ∃ next, invokeUnit f1 world [.rawRegister index, .usize length] = .returned .unit next ∧
      withoutLeases next = withoutLeases current ∧
      (∀ lease, lease ∈ next.leases ↔ lease ∈ current.leases ∧ lease.tag < world.nextTag) :=
  invokeUnit_success f1 world current reachable _ returned

end HasteBootsSliceScopeBody
