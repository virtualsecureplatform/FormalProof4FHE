module
public import FormalProof4FHE.HasteBoots.ScalarCompletedOrigin
@[expose] public section

/-! Completed native records form a growing prefix. Their native round ordinals
identify the unique prior list at an actual producing sampler, including runs
that later reject or remain suspended. -/
namespace FormalProof4FHE.HasteBoots.ScalarCompletedPrefix
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement RoundPacket)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (Machine CompletedRound)
open NativeGoldExtensionArithmetic (Word)

theorem after_field (machine : Machine) (packet : RoundPacket) (status : NativeFieldVector.Status) :
    machine.completed <+: (NativeScalarBatchVerifier.afterField machine packet status).completed := by
  cases status with
  | suspended field => exact List.prefix_refl _
  | finished coefficients transcript =>
    cases decoded : NativeGoldLookupProducer.decode coefficients.values with
    | none => simpa only [NativeScalarBatchVerifier.afterField,NativeScalarBatchVerifier.fail,decoded] using List.prefix_refl machine.completed
    | some challenge =>
      cases updated : NativeScalarBatchUpdate.update machine.state.expected packet.messages.val challenge with
      | none => simpa only [NativeScalarBatchVerifier.afterField,NativeScalarBatchVerifier.fail,decoded,updated] using List.prefix_refl machine.completed
      | some expected =>
        simp only [NativeScalarBatchVerifier.afterField,decoded,updated]
        exact ⟨_,rfl⟩

theorem tick (statement : Statement) (proof : Proof) (machine : Machine) (world : World) :
    machine.completed <+: (NativeScalarBatchVerifier.tickExecute statement proof machine world).1.completed := by
  cases control : machine.control with
  | finished claims => simpa only [NativeScalarBatchVerifier.tickExecute,control] using List.prefix_refl machine.completed
  | failed error => simpa only [NativeScalarBatchVerifier.tickExecute,control] using List.prefix_refl machine.completed
  | sampling packet field =>
    simpa only [NativeScalarBatchVerifier.tickExecute,control] using after_field machine packet
      (NativeFieldVector.driveExecute NativeFields.goldilocksModulus 1 field world).1
  | ready =>
    have kept := ScalarPriorStability.prepare_prior statement proof machine
    cases prepared : NativeScalarBatchVerifier.prepare statement proof machine with
    | inl next =>
      have equal : ScalarPriorStability.prior next = ScalarPriorStability.prior machine := by simpa only [prepared] using kept
      have records := congrArg (fun prior => prior.2.2) equal
      dsimp only [ScalarPriorStability.prior] at records
      simpa only [NativeScalarBatchVerifier.tickExecute,control,prepared,records] using List.prefix_refl machine.completed
    | inr pair =>
      obtain ⟨next,packet⟩ := pair
      have equal : ScalarPriorStability.prior next = ScalarPriorStability.prior machine := by simpa only [prepared] using kept
      have records := congrArg (fun prior => prior.2.2) equal
      dsimp only [ScalarPriorStability.prior] at records
      simpa only [NativeScalarBatchVerifier.tickExecute,control,prepared,records] using List.prefix_refl machine.completed

theorem execute (statement : Statement) (proof : Proof) (fuel : ℕ) (machine : Machine) (world : World) :
    machine.completed <+: (NativeScalarBatchVerifier.execute statement proof fuel machine world).1.completed := by
  induction fuel generalizing machine with
  | zero => exact List.prefix_refl _
  | succ fuel ih => exact (tick statement proof machine world).trans (ih _)

theorem earlier (statement : Statement) (proof : Proof) (first later : ℕ) (ordered : first ≤ later)
    (machine : Machine) (world : World) :
    (NativeScalarBatchVerifier.execute statement proof first machine world).1.completed <+:
      (NativeScalarBatchVerifier.execute statement proof later machine world).1.completed := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [NativeScalarBatchVerifier.execute_add]
  exact execute statement proof extra _ world

/-- A native chain records the position of every occurrence, rather than just
membership. This also rules out confusing equal-looking completed rounds. -/
theorem ordinal (statement : Statement) (proof : Proof) (entries : List CompletedRound) (expected : List Word)
    (chain : NativeScalarBatchHistory.Chain statement proof entries expected)
    (before : List CompletedRound) (entry : CompletedRound) (after : List CompletedRound)
    (parts : entries = before ++ entry :: after) : entry.packet.round.val = before.length := by
  have bound : before.length < entries.length := by rw [parts]; simp only [List.length_append,List.length_cons]; omega
  have getter : entries[before.length]? = some entry := by rw [parts]; simp
  have indexed := congrArg (fun rounds : List ℕ => rounds[before.length]?) (NativeScalarBatchHistory.chain_ordinals chain)
  simpa only [List.getElem?_map,getter,Option.map_some,List.getElem?_range bound,Option.some.injEq] using indexed

/-- The actual producing sampler's retained list is exactly the prefix before
this completed occurrence; no supplied prior-point identity is needed. -/
theorem producing_before (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (fuel index : ℕ) (bounded : index ≤ fuel) (world : World) (entry : CompletedRound)
    (produced : ScalarCompletedOrigin.Produced (NativeScalarBatchVerifier.execute statement proof index
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1 world entry)
    (before after : List CompletedRound)
    (parts : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed = before ++ entry :: after) :
    (NativeScalarBatchVerifier.execute statement proof index
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed = before := by
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff transcript result statement proof).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  have valid := NativeScalarBatchVerifierInvariant.execute_valid statement proof first preflight.1 preflight.2.1 head index
    _ world (NativeScalarBatchVerifierInvariant.initial_valid transcript result statement proof first accepted)
  obtain ⟨field,next,active,_,_,_,_⟩ := produced
  have phase := valid.2.2.2.2
  rw [active] at phase
  have position := ordinal statement proof _ _
    (NativeScalarBatchHistory.initialized_linked transcript result statement proof accepted fuel world).1 before entry after parts
  have lengthEq : (NativeScalarBatchVerifier.execute statement proof index
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed.length = before.length :=
    valid.2.2.2.1.trans (phase.2.1.symm.trans position)
  obtain ⟨suffix,prefixEq⟩ := earlier statement proof index fuel bounded (NativeScalarBatchVerifier.initial transcript statement proof) world
  have taken := congrArg (List.take before.length) (prefixEq.trans parts)
  simp only [List.take_append] at taken
  rw [← lengthEq,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] at taken
  rw [lengthEq,List.take_length,List.take_zero,List.append_nil] at taken
  exact taken

/-- The common point at production is the literal challenge list preceding
the chosen occurrence in the final native chain. -/
theorem producing_point (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (fuel index : ℕ) (bounded : index ≤ fuel) (world : World) (entry : CompletedRound)
    (produced : ScalarCompletedOrigin.Produced (NativeScalarBatchVerifier.execute statement proof index
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1 world entry)
    (before after : List CompletedRound)
    (parts : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed = before ++ entry :: after) :
    (NativeScalarBatchVerifier.execute statement proof index
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.point = before.map (fun item => item.challenge) := by
  have preflight := (NativeScalarBatchPreflight.beginVerify_ok_iff transcript result statement proof).mp accepted
  obtain ⟨first,head,_,_,_⟩ := NativeScalarBatchPreflight.dimensions_success statement preflight.2.1
  have valid := NativeScalarBatchVerifierInvariant.execute_valid statement proof first preflight.1 preflight.2.1 head index
    _ world (NativeScalarBatchVerifierInvariant.initial_valid transcript result statement proof first accepted)
  rw [valid.2.2.1,producing_before transcript result statement proof accepted fuel index bounded world entry produced before after parts]

end FormalProof4FHE.HasteBoots.ScalarCompletedPrefix
