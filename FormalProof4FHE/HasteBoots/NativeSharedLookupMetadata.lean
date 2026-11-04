module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupConfig
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPreflightLink
public import FormalProof4FHE.HasteBoots.NativeSharedLookupValidated

@[expose] public section

/-!
# Scalar verifier metadata derived from rebuilt shared requests

Validated nonzero repetitions make the independent batch nonempty. Native
numeric binding supplies the common positive dimension; the infos compiler
supplies exactly degrees one, three or four. Together with actual prepared
jobs and statement construction these discharge all metadata and node
checks. Only the original algebra proof's literal shape check remains.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupMetadata

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeSharedLookupValues (Policy)
open NativeSharedLookupStatement (Request Prepared)
open NativeLookupBindGeometry (Parameters)
open NativeUsizeMessage (Usize)
open NativeScalarBatchWire (Info Statement)

noncomputable section

theorem info_degree (n : Usize) (requests : List Request) (info : Info)
    (member : info ∈ NativeSharedLookupStatement.infos n requests) :
    info.maxMultiplicands.val = 1 ∨ info.maxMultiplicands.val = 3 ∨ info.maxMultiplicands.val = 4 := by
  obtain ⟨request,_,atRequest⟩ := List.mem_flatMap.mp member
  obtain ⟨_,_,atPair⟩ := List.mem_flatMap.mp atRequest
  simp only [NativeSharedLookupStatement.pair,List.mem_cons,List.not_mem_nil,or_false] at atPair
  rcases atPair with same | same
  · subst info; exact Or.inl rfl
  · subst info
    by_cases full : request.terminal.logicalLength.val = 2^n.val
    · simp only [ite_eq_left full]; decide
    · simp only [ite_eq_right full]; decide

theorem info_bounds (n : Usize) (requests : List Request) (info : Info)
    (member : info ∈ NativeSharedLookupStatement.infos n requests) :
    info.maxMultiplicands.val ≠ 0 ∧ info.maxMultiplicands.val + 1 < 2^64 ∧ info.maxMultiplicands.val < goldilocksModulus := by
  rcases info_degree n requests info member with one | three | four
  · rw [one]; decide
  · rw [three]; decide
  · rw [four]; decide

theorem geometry_positive (registry : List Parameters) (helper : Parameters) (requests : List Request)
    (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper requests = some geometry) : geometry.geometry.1.val ≠ 0 := by
  have accepted := NativeSharedLookupPreflight.preflight_spec registry helper requests geometry preflight
  have nonempty : geometry.bindings ≠ [] := by
    intro empty
    have order := accepted.order
    rw [empty,List.map_nil] at order
    exact accepted.dimensions.2.1 order.symm
  obtain ⟨binding,member⟩ := List.exists_mem_of_ne_nil geometry.bindings nonempty
  have bound := accepted.bound binding member
  have common := congrArg Prod.fst (accepted.common binding member)
  have spec := NativeLookupBindGeometry.bind_spec _ _ _ _ _ bound.geometry
  intro zero
  apply spec.positive
  exact (congrArg Fin.val common).trans zero

/-- For compiled independent infos, positivity/nonemptiness and exact vector
lengths imply both native scalar metadata and interpolation-node checks. -/
theorem dimensions_of_infos (n : Usize) (requests : List Request) (statement : Statement)
    (infos : statement.infos.val = NativeSharedLookupStatement.infos n requests)
    (length : statement.infos.val.length = statement.claims.val.length)
    (nonempty : statement.infos.val ≠ []) (positive : n.val ≠ 0) :
    NativeScalarBatchPreflight.dimensions statement = true := by
  have metadata : NativeScalarBatchPreflight.metadataDimensions statement = true := by
    unfold NativeScalarBatchPreflight.metadataDimensions
    cases source : statement.infos.val with
    | nil => exact (nonempty source).elim
    | cons first tail =>
      have firstMember : first ∈ NativeSharedLookupStatement.infos n requests := by rw [← infos,source]; exact List.mem_cons_self
      have firstDimension := NativeSharedLookupStatement.infos_numVariables n requests first firstMember
      simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc]
      refine ⟨?_,?_,?_⟩
      · rw [← source]; exact length
      · rw [firstDimension]; exact positive
      · intro info member
        have inInfos : info ∈ NativeSharedLookupStatement.infos n requests := by rw [← infos,source]; exact member
        have dimension := NativeSharedLookupStatement.infos_numVariables n requests info inInfos
        have bounds := info_bounds n requests info inInfos
        exact ⟨dimension.trans firstDimension.symm,bounds.1,bounds.2.1⟩
  have nodes : NativeScalarBatchPreflight.interpolationNodes statement = true := by
    rw [NativeScalarBatchPreflight.interpolationNodes,List.all_eq_true]
    intro info member
    rw [infos] at member
    exact (NativeScalarBatchPreflight.nodesFrom_zero_iff _).mpr (info_bounds n requests info member).2.2
  rw [NativeScalarBatchPreflight.dimensions,metadata,nodes]
  rfl

theorem constructed_dimensions {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (original : List Request)
    (rebuilt : NativeSharedLookupConfig.rebuild policy original = some (List.ofFn requests))
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3)) (jobs : List Prepared)
    (prepared : NativeSharedLookupPrepared.prepare completed (NativeSharedLookupStatement.tags fits requests) = some jobs)
    (multiplicities : List (List GoldWord)) (statement : Statement)
    (built : NativeSharedLookupStatement.build geometry.geometry.1 (List.ofFn requests) jobs multiplicities = some statement) :
    NativeScalarBatchPreflight.dimensions statement = true := by
  have positive := geometry_positive registry helper (List.ofFn requests) geometry preflight
  have repeated := NativeSharedLookupConfig.repetitions_positive policy original (List.ofFn requests) rebuilt registry helper geometry preflight
  have count := NativeSharedLookupProofShape.prepared_count fits requests registry helper geometry preflight completed jobs prepared
  have dimensions := NativeSharedLookupPrepared.build_dimensions fits requests geometry.geometry.1 completed jobs prepared multiplicities statement built
  have nonempty : statement.infos.val ≠ [] := by
    intro empty
    have length := dimensions.1
    rw [empty,List.length_nil] at length
    have claims := dimensions.2
    omega
  exact dimensions_of_infos geometry.geometry.1 (List.ofFn requests) statement
    (NativeSharedLookupStatement.build_spec _ _ _ _ _ built).1 dimensions.1 nonempty positive

/-- The actual completed prelude supplies all statement/job invariants;
no independent metadata, nonempty-batch or degree certificate is input. -/
theorem protocol_dimensions {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (original : List Request)
    (rebuilt : NativeSharedLookupConfig.rebuild policy original = some (List.ofFn requests))
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (multiplicities : List (List GoldWord)) (roots : List NativeRootMessage.Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (finished : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready) : NativeScalarBatchPreflight.dimensions ready.statement = true := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests geometry.geometry.1 multiplicities roots rootFits
    w lookupFuel equalityFuel transcript world ready finished
  exact constructed_dimensions fits requests policy original rebuilt registry helper geometry preflight _ ready.jobs contract.prepared
    multiplicities ready.statement contract.built

/-- Native scalar preflight now requires only the original proof-shape check;
its metadata and node checks are consequences of the constructed statement. -/
theorem protocol_beginVerify {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (original : List Request)
    (rebuilt : NativeSharedLookupConfig.rebuild policy original = some (List.ofFn requests))
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (multiplicities : List (List GoldWord)) (roots : List NativeRootMessage.Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (finished : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (proof : NativeScalarBatchPreflight.Proof) (shape : NativeScalarBatchPreflight.proofShape ready.statement proof = true) :
    NativeScalarBatchPreflight.beginVerify ready.equality.transcript ready.statement proof =
      .ok (NativeScalarBatchWire.bindStatement ready.equality.transcript ready.statement) := by
  apply (NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mpr
  exact ⟨shape,protocol_dimensions fits requests policy original rebuilt registry helper geometry preflight multiplicities roots rootFits
    w lookupFuel equalityFuel transcript world ready finished,rfl⟩

/-- The actual backend-gated initializer/prelude supplies the child state,
prepared jobs and built statement. Scalar metadata is derived on that same
execution, without a separately supplied transcript or metadata certificate. -/
theorem validated_beginVerify {A : Type} {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (policy : Policy) (original : List Request)
    (rebuilt : NativeSharedLookupConfig.rebuild policy original = some (List.ofFn requests))
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : NativeSharedLookupProofShape.Values) (rootFits : values.roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (startChild : OracleProgram.Program (A × NativeTranscript.Transcript))
    (world : InputIndexedOracle.World) (state : A) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (finished : (OracleProgram.run (NativeSharedLookupValidated.withChildState fits requests policy registry geometry openingCount values rootFits
      w lookupFuel equalityFuel startChild) world).run.1 = some (state,ready))
    (proof : NativeScalarBatchPreflight.Proof) (shape : NativeScalarBatchPreflight.proofShape ready.statement proof = true) :
    NativeScalarBatchPreflight.beginVerify ready.equality.transcript ready.statement proof =
      .ok (NativeScalarBatchWire.bindStatement ready.equality.transcript ready.statement) := by
  have completed := NativeSharedLookupValidated.withChildState_spec fits requests policy registry geometry openingCount values rootFits
    w lookupFuel equalityFuel startChild world state ready finished
  exact protocol_beginVerify fits requests policy original rebuilt registry helper geometry preflight values.multiplicities values.roots rootFits
    w lookupFuel equalityFuel (OracleProgram.run startChild world).run.1.2 world ready completed.2.2.2 proof shape

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupMetadata
