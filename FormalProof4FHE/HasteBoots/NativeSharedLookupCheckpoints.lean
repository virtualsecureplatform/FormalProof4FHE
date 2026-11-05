module

public import FormalProof4FHE.HasteBoots.NativeCheckpointBoundary
public import FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix
public import FormalProof4FHE.HasteBoots.NativeSharedLookupExecution

@[expose] public section

/-! Source checkpoints at the original registered-parent/child boundary.
All original registry slots are recorded, including unused slots and earlier
alias representatives. Helper roots have a later, distinct placement obligation.
Alias grouping, reader probability laws and complete PCS composition remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints

open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript Observation)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

structure Context (C S B : Type) where
  row : RowDescription C
  registry : NativePrefixCodec.Vector (Oracle C)
  helper : Parameters C
  parent : Transcript
  requests : NativePrefixCodec.Vector Request
  proof : NativeSharedLookupProofData.Proof S B
  lookupFuel : ℕ
  equalityFuel : ℕ
  scalarFuel : ℕ

abbrev Prepared := Transcript × Option NativeSharedLookupPreflight.Output

variable {C S B Cfg : Type}

/-- Slot tags retain the full original registry, independently of usage or
later alias grouping. Every possible first registered representative is covered. -/
def roots (registry : NativePrefixCodec.Vector (Oracle C)) : List (Fin registry.val.length × Digest) :=
  List.ofFn (fun index => (index,(registry.val[index.val]).root))

theorem roots_length (registry : NativePrefixCodec.Vector (Oracle C)) : (roots registry).length = registry.val.length :=
  List.length_ofFn

theorem root_mem (registry : NativePrefixCodec.Vector (Oracle C)) (slot : Fin registry.val.length) :
    (slot,(registry.val[slot.val]).root) ∈ roots registry :=
  List.mem_ofFn.mpr ⟨slot,rfl⟩

/-- Embed original slot tags into the complete execution's configuration
family, which may also contain helper roots with other trusted shapes. -/
def taggedRoots (registry : NativePrefixCodec.Vector (Oracle C)) (tag : Fin registry.val.length → Cfg) : List (Cfg × Digest) :=
  (roots registry).map (fun entry => (tag entry.1,entry.2))

theorem tagged_mem (registry : NativePrefixCodec.Vector (Oracle C)) (tag : Fin registry.val.length → Cfg)
    (slot : Fin registry.val.length) : (tag slot,(registry.val[slot.val]).root) ∈ taggedRoots registry tag :=
  List.mem_map.mpr ⟨(slot,(registry.val[slot.val]).root),root_mem registry slot,rfl⟩

def Context.prepare (ctx : Context C S B) : OracleProgram.Program Prepared :=
  NativeSharedLookupParent.prepare ctx.row ctx.registry ctx.helper ctx.parent ctx.requests

def selected (ctx : Context C S B) (tag : Fin ctx.registry.val.length → Cfg) (prepared : Prepared) : List (Cfg × Digest) :=
  match prepared.2 with
  | none => []
  | some _ => taggedRoots ctx.registry tag

noncomputable section

def Context.tail (ctx : Context C S B) (prepared : Prepared) : OracleProgram.Program (Option NativeSharedLookupBody.Outcome) :=
  match prepared.2 with
  | none => .pure none
  | some geometry => OracleProgram.bind
    (NativeSharedLookupChild.launch ctx.requests.property.le (models ctx.requests) .retain
      (ctx.registry.val.map Oracle.geometry) geometry ctx.proof ctx.lookupFuel ctx.equalityFuel prepared.1)
    (fun launched => match launched with
      | none => .pure none
      | some ready => OracleProgram.bind
        (NativeSharedLookupExecution.continueBody ctx.registry ctx.requests ctx.proof ctx.scalarFuel ⟨geometry,ready⟩)
        (fun result => .pure (some result)))

def Context.native (ctx : Context C S B) : OracleProgram.Program (Option NativeSharedLookupBody.Outcome) :=
  NativeSharedLookupExecution.protocol ctx.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel

private theorem program_assoc {A D E : Type} (front : OracleProgram.Program A)
    (middle : A → OracleProgram.Program D) (last : D → OracleProgram.Program E) :
    OracleProgram.bind (OracleProgram.bind front middle) last =
      OracleProgram.bind front (fun value => OracleProgram.bind (middle value) last) := by
  induction front with
  | pure value => rfl
  | start input next ih => exact congrArg (OracleProgram.Program.start input) ih
  | read input offset count next ih =>
    simp only [OracleProgram.bind]
    congr 1
    funext answer
    exact ih answer
  | hash input next ih =>
    simp only [OracleProgram.bind]
    congr 1
    funext answer
    exact ih answer

/-- The boundary is a factorization of the original entry point, not a
replacement lookup algorithm or a supplied prepared transcript. -/
theorem native_eq (ctx : Context C S B) : ctx.native = OracleProgram.bind ctx.prepare ctx.tail := by
  unfold Context.native NativeSharedLookupExecution.protocol NativeSharedLookupParent.begin Context.prepare
  rw [program_assoc]
  congr 1
  funext packet
  rcases packet with ⟨parent,geometry⟩
  cases geometry with
  | none => rfl
  | some geometry =>
    rw [program_assoc]
    congr 1
    funext launched
    cases launched <;> rfl

def freeze (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.registry.val.length → Cfg) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Prepared × List Observation) :=
  NativeCheckpointBoundary.freeze reader ctx.prepare (selected ctx tag)

def program (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.registry.val.length → Cfg) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest)
      (Option NativeSharedLookupBody.Outcome × List Observation) :=
  NativeCheckpointBoundary.program reader ctx.prepare (selected ctx tag) ctx.tail

/-- The entire freeze computation, including context hashes and root tags,
is independent of the reader which will supply later lookup challenges. -/
theorem freeze_independent (ctx : Context C S B) (tag : Fin ctx.registry.val.length → Cfg) (left right : NativeCheckpointProgram.Reader) :
    freeze ctx left tag = freeze ctx right tag :=
  NativeCheckpointBoundary.freeze_independent ctx.prepare
    (NativeSharedLookupHashPrefix.prepare ctx.row ctx.registry ctx.helper ctx.parent ctx.requests) (selected ctx tag) left right

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
variable [SampleableType Digest]

theorem native_replay (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.registry.val.length → Cfg) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader tag)).run before)) :
    (OracleProgram.run ctx.native (NativeCheckpointProgram.world reader after.hash.cache)).run = result := by
  rw [native_eq]
  exact NativeCheckpointBoundary.native_replay reader ctx.prepare (selected ctx tag) ctx.tail
    NativeGoldColumnAuthentication.encoding dummy shape before after result supported

/-- A returned body result derives successful parent preparation. Every
original slot has a snapshot of that exact earlier hash log, before the
child continuation, and the final state retains all of them. -/
theorem recorded_sources (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.registry.val.length → Cfg) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader tag)).run before))
    (returned : result.1 ≠ none) :
    ∃ parent geometry observations earlier middle later,
      (((parent,some geometry),observations),earlier) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader ctx.prepare)).run before) ∧
      middle = RecordRoots.state shape (taggedRoots ctx.registry tag) earlier ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader (ctx.tail (parent,some geometry)))).run middle) ∧
      result = (later.1,observations ++ later.2) ∧
      (∀ slot : Fin ctx.registry.val.length,
        ⟨tag slot,⟨(ctx.registry.val[slot.val]).root,earlier.hash.log⟩⟩ ∈ middle.checkpoints.checkpoints) ∧
      (∀ slot : Fin ctx.registry.val.length,
        ⟨tag slot,⟨(ctx.registry.val[slot.val]).root,earlier.hash.log⟩⟩ ∈ after.checkpoints.checkpoints) := by
  obtain ⟨⟨⟨parent,geometry⟩,observations⟩,earlier,middle,later,prepared,same,continued,resultSame,recorded⟩ :=
    NativeCheckpointBoundary.program_recorded reader ctx.prepare (selected ctx tag) ctx.tail NativeGoldColumnAuthentication.encoding dummy shape before after result supported
  cases geometry with
  | none =>
    have final := eq_of_mem_support_pure _ continued
    cases final
    exact (returned (congrArg Prod.fst resultSame)).elim
  | some geometry =>
    refine ⟨parent,geometry,observations,earlier,middle,later,prepared,same,continued,resultSame,?_,?_⟩
    · intro slot
      rw [same]
      exact RecordRoots.recorded shape (taggedRoots ctx.registry tag) earlier _ (tagged_mem ctx.registry tag slot)
    · intro slot
      exact recorded _ (tagged_mem ctx.registry tag slot)

end
end FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints
