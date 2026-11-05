module

public import FormalProof4FHE.HasteBoots.NativeCheckpointBoundary
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude

@[expose] public section

/-! Helper snapshots after the actual lookup sampler, before equality draws.
The native finished/job/count gate is computed. Helper words may depend on
the preceding outer lookup challenge; no reader-independence claim is made.
Adversarial prequeries and joint-world probability transport remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints

open NativeTranscript (Transcript Observation)
open NativeRootMessage (Digest)
open NativeUsizeMessage (Usize)
open NativeSharedLookupStatement (Request Prepared tags)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

structure Context (count : ℕ) where
  fits : count ≤ 2^64
  requests : Fin count → Request
  n : Usize
  multiplicities : List (List NativeFieldRepresentation.GoldWord)
  roots : NativePrefixCodec.Vector Digest
  w : ℕ
  lookupFuel : ℕ
  equalityFuel : ℕ
  transcript : Transcript

structure Ready where
  transcript : Transcript
  jobs : List Prepared

noncomputable section
variable {count : ℕ} {Cfg : Type}

def Context.lookup (ctx : Context count) : OracleProgram.Program NativeGoldLookupBatch.Machine :=
  NativeGoldLookupBatch.steps ctx.w ctx.lookupFuel
    (NativeGoldLookupBatch.initial (NativeGoldLookupBatch.schedule ctx.fits
      (fun i => ⟨(ctx.requests i).columns,(ctx.requests i).table,(ctx.requests i).repetitions⟩)) ctx.transcript)

/-- Exactly the original finished-sampler, prepared-job and root-count gates. -/
def gate (ctx : Context count) (batch : NativeGoldLookupBatch.Machine) : Option Ready :=
  let projected := NativeGoldLookupBatch.project batch
  match projected.control with
  | .finished transcript =>
    (NativeSharedLookupPrepared.prepare projected.completed (tags ctx.fits ctx.requests)).bind (fun jobs =>
      if ctx.roots.val.length = jobs.length then some ⟨transcript,jobs⟩ else none)
  | _ => none

def Context.tail (ctx : Context count) (batch : NativeGoldLookupBatch.Machine) :
    OracleProgram.Program (Option (NativeSharedLookupPrelude.Ready ctx.n.val)) :=
  match gate ctx batch with
  | none => .pure none
  | some ready => OracleProgram.bind
    (NativeLookupEquality.request NativeExtensionFields.goldilocksBasis ctx.w ctx.n.val ctx.equalityFuel ready.transcript ctx.roots.val ctx.roots.property)
    (fun machine => .pure (NativeSharedLookupPrelude.pack ctx.n (List.ofFn ctx.requests) ready.jobs ctx.multiplicities machine))

def Context.native (ctx : Context count) : OracleProgram.Program (Option (NativeSharedLookupPrelude.Ready ctx.n.val)) :=
  NativeSharedLookupPrelude.protocol ctx.fits ctx.requests ctx.n ctx.multiplicities ctx.roots.val ctx.roots.property
    ctx.w ctx.lookupFuel ctx.equalityFuel ctx.transcript

theorem native_eq (ctx : Context count) : ctx.native = OracleProgram.bind ctx.lookup ctx.tail := by
  unfold Context.native NativeSharedLookupPrelude.protocol Context.lookup
  congr 1
  funext batch
  unfold NativeSharedLookupPrelude.compile Context.tail gate
  dsimp only
  cases (NativeGoldLookupBatch.project batch).control with
  | ready todo transcript => rfl
  | sampling job todo selection => rfl
  | finished transcript =>
    cases NativeSharedLookupPrepared.prepare (NativeGoldLookupBatch.project batch).completed (tags ctx.fits ctx.requests) with
    | none => rfl
    | some jobs => simp only [Option.bind_some]; split <;> rfl

theorem gate_spec (ctx : Context count) (batch : NativeGoldLookupBatch.Machine) (ready : Ready)
    (success : gate ctx batch = some ready) :
    (NativeGoldLookupBatch.project batch).control = .finished ready.transcript ∧
      NativeSharedLookupPrepared.prepare (NativeGoldLookupBatch.project batch).completed (tags ctx.fits ctx.requests) = some ready.jobs ∧
      ctx.roots.val.length = ready.jobs.length := by
  unfold gate at success
  dsimp only at success
  cases state : (NativeGoldLookupBatch.project batch).control with
  | ready todo transcript => simp only [state] at success; contradiction
  | sampling job todo selection => simp only [state] at success; contradiction
  | finished transcript =>
    rw [state] at success
    cases prepared : NativeSharedLookupPrepared.prepare (NativeGoldLookupBatch.project batch).completed (tags ctx.fits ctx.requests) with
    | none => simp only [prepared,Option.bind_none] at success; contradiction
    | some jobs =>
      simp only [prepared,Option.bind_some] at success
      split at success
      next size => cases success; exact ⟨rfl,rfl,size⟩
      next => contradiction

def roots (ctx : Context count) (tag : Fin ctx.roots.val.length → Cfg) : List (Cfg × Digest) :=
  List.ofFn (fun index => (tag index,ctx.roots.val[index.val]))

theorem root_mem (ctx : Context count) (tag : Fin ctx.roots.val.length → Cfg) (index : Fin ctx.roots.val.length) :
    (tag index,ctx.roots.val[index.val]) ∈ roots ctx tag := List.mem_ofFn.mpr ⟨index,rfl⟩

def selected (ctx : Context count) (tag : Fin ctx.roots.val.length → Cfg) (batch : NativeGoldLookupBatch.Machine) : List (Cfg × Digest) :=
  if (gate ctx batch).isSome then roots ctx tag else []

def freeze (ctx : Context count) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.roots.val.length → Cfg) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (NativeGoldLookupBatch.Machine × List Observation) :=
  NativeCheckpointBoundary.freeze reader ctx.lookup (selected ctx tag)

def program (ctx : Context count) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.roots.val.length → Cfg) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (NativeSharedLookupPrelude.Ready ctx.n.val) × List Observation) :=
  NativeCheckpointBoundary.program reader ctx.lookup (selected ctx tag) ctx.tail

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
variable [SampleableType Digest]

theorem native_replay (ctx : Context count) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.roots.val.length → Cfg)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option (NativeSharedLookupPrelude.Ready ctx.n.val) × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader tag)).run before)) :
    (OracleProgram.run ctx.native (NativeCheckpointProgram.world reader after.hash.cache)).run = result := by
  rw [native_eq]
  exact NativeCheckpointBoundary.native_replay reader ctx.lookup (selected ctx tag) ctx.tail NativeGoldColumnAuthentication.encoding dummy shape before after result supported

/-- A returned equality/statement result derives the actual completed outer
sampler and its checked job order. All helper snapshots precede equality. -/
theorem recorded_helpers (ctx : Context count) (reader : NativeCheckpointProgram.Reader) (tag : Fin ctx.roots.val.length → Cfg)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option (NativeSharedLookupPrelude.Ready ctx.n.val) × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader tag)).run before)) (returned : result.1 ≠ none) :
    ∃ batch observations ready earlier middle later,
      ((batch,observations),earlier) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader ctx.lookup)).run before) ∧
      gate ctx batch = some ready ∧
      middle = RecordRoots.state shape (roots ctx tag) earlier ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader (ctx.tail batch))).run middle) ∧
      result = (later.1,observations ++ later.2) ∧
      (∀ index : Fin ctx.roots.val.length,
        ⟨tag index,⟨ctx.roots.val[index.val],earlier.hash.log⟩⟩ ∈ middle.checkpoints.checkpoints) ∧
      (∀ index : Fin ctx.roots.val.length,
        ⟨tag index,⟨ctx.roots.val[index.val],earlier.hash.log⟩⟩ ∈ after.checkpoints.checkpoints) := by
  obtain ⟨⟨batch,observations⟩,earlier,middle,later,prepared,same,continued,resultSame,recorded⟩ :=
    NativeCheckpointBoundary.program_recorded reader ctx.lookup (selected ctx tag) ctx.tail NativeGoldColumnAuthentication.encoding dummy shape before after result supported
  cases checked : gate ctx batch with
  | none =>
    simp only [Context.tail,checked,NativeCheckpointProgram.compile,simulateQ_pure,StateT.run_pure] at continued
    have final := eq_of_mem_support_pure _ continued
    cases final
    exact (returned (congrArg Prod.fst resultSame)).elim
  | some ready =>
    have chosen : selected ctx tag batch = roots ctx tag := by simp only [selected,checked,Option.isSome_some,ite_true]
    rw [chosen] at same recorded
    refine ⟨batch,observations,ready,earlier,middle,later,prepared,checked,same,continued,resultSame,?_,?_⟩
    · intro index
      rw [same]
      exact RecordRoots.recorded shape (roots ctx tag) earlier _ (root_mem ctx tag index)
    · intro index
      exact recorded _ (root_mem ctx tag index)

end
end FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints
