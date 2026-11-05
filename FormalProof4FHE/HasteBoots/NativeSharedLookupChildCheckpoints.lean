module

public import FormalProof4FHE.HasteBoots.NativeProgramComposition
public import FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints
public import FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints

@[expose] public section

/-! Checked child creation, outer lookup sampling, helper recording and the
original equality/scalar/terminal body. Source checkpoints remain earlier.
These are operational boundaries, not a proof of global prequery freshness. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints

open NativeSharedLookupCheckpoints (Context Prepared)
open NativeSharedLookupParent (Oracle models)
open NativeTranscript (Transcript Observation)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

noncomputable section
variable {C S B Cfg : Type}

def window (ctx : Context C S B) (geometry : NativeSharedLookupPreflight.Output) (child : Transcript) :
    NativeSharedLookupHelperCheckpoints.Context ctx.requests.val.length :=
  ⟨ctx.requests.property.le,models ctx.requests,geometry.geometry.1,ctx.proof.values.multiplicities,ctx.proof.roots,
    7,ctx.lookupFuel,ctx.equalityFuel,child⟩

structure Head where
  state : NativeSharedLookupChild.State
  child : Transcript
  batch : NativeGoldLookupBatch.Machine

/-- Preserve the native proof/value gates before creating or sampling a child. -/
def head (ctx : Context C S B) (prepared : Prepared) : OracleProgram.Program (Option Head) :=
  match prepared.2 with
  | none => .pure none
  | some geometry =>
    if NativeSharedLookupValidated.checks .retain (ctx.registry.val.map Oracle.geometry) (List.ofFn (models ctx.requests))
        geometry ctx.proof.helperOpenings.val.length ctx.proof.values then
      OracleProgram.bind (NativeSharedLookupChild.start prepared.1 ctx.proof.multiplicities) (fun seed =>
        OracleProgram.bind (window ctx geometry seed.2).lookup (fun batch => .pure (some ⟨seed.1,seed.2,batch⟩)))
    else .pure none

def tail (ctx : Context C S B) (prepared : Prepared) (sampled : Option Head) :
    OracleProgram.Program (Option NativeSharedLookupBody.Outcome) :=
  match prepared.2,sampled with
  | some geometry,some sampled =>
    OracleProgram.bind ((window ctx geometry sampled.child).tail sampled.batch) (fun ready => match ready with
      | none => .pure none
      | some ready => OracleProgram.bind
        (NativeSharedLookupExecution.continueBody ctx.registry ctx.requests ctx.proof ctx.scalarFuel ⟨geometry,sampled.state,ready⟩)
        (fun result => .pure (some result)))
  | _,_ => .pure none

/-- Exact factorization of the original checked child/body continuation. -/
theorem native_eq (ctx : Context C S B) (prepared : Prepared) :
    ctx.tail prepared = OracleProgram.bind (head ctx prepared) (tail ctx prepared) := by
  rcases prepared with ⟨parent,geometry⟩
  cases geometry with
  | none => rfl
  | some geometry =>
    unfold NativeSharedLookupCheckpoints.Context.tail NativeSharedLookupChild.launch NativeSharedLookupValidated.withChildState head
    dsimp only
    split
    next checked =>
      simp only [NativeProgramComposition.bind_assoc]
      congr 1
      funext seed
      change OracleProgram.bind (window ctx geometry seed.2).native _ = _
      rw [NativeSharedLookupHelperCheckpoints.native_eq]
      dsimp only [window]
      simp only [NativeProgramComposition.bind_assoc]
      congr 1
      funext batch
      change OracleProgram.bind ((window ctx geometry seed.2).tail batch) _ =
        OracleProgram.bind ((window ctx geometry seed.2).tail batch) _
      congr 1
      funext ready
      cases ready <;> rfl
    next rejected => simp only [OracleProgram.bind,tail]

/-- Roots are selected only after the original finished/job/count gate. -/
def selected (ctx : Context C S B) (prepared : Prepared) (tag : Fin ctx.proof.roots.val.length → Cfg)
    (sampled : Option Head) : List (Cfg × Digest) :=
  match prepared.2,sampled with
  | some geometry,some sampled => NativeSharedLookupHelperCheckpoints.selected (window ctx geometry sampled.child) tag sampled.batch
  | _,_ => []

def program (ctx : Context C S B) (prepared : Prepared) (reader : NativeCheckpointProgram.Reader)
    (tag : Fin ctx.proof.roots.val.length → Cfg) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option NativeSharedLookupBody.Outcome × List Observation) :=
  NativeCheckpointBoundary.program reader (head ctx prepared) (selected ctx prepared tag) (tail ctx prepared)

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
variable [SampleableType Digest]

theorem native_replay (ctx : Context C S B) (prepared : Prepared) (reader : NativeCheckpointProgram.Reader)
    (tag : Fin ctx.proof.roots.val.length → Cfg) (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx prepared reader tag)).run before)) :
    (OracleProgram.run (ctx.tail prepared) (NativeCheckpointProgram.world reader after.hash.cache)).run = result := by
  rw [native_eq]
  exact NativeCheckpointBoundary.native_replay reader (head ctx prepared) (selected ctx prepared tag) (tail ctx prepared)
    NativeGoldColumnAuthentication.encoding dummy shape before after result supported

/-- A returned body result recovers the actual child/outer-sampler prefix and
all checked helper snapshots before equality/scalar continuation. -/
theorem recorded_helpers (ctx : Context C S B) (prepared : Prepared) (reader : NativeCheckpointProgram.Reader)
    (tag : Fin ctx.proof.roots.val.length → Cfg) (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx prepared reader tag)).run before)) (returned : result.1 ≠ none) :
    ∃ geometry sampled observations ready earlier middle later,
      prepared.2 = some geometry ∧
      ((some sampled,observations),earlier) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader (head ctx prepared))).run before) ∧
      NativeSharedLookupHelperCheckpoints.gate (window ctx geometry sampled.child) sampled.batch = some ready ∧
      middle = RecordRoots.state shape (NativeSharedLookupHelperCheckpoints.roots (window ctx geometry sampled.child) tag) earlier ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader (tail ctx prepared (some sampled)))).run middle) ∧
      (∀ index : Fin ctx.proof.roots.val.length,
        ⟨tag index,⟨ctx.proof.roots.val[index.val],earlier.hash.log⟩⟩ ∈ middle.checkpoints.checkpoints) ∧
      (∀ index : Fin ctx.proof.roots.val.length,
        ⟨tag index,⟨ctx.proof.roots.val[index.val],earlier.hash.log⟩⟩ ∈ after.checkpoints.checkpoints) := by
  obtain ⟨⟨sampled,observations⟩,earlier,middle,later,executed,same,continued,resultSame,recorded⟩ :=
    NativeCheckpointBoundary.program_recorded reader (head ctx prepared) (selected ctx prepared tag) (tail ctx prepared)
      NativeGoldColumnAuthentication.encoding dummy shape before after result supported
  cases geometryRead : prepared.2 with
  | none =>
    simp only [tail,geometryRead,NativeCheckpointProgram.compile,simulateQ_pure,StateT.run_pure] at continued
    have final := eq_of_mem_support_pure _ continued
    cases final
    exact (returned (congrArg Prod.fst resultSame)).elim
  | some geometry =>
    cases sampled with
    | none =>
      simp only [tail,geometryRead,NativeCheckpointProgram.compile,simulateQ_pure,StateT.run_pure] at continued
      have final := eq_of_mem_support_pure _ continued
      cases final
      exact (returned (congrArg Prod.fst resultSame)).elim
    | some sampled =>
      cases checked : NativeSharedLookupHelperCheckpoints.gate (window ctx geometry sampled.child) sampled.batch with
      | none =>
        simp only [tail,geometryRead,NativeSharedLookupHelperCheckpoints.Context.tail,checked,OracleProgram.bind,
          NativeCheckpointProgram.compile,simulateQ_pure,StateT.run_pure] at continued
        have final := eq_of_mem_support_pure _ continued
        cases final
        exact (returned (congrArg Prod.fst resultSame)).elim
      | some ready =>
        have chosen : selected ctx prepared tag (some sampled) =
            NativeSharedLookupHelperCheckpoints.roots (window ctx geometry sampled.child) tag := by
          simp only [selected,geometryRead,NativeSharedLookupHelperCheckpoints.selected,checked,Option.isSome_some,ite_true]
        rw [chosen] at same recorded
        refine ⟨geometry,sampled,observations,ready,earlier,middle,later,rfl,executed,checked,same,continued,?_,?_⟩
        · intro index
          rw [same]
          exact RecordRoots.recorded shape _ earlier _ (NativeSharedLookupHelperCheckpoints.root_mem (window ctx geometry sampled.child) tag index)
        · intro index
          exact recorded _ (NativeSharedLookupHelperCheckpoints.root_mem (window ctx geometry sampled.child) tag index)

end
end FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints
