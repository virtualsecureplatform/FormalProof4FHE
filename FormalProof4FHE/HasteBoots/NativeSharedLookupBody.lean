module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupParent

@[expose] public section

/-!
# Shared child body through strict terminal guards and finishing

The same ready prelude, proof and retained child binding feed the actual
scalar verifier. Only returned scalar claims enter the terminal guards;
only a successful guard binds terminal values and finishes the child.
A bound result is ready for PCS checks, not an authenticated proof.
Analysis fuel suspends execution and is not a native retry cutoff.
-/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupBody

open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupStatement (Request)
open NativeScalarBatchVerifier (Machine SubClaim)
open OracleProgram (Program bind run)

inductive Error where
  | scalar (reason : NativeScalarBatchVerifier.Error)
  | noSource | terminal | noParent
  | lineage (reason : TypedTranscriptChild.Error)
  deriving DecidableEq

/-- Retained operational output before helper/source PCS authentication. -/
structure Bound where
  machine : Machine
  claims : List SubClaim
  sourceVariables : ℕ
  terminal : NativeSharedLookupGuard.Result
  parent : Transcript
  child : TypedTranscriptChild.Child

inductive Outcome where
  | suspended (machine : Machine)
  | rejected (reason : Error) (machine : Machine)
  | bound (result : Bound)

noncomputable section

def inputs {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B) : NativeSharedLookupGuard.Inputs :=
  NativeSharedLookupPrelude.guardInputs requests ready proof.values.sources proof.values.helpers

def finish {S B : Type} (state : NativeSharedLookupChild.State) (proof : NativeSharedLookupProofData.Proof S B)
    (machine : Machine) : Program TypedTranscriptChild.FinishResult :=
  NativeSharedLookupChild.finish state (NativeSharedLookupChild.bindTerminal machine.state.transcript proof)

def afterScalar {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (machine : Machine) : Program Outcome :=
  match machine.control with
  | .ready | .sampling _ _ => .pure (.suspended machine)
  | .failed reason => .pure (.rejected (.scalar reason) machine)
  | .finished claims =>
    match registry.head? with
    | none => .pure (.rejected .noSource machine)
    | some first =>
      match NativeSharedLookupGuard.guard (inputs requests ready proof) claims first.numVariables.val width with
      | none => .pure (.rejected .terminal machine)
      | some terminal => bind (finish state proof machine) (fun finished =>
        match finished.outcome with
        | .error reason => .pure (.rejected (.lineage reason) machine)
        | .ok () => match finished.parent with
          | none => .pure (.rejected .noParent machine)
          | some parent => .pure (.bound ⟨machine,claims,first.numVariables.val,terminal,parent,finished.child⟩))

def body {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) : Program Outcome :=
  bind (NativeScalarBatchVerifier.verifyPrefix fuel ready.equality.transcript ready.statement proof.algebra)
    (afterScalar requests registry width state ready proof)

/-- The scalar prefix and the finish prefix remain in the same ordered
oracle log; terminal guards and value binding add no oracle observations. -/
theorem run_body {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) (world : World) :
    (run (body requests registry width state ready proof fuel) world).run =
      let scalar := NativeScalarBatchVerifier.execute ready.statement proof.algebra fuel
        (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof.algebra) world
      let later := (run (afterScalar requests registry width state ready proof scalar.1) world).run
      (later.1,scalar.2 ++ later.2) := by
  simp only [body,NativeScalarBatchVerifier.verifyPrefix,OracleProgram.run_bind,ObservationReplay.run_bind,NativeScalarBatchVerifier.run_steps]

structure BoundContract {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (world : World) (result : Bound) : Prop where
  scalar : result.machine.control = .finished result.claims
  source : ∃ first, registry.head? = some first ∧ result.sourceVariables = first.numVariables.val
  guarded : NativeSharedLookupGuard.guard (inputs requests ready proof) result.claims result.sourceVariables width = some result.terminal
  finished : (run (finish state proof result.machine) world).run.1 = ⟨.ok (),some result.parent,result.child⟩

theorem afterScalar_bound {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (machine : Machine) (world : World) (result : Bound)
    (success : (run (afterScalar requests registry width state ready proof machine) world).run.1 = .bound result) :
    result.machine = machine ∧ BoundContract requests registry width state ready proof world result := by
  cases control : machine.control with
  | ready => simp only [afterScalar,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | sampling packet field => simp only [afterScalar,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | failed reason => simp only [afterScalar,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | finished claims =>
    cases source : registry.head? with
    | none => simp only [afterScalar,control,source,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some first =>
      cases guarded : NativeSharedLookupGuard.guard (inputs requests ready proof) claims first.numVariables.val width with
      | none => simp only [afterScalar,control,source,guarded,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
      | some terminal =>
        simp only [afterScalar,control,source,guarded,OracleProgram.run_bind,ObservationReplay.run_bind] at success
        cases finished : (run (finish state proof machine) world).run.1 with
        | mk outcome parent child =>
          cases outcome with
          | error reason => simp only [finished,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
          | ok value =>
            cases value
            cases parent with
            | none => simp only [finished,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
            | some parent =>
              simp only [finished,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
              have same := Outcome.bound.inj success
              subst result
              exact ⟨rfl,control,⟨first,source,rfl⟩,guarded,finished⟩

theorem body_bound {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) (world : World) (result : Bound)
    (success : (run (body requests registry width state ready proof fuel) world).run.1 = .bound result) :
    result.machine = (NativeScalarBatchVerifier.execute ready.statement proof.algebra fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof.algebra) world).1 ∧
      BoundContract requests registry width state ready proof world result := by
  rw [run_body] at success
  exact afterScalar_bound requests registry width state ready proof _ world result success

/-- A completed scalar run derives its own successful initial preflight;
neither acceptance nor a first-info certificate is an input. -/
theorem finished_preflight (transcript : Transcript) (statement : NativeScalarBatchWire.Statement)
    (proof : NativeScalarBatchPreflight.Proof) (fuel : ℕ) (world : World) (claims : List SubClaim)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims) :
    ∃ bound first, NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok bound ∧
      statement.infos.val.head? = some first := by
  cases accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof with
  | error reason =>
    have failed := NativeScalarBatchVerifier.initial_failure transcript statement proof reason accepted
    have stopped := NativeScalarBatchVerifier.execute_terminal statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world (.inr ⟨.reject reason,by rw [failed]⟩)
    rw [stopped,failed] at finished
    contradiction
  | ok bound =>
    obtain ⟨first,head,_⟩ := NativeScalarBatchPreflight.dimensions_success statement
      ((NativeScalarBatchPreflight.beginVerify_ok_iff transcript bound statement proof).mp accepted).2.1
    exact ⟨bound,first,rfl,head⟩

/-- Every bound result inherits the existing independent scalar equations,
actual sampled point and original slot/terminal evidence. -/
theorem body_linked {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) (world : World) (result : Bound)
    (success : (run (body requests registry width state ready proof fuel) world).run.1 = .bound result) :
    ∃ first, NativeSharedLookupBatchLink.Linked (inputs requests ready proof) ready.statement proof.algebra first
      result.machine result.claims result.sourceVariables width result.terminal := by
  have actual := body_bound requests registry width state ready proof fuel world result success
  have finished := actual.2.scalar
  rw [actual.1] at finished
  obtain ⟨bound,first,accepted,head⟩ := finished_preflight ready.equality.transcript ready.statement proof.algebra fuel world result.claims finished
  refine ⟨first,?_⟩
  rw [actual.1]
  exact NativeSharedLookupBatchLink.initialized_link (inputs requests ready proof) ready.equality.transcript bound
    ready.statement proof.algebra first accepted head fuel world result.claims finished result.sourceVariables width result.terminal actual.2.guarded

/-- Strict terminal failure cannot bind terminal values or query the parent
checkpoint; the scalar transcript remains the last computed child state. -/
theorem terminal_failure {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (machine : Machine) (claims : List SubClaim) (world : World) (first : Parameters)
    (completed : machine.control = .finished claims) (source : registry.head? = some first)
    (rejected : NativeSharedLookupGuard.guard (inputs requests ready proof) claims first.numVariables.val width = none) :
    (run (afterScalar requests registry width state ready proof machine) world).run = (.rejected .terminal machine,[]) := by
  simp only [afterScalar,completed,source,rejected,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- Successful finishing clears the returned binding. Earlier immutable
snapshots are outside this per-child state guarantee. -/
theorem bound_spent {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (world : World) (result : Bound) (contract : BoundContract requests registry width state ready proof world result) :
    result.child.binding = none := by
  have finished := contract.finished
  simp only [finish,NativeSharedLookupChild.finish,TypedTranscriptChild.run_finish] at finished
  have spent := TypedTranscriptChild.accepted_binding_spent world (some state.parent)
    ⟨some (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof),some state.binding⟩
    (by rw [finished])
  simpa only [finished] using spent

/-- The complete accepting finish log contains the retained-parent
checkpoint and child fingerprint queries, even when their keys repeat. -/
theorem bound_finish_log {S B : Type} {count dimension : ℕ} (requests : Fin count → Request)
    (registry : List Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (world : World) (result : Bound) (contract : BoundContract requests registry width state ready proof world result) :
    (run (finish state proof result.machine) world).run.2.length = 4 := by
  have finished := contract.finished
  simp only [finish,NativeSharedLookupChild.finish,TypedTranscriptChild.run_finish] at finished ⊢
  have accepted : (TypedTranscriptChild.finishExecute world (some state.parent)
      ⟨some (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof),some state.binding⟩).1.outcome = .ok () := by rw [finished]
  have conditions := (TypedTranscriptChild.finish_accepts_iff world state.parent
    (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof) state.binding).mp accepted
  exact TypedTranscriptChild.finish_success_log_length world state.parent
    (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof) state.binding conditions.1 conditions.2.1 conditions.2.2

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupBody
