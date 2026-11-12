module
public import FormalProof4FHE.HasteBoots.LookupRequestRebuild
public import FormalProof4FHE.HasteBoots.AllocatedLookupExecution
@[expose] public section

/-! Configuration rebuilding precedes the existing allocated native entry
point. Rejected configurations issue no oracle work or verifier calls. The
success theorem derives the rebuilt request geometry on the actual assembled
context. This logical entry point still needs Rust/caller cost refinement. -/
namespace FormalProof4FHE.HasteBoots.RebuiltLookupExecution
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeSharedLookupValues (Policy)
open NativeGoldHelperVerification (Context)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)
noncomputable section

inductive Outcome (Memory : Type) where
  | invalid
  | allocated (result : AllocatedLookupExecution.Outcome Memory)

def program {Memory : Type} (policy : Policy) (requests : Vector Request) (entries : List Entry)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) :
    Program (Outcome Memory) :=
  match LookupRequestRebuild.rebuild policy requests with
  | none => .pure .invalid
  | some rebuilt => bind (AllocatedLookupExecution.program entries helperHandle references {template with requests := rebuilt}
      chooseHelper chooseBatch memory) (fun result => .pure (.allocated result))

theorem rejected {Memory : Type} (policy : Policy) (requests : Vector Request) (entries : List Entry)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (world : World) (failed : LookupRequestRebuild.rebuild policy requests = none) :
    (run (program policy requests entries helperHandle references template chooseHelper chooseBatch memory) world).run = (.invalid,[]) := by
  simp only [program,failed,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem assembled_requests (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template ctx : Context (Vector Opening)) (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx) :
    ctx.requests = template.requests := by
  have borrowed := (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).2
  unfold AllocatedHelperContext.borrow at borrowed
  obtain ⟨entry,_,same⟩ := Option.map_eq_some_iff.mp borrowed
  exact (congrArg (fun actual => actual.requests) same).symm

theorem verification_origin {Memory : Type} (policy : Policy) (requests : Vector Request) (entries : List Entry)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (world : World) (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (program policy requests entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 =
      .allocated (.verification ctx result)) :
    ∃ rebuilt, LookupRequestRebuild.rebuild policy requests = some rebuilt ∧
      (run (AllocatedLookupExecution.program entries helperHandle references {template with requests := rebuilt}
        chooseHelper chooseBatch memory) world).run.1 = .verification ctx result ∧
      ctx.requests = rebuilt ∧ NativeSharedLookupConfig.Valid (ctx.requests.val.map Request.toModel) ∧
      (run (program policy requests entries helperHandle references template chooseHelper chooseBatch memory) world).run.2 =
        (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2 := by
  unfold program at executed ⊢
  cases built : LookupRequestRebuild.rebuild policy requests with
  | none => simp only [built,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some rebuilt =>
    simp only [built,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed ⊢
    have actual := Outcome.allocated.inj executed
    have allocated := AllocatedLookupExecution.verification_origin entries helperHandle references {template with requests := rebuilt}
      chooseHelper chooseBatch memory world ctx result actual
    have kept : ctx.requests = rebuilt := assembled_requests entries helperHandle references _ ctx allocated.1
    refine ⟨rebuilt,rfl,actual,kept,?_,?_⟩
    · rw [kept]
      exact LookupRequestRebuild.valid built
    · simpa only [List.append_nil] using allocated.2.2

end
end FormalProof4FHE.HasteBoots.RebuiltLookupExecution
