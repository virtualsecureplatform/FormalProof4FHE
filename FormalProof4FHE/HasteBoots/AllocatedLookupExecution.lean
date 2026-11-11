module
public import FormalProof4FHE.HasteBoots.AllocatedLookupContext
public import FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
@[expose] public section

/-! Execute the actual native lookup only after successful original source
collection and helper borrowing. Failed assembly has an explicit outcome and
cannot invoke either verifier scheduler. Assembly cost remains a separate
physical refinement obligation. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupExecution
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)
noncomputable section

inductive Outcome (Memory : Type) where
  | unavailable
  | verification (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)

def program {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) : Program (Outcome Memory) :=
  match AllocatedLookupContext.assemble entries helperHandle references template with
  | none => .pure .unavailable
  | some ctx => bind (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory)
      (fun result => .pure (.verification ctx result))

theorem unavailable {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (failed : AllocatedLookupContext.assemble entries helperHandle references template = none) :
    (run (program entries helperHandle references template chooseHelper chooseBatch memory) world).run = (.unavailable,[]) := by
  simp only [program,failed,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

/-- The returned context is the one actually assembled and executed; the
complete observation history is exactly the native verifier history. -/
theorem verification_origin {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result) :
    AllocatedLookupContext.assemble entries helperHandle references template = some ctx ∧
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1 = result ∧
      (run (program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2 =
        (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2 := by
  unfold program at executed ⊢
  cases assembled : AllocatedLookupContext.assemble entries helperHandle references template with
  | none => simp only [assembled,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | some actual =>
    simp only [assembled,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed ⊢
    obtain ⟨rfl,equal⟩ := Outcome.verification.inj executed
    exact ⟨rfl,equal,by simp⟩

end
end FormalProof4FHE.HasteBoots.AllocatedLookupExecution
