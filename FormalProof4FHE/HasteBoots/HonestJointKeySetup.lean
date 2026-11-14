module
public import FormalProof4FHE.HasteBoots.HonestControlKeySetup
public import FormalProof4FHE.HasteBoots.HonestKeySetupReceipts
public import FormalProof4FHE.HasteBoots.HonestSetupContinuation
@[expose] public section

/-! Actual blind-rotation and key-switch key setup share one cache and log.
Both factual receipts and initial verifier invariants come from that execution. -/
namespace FormalProof4FHE.HasteBoots.HonestJointKeySetup
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q cells lanes rows levels c keyLevels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} {H : Cfg → ℕ}
variable (controlParameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
  (keyParameters : Fin keyLevels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
  (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
  (original : NativeKeySwitch.Key q (2^(c+2)) keyLevels)

/-- The second setup follows the actual control-key hashes without resetting state. -/
def program {ι : Type} {base : OracleSpec ι} :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      ((Fin (2*levels) → Digest) × (Fin keyLevels → Digest)) := do
  let controlRoots ← HonestControlKeySetup.program controlParameters enc psi controls
  let keyRoots ← HonestKeySetupReceipts.program keyParameters enc psi original
  pure (controlRoots,keyRoots)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {ι : Type} {base : OracleSpec ι}

/-- A subsequent supported key-switch setup establishes its receipt and preserves
all invariants already supplied by actual earlier setup. -/
theorem keys_from_state (impl : QueryImpl base ProbComp) (dummy : Digest) (shape : Cfg → Skeleton)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (incoming : HonestSetupContinuation.Ready enc dummy shape initial)
    (result : (Fin keyLevels → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestKeySetupReceipts.program keyParameters enc psi original)).run initial)) :
    HonestKeyQueryReceipt.Receipt keyParameters enc psi original result.1 result.2.hash.log ∧
      HonestSetupContinuation.Ready enc dummy shape result.2 := by
  rw [HonestKeySetupReceipts.program,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
  obtain ⟨built,present,equal⟩ := supported
  subst result
  exact ⟨HonestKeyQueryReceipt.of_setup impl keyParameters enc dummy psi original shape initial built present,
    HonestSetupContinuation.from_state impl enc dummy shape keyParameters
      (HonestRecordedEvaluationKey.table keyParameters psi original) initial incoming built present⟩

abbrev Result (shape : Cfg → Skeleton) :=
  ((Fin (2*levels) → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
    ((Fin keyLevels → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)

/-- Retain the intermediate actual setup state as evidence for both executions. -/
def witness (impl : QueryImpl base ProbComp) (dummy : Digest) (shape : Cfg → Skeleton) :
    ProbComp (Result (levels := levels) (keyLevels := keyLevels) (Input := Input) (Digest := Digest) shape) := do
  let controlBuilt ← (simulateQ (CheckpointExecution.handler impl enc dummy shape)
    (HonestControlKeySetup.program controlParameters enc psi controls)).run (CheckpointExecution.empty shape)
  let keyBuilt ← (simulateQ (CheckpointExecution.handler impl enc dummy shape)
    (HonestKeySetupReceipts.program keyParameters enc psi original)).run controlBuilt.2
  pure (controlBuilt,keyBuilt)

/-- Recover both literal supported calls, with the second starting at the first end. -/
theorem parts (impl : QueryImpl base ProbComp) (dummy : Digest) (shape : Cfg → Skeleton)
    (result : Result (levels := levels) (keyLevels := keyLevels) (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support (witness controlParameters keyParameters enc psi controls original impl dummy shape)) :
    result.1 ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestControlKeySetup.program controlParameters enc psi controls)).run (CheckpointExecution.empty shape)) ∧
    result.2 ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestKeySetupReceipts.program keyParameters enc psi original)).run result.1.2) := by
  simp only [witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,second,secondSupported,equal⟩ := supported
  subst result
  exact ⟨firstSupported,secondSupported⟩

/-- Both real setups project to one raw oracle run, keeping the entire final monitor. -/
theorem project_witness (impl : QueryImpl base ProbComp) (dummy : Digest) (shape : Cfg → Skeleton) :
    (fun result => ((result.1.1,result.2.1),result.2.2)) <$>
      witness controlParameters keyParameters enc psi controls original impl dummy shape =
    (simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program controlParameters keyParameters enc psi controls original)).run (CheckpointExecution.empty shape) := by
  simp only [witness,program,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,map_bind,map_pure]

/-- Both receipts refer to the same final log; readiness is derived from actual
setup support, including the shared populated cache and every later geometry. -/
theorem initialized (impl : QueryImpl base ProbComp) (dummy : Digest) (shape : Cfg → Skeleton)
    (result : Result (levels := levels) (keyLevels := keyLevels) (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support (witness controlParameters keyParameters enc psi controls original impl dummy shape)) :
    HonestControlKeySetup.Receipt controlParameters enc psi controls result.1.1 result.2.2.hash.log ∧
    HonestKeyQueryReceipt.Receipt keyParameters enc psi original result.2.1 result.2.2.hash.log ∧
    HonestSetupContinuation.Ready enc dummy shape result.2.2 := by
  have executed := parts controlParameters keyParameters enc psi controls original impl dummy shape result supported
  have control := HonestControlKeySetup.initialized impl controlParameters enc dummy psi controls shape result.1 executed.1
  have ready : HonestSetupContinuation.Ready enc dummy shape result.1.2 :=
    ⟨control.2.1,control.2.2.1,control.2.2.2.1,control.2.2.2.2⟩
  have keys := keys_from_state keyParameters enc psi original impl dummy shape result.1.2 ready result.2 executed.2
  have growing := SharedHashLog.run impl enc dummy shape
    (HonestKeySetupReceipts.program keyParameters enc psi original) result.1.2 result.2 executed.2
  exact ⟨HonestControlKeySetup.mono controlParameters enc psi controls result.1.1
    result.1.2.hash.log result.2.2.hash.log growing control.1,keys.1,keys.2⟩

/-- The same receipts and invariants are available directly from the raw program's
supported return; no intermediate roots or initial-state certificates are assumed. -/
theorem initialized_program (impl : QueryImpl base ProbComp) (dummy : Digest) (shape : Cfg → Skeleton)
    (result : ((Fin (2*levels) → Digest) × (Fin keyLevels → Digest)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program controlParameters keyParameters enc psi controls original)).run (CheckpointExecution.empty shape))) :
    HonestControlKeySetup.Receipt controlParameters enc psi controls result.1.1 result.2.hash.log ∧
    HonestKeyQueryReceipt.Receipt keyParameters enc psi original result.1.2 result.2.hash.log ∧
    HonestSetupContinuation.Ready enc dummy shape result.2 := by
  rw [←project_witness controlParameters keyParameters enc psi controls original impl dummy shape,
    support_map,Set.mem_image] at supported
  obtain ⟨actual,present,equal⟩ := supported
  subst result
  exact initialized controlParameters keyParameters enc psi controls original impl dummy shape actual present

end
end FormalProof4FHE.HasteBoots.HonestJointKeySetup
