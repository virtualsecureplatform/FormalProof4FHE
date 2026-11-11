module
public import FormalProof4FHE.HasteBoots.ParentSeedCollisionRisk
public import FormalProof4FHE.HasteBoots.ReceiptProgramObservation
@[expose] public section

/-! Recognized parent-key naming in the next request agrees with the actual
raw observation at that position, including starts and empty reads. -/
namespace FormalProof4FHE.HasteBoots.ParentSeedObservation
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)

theorem candidate {A : Type} (program : Program A) (world : World) (position : ℕ) (entry : Observation)
    (found : (run program world).run.2[position]? = some entry) :
    (CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1).bind ParentSeedCollisionRisk.candidate =
      ParentSeedCandidates.candidate entry := by
  induction program generalizing position with
  | pure value => cases position <;> simp only [run,CanonicalTranscriptSampler.run_pure,List.getElem?_nil] at found <;> contradiction
  | start input next ih =>
    cases position with
    | zero =>
      have same : Observation.start input = entry := Option.some.inj found
      subst entry
      rfl
    | succ position => exact ih position found
  | read input offset count next ih =>
    cases position with
    | zero =>
      have same : Observation.output input offset (InputIndexedOracle.bytes world input offset count) = entry := Option.some.inj found
      subst entry
      rfl
    | succ position => exact ih _ position found
  | hash input next ih =>
    cases position with
    | zero =>
      have same : Observation.hash input (List.ofFn (InputIndexedOracle.sha512 world input)) = entry := Option.some.inj found
      subst entry
      rfl
    | succ position => exact ih _ position found

end FormalProof4FHE.HasteBoots.ParentSeedObservation
