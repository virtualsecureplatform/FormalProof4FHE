module
public import FormalProof4FHE.HasteBoots.ReceiptCollisionRisk
public import FormalProof4FHE.HasteBoots.OracleProgramMachine
@[expose] public section

/-! The candidate named by an actual observation is the candidate in the
causal next request at its exact raw-log position. -/
namespace FormalProof4FHE.HasteBoots.ReceiptProgramObservation
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)

theorem history {A : Type} (program : Program A) (world : World) (position : ℕ) :
    (runPrefix position program world).run.2 = (run program world).run.2.take position := by
  induction program generalizing position with
  | pure value => cases position <;> rfl
  | start input next ih =>
    cases position with
    | zero => rfl
    | succ position => exact congrArg (List.cons (.start input)) (ih position)
  | read input offset count next ih =>
    cases position with
    | zero => rfl
    | succ position => exact congrArg (List.cons (.output input offset (InputIndexedOracle.bytes world input offset count))) (ih _ position)
  | hash input next ih =>
    cases position with
    | zero => rfl
    | succ position => exact congrArg (List.cons (.hash input (List.ofFn (InputIndexedOracle.sha512 world input)))) (ih _ position)

theorem candidate {A : Type} (program : Program A) (world : World) (position : ℕ) (entry : Observation)
    (found : (run program world).run.2[position]? = some entry) :
    (CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1).bind ReceiptCollisionRisk.candidate =
      ReceiptPayloadView.candidate entry := by
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
      change (if 0 < count then ReceiptPayloadView.read input else none) =
        (if InputIndexedOracle.bytes world input offset count = [] then none else ReceiptPayloadView.read input)
      simp only [← List.length_eq_zero_iff,InputIndexedOracle.bytes_length]
      by_cases positive : 0 < count
      · simp only [positive,Nat.ne_of_gt positive,ite_true,ite_false]
      · have zero : count = 0 := by omega
        simp only [zero,Nat.lt_irrefl,ite_false,ite_true]
    | succ position => exact ih _ position found
  | hash input next ih =>
    cases position with
    | zero =>
      have same : Observation.hash input (List.ofFn (InputIndexedOracle.sha512 world input)) = entry := Option.some.inj found
      subst entry
      rfl
    | succ position => exact ih _ position found

end FormalProof4FHE.HasteBoots.ReceiptProgramObservation
