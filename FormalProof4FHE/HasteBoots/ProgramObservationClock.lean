module
public import FormalProof4FHE.HasteBoots.ByteScalarLogWork
@[expose] public section

/-! Every primitive program step emits one original observation. Scores
that vanish without a next request are supported before the exact original
log length, with no uniform completion depth assumption. -/
namespace FormalProof4FHE.HasteBoots.ProgramObservationClock
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
noncomputable section

theorem complete_length {A : Type} (program : Program A) (world : World) :
    (runPrefix (run program world).run.2.length program world).run =
      (.inr (run program world).run.1,(run program world).run.2) := by
  induction program with
  | pure value => rfl
  | start input rest ih =>
    change ((runPrefix (run rest world).run.2.length rest world).run.1,
      [.start input] ++ (runPrefix (run rest world).run.2.length rest world).run.2) = _
    rw [ih]
    rfl
  | read input offset count rest ih =>
    have same := ih (InputIndexedOracle.bytes world input offset count)
    change ((runPrefix (run (rest (InputIndexedOracle.bytes world input offset count)) world).run.2.length
      (rest (InputIndexedOracle.bytes world input offset count)) world).run.1,
      [.output input offset (InputIndexedOracle.bytes world input offset count)] ++
      (runPrefix (run (rest (InputIndexedOracle.bytes world input offset count)) world).run.2.length
        (rest (InputIndexedOracle.bytes world input offset count)) world).run.2) = _
    rw [same]
    rfl
  | hash input rest ih =>
    have same := ih (InputIndexedOracle.sha512 world input)
    change ((runPrefix (run (rest (InputIndexedOracle.sha512 world input)) world).run.2.length
      (rest (InputIndexedOracle.sha512 world input)) world).run.1,
      [.hash input (List.ofFn (InputIndexedOracle.sha512 world input))] ++
      (runPrefix (run (rest (InputIndexedOracle.sha512 world input)) world).run.2.length
        (rest (InputIndexedOracle.sha512 world input)) world).run.2) = _
    rw [same]
    rfl

theorem request_after_length {A : Type} (program : Program A) (world : World) (position : ℕ)
    (later : (run program world).run.2.length ≤ position) :
    CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1 = none := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le later
  have first : (run (OracleMachine.take OracleProgramMachine.step (run program world).run.2.length program) world).run.1 =
      .inr (run program world).run.1 := by
    rw [OracleProgramMachine.take_run,complete_length]
  have same := OracleMachine.completed_run OracleProgramMachine.step _ extra program world _ first
  simp only [OracleProgramMachine.take_run] at same
  rw [same,complete_length]
  rfl

theorem score_sum {A : Type} (program : Program A) (world : World)
    (score : (Program A ⊕ A) × List NativeTranscript.Observation → ENNReal) (cap : ENNReal)
    (bounded : ∀ packet, score packet ≤ cap)
    (absent : ∀ packet, CausalSeedExposure.request OracleProgramMachine.step packet.1 = none → score packet = 0) :
    (∑' position : ℕ, score (runPrefix position program world).run) ≤ (run program world).run.2.length * cap := by
  rw [tsum_eq_sum (s := Finset.range (run program world).run.2.length) (fun position outside =>
    absent _ (request_after_length program world position (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using outside))))]
  calc
    _ ≤ ∑ _position ∈ Finset.range (run program world).run.2.length, cap := Finset.sum_le_sum (fun _ _ => bounded _)
    _ = _ := by simp [nsmul_eq_mul]

end
end FormalProof4FHE.HasteBoots.ProgramObservationClock
