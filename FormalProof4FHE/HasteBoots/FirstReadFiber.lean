module
public import FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
public import FormalProof4FHE.HasteBoots.ReceiptProgramObservation
@[expose] public section

/-! Replay of the complete pre-read packet preserves the actual earliest
read, including its position, offset, width and continuation. No equality of
future outputs or completed executions is required. -/
namespace FormalProof4FHE.HasteBoots.FirstReadFiber
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ProgramFirstStreamRead (First)
noncomputable section

theorem output_of_active {A : Type} (program : Program A) (world : World) (position : ℕ)
    (input : Input) (offset count : ℕ) (next : Input → Program A)
    (active : (runPrefix position program world).run.1 = .inl (.read input offset count next)) :
    (run program world).run.2[position]? = some (.output input offset (InputIndexedOracle.bytes world input offset count)) := by
  induction program generalizing position with
  | pure value => cases position <;> cases active
  | start key tail ih =>
    cases position with
    | zero => cases active
    | succ position => exact ih position active
  | read key start amount tail ih =>
    cases position with
    | zero =>
      have same := Program.read.inj (Sum.inl.inj active)
      obtain ⟨rfl,rfl,rfl,rfl⟩ := same
      rfl
    | succ position => exact ih _ position active
  | hash key tail ih =>
    cases position with
    | zero => cases active
    | succ position => exact ih _ position active

/-- The first read transports directly to another world on the same raw
prefix fiber, keeping its exact position and native read parameters. -/
def transport {A : Type} {program : Program A} {world : World} {input : Input}
    (first : First program world input) (other : World)
    (same : (runPrefix first.position program other).run = (runPrefix first.position program world).run) :
    First program other input where
  position := first.position
  offset := first.offset
  count := first.count
  next := first.next
  active := by rw [congrArg Prod.fst same]; exact first.active
  history := ReceiptProgramObservation.history program other first.position
  fresh := by rw [congrArg Prod.snd same]; exact first.fresh
  positive := first.positive
  outputAt := output_of_active program other first.position input first.offset first.count first.next
    (by rw [congrArg Prod.fst same]; exact first.active)

theorem position_on_fiber {A : Type} {program : Program A} {world other : World} {input : Input}
    (first : First program world input) (later : First program other input)
    (same : (runPrefix first.position program other).run = (runPrefix first.position program world).run) :
    later.position = first.position :=
  later.position_unique (transport first other same)

end
end FormalProof4FHE.HasteBoots.FirstReadFiber
