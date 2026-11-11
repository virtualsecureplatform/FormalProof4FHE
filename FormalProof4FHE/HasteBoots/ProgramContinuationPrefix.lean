module
public import FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
@[expose] public section

/-! Appending a causal continuation preserves every active original prefix
and first positive read, with the same observation ordinal. -/
namespace FormalProof4FHE.HasteBoots.ProgramContinuationPrefix
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix bind)
noncomputable section

theorem active_bind {A B : Type} (program : Program A) (next : A → Program B)
    (position : ℕ) (world : World) (tail : Program A)
    (active : (runPrefix position program world).run.1 = .inl tail) :
    (runPrefix position (bind program next) world).run =
      (.inl (bind tail next),(runPrefix position program world).run.2) := by
  induction position generalizing program tail with
  | zero => cases program <;> simp only [runPrefix] at active ⊢ <;> cases active <;> rfl
  | succ position ih =>
    cases program with
    | pure value => cases active
    | start input rest =>
      have same := ih rest tail active
      change ((runPrefix position (bind rest next) world).run.1,
        [.start input] ++ (runPrefix position (bind rest next) world).run.2) = _
      rw [same]
      rfl
    | read input offset count rest =>
      have same := ih (rest (InputIndexedOracle.bytes world input offset count)) tail active
      change ((runPrefix position (bind (rest (InputIndexedOracle.bytes world input offset count)) next) world).run.1,
        [.output input offset (InputIndexedOracle.bytes world input offset count)] ++
        (runPrefix position (bind (rest (InputIndexedOracle.bytes world input offset count)) next) world).run.2) = _
      rw [same]
      rfl
    | hash input rest =>
      have same := ih (rest (InputIndexedOracle.sha512 world input)) tail active
      change ((runPrefix position (bind (rest (InputIndexedOracle.sha512 world input)) next) world).run.1,
        [.hash input (List.ofFn (InputIndexedOracle.sha512 world input))] ++
        (runPrefix position (bind (rest (InputIndexedOracle.sha512 world input)) next) world).run.2) = _
      rw [same]
      rfl

theorem log_prefix {A B : Type} (program : Program A) (next : A → Program B) (world : World) :
    (run program world).run.2.IsPrefix (run (bind program next) world).run.2 := by
  rw [OracleProgram.run_bind,ObservationReplay.run_bind]
  exact ⟨_,rfl⟩

def first {A B : Type} {program : Program A} {world : World} {input : Input}
    (original : ProgramFirstStreamRead.First program world input) (next : A → Program B) :
    ProgramFirstStreamRead.First (bind program next) world input where
  position := original.position
  offset := original.offset
  count := original.count
  next := fun values => bind (original.next values) next
  active := by
    have same := active_bind program next original.position world _ original.active
    exact congrArg Prod.fst same
  history := by
    have same := congrArg Prod.snd (active_bind program next original.position world _ original.active)
    rw [same,original.history,OracleProgram.run_bind,ObservationReplay.run_bind]
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp original.outputAt
    exact (List.take_append_of_le_length (by omega)).symm
  fresh := by
    rw [show (runPrefix original.position (bind program next) world).run.2 =
      (runPrefix original.position program world).run.2 from congrArg Prod.snd (active_bind program next original.position world _ original.active)]
    exact original.fresh
  positive := original.positive
  outputAt := by
    rw [OracleProgram.run_bind,ObservationReplay.run_bind]
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp original.outputAt
    rw [List.getElem?_append_left (by omega)]
    exact original.outputAt

end
end FormalProof4FHE.HasteBoots.ProgramContinuationPrefix
