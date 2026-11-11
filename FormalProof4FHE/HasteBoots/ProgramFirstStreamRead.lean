module
public import FormalProof4FHE.HasteBoots.LookupScalarTrace
public import FormalProof4FHE.HasteBoots.OracleProgramMachine
@[expose] public section

/-! Recover an actual causal first positive stream read from a complete raw
program history. Starts, hashes and zero-length reads stay in the prefix;
earlier adversarial partial reads of the same input determine selection. -/
namespace FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
noncomputable section

structure First {A : Type} (program : Program A) (world : World) (input : Input) where
  position : ℕ
  offset : ℕ
  count : ℕ
  next : Input → Program A
  active : (runPrefix position program world).run.1 = .inl (.read input offset count next)
  history : (runPrefix position program world).run.2 = ((run program world).run.2.take position)
  fresh : CausalStreamExposure.seen (runPrefix position program world).run.2 input = false
  positive : 0 < count
  outputAt : (run program world).run.2[position]? = some (Observation.output input offset (InputIndexedOracle.bytes world input offset count))

theorem recover {A : Type} (program : Program A) (world : World) (input : Input)
    (seen : CausalStreamExposure.seen (run program world).run.2 input = true) : Nonempty (First program world input) := by
  induction program with
  | pure value => simp only [run,CausalStreamExposure.seen] at seen; contradiction
  | start key next ih =>
    have later : CausalStreamExposure.seen (run next world).run.2 input = true := seen
    obtain ⟨first⟩ := ih later
    refine ⟨⟨first.position+1,first.offset,first.count,first.next,?_,?_,?_,first.positive,?_⟩⟩
    · exact first.active
    · change Observation.start key :: (runPrefix first.position next world).run.2 =
        (Observation.start key :: (run next world).run.2).take (first.position+1)
      rw [List.take_succ_cons,first.history]
    · exact first.fresh
    · exact first.outputAt
  | hash key next ih =>
    have later : CausalStreamExposure.seen (run (next (InputIndexedOracle.sha512 world key)) world).run.2 input = true := seen
    obtain ⟨first⟩ := ih (InputIndexedOracle.sha512 world key) later
    refine ⟨⟨first.position+1,first.offset,first.count,first.next,?_,?_,?_,first.positive,?_⟩⟩
    · exact first.active
    · change Observation.hash key (List.ofFn (InputIndexedOracle.sha512 world key)) :: (runPrefix first.position (next (InputIndexedOracle.sha512 world key)) world).run.2 =
        (Observation.hash key (List.ofFn (InputIndexedOracle.sha512 world key)) :: (run (next (InputIndexedOracle.sha512 world key)) world).run.2).take (first.position+1)
      rw [List.take_succ_cons,first.history]
    · exact first.fresh
    · exact first.outputAt
  | read key offset count next ih =>
    let values := InputIndexedOracle.bytes world key offset count
    by_cases touched : CausalStreamExposure.touches input (.output key offset values) = true
    · have info : key = input ∧ 0 < count := by
        simpa only [CausalStreamExposure.touches,decide_eq_true_eq,values,InputIndexedOracle.bytes_length] using touched
      obtain ⟨same,positive⟩ := info
      subst key
      exact ⟨⟨0,offset,count,next,rfl,rfl,rfl,positive,rfl⟩⟩
    · have untouched : CausalStreamExposure.touches input (.output key offset values) = false := Bool.eq_false_iff.mpr touched
      have later : CausalStreamExposure.seen (run (next values) world).run.2 input = true := by
        change (CausalStreamExposure.touches input (.output key offset values) || CausalStreamExposure.seen (run (next values) world).run.2 input) = true at seen
        rwa [untouched,Bool.false_or] at seen
      obtain ⟨first⟩ := ih values later
      refine ⟨⟨first.position+1,first.offset,first.count,first.next,?_,?_,?_,first.positive,?_⟩⟩
      · exact first.active
      · change Observation.output key offset values :: (runPrefix first.position (next values) world).run.2 =
          (Observation.output key offset values :: (run (next values) world).run.2).take (first.position+1)
        rw [List.take_succ_cons,first.history]
      · change (CausalStreamExposure.touches input (.output key offset values) || CausalStreamExposure.seen (runPrefix first.position (next values) world).run.2 input) = false
        rw [untouched,first.fresh]
        rfl
      · exact first.outputAt

theorem First.selected {A : Type} {program : Program A} {world : World} {input : Input} (first : First program world input) :
    CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix first.position program world).run = some input := by
  simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,first.active,OracleProgramMachine.step,first.positive,first.fresh,and_self,ite_true]

/-- The complete input has one earliest positive observation, regardless
of which later native occurrence established that it was exposed. -/
theorem First.position_unique {A : Type} {program : Program A} {world : World} {input : Input}
    (left right : First program world input) : left.position = right.position := by
  have noEarlier (first later : First program world input) (before : first.position < later.position) : False := by
    have present : ((run program world).run.2.take later.position)[first.position]? =
        some (Observation.output input first.offset (InputIndexedOracle.bytes world input first.offset first.count)) := by
      rw [List.getElem?_take_of_lt before]
      exact first.outputAt
    have seen : CausalStreamExposure.seen ((run program world).run.2.take later.position) input = true := by
      apply List.any_eq_true.mpr
      refine ⟨_,List.mem_of_getElem? present,?_⟩
      simp only [CausalStreamExposure.touches,decide_eq_true_eq,true_and]
      simpa only [InputIndexedOracle.bytes_length] using first.positive
    rw [← later.history,later.fresh] at seen
    contradiction
  exact Nat.le_antisymm (Nat.le_of_not_gt (noEarlier right left)) (Nat.le_of_not_gt (noEarlier left right))

/-- An actual positive output yields the earliest causal read even if it
occurred at an arbitrary far offset, before native verification began. -/
theorem of_output {A : Type} (program : Program A) (world : World) (input : Input) (offset : ℕ) (values : Input)
    (positive : values ≠ []) (present : Observation.output input offset values ∈ (run program world).run.2) :
    Nonempty (First program world input) := by
  apply recover program world input
  apply List.any_eq_true.mpr
  refine ⟨_,present,?_⟩
  simp only [CausalStreamExposure.touches,decide_eq_true_eq,true_and]
  exact List.length_pos_iff.mpr positive

end
end FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
