module
public import FormalProof4FHE.HasteBoots.SharedContinuation
@[expose] public section

/-! Append a memory-selected dependent child without losing the actual
predecessor or resetting its state. These are execution/bookkeeping lemmas;
no child security bound is part of this interface. -/
namespace FormalProof4FHE.HasteBoots.DependentStageContinuation
noncomputable section
variable {Before Memory State : Type} {Result : Memory → Type}

def program (select : Before → Option Memory) (start : Before → State)
    (child : (memory : Memory) → State → ProbComp (Result memory)) (before : Before) :
    ProbComp (Before × Option (Sigma Result)) :=
  match select before with
  | none => pure (before,none)
  | some memory => do
    let result ← child memory (start before)
    pure (before,some ⟨memory,result⟩)

def finalState (start : Before → State) (finish : (memory : Memory) → Result memory → State)
    (outcome : Before × Option (Sigma Result)) : State :=
  match outcome.2 with
  | none => start outcome.1
  | some result => finish result.1 result.2

variable (select : Before → Option Memory) (start : Before → State)
  (child : (memory : Memory) → State → ProbComp (Result memory))

/-- Every branch preserves its actual predecessor value. -/
theorem predecessor (before : Before) (outcome : Before × Option (Sigma Result))
    (supported : outcome ∈ support (program select start child before)) : outcome.1 = before := by
  cases selected : select before with
  | none =>
    simp only [program,selected,support_pure,Set.mem_singleton_iff] at supported
    exact congrArg Prod.fst supported
  | some memory =>
    simp only [program,selected,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
    obtain ⟨result,_,same⟩ := supported
    exact congrArg Prod.fst same

/-- The selected memory tag and actual child support are derived from the
executed continuation, not supplied by a child result. -/
theorem reached (before : Before) (result : Sigma Result)
    (supported : (before,some result) ∈ support (program select start child before)) :
    select before = some result.1 ∧ result.2 ∈ support (child result.1 (start before)) := by
  cases selected : select before with
  | none => simp [program,selected] at supported
  | some memory =>
    simp only [program,selected,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
    obtain ⟨actual,present,same⟩ := supported
    have equal : result = ⟨memory,actual⟩ := Option.some.inj (congrArg Prod.snd same)
    cases equal
    exact ⟨rfl,present⟩

/-- State invariants pass through actual selected child executions and all
skipped paths. Concrete callers discharge the local fact from their program. -/
theorem preserves (finish : (memory : Memory) → Result memory → State) (property : State → Prop)
    (localFact : ∀ memory state result, result ∈ support (child memory state) → property state → property (finish memory result))
    (before : Before) (outcome : Before × Option (Sigma Result))
    (supported : outcome ∈ support (program select start child before)) (incoming : property (start before)) :
    property (finalState start finish outcome) := by
  have same := predecessor select start child before outcome supported
  have actual : outcome ∈ support (program select start child outcome.1) := by simpa only [same] using supported
  cases selected : outcome.2 with
  | none => simpa only [finalState,selected,same] using incoming
  | some result =>
    have present : (outcome.1,some result) ∈ support (program select start child outcome.1) := by simpa only [←selected] using actual
    have reached := (reached select start child outcome.1 result present).2
    simpa only [finalState,selected] using localFact result.1 (start outcome.1) result.2 reached (same.symm ▸ incoming)

/-- Appending a reached-or-skipped child cannot increase a predecessor event;
no losslessness assumption or repeated execution is needed. -/
theorem earlier_event_le (prior : ProbComp Before) (event : Before → Prop) :
    Pr{let outcome ← (prior >>= program select start child)}[event outcome.1] ≤ Pr{let before ← prior}[event before] := by
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  apply prEvent_eq_zero_of_forall_mem_support
  intro outcome supported accepted
  exact outside ((predecessor select start child before outcome supported) ▸ accepted)


/-- A final clear state excludes any bad predecessor state when the actual
selected child preserves badness. Concrete callers derive that local fact. -/
theorem earlier_safe_event_le (finish : (memory : Memory) → Result memory → State) (bad : State → Prop)
    (localFact : ∀ memory state result, result ∈ support (child memory state) → bad state → bad (finish memory result))
    (prior : ProbComp Before) (event : Before → Prop) :
    Pr{let outcome ← (prior >>= program select start child)}[event outcome.1 ∧ ¬bad (finalState start finish outcome)] ≤
    Pr{let before ← prior}[event before ∧ ¬bad (start before)] := by
  have included := prEvent_mono_of_support (prior >>= program select start child)
    (fun outcome => event outcome.1 ∧ ¬bad (finalState start finish outcome))
    (fun outcome => event outcome.1 ∧ ¬bad (start outcome.1)) (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro failure
      simp only [support_bind,Set.mem_iUnion] at supported
      obtain ⟨before,_,present⟩ := supported
      have same := predecessor select start child before outcome present
      have earlier : bad (start before) := by simpa only [same] using failure
      exact accepted.2 (preserves select start child finish bad localFact before outcome present earlier))
  exact included.trans (earlier_event_le select start child prior (fun before => event before ∧ ¬bad (start before)))

end
end FormalProof4FHE.HasteBoots.DependentStageContinuation
