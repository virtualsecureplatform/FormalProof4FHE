module
public import FormalProof4FHE.HasteBoots.NativeSliceLLBC
@[expose] public section

/-! Checked cleanup of references created during a source scope. This performs
ledger operations, not Rust value destructors or physical deallocation. Source
lifetime correspondence is a separate obligation. A blocked cleanup retains its
executed prefix and exposes the unprocessed suffix. -/
namespace FormalProof4FHE.HasteBoots.NativeReferenceCleanup
open NativeReferenceMachine (State Reference)
open NativeByteBorrow (Lease)

/-- Stable tag identity is resolved against actual reference registers. -/
def endTag (world : State) (tag : Nat) : Option State :=
  let index := world.references.idxOf ⟨tag⟩
  if world.references[index]? = some ⟨tag⟩ then
    NativeReferenceMachine.execute world (.endBorrow index)
  else none

structure Result where
  world : State
  ended : List Nat
  pending : List Nat
  deriving DecidableEq

/-- The traversal is over an actual finite lease snapshot, with no execution cap. -/
def release (world : State) : List Nat → Result
  | [] => ⟨world, [], []⟩
  | tag :: tail => match endTag world tag with
    | none => ⟨world, [], tag :: tail⟩
    | some next =>
      let result := release next tail
      {result with ended := tag :: result.ended}

/-- The threshold comes from the actual entered state, not a supplied tag list.
Fresh leases are stored in reverse creation order by the reference machine. -/
def scopeTags (entered current : State) : List Nat :=
  (current.leases.filter (fun lease => decide (entered.nextTag ≤ lease.tag))).map Lease.tag

def closeScope (entered current : State) : Result := release current (scopeTags entered current)

inductive Ends : State → List Nat → State → Prop where
  | nil (world : State) : Ends world [] world
  | cons {world next final : State} {tag : Nat} {tail : List Nat}
      (ended : endTag world tag = some next) (later : Ends next tail final) : Ends world (tag :: tail) final

def withoutLeases (world : State) : State := {world with leases := []}

theorem endTag_executes (world next : State) (tag : Nat) (ended : endTag world tag = some next) :
    ∃ index, world.references[index]? = some ⟨tag⟩ ∧
      NativeReferenceMachine.execute world (.endBorrow index) = some next := by
  dsimp only [endTag] at ended
  split at ended
  · exact ⟨_, ‹_›, ended⟩
  · cases ended

theorem endTag_leases (world next : State) (tag : Nat) (ended : endTag world tag = some next) :
    next = {world with leases := world.leases.filter (fun lease => decide (lease.tag ≠ tag))} := by
  obtain ⟨index, selected, actual⟩ := endTag_executes world next tag ended
  simp only [NativeReferenceMachine.execute, selected, Option.bind] at actual
  unfold NativeByteBorrow.endBorrow at actual
  split at actual
  · cases actual
    rfl
  · cases actual

theorem endTag_frame (world next : State) (tag : Nat) (ended : endTag world tag = some next) :
    withoutLeases next = withoutLeases world := by
  rw [endTag_leases world next tag ended]
  rfl

theorem ends_projects (world next : State) (tags : List Nat) (ended : Ends world tags next) :
    NativeReferenceMachine.Runs world next := by
  induction ended with
  | nil world => exact .refl world
  | cons actual later ih =>
    obtain ⟨index, _, executed⟩ := endTag_executes _ _ _ actual
    exact NativeReferenceMachine.runs_trans _ _ _ (.step (.refl _) (.endBorrow index) executed) ih

theorem release_partition (world : State) (tags : List Nat) :
    tags = (release world tags).ended ++ (release world tags).pending := by
  induction tags generalizing world with
  | nil => rfl
  | cons tag tail ih =>
    simp only [release]
    split
    · rfl
    · simpa only [List.cons_append] using congrArg (List.cons tag) (ih _)

theorem release_ends (world : State) (tags : List Nat) :
    Ends world (release world tags).ended (release world tags).world := by
  induction tags generalizing world with
  | nil => exact .nil world
  | cons tag tail ih =>
    simp only [release]
    split
    · exact .nil world
    · exact .cons ‹_› (ih _)

theorem release_blocked (world : State) (tags : List Nat) (tag : Nat) (tail : List Nat)
    (pending : (release world tags).pending = tag :: tail) :
    endTag (release world tags).world tag = none := by
  induction tags generalizing world with
  | nil => cases pending
  | cons head rest ih =>
    cases actual : endTag world head with
    | none =>
      simp only [release, actual] at pending ⊢
      cases pending
      exact actual
    | some next =>
      simpa only [release, actual] using ih next (by simpa only [release, actual] using pending)

theorem ends_frame (world next : State) (tags : List Nat) (ended : Ends world tags next) :
    withoutLeases next = withoutLeases world := by
  induction ended with
  | nil => rfl
  | cons actual later ih => exact ih.trans (endTag_frame _ _ _ actual)

theorem ends_membership (world next : State) (tags : List Nat) (ended : Ends world tags next) (lease : Lease) :
    lease ∈ next.leases ↔ lease ∈ world.leases ∧ lease.tag ∉ tags := by
  induction ended with
  | nil => exact ⟨fun member => ⟨member, List.not_mem_nil⟩, fun member => member.1⟩
  | cons actual later ih =>
    rw [ih, endTag_leases _ _ _ actual]
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons, not_or]
    tauto

theorem release_projects (world : State) (tags : List Nat) :
    NativeReferenceMachine.Runs world (release world tags).world :=
  ends_projects _ _ _ (release_ends world tags)

theorem release_frame (world : State) (tags : List Nat) :
    withoutLeases (release world tags).world = withoutLeases world :=
  ends_frame _ _ _ (release_ends world tags)

theorem release_membership (world : State) (tags : List Nat) (lease : Lease) :
    lease ∈ (release world tags).world.leases ↔ lease ∈ world.leases ∧ lease.tag ∉ (release world tags).ended :=
  ends_membership _ _ _ (release_ends world tags) lease

theorem closeScope_projects (entered current : State) :
    NativeReferenceMachine.Runs current (closeScope entered current).world := release_projects _ _

theorem closeScope_preserves_older (entered current : State) (lease : Lease)
    (member : lease ∈ current.leases) (older : lease.tag < entered.nextTag) :
    lease ∈ (closeScope entered current).world.leases := by
  apply (release_membership current (scopeTags entered current) lease).mpr
  refine ⟨member, ?_⟩
  intro ended
  have inTags : lease.tag ∈ scopeTags entered current := by
    rw [release_partition current (scopeTags entered current)]
    exact List.mem_append_left _ ended
  simp only [scopeTags, List.mem_map, List.mem_filter, decide_eq_true_eq] at inTags
  obtain ⟨other, ⟨_, newer⟩, same⟩ := inTags
  omega

theorem closeScope_complete (entered current : State) (complete : (closeScope entered current).pending = [])
    (lease : Lease) :
    lease ∈ (closeScope entered current).world.leases ↔ lease ∈ current.leases ∧ lease.tag < entered.nextTag := by
  have partition := release_partition current (scopeTags entered current)
  change (release current (scopeTags entered current)).pending = [] at complete
  rw [complete, List.append_nil] at partition
  change lease ∈ (release current (scopeTags entered current)).world.leases ↔ _
  rw [release_membership, ← partition]
  constructor
  · rintro ⟨member, absent⟩
    refine ⟨member, ?_⟩
    by_contra notOlder
    apply absent
    exact List.mem_map.mpr ⟨lease, List.mem_filter.mpr ⟨member, by simpa using (Nat.le_of_not_gt notOlder)⟩, rfl⟩
  · rintro ⟨member, older⟩
    refine ⟨member, ?_⟩
    intro newer
    simp only [scopeTags, List.mem_map, List.mem_filter, decide_eq_true_eq] at newer
    obtain ⟨other, ⟨_, bound⟩, same⟩ := newer
    omega

theorem closeScope_wellFormed (entered current : State) (valid : NativeReferenceMachine.WellFormed current) :
    NativeReferenceMachine.WellFormed (closeScope entered current).world :=
  NativeSliceLLBC.reference_runs_wellFormed _ _ valid (closeScope_projects entered current)

theorem closeScope_reachable (entered current : State) (reachable : NativeReferenceMachine.Reachable current) :
    NativeReferenceMachine.Reachable (closeScope entered current).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (closeScope_projects entered current)

/-- Reachable grants are newest first, and every resident lease has a real
reference register. These facts justify reverse-order cleanup. -/
def Ready (world : State) : Prop :=
  world.leases.Pairwise (fun newer older => older.tag < newer.tag) ∧
    ∀ lease ∈ world.leases, (⟨lease.tag⟩ : Reference) ∈ world.references

theorem execute_ready (world next : State) (ready : Ready world)
    (valid : NativeReferenceMachine.WellFormed world) (op : NativeReferenceMachine.Op)
    (executed : NativeReferenceMachine.execute world op = some next) : Ready next := by
  cases NativeReferenceMachine.execute_authority world next op executed with
  | stable same =>
    rcases same with ⟨_, leases, references, _⟩
    simpa only [Ready, leases, references] using ready
  | granted parent mode pointer layout registered granted =>
    obtain ⟨tag, borrowed, actual, _, _, leases, references, _⟩ :=
      NativeReferenceMachine.grant_success world next parent mode pointer layout granted
    obtain ⟨fresh, _, _, newLeases, _, _⟩ :=
      NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger world) parent mode pointer layout tag borrowed actual
    rw [Ready, leases, newLeases, references]
    constructor
    · apply List.pairwise_cons.mpr
      refine ⟨?_, ready.1⟩
      intro older member
      rw [fresh]
      exact (valid.2.1.1 older member).1
    · intro lease member
      rcases List.mem_cons.mp member with same | old
      · subst lease
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ready.2 lease old)
  | ended tag borrowed actual same =>
    rw [same]
    have filtered := (NativeByteBorrow.endBorrow_success (NativeReferenceMachine.ledger world) tag borrowed actual).2.2.1
    constructor
    · change borrowed.leases.Pairwise _
      rw [filtered]
      exact ready.1.filter _
    · intro lease member
      change lease ∈ borrowed.leases at member
      rw [filtered] at member
      exact ready.2 lease (List.mem_filter.mp member).1

theorem reachable_ready (world : State) (reachable : NativeReferenceMachine.Reachable world) : Ready world := by
  induction reachable with
  | empty => exact ⟨.nil, by intro lease member; cases member⟩
  | @step before after reachable op executed ih =>
    exact execute_ready before after ih (NativeReferenceMachine.reachable_wellFormed before reachable) op executed

theorem end_newest (world : State) (head : Lease) (tail : List Lease)
    (leases : world.leases = head :: tail) (ready : Ready world)
    (valid : NativeReferenceMachine.WellFormed world) :
    ∃ next, endTag world head.tag = some next ∧ next.leases = tail := by
  have headMember : head ∈ world.leases := by rw [leases]; exact List.mem_cons_self
  have registered := ready.2 head headMember
  have selected := List.getElem?_idxOf registered
  have sorted := List.pairwise_cons.mp (leases ▸ ready.1)
  have noChildren : world.leases.all (fun lease => decide (lease.parent ≠ some head.tag)) = true := by
    apply List.all_eq_true.mpr
    intro child member
    apply decide_eq_true
    intro parent
    have edge := (valid.2.1.1 child member).2.2
    rw [parent] at edge
    rw [leases] at member
    rcases List.mem_cons.mp member with same | old
    · subst child
      omega
    · have before := sorted.1 child old
      omega
  have filtered : world.leases.filter (fun lease => decide (lease.tag ≠ head.tag)) = tail := by
    rw [leases]
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply List.filter_eq_self.mpr
    intro lease member
    apply decide_eq_true
    have before := sorted.1 lease member
    omega
  have found : NativeByteBorrow.lookup world.leases head.tag = some head := by
    rw [leases]
    simp only [NativeByteBorrow.lookup, ite_true]
  have ended : NativeByteBorrow.endBorrow (NativeReferenceMachine.ledger world) head.tag =
      some {(NativeReferenceMachine.ledger world) with leases := tail} := by
    simp only [NativeByteBorrow.endBorrow, NativeReferenceMachine.ledger, found, Option.isSome_some,
      noChildren, Bool.and_self, ite_true, filtered]
  refine ⟨{world with leases := tail}, ?_, rfl⟩
  simp only [endTag, selected, ite_true, NativeReferenceMachine.execute, Option.bind, ended, Option.map_some]
  rfl

theorem release_scope_complete (leases : List Lease) (world : State) (bound : Nat)
    (same : world.leases = leases) (ready : Ready world) (valid : NativeReferenceMachine.WellFormed world) :
    (release world ((leases.filter (fun lease => decide (bound ≤ lease.tag))).map Lease.tag)).pending = [] := by
  induction leases generalizing world with
  | nil => rfl
  | cons head tail ih =>
    by_cases newer : bound ≤ head.tag
    · obtain ⟨next, actual, nextLeases⟩ := end_newest world head tail same ready valid
      obtain ⟨index, _, executed⟩ := endTag_executes world next head.tag actual
      have later := ih next nextLeases (execute_ready world next ready valid _ executed)
        (NativeReferenceMachine.execute_wellFormed world next valid _ executed)
      simpa only [List.filter_cons, newer, decide_true, ↓reduceIte, List.map_cons, release, actual] using later
    · have allOlder : tail.filter (fun lease => decide (bound ≤ lease.tag)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro lease member
        have before := (List.pairwise_cons.mp (same ▸ ready.1)).1 lease member
        simpa only [decide_eq_true_eq] using (show ¬ bound ≤ lease.tag by omega)
      simp only [List.filter_cons, newer, decide_false, Bool.false_eq_true, ↓reduceIte, allOlder, List.map_nil, release]

theorem closeScope_reachable_complete (entered current : State) (reachable : NativeReferenceMachine.Reachable current) :
    (closeScope entered current).pending = [] :=
  release_scope_complete current.leases current entered.nextTag rfl (reachable_ready current reachable)
    (NativeReferenceMachine.reachable_wellFormed current reachable)

/-- Only a normally returned unit result is settled by this composed runner.
Other outcomes keep their source execution prefix unchanged. -/
def settleUnit (entered : State) : NativeSliceLLBC.Flow → NativeSliceLLBC.Flow
  | .returned .unit current =>
    let result := closeScope entered current
    if result.pending.isEmpty then .returned .unit result.world else .invalid result.world
  | flow => flow

def invokeUnit (function : NativeSliceLLBC.Function) (world : State) (args : List NativeSliceLLBC.Input) : NativeSliceLLBC.Flow :=
  settleUnit world (NativeSliceLLBC.invoke function world args)

theorem settleUnit_projects (entered : State) (flow : NativeSliceLLBC.Flow) :
    NativeReferenceMachine.Runs flow.world (settleUnit entered flow).world := by
  cases flow with
  | returned value current =>
    cases value with
    | unit =>
      change NativeReferenceMachine.Runs current
        (if (closeScope entered current).pending.isEmpty then
          NativeSliceLLBC.Flow.returned .unit (closeScope entered current).world
        else .invalid (closeScope entered current).world).world
      split <;> exact closeScope_projects entered current
    | usize word => exact .refl _
    | raw pointer => exact .refl _
    | reference mutable reference length => exact .refl _
  | continued frame => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _

theorem invokeUnit_projects (function : NativeSliceLLBC.Function) (world : State) (args : List NativeSliceLLBC.Input) :
    NativeReferenceMachine.Runs world (invokeUnit function world args).world :=
  NativeReferenceMachine.runs_trans _ _ _ (NativeSliceLLBC.invoke_projects function world args) (settleUnit_projects _ _)

theorem invokeUnit_wellFormed (function : NativeSliceLLBC.Function) (world : State)
    (valid : NativeReferenceMachine.WellFormed world) (args : List NativeSliceLLBC.Input) :
    NativeReferenceMachine.WellFormed (invokeUnit function world args).world :=
  NativeSliceLLBC.reference_runs_wellFormed _ _ valid (invokeUnit_projects function world args)

theorem invokeUnit_reachable (function : NativeSliceLLBC.Function) (world : State)
    (reachable : NativeReferenceMachine.Reachable world) (args : List NativeSliceLLBC.Input) :
    NativeReferenceMachine.Reachable (invokeUnit function world args).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (invokeUnit_projects function world args)

theorem invokeUnit_success (function : NativeSliceLLBC.Function) (world current : State)
    (reachable : NativeReferenceMachine.Reachable world) (args : List NativeSliceLLBC.Input)
    (returned : NativeSliceLLBC.invoke function world args = .returned .unit current) :
    ∃ next, invokeUnit function world args = .returned .unit next ∧
      withoutLeases next = withoutLeases current ∧
      (∀ lease, lease ∈ next.leases ↔ lease ∈ current.leases ∧ lease.tag < world.nextTag) := by
  have currentReachable := NativeSliceLLBC.invoke_reachable function world reachable args
  rw [returned] at currentReachable
  have complete := closeScope_reachable_complete world current currentReachable
  refine ⟨(closeScope world current).world, ?_, release_frame _ _, ?_⟩
  · simp only [invokeUnit, returned, settleUnit, complete, List.isEmpty_nil, ite_true]
  · exact fun lease => closeScope_complete world current complete lease

end FormalProof4FHE.HasteBoots.NativeReferenceCleanup
