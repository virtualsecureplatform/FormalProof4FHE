module
public import FormalProof4FHE.HasteBoots.NativePointerMachine
@[expose] public section

/-! References select minted ledger tags through reference registers. Memory is
shared with the closed pointer machine. This is not a Rust alias refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeReferenceMachine
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Layout)
open NativeByteBorrow (Lease Mode)

structure Reference where
  tag : Nat
  deriving DecidableEq

structure State where
  pointers : NativePointerMachine.State
  nextTag : Nat
  leases : List Lease
  references : List Reference
  births : List Lease
  outputs : List (List Byte)
  deriving DecidableEq

def ledger (state : State) : NativeByteBorrow.State := ⟨state.pointers.heap.memory, state.nextTag, state.leases⟩

def empty : State := ⟨NativePointerMachine.empty, 0, [], [], [], []⟩

inductive Access where
  | read (size alignment : Nat)
  | writeBytes (alignment : Nat) (bytes : List Byte)
  | loadPointer
  | storePointer (value : Nat)
  deriving DecidableEq

def Access.layout : Access → Layout
  | .read size alignment => ⟨size, alignment⟩
  | .writeBytes alignment bytes => ⟨bytes.length, alignment⟩
  | .loadPointer | .storePointer _ => ⟨8, 8⟩

def Access.mode : Access → Mode
  | .read _ _ | .loadPointer => .shared
  | .writeBytes _ _ | .storePointer _ => .exclusive

inductive Op where
  | raw (op : NativePointerMachine.Op)
  | borrow (pointer : Nat) (mode : Mode) (layout : Layout)
  | reborrow (parent pointer : Nat) (mode : Mode) (layout : Layout)
  | endBorrow (reference : Nat)
  | access (reference offset : Nat) (action : Access)
  deriving DecidableEq

def rawPermission (state : State) (register : Nat) (mode : Mode) (layout : Layout) : Bool :=
  state.pointers.registers[register]?.any (fun pointer => NativeByteBorrow.rawAllowed (ledger state) mode pointer layout)

def rawPermissions (state : State) : NativePointerMachine.Op → Bool
  | .allocate _ _ | .fromAddress _ | .withAddress _ _ => true
  | .load slot => rawPermission state slot .shared ⟨8, 8⟩
  | .store slot _ => rawPermission state slot .exclusive ⟨8, 8⟩
  | .writeBytes slot alignment bytes => rawPermission state slot .exclusive ⟨bytes.length, alignment⟩
  | .copy source target size alignment | .copyNonoverlapping source target size alignment =>
    rawPermission state source .shared ⟨size, alignment⟩ && rawPermission state target .exclusive ⟨size, alignment⟩
  | .free register layout => rawPermission state register .exclusive layout

def setPointers (state : State) (pointers : NativePointerMachine.State) : State := {state with pointers}

def grant (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) : Option State :=
  (NativeByteBorrow.borrow (ledger state) parent mode pointer layout).map (fun (tag, next) =>
    ⟨state.pointers, next.nextTag, next.leases, ⟨tag⟩ :: state.references,
      ⟨tag, parent, pointer, layout, mode⟩ :: state.births, state.outputs⟩)

/-- Recovery selects an existing complete pointer value, never an origin from
address bits. The equality check binds the scratch register to the lease base. -/
def prepare (state : State) (base : Pointer) (address : NativePointerStorage.Address) : Option NativePointerMachine.State :=
  let index := state.pointers.registers.idxOf base
  if state.pointers.registers[index]? = some base then
    NativePointerMachine.execute state.pointers (.withAddress index address)
  else none

/-- The scratch register shifts old value indices by one. -/
def perform (state : State) (prepared : NativePointerMachine.State) (pointer : Pointer) : Access → Option State
  | .read size alignment => (NativeByteRange.loadRange prepared.heap.memory pointer ⟨size, alignment⟩).map
    (fun bytes => {state with pointers := prepared, outputs := bytes :: state.outputs})
  | .writeBytes alignment bytes =>
    (NativePointerMachine.execute prepared (.writeBytes 0 alignment bytes)).map (setPointers state)
  | .loadPointer => (NativePointerMachine.execute prepared (.load 0)).map (setPointers state)
  | .storePointer value => (NativePointerMachine.execute prepared (.store 0 (value + 1))).map (setPointers state)

def access (state : State) (reference offset : Nat) (action : Access) : Option State :=
  state.references[reference]?.bind (fun value =>
    (NativeByteBorrow.lookup state.leases value.tag).bind (fun lease =>
      if (action.mode = .shared ∨ lease.mode = .exclusive) ∧ offset + action.layout.size ≤ lease.layout.size then
        (NativeByteRange.pointerAt lease.pointer offset).bind (fun pointer =>
          if NativeByteBorrow.throughAllowed (ledger state) value.tag action.mode pointer action.layout then
            (prepare state lease.pointer pointer.address).bind (fun prepared => perform state prepared pointer action)
          else none)
      else none))

def execute (state : State) : Op → Option State
  | .raw op => if rawPermissions state op then (NativePointerMachine.execute state.pointers op).map (setPointers state) else none
  | .borrow register mode layout => state.pointers.registers[register]?.bind (fun pointer => grant state none mode pointer layout)
  | .reborrow parent register mode layout => state.references[parent]?.bind (fun reference =>
    state.pointers.registers[register]?.bind (fun pointer => grant state (some reference.tag) mode pointer layout))
  | .endBorrow reference => state.references[reference]?.bind (fun value =>
    (NativeByteBorrow.endBorrow (ledger state) value.tag).map (fun next => {state with nextTag := next.nextTag, leases := next.leases}))
  | .access reference offset action => access state reference offset action

def run (state : State) : List Op → Option State
  | [] => some state
  | op :: tail => (execute state op).bind (fun next => run next tail)

inductive Reachable : State → Prop where
  | empty : Reachable empty
  | step {state next : State} (before : Reachable state) (op : Op) (executed : execute state op = some next) : Reachable next

def WellFormed (state : State) : Prop :=
  NativePointerMachine.WellFormed state.pointers ∧ NativeByteBorrow.LedgerValid (ledger state) ∧
    (∀ reference ∈ state.references, ∃ birth ∈ state.births, birth.tag = reference.tag) ∧
    (∀ birth ∈ state.births, birth.tag < state.nextTag)

theorem prepare_success (state : State) (base : Pointer) (address : NativePointerStorage.Address)
    (prepared : NativePointerMachine.State) (executed : prepare state base address = some prepared) :
    NativePointerMachine.execute state.pointers (.withAddress (state.pointers.registers.idxOf base) address) = some prepared ∧
      prepared = NativePointerMachine.push state.pointers ⟨address, base.provenance⟩ := by
  unfold prepare at executed
  dsimp only at executed
  split at executed
  next selected =>
    refine ⟨executed, ?_⟩
    simp only [NativePointerMachine.execute, selected, Option.map_some] at executed
    exact Option.some.inj executed.symm
  next => cases executed

theorem perform_projects (state next : State) (prepared : NativePointerMachine.State) (pointer : Pointer) (action : Access)
    (performed : perform state prepared pointer action = some next) : NativePointerMachine.Runs prepared next.pointers := by
  cases action with
  | read size alignment =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨bytes, _, same⟩ := performed
    subst next
    exact NativePointerMachine.Runs.refl prepared
  | writeBytes alignment bytes =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨pointers, executed, same⟩ := performed
    subst next
    exact NativePointerMachine.Runs.step (.refl prepared) _ executed
  | loadPointer =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨pointers, executed, same⟩ := performed
    subst next
    exact NativePointerMachine.Runs.step (.refl prepared) _ executed
  | storePointer value =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨pointers, executed, same⟩ := performed
    subst next
    exact NativePointerMachine.Runs.step (.refl prepared) _ executed

theorem pointer_runs_trans (start middle finish : NativePointerMachine.State)
    (first : NativePointerMachine.Runs start middle) (second : NativePointerMachine.Runs middle finish) :
    NativePointerMachine.Runs start finish := by
  induction second with
  | refl => exact first
  | step before op executed ih => exact NativePointerMachine.Runs.step ih op executed

theorem grant_success (state next : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (granted : grant state parent mode pointer layout = some next) :
    ∃ tag borrowed, NativeByteBorrow.borrow (ledger state) parent mode pointer layout = some (tag, borrowed) ∧
      next.pointers = state.pointers ∧ next.nextTag = borrowed.nextTag ∧ next.leases = borrowed.leases ∧
      next.references = ⟨tag⟩ :: state.references ∧ next.births = ⟨tag, parent, pointer, layout, mode⟩ :: state.births := by
  simp only [grant, Option.map_eq_some_iff] at granted
  obtain ⟨⟨tag, borrowed⟩, actual, same⟩ := granted
  subst next
  exact ⟨tag, borrowed, actual, rfl, rfl, rfl, rfl, rfl⟩

theorem access_success (state next : State) (reference offset : Nat) (action : Access)
    (executed : access state reference offset action = some next) :
    ∃ value lease pointer prepared, state.references[reference]? = some value ∧
      NativeByteBorrow.lookup state.leases value.tag = some lease ∧
      (action.mode = .shared ∨ lease.mode = .exclusive) ∧ offset + action.layout.size ≤ lease.layout.size ∧
      NativeByteRange.pointerAt lease.pointer offset = some pointer ∧
      NativeByteBorrow.throughAllowed (ledger state) value.tag action.mode pointer action.layout = true ∧
      prepare state lease.pointer pointer.address = some prepared ∧ perform state prepared pointer action = some next := by
  simp only [access, Option.bind_eq_some_iff] at executed
  obtain ⟨value, selected, lease, found, executed⟩ := executed
  split at executed
  next bounded =>
    simp only [Option.bind_eq_some_iff] at executed
    obtain ⟨pointer, shifted, executed⟩ := executed
    split at executed
    next allowed =>
      obtain ⟨prepared, preparedEq, performed⟩ := Option.bind_eq_some_iff.mp executed
      exact ⟨value, lease, pointer, prepared, selected, found, bounded.1, bounded.2, shifted, allowed, preparedEq, performed⟩
    next => cases executed
  next => cases executed

theorem access_projects (state next : State) (reference offset : Nat) (action : Access)
    (executed : access state reference offset action = some next) : NativePointerMachine.Runs state.pointers next.pointers := by
  obtain ⟨_, lease, pointer, prepared, _, _, _, _, _, _, preparedEq, performed⟩ := access_success state next reference offset action executed
  have scratch := (prepare_success state lease.pointer pointer.address prepared preparedEq).1
  exact pointer_runs_trans state.pointers prepared next.pointers
    (NativePointerMachine.Runs.step (.refl state.pointers) _ scratch) (perform_projects state next prepared pointer action performed)

theorem execute_projects (state next : State) (op : Op) (executed : execute state op = some next) :
    NativePointerMachine.Runs state.pointers next.pointers := by
  cases op with
  | raw op =>
    simp only [execute] at executed
    split at executed
    next =>
      obtain ⟨pointers, actual, same⟩ := Option.map_eq_some_iff.mp executed
      subst next
      exact NativePointerMachine.Runs.step (.refl state.pointers) op actual
    next => cases executed
  | borrow register mode layout =>
    obtain ⟨pointer, _, granted⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨_, _, _, same, _⟩ := grant_success state next none mode pointer layout granted
    rw [same]
    exact .refl state.pointers
  | reborrow parent register mode layout =>
    simp only [execute, Option.bind_eq_some_iff] at executed
    obtain ⟨reference, _, pointer, _, granted⟩ := executed
    obtain ⟨_, _, _, same, _⟩ := grant_success state next (some reference.tag) mode pointer layout granted
    rw [same]
    exact .refl state.pointers
  | endBorrow reference =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨value, _, borrowed, _, same⟩ := executed
    subst next
    exact .refl state.pointers
  | access reference offset action => exact access_projects state next reference offset action executed

theorem reachable_pointers (state : State) (reachable : Reachable state) : NativePointerMachine.Reachable state.pointers := by
  induction reachable with
  | empty => exact .empty
  | step before op executed ih => exact NativePointerMachine.runs_reachable _ _ ih (execute_projects _ _ op executed)

def SameAuthority (state next : State) : Prop :=
  next.nextTag = state.nextTag ∧ next.leases = state.leases ∧
    next.references = state.references ∧ next.births = state.births

theorem perform_authority (state next : State) (prepared : NativePointerMachine.State) (pointer : Pointer) (action : Access)
    (performed : perform state prepared pointer action = some next) : SameAuthority state next := by
  cases action with
  | read size alignment =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨_, _, same⟩ := performed
    subst next
    exact ⟨rfl, rfl, rfl, rfl⟩
  | writeBytes alignment bytes =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨_, _, same⟩ := performed
    subst next
    exact ⟨rfl, rfl, rfl, rfl⟩
  | loadPointer =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨_, _, same⟩ := performed
    subst next
    exact ⟨rfl, rfl, rfl, rfl⟩
  | storePointer value =>
    simp only [perform, Option.map_eq_some_iff] at performed
    obtain ⟨_, _, same⟩ := performed
    subst next
    exact ⟨rfl, rfl, rfl, rfl⟩

inductive AuthorityEffect (state next : State) : Prop where
  | stable (same : SameAuthority state next)
  | granted (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
      (registered : pointer ∈ state.pointers.registers)
      (granted : grant state parent mode pointer layout = some next)
  | ended (tag : Nat) (borrowed : NativeByteBorrow.State)
      (ended : NativeByteBorrow.endBorrow (ledger state) tag = some borrowed)
      (same : next = {state with nextTag := borrowed.nextTag, leases := borrowed.leases})

theorem execute_authority (state next : State) (op : Op) (executed : execute state op = some next) : AuthorityEffect state next := by
  cases op with
  | raw op =>
    simp only [execute] at executed
    split at executed
    next =>
      obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp executed
      subst next
      exact .stable ⟨rfl, rfl, rfl, rfl⟩
    next => cases executed
  | borrow register mode layout =>
    obtain ⟨pointer, selected, granted⟩ := Option.bind_eq_some_iff.mp executed
    exact .granted none mode pointer layout (List.mem_of_getElem? selected) granted
  | reborrow parent register mode layout =>
    simp only [execute, Option.bind_eq_some_iff] at executed
    obtain ⟨reference, _, pointer, selected, granted⟩ := executed
    exact .granted (some reference.tag) mode pointer layout (List.mem_of_getElem? selected) granted
  | endBorrow reference =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨value, _, borrowed, ended, same⟩ := executed
    exact .ended value.tag borrowed ended same.symm
  | access reference offset action =>
    obtain ⟨_, _, pointer, prepared, _, _, _, _, _, _, _, performed⟩ := access_success state next reference offset action executed
    exact .stable (perform_authority state next prepared pointer action performed)

theorem empty_wellFormed : WellFormed empty := by
  refine ⟨NativePointerMachine.empty_wellFormed, NativeByteBorrow.empty_wellFormed.2, ?_, ?_⟩
  · intro reference member; cases member
  · intro birth member; cases member

theorem stable_wellFormed (state next : State) (valid : WellFormed state)
    (pointersValid : NativePointerMachine.WellFormed next.pointers) (same : SameAuthority state next) : WellFormed next := by
  obtain ⟨counter, leases, references, births⟩ := same
  refine ⟨pointersValid, NativeByteBorrow.ledger_transport (ledger state) (ledger next) valid.2.1 counter leases, ?_, ?_⟩
  · intro reference member
    rw [references] at member
    obtain ⟨birth, present, sameTag⟩ := valid.2.2.1 reference member
    exact ⟨birth, by rw [births]; exact present, sameTag⟩
  · intro birth member
    rw [births] at member
    rw [counter]
    exact valid.2.2.2 birth member

theorem grant_wellFormed (state next : State) (valid : WellFormed state) (parent : Option Nat) (mode : Mode)
    (pointer : Pointer) (layout : Layout) (granted : grant state parent mode pointer layout = some next) : WellFormed next := by
  obtain ⟨tag, borrowed, actual, samePointers, counter, leases, references, births⟩ := grant_success state next parent mode pointer layout granted
  obtain ⟨fresh, _, raised, _, _, _⟩ := NativeByteBorrow.borrow_success (ledger state) parent mode pointer layout tag borrowed actual
  have borrowedValid := NativeByteBorrow.borrow_wellFormed (ledger state) ⟨valid.1.1, valid.2.1⟩ parent mode pointer layout tag borrowed actual
  have raisedCounter : next.nextTag = state.nextTag + 1 := counter.trans raised
  refine ⟨by rw [samePointers]; exact valid.1,
    NativeByteBorrow.ledger_transport borrowed (ledger next) borrowedValid.2 counter leases, ?_, ?_⟩
  · intro reference member
    rw [references] at member
    rcases List.mem_cons.mp member with same | old
    · subst reference
      exact ⟨⟨tag, parent, pointer, layout, mode⟩, by rw [births]; exact List.mem_cons_self, rfl⟩
    · obtain ⟨birth, present, sameTag⟩ := valid.2.2.1 reference old
      exact ⟨birth, by rw [births]; exact List.mem_cons_of_mem _ present, sameTag⟩
  · intro birth member
    rw [births] at member
    rcases List.mem_cons.mp member with same | old
    · subst birth; dsimp only; rw [raisedCounter, fresh]; exact Nat.lt_succ_self _
    · have before := valid.2.2.2 birth old
      rw [raisedCounter]
      omega

theorem end_wellFormed (state : State) (valid : WellFormed state) (tag : Nat) (borrowed : NativeByteBorrow.State)
    (ended : NativeByteBorrow.endBorrow (ledger state) tag = some borrowed) :
    WellFormed {state with nextTag := borrowed.nextTag, leases := borrowed.leases} := by
  have borrowedValid := NativeByteBorrow.endBorrow_wellFormed (ledger state) ⟨valid.1.1, valid.2.1⟩ tag borrowed ended
  have counter := (NativeByteBorrow.endBorrow_success (ledger state) tag borrowed ended).2.1
  refine ⟨valid.1, NativeByteBorrow.ledger_transport borrowed _ borrowedValid.2 rfl rfl, valid.2.2.1, ?_⟩
  intro birth member
  dsimp only
  rw [counter]
  exact valid.2.2.2 birth member

theorem execute_wellFormed (state next : State) (valid : WellFormed state) (op : Op)
    (executed : execute state op = some next) : WellFormed next := by
  cases execute_authority state next op executed with
  | stable same =>
    exact stable_wellFormed state next valid
      (NativePointerMachine.runs_wellFormed state.pointers next.pointers valid.1 (execute_projects state next op executed)) same
  | granted parent mode pointer layout _registered granted => exact grant_wellFormed state next valid parent mode pointer layout granted
  | ended tag borrowed ended same => subst next; exact end_wellFormed state valid tag borrowed ended

theorem reachable_wellFormed (state : State) (reachable : Reachable state) : WellFormed state := by
  induction reachable with
  | empty => exact empty_wellFormed
  | step before op executed ih => exact execute_wellFormed _ _ ih op executed

theorem execute_counter (state next : State) (op : Op) (executed : execute state op = some next) : state.nextTag ≤ next.nextTag := by
  cases execute_authority state next op executed with
  | stable same => rw [same.1]
  | granted parent mode pointer layout _registered granted =>
    obtain ⟨tag, borrowed, actual, _, counter, _⟩ := grant_success state next parent mode pointer layout granted
    have raised := (NativeByteBorrow.borrow_success (ledger state) parent mode pointer layout tag borrowed actual).2.2.1
    rw [counter, raised]
    exact Nat.le_succ _
  | ended tag borrowed ended same =>
    subst next
    exact Nat.le_of_eq (NativeByteBorrow.endBorrow_success (ledger state) tag borrowed ended).2.1.symm

theorem execute_keeps_revoked (state next : State) (op : Op) (executed : execute state op = some next)
    (tag : Nat) (before : tag < state.nextTag) (absent : NativeByteBorrow.lookup state.leases tag = none) :
    NativeByteBorrow.lookup next.leases tag = none := by
  cases execute_authority state next op executed with
  | stable same => rw [same.2.1]; exact absent
  | granted parent mode pointer layout _registered granted =>
    obtain ⟨fresh, borrowed, actual, _, _, leases, _⟩ := grant_success state next parent mode pointer layout granted
    rw [leases]
    exact NativeByteBorrow.step_keeps_revoked (.borrow (ledger state) parent mode pointer layout fresh borrowed actual) tag before absent
  | ended ending borrowed ended same =>
    subst next
    exact NativeByteBorrow.step_keeps_revoked (.endBorrow (ledger state) ending borrowed ended) tag before absent

inductive Runs : State → State → Prop where
  | refl (state : State) : Runs state state
  | step {start state next : State} (before : Runs start state) (op : Op) (executed : execute state op = some next) : Runs start next

theorem runs_counter (state next : State) (runs : Runs state next) : state.nextTag ≤ next.nextTag := by
  induction runs with
  | refl => exact Nat.le_refl _
  | step before op executed ih => exact Nat.le_trans ih (execute_counter _ _ op executed)

theorem runs_keep_revoked (state next : State) (runs : Runs state next) (tag : Nat)
    (before : tag < state.nextTag) (absent : NativeByteBorrow.lookup state.leases tag = none) :
    NativeByteBorrow.lookup next.leases tag = none := by
  induction runs with
  | refl => exact absent
  | step priorRun op executed ih =>
    have counter := runs_counter _ _ priorRun
    exact execute_keeps_revoked _ _ op executed tag (by omega) ih

theorem missing_access (state : State) (reference offset : Nat) (action : Access) (value : Reference)
    (selected : state.references[reference]? = some value) (absent : NativeByteBorrow.lookup state.leases value.tag = none) :
    access state reference offset action = none := by
  simp only [access, selected, Option.bind, absent]

theorem reference_born_before_counter (state : State) (reachable : Reachable state) (reference : Reference)
    (member : reference ∈ state.references) : reference.tag < state.nextTag := by
  have valid := reachable_wellFormed state reachable
  obtain ⟨birth, present, same⟩ := valid.2.2.1 reference member
  rw [← same]
  exact valid.2.2.2 birth present

theorem access_binding (state next : State) (reference offset : Nat) (action : Access)
    (executed : access state reference offset action = some next) :
    ∃ value lease pointer prepared, state.references[reference]? = some value ∧
      NativeByteBorrow.lookup state.leases value.tag = some lease ∧ lease.tag = value.tag ∧
      pointer.address.val = lease.pointer.address.val + offset ∧ pointer.provenance = lease.pointer.provenance ∧
      prepared.registers[0]? = some pointer ∧
      NativeByteBorrow.throughAllowed (ledger state) value.tag action.mode pointer action.layout = true ∧
      perform state prepared pointer action = some next := by
  obtain ⟨value, lease, pointer, prepared, selected, found, _, _, shifted, allowed, preparedEq, performed⟩ :=
    access_success state next reference offset action executed
  obtain ⟨addressEq, originEq⟩ := NativeByteRange.pointerAt_fields lease.pointer offset pointer shifted
  have same := (prepare_success state lease.pointer pointer.address prepared preparedEq).2
  have pointerEq : (⟨pointer.address, lease.pointer.provenance⟩ : Pointer) = pointer := by
    rw [← originEq]
  refine ⟨value, lease, pointer, prepared, selected, found, (NativeByteBorrow.lookup_selected state.leases value.tag lease found).2,
    addressEq, originEq, ?_, allowed, performed⟩
  rw [same, pointerEq]
  rfl

theorem end_reference_success (state next : State) (reference : Nat) (value : Reference)
    (selected : state.references[reference]? = some value) (ended : execute state (.endBorrow reference) = some next) :
    next.nextTag = state.nextTag ∧ NativeByteBorrow.lookup next.leases value.tag = none := by
  simp only [execute, selected, Option.bind, Option.map_eq_some_iff] at ended
  obtain ⟨borrowed, actual, same⟩ := ended
  subst next
  have outcome := NativeByteBorrow.endBorrow_success (ledger state) value.tag borrowed actual
  exact ⟨outcome.2.1, outcome.2.2.2.1⟩

theorem ended_reference_never_access (state ended future : State) (reachable : Reachable state) (reference : Nat) (value : Reference)
    (selected : state.references[reference]? = some value) (endedEq : execute state (.endBorrow reference) = some ended)
    (later : Runs ended future) (futureIndex offset : Nat) (futureValue : Reference)
    (futureSelected : future.references[futureIndex]? = some futureValue) (sameTag : futureValue.tag = value.tag) (action : Access) :
    access future futureIndex offset action = none := by
  have bound := reference_born_before_counter state reachable value (List.mem_of_getElem? selected)
  obtain ⟨counter, absent⟩ := end_reference_success state ended reference value selected endedEq
  have remains := runs_keep_revoked ended future later value.tag (by omega) absent
  apply missing_access future futureIndex offset action futureValue futureSelected
  rw [sameTag]
  exact remains

theorem runs_trans (start middle finish : State) (first : Runs start middle) (second : Runs middle finish) : Runs start finish := by
  induction second with
  | refl => exact first
  | step before op executed ih => exact Runs.step ih op executed

theorem reachable_birth_borrow (state : State) (reachable : Reachable state) (birth : Lease) (member : birth ∈ state.births) :
    ∃ before after borrowed, Reachable before ∧
      NativeByteBorrow.borrow (ledger before) birth.parent birth.mode birth.pointer birth.layout = some (birth.tag, borrowed) ∧
      (∃ op, execute before op = some after) ∧ Runs after state := by
  induction reachable with
  | empty => cases member
  | @step before after beforeReach op executed ih =>
    have oldBirth : birth ∈ before.births → ∃ earlier later borrowed, Reachable earlier ∧
        NativeByteBorrow.borrow (ledger earlier) birth.parent birth.mode birth.pointer birth.layout = some (birth.tag, borrowed) ∧
        (∃ op, execute earlier op = some later) ∧ Runs later after := by
      intro old
      obtain ⟨earlier, later, borrowed, earlierReach, actual, operation, suffix⟩ := ih old
      exact ⟨earlier, later, borrowed, earlierReach, actual, operation, Runs.step suffix op executed⟩
    cases execute_authority before after op executed with
    | stable same =>
      rw [same.2.2.2] at member
      exact oldBirth member
    | granted parent mode pointer layout _registered granted =>
      obtain ⟨tag, borrowed, actual, _, _, _, _, births⟩ := grant_success before after parent mode pointer layout granted
      rw [births] at member
      rcases List.mem_cons.mp member with same | old
      · subst birth
        exact ⟨before, after, borrowed, beforeReach, actual, ⟨op, executed⟩, Runs.refl after⟩
      · exact oldBirth old
    | ended tag borrowed actual same =>
      rw [same] at member
      exact oldBirth member

theorem reachable_reference_borrow (state : State) (reachable : Reachable state) (reference : Reference)
    (member : reference ∈ state.references) : ∃ birth ∈ state.births, birth.tag = reference.tag ∧
      ∃ before after borrowed, Reachable before ∧
        NativeByteBorrow.borrow (ledger before) birth.parent birth.mode birth.pointer birth.layout = some (birth.tag, borrowed) ∧
        (∃ op, execute before op = some after) ∧ Runs after state := by
  obtain ⟨birth, present, same⟩ := (reachable_wellFormed state reachable).2.2.1 reference member
  exact ⟨birth, present, same, reachable_birth_borrow state reachable birth present⟩

theorem run_reachable (state next : State) (reachable : Reachable state) (ops : List Op) (ran : run state ops = some next) : Reachable next := by
  induction ops generalizing state with
  | nil => cases ran; exact reachable
  | cons op tail ih =>
    obtain ⟨middle, actual, later⟩ := Option.bind_eq_some_iff.mp ran
    exact ih middle (Reachable.step reachable op actual) later

theorem run_wellFormed (ops : List Op) (state : State) (ran : run empty ops = some state) : WellFormed state := by
  exact reachable_wellFormed state (run_reachable empty state Reachable.empty ops ran)

theorem raw_success (state next : State) (op : NativePointerMachine.Op) (executed : execute state (.raw op) = some next) :
    rawPermissions state op = true ∧ NativePointerMachine.execute state.pointers op = some next.pointers := by
  simp only [execute] at executed
  split at executed
  next allowed =>
    obtain ⟨pointers, actual, same⟩ := Option.map_eq_some_iff.mp executed
    subst next
    exact ⟨allowed, actual⟩
  next => cases executed

theorem raw_permission_selected (state : State) (register : Nat) (pointer : Pointer) (mode : Mode) (layout : Layout)
    (selected : state.pointers.registers[register]? = some pointer) (allowed : rawPermission state register mode layout = true) :
    NativeByteBorrow.rawAllowed (ledger state) mode pointer layout = true := by
  simpa only [rawPermission, selected, Option.any] using allowed

theorem raw_free_no_overlap (state next : State) (register : Nat) (pointer : Pointer) (layout : Layout)
    (selected : state.pointers.registers[register]? = some pointer) (freed : execute state (.raw (.free register layout)) = some next)
    (lease : Lease) (member : lease ∈ state.leases) : ¬ NativeByteBorrow.Overlap pointer layout lease.pointer lease.layout := by
  have allowed := (raw_success state next (.free register layout) freed).1
  exact NativeByteBorrow.raw_exclusive_no_overlap (ledger state) pointer layout
    (raw_permission_selected state register pointer .exclusive layout selected allowed) lease member

theorem reachable_unique_birth_tags (state : State) (reachable : Reachable state) :
    state.births.Pairwise (fun left right => left.tag ≠ right.tag) := by
  induction reachable with
  | empty => exact List.Pairwise.nil
  | @step before after beforeReach op executed ih =>
    cases execute_authority before after op executed with
    | stable same => rw [same.2.2.2]; exact ih
    | granted parent mode pointer layout _registered granted =>
      obtain ⟨tag, borrowed, actual, _, _, _, _, births⟩ := grant_success before after parent mode pointer layout granted
      have fresh := (NativeByteBorrow.borrow_success (ledger before) parent mode pointer layout tag borrowed actual).1
      rw [births]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro birth member
      have older := (reachable_wellFormed before beforeReach).2.2.2 birth member
      dsimp only
      rw [fresh]
      exact Nat.ne_of_gt older
    | ended tag borrowed actual same => rw [same]; exact ih

theorem run_reference_borrow (ops : List Op) (state : State) (ran : run empty ops = some state)
    (index : Nat) (reference : Reference) (selected : state.references[index]? = some reference) :
    ∃ birth ∈ state.births, birth.tag = reference.tag ∧ ∃ before after borrowed, Reachable before ∧
      NativeByteBorrow.borrow (ledger before) birth.parent birth.mode birth.pointer birth.layout = some (birth.tag, borrowed) ∧
      (∃ op, execute before op = some after) ∧ Runs after state := by
  exact reachable_reference_borrow state (run_reachable empty state Reachable.empty ops ran) reference (List.mem_of_getElem? selected)

theorem reachable_pointer_origin (state : State) (reachable : Reachable state) (index : Nat) (pointer : Pointer)
    (selected : state.pointers.registers[index]? = some pointer) (origin : NativePointerStorage.Origin)
    (hasOrigin : pointer.provenance = some origin) : NativePointerMachine.Issued state.pointers origin ∧
      origin.generation < state.pointers.heap.memory.nextGeneration := by
  exact NativePointerMachine.reachable_register_origin state.pointers (reachable_pointers state reachable) index pointer selected origin hasOrigin

theorem pointer_execute_keeps_register (state next : NativePointerMachine.State) (op : NativePointerMachine.Op)
    (executed : NativePointerMachine.execute state op = some next) (value : Pointer) (member : value ∈ state.registers) :
    value ∈ next.registers := by
  cases op with
  | allocate base layout =>
    simp only [NativePointerMachine.execute, Option.map_eq_some_iff] at executed
    obtain ⟨⟨pointer, heap⟩, _, same⟩ := executed
    subst next
    exact List.mem_cons_of_mem _ member
  | fromAddress address => cases executed; exact List.mem_cons_of_mem _ member
  | withAddress register address =>
    simp only [NativePointerMachine.execute, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, same⟩ := executed
    subst next
    exact List.mem_cons_of_mem _ member
  | load slot =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, loaded, _, same⟩ := executed
    subst next
    exact List.mem_cons_of_mem _ member
  | store slot data =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, data, _, heap, _, same⟩ := executed
    subst next
    exact member
  | writeBytes slot alignment bytes =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, heap, _, same⟩ := executed
    subst next
    exact member
  | copy source target size alignment =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨sourcePointer, _, targetPointer, _, heap, _, same⟩ := executed
    subst next
    exact member
  | copyNonoverlapping source target size alignment =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨sourcePointer, _, targetPointer, _, heap, _, same⟩ := executed
    subst next
    exact member
  | free register layout =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
    obtain ⟨pointer, _, heap, _, same⟩ := executed
    subst next
    exact member

theorem pointer_runs_keep_register (state next : NativePointerMachine.State) (runs : NativePointerMachine.Runs state next)
    (value : Pointer) (member : value ∈ state.registers) : value ∈ next.registers := by
  induction runs with
  | refl => exact member
  | step before op executed ih => exact pointer_execute_keeps_register _ _ op executed value ih

theorem reachable_lease_registered (state : State) (reachable : Reachable state) (lease : Lease) (member : lease ∈ state.leases) :
    lease.pointer ∈ state.pointers.registers := by
  induction reachable with
  | empty => cases member
  | @step before after beforeReach op executed ih =>
    have inherited : ∀ pointer ∈ before.pointers.registers, pointer ∈ after.pointers.registers :=
      pointer_runs_keep_register before.pointers after.pointers (execute_projects before after op executed)
    cases execute_authority before after op executed with
    | stable same =>
      rw [same.2.1] at member
      exact inherited lease.pointer (ih member)
    | granted parent mode pointer layout registered granted =>
      obtain ⟨tag, borrowed, actual, _, _, leases, _⟩ := grant_success before after parent mode pointer layout granted
      have newLeases := (NativeByteBorrow.borrow_success (ledger before) parent mode pointer layout tag borrowed actual).2.2.2.1
      rw [leases, newLeases] at member
      rcases List.mem_cons.mp member with same | old
      · subst lease; exact inherited pointer registered
      · exact inherited lease.pointer (ih old)
    | ended tag borrowed actual same =>
      have filtered := (NativeByteBorrow.endBorrow_success (ledger before) tag borrowed actual).2.2.1
      rw [same] at member
      change lease ∈ borrowed.leases at member
      rw [filtered] at member
      exact inherited lease.pointer (ih (List.mem_filter.mp member).1)

theorem prepare_of_registered (state : State) (base : Pointer) (address : NativePointerStorage.Address)
    (registered : base ∈ state.pointers.registers) :
    prepare state base address = some (NativePointerMachine.push state.pointers ⟨address, base.provenance⟩) := by
  have selected := List.getElem?_idxOf registered
  simp only [prepare, selected, ite_true, NativePointerMachine.execute, Option.map_some]

theorem prepare_resident_lease (state : State) (reachable : Reachable state) (tag : Nat) (lease : Lease)
    (found : NativeByteBorrow.lookup state.leases tag = some lease) (address : NativePointerStorage.Address) :
    prepare state lease.pointer address = some (NativePointerMachine.push state.pointers ⟨address, lease.pointer.provenance⟩) := by
  exact prepare_of_registered state lease.pointer address
    (reachable_lease_registered state reachable lease (NativeByteBorrow.lookup_selected state.leases tag lease found).1)

end FormalProof4FHE.HasteBoots.NativeReferenceMachine
