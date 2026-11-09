module
public import FormalProof4FHE.HasteBoots.NativeByteBorrowStorage
public import FormalProof4FHE.HasteBoots.NativeReservationErrorFields
@[expose] public section

/-! Storage-loan operations extend the initialized-byte reference machine while
embedding every existing step exactly. Reachability in this extension is stated
separately; storage permission alone is not a Rust typed-reference theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeStorageBorrowMachine
open NativeReferenceMachine (State Reference ledger WellFormed)
open NativePointerStorage (Pointer)
open NativeByteMemory (Layout)
open NativeByteBorrow (Mode)

inductive Op where
  | legacy (op : NativeReferenceMachine.Op)
  | storageBorrow (parent : Option Nat) (register : Nat) (mode : Mode) (layout : Layout)
  deriving DecidableEq

def grant (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) : Option State :=
  (NativeByteBorrowStorage.borrow (ledger state) parent mode pointer layout).map (fun (tag,next) =>
    ⟨state.pointers,next.nextTag,next.leases,⟨tag⟩ :: state.references,
      ⟨tag,parent,pointer,layout,mode⟩ :: state.births,state.outputs⟩)

def parentTag (state : State) : Option Nat → Option (Option Nat)
  | none => some none
  | some index => state.references[index]?.map (fun reference => some reference.tag)

def execute (state : State) : Op → Option State
  | .legacy op => NativeReferenceMachine.execute state op
  | .storageBorrow parent register mode layout => (parentTag state parent).bind (fun tag =>
      state.pointers.registers[register]?.bind (fun pointer => grant state tag mode pointer layout))

def run (state : State) : List Op → Option State
  | [] => some state
  | op :: tail => (execute state op).bind (fun next => run next tail)

inductive Runs : State → State → Prop where
  | refl (state : State) : Runs state state
  | step {start state next : State} (before : Runs start state) (op : Op) (executed : execute state op = some next) : Runs start next

def Reachable (state : State) : Prop := Runs NativeReferenceMachine.empty state

theorem grant_success (state next : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (granted : grant state parent mode pointer layout = some next) :
    ∃ tag borrowed, NativeByteBorrowStorage.borrow (ledger state) parent mode pointer layout = some (tag, borrowed) ∧
      next.pointers = state.pointers ∧ next.nextTag = borrowed.nextTag ∧ next.leases = borrowed.leases ∧
      next.references = ⟨tag⟩ :: state.references ∧ next.births = ⟨tag, parent, pointer, layout, mode⟩ :: state.births := by
  simp only [grant, Option.map_eq_some_iff] at granted
  obtain ⟨⟨tag, borrowed⟩, actual, same⟩ := granted
  subst next
  exact ⟨tag, borrowed, actual, rfl, rfl, rfl, rfl, rfl⟩

theorem grant_wellFormed (state next : State) (valid : WellFormed state) (parent : Option Nat) (mode : Mode)
    (pointer : Pointer) (layout : Layout) (granted : grant state parent mode pointer layout = some next) : WellFormed next := by
  obtain ⟨tag, borrowed, actual, samePointers, counter, leases, references, births⟩ := grant_success state next parent mode pointer layout granted
  obtain ⟨fresh, _, raised, _, _, _⟩ := NativeByteBorrowStorage.borrow_success (ledger state) parent mode pointer layout tag borrowed actual
  have borrowedValid := NativeByteBorrowStorage.borrow_wellFormed (ledger state) ⟨valid.1.1, valid.2.1⟩ parent mode pointer layout tag borrowed actual
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

theorem grant_incoming (before after : State) (parent : Option Nat) (mode : NativeByteBorrow.Mode)
    (pointer : Pointer) (layout : NativeByteMemory.Layout)
    (granted : grant before parent mode pointer layout = some after) : NativeIncomingReference.Preserves before after := by
  obtain ⟨tag,ledger,borrowed,pointers,counter,leases,references,births⟩ :=
    grant_success before after parent mode pointer layout granted
  obtain ⟨fresh,_,raised,leaseEq,_⟩ := NativeByteBorrowStorage.borrow_success (NativeReferenceMachine.ledger before)
    parent mode pointer layout tag ledger borrowed
  change tag = before.nextTag at fresh
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [counter,raised]; exact Nat.le_succ _
  · intro reference member; rw [references]; exact List.mem_cons_of_mem _ member
  · intro value member; rw [pointers]; exact member
  · intro birth member; rw [births]; exact List.mem_cons_of_mem _ member
  · intro query older
    rw [leases,leaseEq,fresh]
    simp only [NativeByteBorrow.lookup,show before.nextTag ≠ query by omega,ite_false]
    rfl

theorem legacy_exact (state : State) (op : NativeReferenceMachine.Op) :
    execute state (.legacy op) = NativeReferenceMachine.execute state op := rfl

theorem legacy_grant_refines (state next : State) (parent : Option Nat) (mode : Mode)
    (pointer : Pointer) (layout : Layout) (executed : NativeReferenceMachine.grant state parent mode pointer layout = some next) :
    grant state parent mode pointer layout = some next := by
  obtain ⟨⟨tag,borrowed⟩,actual,same⟩ := Option.map_eq_some_iff.mp executed
  unfold grant
  rw [NativeByteBorrowStorage.initialized_refines _ _ _ _ _ _ _ actual]
  exact congrArg some same

theorem execute_wellFormed (state next : State) (valid : WellFormed state) (op : Op)
    (executed : execute state op = some next) : WellFormed next := by
  cases op with
  | legacy op => exact NativeReferenceMachine.execute_wellFormed state next valid op executed
  | storageBorrow parent register mode layout =>
    simp only [execute,Option.bind_eq_some_iff] at executed
    obtain ⟨tag,_,pointer,_,granted⟩ := executed
    exact grant_wellFormed state next valid tag mode pointer layout granted

theorem execute_projects (state next : State) (op : Op) (executed : execute state op = some next) :
    NativePointerMachine.Runs state.pointers next.pointers := by
  cases op with
  | legacy op => exact NativeReferenceMachine.execute_projects state next op executed
  | storageBorrow parent register mode layout =>
    simp only [execute,Option.bind_eq_some_iff] at executed
    obtain ⟨tag,_,pointer,_,granted⟩ := executed
    have same := (grant_success state next tag mode pointer layout granted).choose_spec.choose_spec.2.1
    rw [same]
    exact .refl _

theorem storage_incoming (state next : State) (parent : Option Nat) (register : Nat) (mode : Mode) (layout : Layout)
    (executed : execute state (.storageBorrow parent register mode layout) = some next) :
    NativeIncomingReference.Preserves state next := by
  simp only [execute,Option.bind_eq_some_iff] at executed
  obtain ⟨tag,_,pointer,_,granted⟩ := executed
  exact grant_incoming state next tag mode pointer layout granted

theorem storage_heap (state next : State) (parent : Option Nat) (register : Nat) (mode : Mode) (layout : Layout)
    (executed : execute state (.storageBorrow parent register mode layout) = some next) :
    next.pointers.heap = state.pointers.heap := by
  simp only [execute,Option.bind_eq_some_iff] at executed
  obtain ⟨tag,_,pointer,_,granted⟩ := executed
  obtain ⟨_,_,_,pointers,_⟩ := grant_success state next tag mode pointer layout granted
  rw [pointers]

theorem runs_trans (start middle finish : State) (first : Runs start middle) (second : Runs middle finish) : Runs start finish := by
  induction second with
  | refl => exact first
  | step before op executed ih => exact .step ih op executed

theorem legacy_runs (state next : State) (runs : NativeReferenceMachine.Runs state next) : Runs state next := by
  induction runs with
  | refl => exact .refl _
  | step before op executed ih => exact .step ih (.legacy op) executed

theorem legacy_reachable (state : State) (reachable : NativeReferenceMachine.Reachable state) : Reachable state := by
  induction reachable with
  | empty => exact .refl _
  | step before op executed ih => exact .step ih (.legacy op) executed

theorem runs_wellFormed (state next : State) (valid : WellFormed state) (runs : Runs state next) : WellFormed next := by
  induction runs with
  | refl => exact valid
  | step before op executed ih => exact execute_wellFormed _ _ ih op executed

theorem reachable_wellFormed (state : State) (reachable : Reachable state) : WellFormed state :=
  runs_wellFormed _ _ NativeReferenceMachine.empty_wellFormed reachable

theorem runs_projects (state next : State) (runs : Runs state next) : NativePointerMachine.Runs state.pointers next.pointers := by
  induction runs with
  | refl => exact .refl _
  | step before op executed ih =>
    exact NativeReferenceMachine.pointer_runs_trans _ _ _ ih (execute_projects _ _ op executed)

theorem run_projects (state next : State) (ops : List Op) (executed : run state ops = some next) : Runs state next := by
  induction ops generalizing state with
  | nil => cases executed; exact .refl _
  | cons op tail ih =>
    obtain ⟨middle,step,rest⟩ := Option.bind_eq_some_iff.mp executed
    exact runs_trans state middle next (.step (.refl state) op step) (ih middle rest)

theorem read_projects (state : State) (index : Nat) : Runs state (NativeReservationErrorFields.read state index).world :=
  legacy_runs _ _ (NativeReservationErrorFields.read_projects state index)

theorem read_reachable (state : State) (index : Nat) (reachable : Reachable state) :
    Reachable (NativeReservationErrorFields.read state index).world := runs_trans _ _ _ reachable (read_projects state index)

theorem borrow_read_reachable (state next : State) (parent : Option Nat) (register index : Nat)
    (mode : Mode) (layout : Layout) (reachable : Reachable state)
    (borrowed : execute state (.storageBorrow parent register mode layout) = some next) :
    Reachable (NativeReservationErrorFields.read next index).world :=
  read_reachable next index (.step reachable (.storageBorrow parent register mode layout) borrowed)

theorem borrow_read_wellFormed (state next : State) (parent : Option Nat) (register index : Nat)
    (mode : Mode) (layout : Layout) (valid : WellFormed state)
    (borrowed : execute state (.storageBorrow parent register mode layout) = some next) :
    WellFormed (NativeReservationErrorFields.read next index).world :=
  NativeReservationErrorFields.read_wellFormed next index
    (execute_wellFormed state next valid (.storageBorrow parent register mode layout) borrowed)

theorem borrow_read_heap (state next : State) (parent : Option Nat) (register index : Nat)
    (mode : Mode) (layout : Layout)
    (borrowed : execute state (.storageBorrow parent register mode layout) = some next) :
    (NativeReservationErrorFields.read next index).world.pointers.heap = state.pointers.heap :=
  (NativeReservationErrorFields.read_heap next index).trans (storage_heap state next parent register mode layout borrowed)

end FormalProof4FHE.HasteBoots.NativeStorageBorrowMachine
