module
public import FormalProof4FHE.HasteBoots.NativePointerByteMemory
@[expose] public section

/-! Finite LLBC body semantics for Copy scalars and thin raw pointers. Calls
contain their retained bodies; recursion and other source forms are outside
this profile. This supplies no compiler, Rust alias or work refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeScalarLLBC
open NativePointerStorage (Pointer)
open NativePointerByteMemory (State)
open NativeWord64Memory (Word)

inductive Ty where
  | unit
  | word
  | ptr (mutable : Bool) (pointee : Ty)
  deriving DecidableEq

inductive Value where
  | unit
  | word (value : Word)
  | pointer (value : Pointer)
  deriving DecidableEq

def fits : Ty → Value → Bool
  | .unit, .unit | .word, .word _ | .ptr _ _, .pointer _ => true
  | _, _ => false

inductive Slot where
  | dead
  | live (value : Option Value)
  deriving DecidableEq

structure Frame where
  types : List Ty
  slots : List Slot
  heap : State
  deriving DecidableEq

inductive Place where
  | var (index : Nat)
  | deref (base : Nat) (pointee : Ty)
  deriving DecidableEq

inductive Operand where
  | copy (place : Place)
  | move (index : Nat)
  deriving DecidableEq

inductive Rvalue where
  | use (operand : Operand)
  | castMutToConst (operand : Operand)
  | unit
  deriving DecidableEq

inductive Body where
  | ret
  | resume
  | storageLive (index : Nat) (next : Body)
  | storageDead (index : Nat) (next : Body)
  | assign (target : Place) (value : Rvalue) (next : Body)
  | call (name : String) (types : List Ty) (argCount : Nat) (target : Place)
      (args : List Operand) (callee unwind next : Body)
  deriving DecidableEq

structure Function where
  name : String
  types : List Ty
  argCount : Nat
  body : Body
  deriving DecidableEq

inductive Outcome where
  | returned (value : Value) (heap : State)
  | unwind (heap : State)
  | invalid (heap : State)
  deriving DecidableEq

def Outcome.heap : Outcome → State
  | .returned _ heap | .unwind heap | .invalid heap => heap

def readLocal (frame : Frame) (index : Nat) : Option Value :=
  match frame.slots[index]? with
  | some (.live (some value)) => some value
  | _ => none

def pointer (frame : Frame) (index : Nat) : Option Pointer :=
  (readLocal frame index).bind (fun value => match value with | .pointer pointer => some pointer | _ => none)

def load (heap : State) (pointer : Pointer) : Ty → Option Value
  | .word => (NativeWord64Memory.load heap.memory pointer).map Value.word
  | .ptr _ _ => (NativePointerByteMemory.load heap pointer).map Value.pointer
  | .unit => none

def store (heap : State) (pointer : Pointer) : Ty → Value → Option State
  | .word, .word value => NativePointerByteMemory.writeWord heap pointer value
  | .ptr _ _, .pointer value => NativePointerByteMemory.store heap pointer value
  | _, _ => none

def readPlace (frame : Frame) : Place → Option Value
  | .var index => readLocal frame index
  | .deref base ty => (pointer frame base).bind (fun p => load frame.heap p ty)

def writeLocal (frame : Frame) (index : Nat) (value : Value) : Option Frame :=
  frame.types[index]?.bind (fun ty =>
    if fits ty value then
      match frame.slots[index]? with
      | some (.live _) => some {frame with slots := frame.slots.set index (.live (some value))}
      | _ => none
    else none)

def writePlace (frame : Frame) : Place → Value → Option Frame
  | .var index, value => writeLocal frame index value
  | .deref base ty, value => (pointer frame base).bind (fun p =>
    (store frame.heap p ty value).map (fun heap => {frame with heap}))

def storageLive (frame : Frame) (index : Nat) : Option Frame :=
  match frame.slots[index]? with
  | some .dead => some {frame with slots := frame.slots.set index (.live none)}
  | _ => none

def storageDead (frame : Frame) (index : Nat) : Option Frame :=
  match frame.slots[index]? with
  | some (.live _) => some {frame with slots := frame.slots.set index .dead}
  | _ => none

def evalOperand (frame : Frame) : Operand → Option (Value × Frame)
  | .copy place => (readPlace frame place).map (fun value => (value, frame))
  | .move index => (readLocal frame index).map (fun value =>
    (value, {frame with slots := frame.slots.set index (.live none)}))

def evalRvalue (frame : Frame) : Rvalue → Option (Value × Frame)
  | .unit => some (.unit, frame)
  | .use operand => evalOperand frame operand
  | .castMutToConst operand => (evalOperand frame operand).bind (fun (value, next) =>
    match value with | .pointer _ => some (value, next) | _ => none)

def evalArgs (frame : Frame) : List Operand → Option (List Value × Frame)
  | [] => some ([], frame)
  | operand :: tail => (evalOperand frame operand).bind (fun (value, next) =>
    (evalArgs next tail).map (fun (values, final) => (value :: values, final)))

def initial (types : List Ty) (argCount : Nat) (args : List Value) (heap : State) : Option Frame :=
  if args.length = argCount ∧ argCount + 1 ≤ types.length ∧
      (((types.drop 1).take argCount).zip args).all (fun (ty, value) => fits ty value) = true then
    some ⟨types, .dead :: (args.map (fun value => Slot.live (some value)) ++ List.replicate (types.length - argCount - 1) Slot.dead), heap⟩
  else none

def eval : Body → Frame → Outcome
  | .ret, frame => match readLocal frame 0 with
    | some value => .returned value frame.heap
    | none => .invalid frame.heap
  | .resume, frame => .unwind frame.heap
  | .storageLive index next, frame => match storageLive frame index with
    | some nextFrame => eval next nextFrame
    | none => .invalid frame.heap
  | .storageDead index next, frame => match storageDead frame index with
    | some nextFrame => eval next nextFrame
    | none => .invalid frame.heap
  | .assign target value next, frame => match evalRvalue frame value with
    | none => .invalid frame.heap
    | some (value, evaluated) => match writePlace evaluated target value with
      | none => .invalid evaluated.heap
      | some updated => eval next updated
  | .call _ types argCount target args callee unwind next, frame => match evalArgs frame args with
    | none => .invalid frame.heap
    | some (values, evaluated) => match initial types argCount values evaluated.heap with
      | none => .invalid evaluated.heap
      | some called => match eval callee called with
        | .invalid heap => .invalid heap
        | .unwind heap => eval unwind {evaluated with heap}
        | .returned value heap => match writePlace {evaluated with heap} target value with
          | none => .invalid heap
          | some updated => eval next updated

def invoke (function : Function) (heap : State) (args : List Value) : Outcome :=
  match initial function.types function.argCount args heap with
  | some frame => eval function.body frame
  | none => .invalid heap

theorem store_wellFormed (heap next : State) (valid : NativeByteMemory.WellFormed heap.memory)
    (pointer : Pointer) (ty : Ty) (value : Value) (stored : store heap pointer ty value = some next) :
    NativeByteMemory.WellFormed next.memory := by
  cases ty with
  | unit => cases value <;> cases stored
  | word =>
    cases value with
    | unit => cases stored
    | word value => exact NativePointerByteMemory.writeBytes_wellFormed heap next valid pointer 8 _ stored
    | pointer value => cases stored
  | ptr mutable pointee =>
    cases value with
    | unit => cases stored
    | word value => cases stored
    | pointer value => exact NativePointerByteMemory.store_wellFormed heap next valid pointer value stored

theorem writeLocal_heap (frame next : Frame) (index : Nat) (value : Value) (written : writeLocal frame index value = some next) :
    next.heap = frame.heap := by
  unfold writeLocal at written
  cases found : frame.types[index]? with
  | none => simp only [found, Option.bind_none] at written; cases written
  | some ty =>
    simp only [found, Option.bind_some] at written
    split at written
    next =>
      cases slot : frame.slots[index]? with
      | none => simp only [slot] at written; cases written
      | some old =>
        cases old with
        | dead => simp only [slot] at written; cases written
        | live previous => simp only [slot] at written; cases written; rfl
    next => cases written

theorem writePlace_wellFormed (frame next : Frame) (valid : NativeByteMemory.WellFormed frame.heap.memory)
    (place : Place) (value : Value) (written : writePlace frame place value = some next) :
    NativeByteMemory.WellFormed next.heap.memory := by
  cases place with
  | var index => rw [writeLocal_heap frame next index value written]; exact valid
  | deref base ty =>
    simp only [writePlace, Option.bind_eq_some_iff, Option.map_eq_some_iff] at written
    obtain ⟨pointer, _, heap, stored, same⟩ := written
    subst next
    exact store_wellFormed frame.heap heap valid pointer ty value stored

theorem storageLive_heap (frame next : Frame) (index : Nat) (changed : storageLive frame index = some next) : next.heap = frame.heap := by
  unfold storageLive at changed
  cases slot : frame.slots[index]? with
  | none => simp only [slot] at changed; cases changed
  | some value =>
    cases value with
    | dead => simp only [slot] at changed; cases changed; rfl
    | live previous => simp only [slot] at changed; cases changed

theorem storageDead_heap (frame next : Frame) (index : Nat) (changed : storageDead frame index = some next) : next.heap = frame.heap := by
  unfold storageDead at changed
  cases slot : frame.slots[index]? with
  | none => simp only [slot] at changed; cases changed
  | some value =>
    cases value with
    | dead => simp only [slot] at changed; cases changed
    | live previous => simp only [slot] at changed; cases changed; rfl

theorem evalOperand_heap (frame next : Frame) (operand : Operand) (value : Value)
    (evaluated : evalOperand frame operand = some (value, next)) : next.heap = frame.heap := by
  cases operand with
  | copy place =>
    simp only [evalOperand, Option.map_eq_some_iff] at evaluated
    obtain ⟨_, _, same⟩ := evaluated
    cases same
    rfl
  | move index =>
    simp only [evalOperand, Option.map_eq_some_iff] at evaluated
    obtain ⟨_, _, same⟩ := evaluated
    cases same
    rfl

theorem evalRvalue_heap (frame next : Frame) (rvalue : Rvalue) (value : Value)
    (evaluated : evalRvalue frame rvalue = some (value, next)) : next.heap = frame.heap := by
  cases rvalue with
  | unit => cases evaluated; rfl
  | use operand => exact evalOperand_heap frame next operand value evaluated
  | castMutToConst operand =>
    simp only [evalRvalue, Option.bind_eq_some_iff] at evaluated
    obtain ⟨⟨input, changed⟩, first, evaluated⟩ := evaluated
    cases input with
    | unit => cases evaluated
    | word word => cases evaluated
    | pointer pointer => cases evaluated; exact evalOperand_heap frame _ operand (.pointer pointer) first

theorem evalArgs_heap (frame next : Frame) (args : List Operand) (values : List Value)
    (evaluated : evalArgs frame args = some (values, next)) : next.heap = frame.heap := by
  induction args generalizing frame values with
  | nil => cases evaluated; rfl
  | cons operand tail ih =>
    simp only [evalArgs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at evaluated
    obtain ⟨⟨value, middle⟩, first, ⟨later, final⟩, rest, same⟩ := evaluated
    cases same
    exact (ih middle later rest).trans (evalOperand_heap frame middle operand value first)

theorem initial_heap (types : List Ty) (argCount : Nat) (args : List Value) (heap : State) (frame : Frame)
    (initialized : initial types argCount args heap = some frame) : frame.heap = heap := by
  unfold initial at initialized
  split at initialized
  · cases initialized; rfl
  · cases initialized

theorem eval_wellFormed (body : Body) (frame : Frame) (valid : NativeByteMemory.WellFormed frame.heap.memory) :
    NativeByteMemory.WellFormed (eval body frame).heap.memory := by
  induction body generalizing frame with
  | ret => simp only [eval]; split <;> exact valid
  | resume => exact valid
  | storageLive index next ih =>
    simp only [eval]
    split
    next changed =>
      have same := storageLive_heap frame _ index changed
      apply ih
      rw [same]
      exact valid
    next => exact valid
  | storageDead index next ih =>
    simp only [eval]
    split
    next changed =>
      have same := storageDead_heap frame _ index changed
      apply ih
      rw [same]
      exact valid
    next => exact valid
  | assign target value next ih =>
    simp only [eval]
    split
    next => exact valid
    next evaluated =>
      have same := evalRvalue_heap frame _ value _ evaluated
      have evaluatedValid : NativeByteMemory.WellFormed ‹Frame›.heap.memory := by rw [same]; exact valid
      split
      next => exact evaluatedValid
      next written => exact ih _ (writePlace_wellFormed _ _ evaluatedValid target _ written)
  | call name types argCount target args callee unwind next calleeIH unwindIH nextIH =>
    simp only [eval]
    split
    next => exact valid
    next evaluated =>
      have same := evalArgs_heap frame _ args _ evaluated
      have evaluatedValid : NativeByteMemory.WellFormed ‹Frame›.heap.memory := by rw [same]; exact valid
      split
      next => exact evaluatedValid
      next initialized =>
        have same := initial_heap types argCount _ _ _ initialized
        have calledValid : NativeByteMemory.WellFormed ‹Frame›.heap.memory := by rw [same]; exact evaluatedValid
        have resultValid := calleeIH _ calledValid
        split
        next result => rw [result] at resultValid; exact resultValid
        next result =>
          rw [result] at resultValid
          exact unwindIH _ resultValid
        next result =>
          rw [result] at resultValid
          split
          next => exact resultValid
          next written => exact nextIH _ (writePlace_wellFormed _ _ resultValid target _ written)

theorem invoke_wellFormed (function : Function) (heap : State) (valid : NativeByteMemory.WellFormed heap.memory) (args : List Value) :
    NativeByteMemory.WellFormed (invoke function heap args).heap.memory := by
  unfold invoke
  split
  next initialized =>
    apply eval_wellFormed
    rw [initial_heap function.types function.argCount args heap _ initialized]
    exact valid
  next => exact valid

end FormalProof4FHE.HasteBoots.NativeScalarLLBC
