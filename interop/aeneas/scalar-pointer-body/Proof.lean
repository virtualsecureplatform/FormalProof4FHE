namespace HasteBootsScalarPointerBody
open FormalProof4FHE.HasteBoots
open NativeScalarLLBC
open NativePointerStorage (Pointer)
open NativePointerByteMemory (State)
open NativeWord64Memory (Word)

theorem word_layout_exact : g0.val = 8 ∧ g1.val = 8 := by decide

theorem pointer_layout_exact : g2.val = 8 ∧ g3.val = 8 := by decide

attribute [local simp] f0 f1 f2 f3 f4 f5 f6 f7 f8
  NativeScalarLLBC.invoke NativeScalarLLBC.initial NativeScalarLLBC.eval
  NativeScalarLLBC.evalArgs NativeScalarLLBC.evalRvalue NativeScalarLLBC.evalOperand
  NativeScalarLLBC.storageLive NativeScalarLLBC.storageDead NativeScalarLLBC.writePlace
  NativeScalarLLBC.writeLocal NativeScalarLLBC.readPlace NativeScalarLLBC.readLocal
  NativeScalarLLBC.pointer NativeScalarLLBC.load NativeScalarLLBC.store NativeScalarLLBC.fits

theorem read_word_body (heap : State) (source : Pointer) :
    invoke f5 heap [.pointer source] = match NativeWord64Memory.load heap.memory source with
      | none => .invalid heap
      | some word => .returned (.word word) heap := by
  cases read : NativeWord64Memory.load heap.memory source <;> simp_all

theorem write_word_body (heap : State) (target : Pointer) (word : Word) :
    invoke f6 heap [.pointer target, .word word] = match NativePointerByteMemory.writeWord heap target word with
      | none => .invalid heap
      | some next => .returned .unit next := by
  cases written : NativePointerByteMemory.writeWord heap target word <;> simp_all

theorem read_pointer_body (heap : State) (source : Pointer) :
    invoke f7 heap [.pointer source] = match NativePointerByteMemory.load heap source with
      | none => .invalid heap
      | some value => .returned (.pointer value) heap := by
  cases read : NativePointerByteMemory.load heap source <;> simp_all

theorem write_pointer_body (heap : State) (target value : Pointer) :
    invoke f8 heap [.pointer target, .pointer value] = match NativePointerByteMemory.store heap target value with
      | none => .invalid heap
      | some next => .returned .unit next := by
  cases written : NativePointerByteMemory.store heap target value <;> simp_all

theorem read_word_wrapper (heap : State) (source : Pointer) : invoke f0 heap [.pointer source] = invoke f5 heap [.pointer source] := by
  cases read : NativeWord64Memory.load heap.memory source <;> simp_all

theorem write_word_wrapper (heap : State) (target : Pointer) (word : Word) :
    invoke f1 heap [.pointer target, .word word] = invoke f6 heap [.pointer target, .word word] := by
  cases written : NativePointerByteMemory.writeWord heap target word <;> simp_all

theorem read_pointer_wrapper (heap : State) (source : Pointer) : invoke f3 heap [.pointer source] = invoke f7 heap [.pointer source] := by
  cases read : NativePointerByteMemory.load heap source <;> simp_all

theorem write_pointer_wrapper (heap : State) (target value : Pointer) :
    invoke f4 heap [.pointer target, .pointer value] = invoke f8 heap [.pointer target, .pointer value] := by
  cases written : NativePointerByteMemory.store heap target value <;> simp_all

theorem replace_word_wrapper (heap : State) (target : Pointer) (word : Word) :
    invoke f2 heap [.pointer target, .word word] = match NativeWord64Memory.load heap.memory target with
      | none => .invalid heap
      | some old => match NativePointerByteMemory.writeWord heap target word with
        | none => .invalid heap
        | some next => .returned (.word old) next := by
  cases read : NativeWord64Memory.load heap.memory target with
  | none => simp_all
  | some old => cases written : NativePointerByteMemory.writeWord heap target word <;> simp_all

end HasteBootsScalarPointerBody
