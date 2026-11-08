namespace HasteBootsByteDeallocationBoundary
open FormalProof4FHE.HasteBoots
open NativeByteDropCalls
open NativeSliceLLBC (Frame Raw Flow)
open NativeReferenceMachine (State)
open NativeWord64Memory (Word)

def entry (world : State) (pointer : Raw) (size alignment : Word) : Frame :=
  ⟨[.unit,.raw false,.usize,.usize],
    [.dead,.live (some (.raw pointer)),.live (some (.usize size)),.live (some (.usize alignment))],world⟩

theorem alignment_values : alignmentValues = (List.range 64).map (fun exponent => 2 ^ exponent) := by decide

theorem external_classification_preserved : boundary.classification = .externalBody := rfl

theorem boundary_code : boundary.code = .deallocate [.move 1,.move 2,.move 3] := rfl

theorem initial_exact (world : State) (pointer : Raw) (size alignment : Word) (thin : pointer.length = none) :
    NativeSliceLLBC.initial boundary.types boundary.argCount [.raw pointer,.usize size,.usize alignment] world =
      some (entry world pointer size alignment) := by
  simp [NativeSliceLLBC.initial, boundary, NativeSliceLLBC.fits, thin, entry]

theorem checked_alignment (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    alignment.val ∈ alignmentValues := by
  rw [alignment_values]
  exact (NativeByteDeallocation.execute_success world next pointer size alignment freed).2.2.1.1

theorem boundary_execution (world next : State) (pointer : Raw) (size alignment : Word)
    (freed : NativeByteDeallocation.execute world pointer size alignment = some next) :
    Runs boundary.code (entry world pointer size alignment) (.returned .unit next) := by
  rw [boundary_code]
  have executed := Runs.deallocate (entry world pointer size alignment) [.move 1,.move 2,.move 3]
  simpa only [NativeByteDeallocation.eval, NativeSliceLLBC.evalArgs, NativeSliceLLBC.evalOperand,
    NativeSliceLLBC.readLocal, entry, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.map_some, Option.bind_some, List.set_cons_zero, List.set_cons_succ, freed] using executed

theorem every_invocation_projects (world : State) (args : List NativeSliceLLBC.Input) (flow : Flow)
    (invoked : Invokes boundary world args flow) : NativeReferenceMachine.Runs world flow.world :=
  invokes_projects boundary world args flow invoked


theorem every_execution_exact (frame : Frame) (flow : Flow) (executed : Runs boundary.code frame flow) :
    flow = NativeByteDeallocation.eval frame [.move 1,.move 2,.move 3] := by
  rw [boundary_code] at executed
  cases executed
  rfl

theorem every_return_frees_one (frame : Frame) (value : NativeSliceLLBC.Value) (world : State)
    (executed : Runs boundary.code frame (.returned value world)) :
    world.pointers.heap.memory.blocks.length + 1 = frame.world.pointers.heap.memory.blocks.length :=
  NativeByteDeallocation.eval_return_frees_one frame _ value world
    (every_execution_exact frame (.returned value world) executed).symm

end HasteBootsByteDeallocationBoundary
