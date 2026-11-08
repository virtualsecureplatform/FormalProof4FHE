namespace HasteBootsDiscriminantProof
open Aeneas Aeneas.Std Result
open hasteboots_discriminants

theorem process_exact {T : Type} (input : core.result.Result Unit String)
    (bytes : alloc.vec.Vec U8) (other : T) :
    process input bytes other = ok (match input with
      | .Ok _ => .Ok bytes
      | .Err error => .Err error) := by
  cases input <;> rfl

theorem process_success {T : Type} (bytes : alloc.vec.Vec U8) (other : T) :
    process (.Ok ()) bytes other = ok (.Ok bytes) := rfl

theorem process_error {T : Type} (error : String)
    (bytes : alloc.vec.Vec U8) (other : T) :
    process (.Err error) bytes other = ok (.Err error) := rfl

end HasteBootsDiscriminantProof
