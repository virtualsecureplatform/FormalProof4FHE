namespace HasteBootsRawVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem glue_body_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f4.body frame).world := eval_projects f4.body frame

theorem glue_invocation_projects (world : NativeReferenceMachine.State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke f4 world args).world := invoke_projects f4 world args

theorem method_body_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f5.body frame).world := eval_projects f5.body frame

theorem method_invocation_projects (world : NativeReferenceMachine.State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke f5 world args).world := invoke_projects f5 world args

end HasteBootsRawVecDrop
