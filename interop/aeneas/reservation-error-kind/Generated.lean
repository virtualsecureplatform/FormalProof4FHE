module
public import FormalProof4FHE.HasteBoots.NativeAllocatorLLBC
public import FormalProof4FHE.HasteBoots.NativeReservationErrorRead
@[expose] public section
namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)
def tags : NativeReservationErrorLocal.Tags := ⟨0,1,2,3,4⟩
def alignmentDiscriminants : List NativeWord64Memory.Word := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 68719476736, 137438953472, 274877906944, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 70368744177664, 140737488355328, 281474976710656, 562949953421312, 1125899906842624, 2251799813685248, 4503599627370496, 9007199254740992, 18014398509481984, 36028797018963968, 72057594037927936, 144115188075855872, 288230376151711744, 576460752303423488, 1152921504606846976, 2305843009213693952, 4611686018427387904, 9223372036854775808]
def alignmentType : NativeRecordValues.Ty := .record 3 (.pair (.enumeration 4 alignmentDiscriminants) (.scalar .unit))
def layoutType : NativeRecordValues.Ty := .record 2 (.pair (.scalar .usize) (.pair alignmentType (.scalar .unit)))
def kindType : NativeRecordValues.Ty := .record 1 (.choice (.scalar .unit) (.pair layoutType (.pair (.scalar .unit) (.scalar .unit))))
def errorType : NativeRecordValues.Ty := .record 0 (.pair kindType (.scalar .unit))
def allocationBody : Body := .live 2 (.assign 2 (.use (.copy 1 [(.unwrap 0),.left,(.unwrap 1),(.active true),.left]) true .byte)
  (.assign 0 (.aggregate (some 1) (some true) [(.move 2 []),.unit]) (.dead 2 (.dead 1 (.dead 3 .ret)))))
def overflowBody : Body := .live 3 (.assign 3 (.aggregate (some 1) (some false) [])
  (.assign 0 (.use (.move 3 []) true .byte) (.dead 1 (.dead 3 .ret))))
def getterBody : Body := .live 0 (.matchChoice 1 [(.unwrap 0),.left] 1 .done allocationBody overflowBody)
def materializedFrame (world : NativeReferenceMachine.State) (kind : Kind) : Frame :=
  ⟨[kindType,errorType,layoutType,kindType],[.live none,.live (some (NativeReservationErrorLocal.encode tags kind)),.dead,.dead],world⟩
def invoke (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) : Flow :=
  match NativeReservationErrorRead.resolveOperand world value with
  | none => .invalid world
  | some index => match NativeReservationErrorFields.read world index with
    | .invalid next => .invalid next
    | .value kind next => eval getterBody (materializedFrame next kind)
end HasteBootsReservationErrorKind
