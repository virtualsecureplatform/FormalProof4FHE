module
public import FormalProof4FHE.HasteBoots.NativeByteLoopLLBC
@[expose] public section

namespace HasteBootsByteLoopBody
open FormalProof4FHE.HasteBoots.NativeByteLoopLLBC

-- Original body SHA256 15080447fe4d6ec2ec15da3c48d8d42342f86739c91ec8716bb98b3d63997d1e
def f4 : Function :=
  ⟨"hasteboots_byte_drop_loop::<slice>::drop_glue#4", [.unit, .sliceRef, .usize, .usize, .rawByte, .boolean, .sliceRef, .byteRef],
    (.storageLive 0 (.storageLive 2 (.storageLive 3 (.storageLive 4 (.storageLive 5 (.assign 0 .unit (.assign 2 (.use (.metadata 1) false) (.assign 3 (.use (.literal ⟨0, by decide⟩) true) .done)))))))),
    (.assign 5 (.eq (.copy 3) (.copy 2)) (.branch (.move 5) .breaking (.storageLive 6 (.assign 6 (.borrowSlice 1) (.storageLive 7 (.index 7 (.move 6) (.copy 3) (.storageDead 7 (.storageDead 6 .abort)) (.assign 4 (.rawByte 7) (.assign 3 (.addWrap (.move 3) (.literal ⟨1, by decide⟩)) .continuing)))))) .done)),
    (.storageDead 5 (.storageDead 4 (.storageDead 3 (.storageDead 2 (.storageDead 1 (.storageDead 7 (.storageDead 6 .ret)))))))⟩

end HasteBootsByteLoopBody
