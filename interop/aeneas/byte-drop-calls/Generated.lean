module
public import FormalProof4FHE.HasteBoots.NativeByteDropCalls
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

namespace HasteBootsByteDropProbe
open FormalProof4FHE.HasteBoots.NativeByteDropCalls

-- Retained original body SHA256 f2086082bf6a12ebc78a91345f38e00d91b0a76f1a6f8e8656d9ebbc2f225577
def f0 : Definition :=
  ⟨"hasteboots_byte_drop_loop::drop_bytes#0", .transparent, [.unit, (.raw false), .usize, (.raw true), (.raw false), .usize], 2,
    (.native (.storageLive 0 (.assign 0 .unit (.storageLive 3 (.storageLive 4 (.assign 4 (.use (.copy 1)) (.storageLive 5 (.assign 5 (.use (.copy 2)) .done))))))) (.call "core::ptr::slice_from_raw_parts_mut#1" .transparent [(.raw true), (.raw false), .usize] 2 3 [(.move 4), (.move 5)] (.native (.storageLive 0 (.parts 0 (.copy 1) (.copy 2) .abort (.storageDead 2 (.storageDead 1 .ret)))) .done) (.native (.storageDead 2 (.storageDead 1 .resume)) .done) (.native (.storageDead 5 (.storageDead 4 .done)) (.call "core::ptr::drop_in_place#2" .transparent [.unit, (.raw true), (.reference true)] 1 0 [(.move 3)] (.native (.storageLive 0 (.assign 0 .unit (.storageLive 2 (.assign 2 (.borrow true 1 .byte) .done)))) (.call "core::ptr::drop_glue#3" .foreignBody [.unit, (.reference true), (.reference true), .unit] 1 0 [(.move 2)] (.native (.storageLive 0 (.assign 0 .unit (.storageLive 2 (.assign 2 (.borrow true 1 .byte) (.storageLive 3 .done))))) (.call "hasteboots_byte_drop_loop::<slice>::drop_glue#4" .transparent [.unit, (.reference true)] 1 3 [(.move 2)] (.loop .transparent HasteBootsByteLoopBody.f4) (.native (.storageDead 1 .resume) .done) (.native (.storageDead 1 (.storageDead 3 (.storageDead 2 .ret))) .done))) (.native (.storageDead 1 .resume) .done) (.native (.storageDead 2 (.storageDead 1 .ret)) .done))) (.native (.storageDead 2 (.storageDead 1 .resume)) .done) (.native (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))) .done)))))⟩

-- Retained original body SHA256 98d104ffd7493b7b030526052af8422ac5b894e01e01d763f91957e0b738c70a
def f1 : Definition :=
  ⟨"core::ptr::slice_from_raw_parts_mut#1", .transparent, [(.raw true), (.raw false), .usize], 2,
    (.native (.storageLive 0 (.parts 0 (.copy 1) (.copy 2) .abort (.storageDead 2 (.storageDead 1 .ret)))) .done)⟩

-- Retained original body SHA256 5440166e6afab50c204b504726b9107923051dcaa18c8dd6a1da394661633341
def f2 : Definition :=
  ⟨"core::ptr::drop_in_place#2", .transparent, [.unit, (.raw true), (.reference true)], 1,
    (.native (.storageLive 0 (.assign 0 .unit (.storageLive 2 (.assign 2 (.borrow true 1 .byte) .done)))) (.call "core::ptr::drop_glue#3" .foreignBody [.unit, (.reference true), (.reference true), .unit] 1 0 [(.move 2)] (.native (.storageLive 0 (.assign 0 .unit (.storageLive 2 (.assign 2 (.borrow true 1 .byte) (.storageLive 3 .done))))) (.call "hasteboots_byte_drop_loop::<slice>::drop_glue#4" .transparent [.unit, (.reference true)] 1 3 [(.move 2)] (.loop .transparent HasteBootsByteLoopBody.f4) (.native (.storageDead 1 .resume) .done) (.native (.storageDead 1 (.storageDead 3 (.storageDead 2 .ret))) .done))) (.native (.storageDead 1 .resume) .done) (.native (.storageDead 2 (.storageDead 1 .ret)) .done)))⟩

-- Retained original body SHA256 7f1771159b3a7cef1a6cdc194a1b2416b4fd88d1138c1237b7aa087d0b0197a4
def f3 : Definition :=
  ⟨"core::ptr::drop_glue#3", .foreignBody, [.unit, (.reference true), (.reference true), .unit], 1,
    (.native (.storageLive 0 (.assign 0 .unit (.storageLive 2 (.assign 2 (.borrow true 1 .byte) (.storageLive 3 .done))))) (.call "hasteboots_byte_drop_loop::<slice>::drop_glue#4" .transparent [.unit, (.reference true)] 1 3 [(.move 2)] (.loop .transparent HasteBootsByteLoopBody.f4) (.native (.storageDead 1 .resume) .done) (.native (.storageDead 1 (.storageDead 3 (.storageDead 2 .ret))) .done)))⟩

end HasteBootsByteDropProbe
