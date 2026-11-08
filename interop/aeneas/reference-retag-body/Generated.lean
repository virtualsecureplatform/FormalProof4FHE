module
public import FormalProof4FHE.HasteBoots.NativeReferenceCleanup
@[expose] public section

namespace HasteBootsReferenceRetagBody
open FormalProof4FHE.HasteBoots.NativeSliceLLBC

def g0 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g1 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g2 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g3 : Fin (2 ^ 64) := ⟨1, by decide⟩

-- Retained hasteboots_reference_retag_body::borrowed#0; original body SHA256 5314cd2f72551680a49b7826c7c0c4bbe0d0723234677dc913a5a2e2d9a98ad6
def f0 : Function :=
  ⟨"hasteboots_reference_retag_body::borrowed#0", [(.reference false), (.reference false)], 1,
    (.storageLive 0 (.assign 0 (.use (.copy 1) true .byte) (.storageDead 1 .ret)))⟩

-- Retained hasteboots_reference_retag_body::shared_scope#1; original body SHA256 674d1217b1f53d0c78ec0377ef4250bd691eca28b6b35c5c44d5b3566c85266b
def f1 : Function :=
  ⟨"hasteboots_reference_retag_body::shared_scope#1", [.unit, (.raw false), .usize, (.reference false), (.raw false), .usize, (.reference false), (.reference false)], 2,
    (.storageLive 0 (.assign 0 .unit (.storageLive 3 (.storageLive 4 (.assign 4 (.use (.copy 1)) (.storageLive 5 (.assign 5 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts#3" [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 3 [(.move 4), (.move 5)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "eb14dba53b94e1a16cbcfbf0e29dbf5f08d1fd4b0809b01d0d02d71c9eb471d3" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 5 (.storageDead 4 (.storageLive 6 (.storageLive 7 (.assign 7 (.borrow false 3 .byte) (.call "hasteboots_reference_retag_body::borrowed#0" [(.reference false), (.reference false)] 1 6 [(.move 7)] (.storageLive 0 (.assign 0 (.use (.copy 1) true .byte) (.storageDead 1 .ret))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 7 (.assign 0 .unit (.storageDead 6 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))))))))))))⟩

-- Retained hasteboots_reference_retag_body::mutable_scope#2; original body SHA256 6b2901d624fcf87f4ae9f0469282ce47f5fa6ab786b136adb829b6bef90cdd63
def f2 : Function :=
  ⟨"hasteboots_reference_retag_body::mutable_scope#2", [.unit, (.raw false), .usize, (.reference true), (.reference true), (.raw false), .usize, (.reference true), (.reference true)], 2,
    (.storageLive 0 (.assign 0 .unit (.storageLive 3 (.storageLive 4 (.storageLive 5 (.assign 5 (.use (.copy 1)) (.storageLive 6 (.assign 6 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts_mut#4" [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 4 [(.move 5), (.move 6)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "b1be6d4cf92b33c256707cb592b1e39708a5d6bfe5f5030000d3cd33d38c6374" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 6 (.storageDead 5 (.assign 3 (.borrow true 4 .byte) (.storageDead 4 (.storageLive 7 (.storageLive 8 (.assign 8 (.use (.move 3) true .byte) (.call "hasteboots_reference_retag_body::identity#5" [(.reference true), (.reference true)] 1 7 [(.move 8)] (.storageLive 0 (.assign 0 (.use (.move 1) true .byte) (.storageDead 1 .ret))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 8 (.assign 0 .unit (.storageDead 7 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))))))))))))))⟩

-- Retained core::slice::raw::from_raw_parts#3; original body SHA256 4376a4e16dbf1ad9f564de18816b33455d8d426e7cdea0a65d9dee9c6e86bf9b
def f3 : Function :=
  ⟨"core::slice::raw::from_raw_parts#3", [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "eb14dba53b94e1a16cbcfbf0e29dbf5f08d1fd4b0809b01d0d02d71c9eb471d3" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

-- Retained core::slice::raw::from_raw_parts_mut#4; original body SHA256 5198757c7779c054a7f1cf4bd0678cfad789e2a9cac4111870a7d40f2f5b6885
def f4 : Function :=
  ⟨"core::slice::raw::from_raw_parts_mut#4", [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "b1be6d4cf92b33c256707cb592b1e39708a5d6bfe5f5030000d3cd33d38c6374" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

-- Retained hasteboots_reference_retag_body::identity#5; original body SHA256 bb149cd52ec2714cf4f8322330535e6e9a04e4ca37150e48224ae0c020fddfdf
def f5 : Function :=
  ⟨"hasteboots_reference_retag_body::identity#5", [(.reference true), (.reference true)], 1,
    (.storageLive 0 (.assign 0 (.use (.move 1) true .byte) (.storageDead 1 .ret)))⟩

end HasteBootsReferenceRetagBody
