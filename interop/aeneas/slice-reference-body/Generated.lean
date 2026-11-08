module
public import FormalProof4FHE.HasteBoots.NativeSliceLLBC
@[expose] public section

namespace HasteBootsSliceReferenceBody
open FormalProof4FHE.HasteBoots.NativeSliceLLBC

def g0 : Fin (2 ^ 64) := ⟨8, by decide⟩

def g1 : Fin (2 ^ 64) := ⟨8, by decide⟩

def g2 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g3 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g4 : Fin (2 ^ 64) := ⟨8, by decide⟩

def g5 : Fin (2 ^ 64) := ⟨8, by decide⟩

def g6 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g7 : Fin (2 ^ 64) := ⟨1, by decide⟩

-- Retained hasteboots_slice_reference_body::shared_words#0; original body SHA256 259442ee9a650af2fcdb5892caca751ee8676d823d11547bf0696d9769d872cb
def f0 : Function :=
  ⟨"hasteboots_slice_reference_body::shared_words#0", [(.reference false), (.raw false), .usize, (.reference false), (.raw false), .usize], 2,
    (.storageLive 0 (.storageLive 3 (.storageLive 4 (.assign 4 (.use (.copy 1)) (.storageLive 5 (.assign 5 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts#4" [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 3 [(.move 4), (.move 5)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "430af7d71213471034388e0eef70f50c5402b72c01e531bb335beabca31f02f8" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .word) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.assign 0 (.borrow false 3 .word) (.storageDead 5 (.storageDead 4 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))))⟩

-- Retained hasteboots_slice_reference_body::mutable_words#1; original body SHA256 7113eeee21f8ec70610ccf02ba9949dd579db2a73d8a0d00a696a16163638187
def f1 : Function :=
  ⟨"hasteboots_slice_reference_body::mutable_words#1", [(.reference true), (.raw false), .usize, (.reference true), (.reference true), (.reference true), (.raw false), .usize], 2,
    (.storageLive 0 (.storageLive 3 (.storageLive 4 (.storageLive 5 (.storageLive 6 (.assign 6 (.use (.copy 1)) (.storageLive 7 (.assign 7 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts_mut#5" [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 5 [(.move 6), (.move 7)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "293edef4c800c683b3c96e09ff113515c6b78dda3e29ca30aacb86fd546d6796" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .word) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.assign 4 (.borrow true 5 .word) (.storageDead 7 (.storageDead 6 (.storageDead 5 (.assign 3 (.borrow true 4 .word) (.storageDead 4 (.assign 0 (.borrow true 3 .word) (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))))))))))⟩

-- Retained hasteboots_slice_reference_body::shared_bytes#2; original body SHA256 6e1e2674df920e57084d375ea23961aa0112badd2640c546d96abaaddca97399
def f2 : Function :=
  ⟨"hasteboots_slice_reference_body::shared_bytes#2", [(.reference false), (.raw false), .usize, (.reference false), (.raw false), .usize], 2,
    (.storageLive 0 (.storageLive 3 (.storageLive 4 (.assign 4 (.use (.copy 1)) (.storageLive 5 (.assign 5 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts#6" [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 3 [(.move 4), (.move 5)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "0d2c71ae0a64659f8d8edc1a1ad68d2e7a98a40ea5b08db3df105d9c0c9cad12" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.assign 0 (.borrow false 3 .byte) (.storageDead 5 (.storageDead 4 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))))⟩

-- Retained hasteboots_slice_reference_body::mutable_bytes#3; original body SHA256 fc0d50e4f2ba8367325851ac0aab80e81920c426b08b4204abc7519426282ecf
def f3 : Function :=
  ⟨"hasteboots_slice_reference_body::mutable_bytes#3", [(.reference true), (.raw false), .usize, (.reference true), (.reference true), (.reference true), (.raw false), .usize], 2,
    (.storageLive 0 (.storageLive 3 (.storageLive 4 (.storageLive 5 (.storageLive 6 (.assign 6 (.use (.copy 1)) (.storageLive 7 (.assign 7 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts_mut#7" [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 5 [(.move 6), (.move 7)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "6ed931a3b5516a360ee5af3ba9d6fe71749989aa94650959a2cf2071b1305be6" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.assign 4 (.borrow true 5 .byte) (.storageDead 7 (.storageDead 6 (.storageDead 5 (.assign 3 (.borrow true 4 .byte) (.storageDead 4 (.assign 0 (.borrow true 3 .byte) (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))))))))))⟩

-- Retained core::slice::raw::from_raw_parts#4; original body SHA256 e07a78e05f9749c8418b678005242b2c3bca1e3fb3119a9d217534a61f7f99c8
def f4 : Function :=
  ⟨"core::slice::raw::from_raw_parts#4", [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "430af7d71213471034388e0eef70f50c5402b72c01e531bb335beabca31f02f8" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .word) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

-- Retained core::slice::raw::from_raw_parts_mut#5; original body SHA256 543071a74701c957feaddcd5589d435fb5d751c1dcf981c013b8dac37abce407
def f5 : Function :=
  ⟨"core::slice::raw::from_raw_parts_mut#5", [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "293edef4c800c683b3c96e09ff113515c6b78dda3e29ca30aacb86fd546d6796" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .word) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

-- Retained core::slice::raw::from_raw_parts#6; original body SHA256 7999649bdf50210de1f13c7559cc1597e56abced4da9723792a71c6645dc3c91
def f6 : Function :=
  ⟨"core::slice::raw::from_raw_parts#6", [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "0d2c71ae0a64659f8d8edc1a1ad68d2e7a98a40ea5b08db3df105d9c0c9cad12" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

-- Retained core::slice::raw::from_raw_parts_mut#7; original body SHA256 72c59acdbf066f62c8c5d09b2c6116abc994195baa7826bf2f7e81cd376ec085
def f7 : Function :=
  ⟨"core::slice::raw::from_raw_parts_mut#7", [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "6ed931a3b5516a360ee5af3ba9d6fe71749989aa94650959a2cf2071b1305be6" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

end HasteBootsSliceReferenceBody
