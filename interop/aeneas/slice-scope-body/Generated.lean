module
public import FormalProof4FHE.HasteBoots.NativeReferenceCleanup
@[expose] public section

namespace HasteBootsSliceScopeBody
open FormalProof4FHE.HasteBoots.NativeSliceLLBC

def g0 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g1 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g2 : Fin (2 ^ 64) := ⟨1, by decide⟩

def g3 : Fin (2 ^ 64) := ⟨1, by decide⟩

-- Retained hasteboots_slice_scope_body::shared_scope#0; original body SHA256 1a278ccf27d7769806afce5c38f25acbb491bea1e74ad93dd38c283b73d4cd11
def f0 : Function :=
  ⟨"hasteboots_slice_scope_body::shared_scope#0", [.unit, (.raw false), .usize, (.reference false), (.raw false), .usize], 2,
    (.storageLive 0 (.assign 0 .unit (.storageLive 3 (.storageLive 4 (.assign 4 (.use (.copy 1)) (.storageLive 5 (.assign 5 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts#2" [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 3 [(.move 4), (.move 5)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "9315eb424758242faf6ec9b4c6825271035ab0304501d4c68500468626072dba" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 5 (.storageDead 4 (.assign 0 .unit (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))))))⟩

-- Retained hasteboots_slice_scope_body::mutable_scope#1; original body SHA256 8fb4d4a0a4b2be0a8c5ed2bd8e019b9bf1bd45efa7047e187ec1df9fe7693334
def f1 : Function :=
  ⟨"hasteboots_slice_scope_body::mutable_scope#1", [.unit, (.raw false), .usize, (.reference true), (.reference true), (.raw false), .usize], 2,
    (.storageLive 0 (.assign 0 .unit (.storageLive 3 (.storageLive 4 (.storageLive 5 (.assign 5 (.use (.copy 1)) (.storageLive 6 (.assign 6 (.use (.copy 2)) (.call "core::slice::raw::from_raw_parts_mut#3" [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)] 2 4 [(.move 5), (.move 6)] (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "c9d3f1914f4c00ebde49525ec724c220ef62d7af1ce09cf3b9e8b5d6812a85fd" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 6 (.storageDead 5 (.assign 3 (.borrow true 4 .byte) (.storageDead 4 (.assign 0 .unit (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))))))))⟩

-- Retained core::slice::raw::from_raw_parts#2; original body SHA256 168e93bf1526e323323d9e9b931fd7f902f08371d4ec0dde50f4c32feb54bdfd
def f2 : Function :=
  ⟨"core::slice::raw::from_raw_parts#2", [(.reference false), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "9315eb424758242faf6ec9b4c6825271035ab0304501d4c68500468626072dba" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow false 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

-- Retained core::slice::raw::from_raw_parts_mut#3; original body SHA256 207db0299c35f9e3efe6dfaed056c407d60652c289f832f3ffb2990fd7a43c75
def f3 : Function :=
  ⟨"core::slice::raw::from_raw_parts_mut#3", [(.reference true), (.raw false), .usize, .unit, (.raw false), (.raw true)], 2,
    (.storageLive 0 (.storageLive 3 (.constIf false (.storageLive 4 (.assign 4 (.rawCast (.copy 1)) (.unsupported "c9d3f1914f4c00ebde49525ec724c220ef62d7af1ce09cf3b9e8b5d6812a85fd" (.storageDead 4 .done)))) .done (.storageLive 5 (.parts 5 (.copy 1) (.copy 2) .abort (.assign 0 (.borrow true 5 .byte) (.storageDead 5 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))⟩

end HasteBootsSliceScopeBody
