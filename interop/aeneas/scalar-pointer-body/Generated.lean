module
public import FormalProof4FHE.HasteBoots.NativeScalarLLBC
public import FormalProof4FHE.HasteBoots.NativeReferenceMachine
@[expose] public section

-- Generated from retained original LLBC bodies; no function-name semantic overrides.
namespace HasteBootsScalarPointerBody
open FormalProof4FHE.HasteBoots.NativeScalarLLBC

-- Original evaluated usize global 0
def g0 : Fin (2 ^ 64) := ⟨8, by decide⟩

-- Original evaluated usize global 1
def g1 : Fin (2 ^ 64) := ⟨8, by decide⟩

-- Original evaluated usize global 2
def g2 : Fin (2 ^ 64) := ⟨8, by decide⟩

-- Original evaluated usize global 3
def g3 : Fin (2 ^ 64) := ⟨8, by decide⟩

-- Original function hasteboots_scalar_pointer_body::read_word#0; body SHA256 a9116fb2f60628db52ec65b9db5feb9875d280b7f5a5761c6033d3b4b79ef393
def f0 : Function :=
  ⟨"hasteboots_scalar_pointer_body::read_word#0", [.word, (.ptr false .word), (.ptr false .word)], 1,
    (.storageLive 0 (.storageLive 2 (.assign (.var 2) (.use (.copy (.var 1))) (.call "core::ptr::read#5" [.word, (.ptr false .word)] 1 (.var 0) [(.move 2)] (.storageLive 0 (.assign (.var 0) (.use (.copy (.deref 1 .word))) (.storageDead 1 .ret))) (.storageDead 1 .resume) (.storageDead 2 (.storageDead 1 .ret))))))⟩

-- Original function hasteboots_scalar_pointer_body::write_word#1; body SHA256 f78ec15c3178787db71e45b1bb4144a49dc48cfc074d579a4da9baa290cab08e
def f1 : Function :=
  ⟨"hasteboots_scalar_pointer_body::write_word#1", [.unit, (.ptr true .word), .word, (.ptr true .word), .word], 2,
    (.storageLive 0 (.assign (.var 0) .unit (.storageLive 3 (.assign (.var 3) (.use (.copy (.var 1))) (.storageLive 4 (.assign (.var 4) (.use (.copy (.var 2))) (.call "core::ptr::write#6" [.unit, (.ptr true .word), .word] 2 (.var 0) [(.move 3), (.move 4)] (.storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 .word) (.use (.move 2)) (.storageDead 2 (.storageDead 1 .ret))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 4 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))⟩

-- Original function hasteboots_scalar_pointer_body::replace_word#2; body SHA256 097bf4e44ce8972aa91610ede766e3051ccd8c21fd466b4ef78760b3a3a75f55
def f2 : Function :=
  ⟨"hasteboots_scalar_pointer_body::replace_word#2", [.word, (.ptr true .word), .word, .word, (.ptr false .word), (.ptr true .word), .unit, (.ptr true .word), .word], 2,
    (.storageLive 0 (.storageLive 3 (.storageLive 4 (.storageLive 5 (.assign (.var 5) (.use (.copy (.var 1))) (.assign (.var 4) (.castMutToConst (.move 5)) (.storageDead 5 (.call "core::ptr::read#5" [.word, (.ptr false .word)] 1 (.var 3) [(.move 4)] (.storageLive 0 (.assign (.var 0) (.use (.copy (.deref 1 .word))) (.storageDead 1 .ret))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 4 (.storageLive 6 (.storageLive 7 (.assign (.var 7) (.use (.copy (.var 1))) (.storageLive 8 (.assign (.var 8) (.use (.copy (.var 2))) (.call "core::ptr::write#6" [.unit, (.ptr true .word), .word] 2 (.var 6) [(.move 7), (.move 8)] (.storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 .word) (.use (.move 2)) (.storageDead 2 (.storageDead 1 .ret))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 8 (.storageDead 7 (.storageDead 6 (.assign (.var 0) (.use (.copy (.var 3))) (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret))))))))))))))))))))))⟩

-- Original function hasteboots_scalar_pointer_body::read_pointer#3; body SHA256 3dbf3b23aba5488929cfb67df1aa4642f492fb74d67540607ae33dd372db5bfc
def f3 : Function :=
  ⟨"hasteboots_scalar_pointer_body::read_pointer#3", [(.ptr true .word), (.ptr false (.ptr true .word)), (.ptr false (.ptr true .word))], 1,
    (.storageLive 0 (.storageLive 2 (.assign (.var 2) (.use (.copy (.var 1))) (.call "core::ptr::read#7" [(.ptr true .word), (.ptr false (.ptr true .word))] 1 (.var 0) [(.move 2)] (.storageLive 0 (.assign (.var 0) (.use (.copy (.deref 1 (.ptr true .word)))) (.storageDead 1 .ret))) (.storageDead 1 .resume) (.storageDead 2 (.storageDead 1 .ret))))))⟩

-- Original function hasteboots_scalar_pointer_body::write_pointer#4; body SHA256 6de7b242ce904fe955f41ab2f96c70ee0a3ea32a801b4375a39da0f525ba641c
def f4 : Function :=
  ⟨"hasteboots_scalar_pointer_body::write_pointer#4", [.unit, (.ptr true (.ptr true .word)), (.ptr true .word), (.ptr true (.ptr true .word)), (.ptr true .word)], 2,
    (.storageLive 0 (.assign (.var 0) .unit (.storageLive 3 (.assign (.var 3) (.use (.copy (.var 1))) (.storageLive 4 (.assign (.var 4) (.use (.copy (.var 2))) (.call "core::ptr::write#8" [.unit, (.ptr true (.ptr true .word)), (.ptr true .word)] 2 (.var 0) [(.move 3), (.move 4)] (.storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 (.ptr true .word)) (.use (.move 2)) (.storageDead 2 (.storageDead 1 .ret))))) (.storageDead 2 (.storageDead 1 .resume)) (.storageDead 4 (.storageDead 3 (.storageDead 2 (.storageDead 1 .ret)))))))))))⟩

-- Original function core::ptr::read#5; body SHA256 131fce339788a5fdb63f3aa39251769292d358cddbb14a8e7b73fc833f4235d1
def f5 : Function :=
  ⟨"core::ptr::read#5", [.word, (.ptr false .word)], 1,
    (.storageLive 0 (.assign (.var 0) (.use (.copy (.deref 1 .word))) (.storageDead 1 .ret)))⟩

-- Original function core::ptr::write#6; body SHA256 1adad30d1758a9f0984a245e9348b2b1b41c0cfdda92625156fb5241cb851c5b
def f6 : Function :=
  ⟨"core::ptr::write#6", [.unit, (.ptr true .word), .word], 2,
    (.storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 .word) (.use (.move 2)) (.storageDead 2 (.storageDead 1 .ret)))))⟩

-- Original function core::ptr::read#7; body SHA256 3b85a2b7adb424cdbb1957955482cffcd38ecaa7b3bb3b0f90e74e4919e0fff3
def f7 : Function :=
  ⟨"core::ptr::read#7", [(.ptr true .word), (.ptr false (.ptr true .word))], 1,
    (.storageLive 0 (.assign (.var 0) (.use (.copy (.deref 1 (.ptr true .word)))) (.storageDead 1 .ret)))⟩

-- Original function core::ptr::write#8; body SHA256 74c80afa44019ef28378f4ccca36db0925812136aa6471b73571463fc5da54ef
def f8 : Function :=
  ⟨"core::ptr::write#8", [.unit, (.ptr true (.ptr true .word)), (.ptr true .word)], 2,
    (.storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 (.ptr true .word)) (.use (.move 2)) (.storageDead 2 (.storageDead 1 .ret)))))⟩

end HasteBootsScalarPointerBody
