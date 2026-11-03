module

public import FormalProof4FHE.HasteBoots.NativeBlindRotation

@[expose] public section

/-!
# Native one-block RLWE key switching and partial sample extraction

The target native profile has N=1024 and next_power_of_two(728)=1024,
so `key_switch_for_rlwe` takes its equal-dimension branch: there is one
polynomial gadget key and no preliminary nonce permutation. We explicitly
subtract its digit-weighted product, extract the constant coefficient, then
truncate the extracted mask. Other dimension branches are not modeled here.
`Trace.product` stores the positive gadget product. Rust's final Hadamard
sum trace instead records final-minus-initial, its negative; a representation
refinement must include this sign conversion.
-/

open scoped BigOperators
open FormalProof4FHE.HasteBoots.NativeBlindRotation

namespace FormalProof4FHE.HasteBoots.NativeKeySwitch

variable {q n dimension levels : ℕ} [NeZero n]

def zeroIndex : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

abbrev Key (q n levels : ℕ) := Fin levels → Cipher q n

/-- Coefficient-domain counterpart of the NTT constant-body initialization. -/
def initial (acc : Cipher q n) : Cipher q n :=
  fun half index => if half && (index.val == 0) then acc true zeroIndex else 0

def product (bits : ℕ) (key : Key q n levels) (poly : Poly q n) : Cipher q n :=
  fun half index => ∑ level : Fin levels, mul (digit bits level poly) (key level half) index

def switch (bits : ℕ) (key : Key q n levels) (acc : Cipher q n) : Cipher q n :=
  initial acc - product bits key (acc false)

/-- Extract (a0,-a(N-1),...,-a1;b0), retaining the requested original LWE dimension. -/
def extract (shape : dimension ≤ n) (acc : Cipher q n) : NativePublic.Ciphertext q dimension where
  mask i := if h : i.val = 0 then acc false zeroIndex else
    -(acc false ⟨n - i.val, by have := i.isLt; omega⟩)
  body := acc true zeroIndex

structure Trace (q n : ℕ) where
  product : Cipher q n
  switched : Cipher q n

/-- Explicit arithmetic constraints for the one-block final stage. -/
def Valid (bits : ℕ) (key : Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) (trace : Trace q n) (output : NativePublic.Ciphertext q dimension) : Prop :=
  trace.product = product bits key (acc false) ∧
  trace.switched = initial acc - trace.product ∧ output = extract shape trace.switched

def makeTrace (bits : ℕ) (key : Key q n levels) (acc : Cipher q n) : Trace q n :=
  let p := product bits key (acc false)
  ⟨p, initial acc - p⟩

theorem makeTrace_valid (bits : ℕ) (key : Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) :
    Valid bits key shape acc (makeTrace bits key acc) (extract shape (switch bits key acc)) :=
  ⟨rfl, rfl, rfl⟩

theorem valid_output (bits : ℕ) (key : Key q n levels) (shape : dimension ≤ n)
    (acc : Cipher q n) (trace : Trace q n) (output : NativePublic.Ciphertext q dimension)
    (valid : Valid bits key shape acc trace output) :
    output = extract shape (switch bits key acc) := by
  rcases valid with ⟨hp, hs, ho⟩
  rw [ho, hs, hp]
  rfl

end FormalProof4FHE.HasteBoots.NativeKeySwitch
