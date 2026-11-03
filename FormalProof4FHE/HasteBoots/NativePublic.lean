module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Native public NAND preprocessing

Independent mathematical model of `packed_pbs::public_inputs` and
`packed_monomial::{switch_public_scalar,nand_lut,initial_accumulator}`.
Natural-number arithmetic specifies the exact result, not machine overflow.
Blind rotation and final key switching are not specified in this file.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NativePublic

structure Ciphertext (q dimension : ℕ) where
  mask : Fin dimension → ZMod q
  body : ZMod q
  deriving DecidableEq

variable {q dimension n : ℕ}

/-- The native NAND input is the component-wise sum in the coefficient field. -/
def add (left right : Ciphertext q dimension) : Ciphertext q dimension :=
  ⟨left.mask + right.mask, left.body + right.body⟩

/-- Exact nearest-integer modulus switching, with half ties rounded up. -/
def roundModulus (before after value : ℕ) : ℕ :=
  ((value * after + before / 2) / before) % after

theorem roundModulus_lt (before after value : ℕ) (positive : 0 < after) :
    roundModulus before after value < after := Nat.mod_lt _ positive

/-- At native N=1024, every canonical 64-bit field residue fits the Rust u128 fast path. -/
theorem native_round_numerator_fits (before value : ℕ)
    (wordBound : before < 2 ^ 64) (canonical : value < before) :
    value * 2048 + before / 2 < 2 ^ 128 := by
  have halfBound := Nat.div_le_self before 2
  omega

/-- Canonical representative conversion, before the checked machine-word conversion. -/
def switchScalar (after : ℕ) (value : ZMod q) : ℕ :=
  roundModulus q after value.val

/-- Configured-stride NAND LUT; the second stride begins target mid, not target zero. -/
def nandLut (stride : ℕ) (index : Fin n) : ZMod q :=
  let mid := n / 2 + n / 4
  let low : ZMod q := (q / 8 : ℕ)
  if index.val < mid then
    if index.val % stride = 0 then low else 0
  else if (index.val - mid) % stride = 0 then -low else 0

/-- Public negative-body exponent in Z_(2N). -/
def initialRotation (body : ZMod q) : ℕ :=
  (2 * n - switchScalar (2 * n) body) % (2 * n)

/-- The exact scatter into the public (zero mask, rotated LUT) coefficient vector. -/
def initialAccumulator (lut : Fin n → ZMod q) (body : ZMod q)
    (index : Fin (2 * n)) : ZMod q :=
  ∑ j : Fin n,
    let target := (j.val + initialRotation (n := n) body) % (2 * n)
    if target < n then
      if index.val = n + target then lut j else 0
    else if index.val = target then -lut j else 0

/-- Every coefficient of the initial nonce polynomial is zero, for any body and LUT. -/
theorem initialAccumulator_mask_zero (lut : Fin n → ZMod q) (body : ZMod q)
    (index : Fin (2 * n)) (maskIndex : index.val < n) :
    initialAccumulator lut body index = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  dsimp only
  split_ifs <;> first | rfl | omega

/-- Public data deterministically derived from the two NAND input ciphertexts. -/
structure Frontend (q dimension n : ℕ) where
  combined : Ciphertext q dimension
  rotations : Fin dimension → ℕ
  initial : Fin (2 * n) → ZMod q

/-- No witness or prover-supplied output is used to construct this data. -/
def frontend (stride : ℕ) (left right : Ciphertext q dimension) : Frontend q dimension n :=
  let combined := add left right
  ⟨combined, fun i => switchScalar (2 * n) (combined.mask i),
    initialAccumulator (nandLut stride) combined.body⟩

theorem frontend_rotation_lt (stride : ℕ) (left right : Ciphertext q dimension)
    (positive : 0 < n) (i : Fin dimension) :
    (frontend (n := n) stride left right).rotations i < 2 * n :=
  roundModulus_lt _ _ _ (by omega)

end FormalProof4FHE.HasteBoots.NativePublic
