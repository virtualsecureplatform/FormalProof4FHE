module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixProductLoop

@[expose] public section

/-!
# Literal row-major payload execution of matrix multiplication

The array/list payload has its exact square length throughout execution.
Every accumulator read uses a proved row-major bound; each update is one
raw list-set write. The nested loops preserve the native a,c,b order.
Serialization from the finite-state loop commutes with every step and with
the complete program, rather than assuming a correct final matrix.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixProductPayload

open NativeFieldRepresentation
open NativeGoldMatrixProductLoop (State)

structure Payload (width : ℕ) where
  values : List GoldWord
  length : values.length = width * width

def serialize {width : ℕ} (out : State width) : Payload width :=
  ⟨NativeGoldMatrixProductLoop.flatten out, NativeGoldMatrixProductLoop.flatten_length out⟩

def zero (width : ℕ) : Payload width := ⟨List.replicate (width * width) 0, List.length_replicate⟩

def step {width : ℕ} (left right : State width) (a c b : Fin width) (out : Payload width) : Payload width :=
  ⟨out.values.set (a.val * width + b.val) (NativeGoldArithmetic.add
    (out.values[a.val * width + b.val]'(by rw [out.length]; exact NativeGoldMatrixMeaning.address_bound width a b))
    (NativeGoldArithmetic.mul (left a c) (right c b))), by rw [List.length_set, out.length]⟩

def bLoop {width : ℕ} (left right : State width) (a c : Fin width) :
    (count : ℕ) → count ≤ width → Payload width → Payload width
  | 0, _, out => out
  | count + 1, bound, out => step left right a c ⟨count, by omega⟩
      (bLoop left right a c count (by omega) out)

def cLoop {width : ℕ} (left right : State width) (a : Fin width) :
    (count : ℕ) → count ≤ width → Payload width → Payload width
  | 0, _, out => out
  | count + 1, bound, out => bLoop left right a ⟨count, by omega⟩ width (by omega)
      (cLoop left right a count (by omega) out)

def aLoop {width : ℕ} (left right : State width) :
    (count : ℕ) → count ≤ width → Payload width → Payload width
  | 0, _, out => out
  | count + 1, bound, out => cLoop left right ⟨count, by omega⟩ width (by omega)
      (aLoop left right count (by omega) out)

def run {width : ℕ} (left right : State width) : Payload width :=
  aLoop left right width (by omega) (zero width)

@[ext] theorem Payload.ext {width : ℕ} {left right : Payload width} (same : left.values = right.values) : left = right := by
  cases left; cases right; cases same; rfl

theorem serialize_zero (width : ℕ) : serialize (fun _ _ : Fin width => (0 : GoldWord)) = zero width := by
  apply Payload.ext
  apply List.ext_getElem (by simp only [serialize, NativeGoldMatrixProductLoop.flatten_length, zero, List.length_replicate])
  intro index leftPresent rightPresent
  simp only [serialize, NativeGoldMatrixProductLoop.flatten, List.getElem_ofFn, zero, List.getElem_replicate]

theorem serialize_step {width : ℕ} (left right : State width) (a c b : Fin width) (out : State width) :
    serialize (NativeGoldMatrixProductLoop.step left right a c b out) = step left right a c b (serialize out) := by
  apply Payload.ext
  change NativeGoldMatrixProductLoop.flatten (NativeGoldMatrixProductLoop.write out a b
    (NativeGoldArithmetic.add (out a b) (NativeGoldArithmetic.mul (left a c) (right c b)))) = _
  rw [NativeGoldMatrixProductLoop.flatten_write]
  change _ = (NativeGoldMatrixProductLoop.flatten out).set (a.val * width + b.val)
    (NativeGoldArithmetic.add ((NativeGoldMatrixProductLoop.flatten out)[a.val * width + b.val]'(by
      rw [NativeGoldMatrixProductLoop.flatten_length]; exact NativeGoldMatrixMeaning.address_bound width a b))
      (NativeGoldArithmetic.mul (left a c) (right c b)))
  rw [NativeGoldMatrixProductLoop.flatten_get]

theorem serialize_bLoop {width : ℕ} (left right : State width) (a c : Fin width)
    (count : ℕ) (bound : count ≤ width) (out : State width) :
    serialize (NativeGoldMatrixProductLoop.bLoop left right a c count bound out) =
      bLoop left right a c count bound (serialize out) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [NativeGoldMatrixProductLoop.bLoop, bLoop, serialize_step, ih (by omega)]

theorem serialize_cLoop {width : ℕ} (left right : State width) (a : Fin width)
    (count : ℕ) (bound : count ≤ width) (out : State width) :
    serialize (NativeGoldMatrixProductLoop.cLoop left right a count bound out) =
      cLoop left right a count bound (serialize out) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [NativeGoldMatrixProductLoop.cLoop, cLoop, serialize_bLoop, ih (by omega)]

theorem serialize_aLoop {width : ℕ} (left right : State width)
    (count : ℕ) (bound : count ≤ width) (out : State width) :
    serialize (NativeGoldMatrixProductLoop.aLoop left right count bound out) =
      aLoop left right count bound (serialize out) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [NativeGoldMatrixProductLoop.aLoop, aLoop, serialize_cLoop, ih (by omega)]

theorem run_eq_serialize {width : ℕ} (left right : State width) :
    run left right = serialize (NativeGoldMatrixProductLoop.product left right) := by
  rw [NativeGoldMatrixProductLoop.product, serialize_aLoop, serialize_zero]
  rfl

end FormalProof4FHE.HasteBoots.NativeGoldMatrixProductPayload
