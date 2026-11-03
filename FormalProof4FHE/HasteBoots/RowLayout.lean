module

public import FormalProof4FHE.HasteBoots.BlockEncoder
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Flattening and padding for block-symbol rows

The source index is `block * b + lane`, exactly the coordinate gathering loop
in Rust `BlockReedSolomonCode::encode_row`. Entries beyond the original input
are zero, including a partially occupied last symbol. The NTT itself is not
modeled here: `encode` below uses the already verified direct evaluation.
-/

namespace FormalProof4FHE.HasteBoots.RowLayout

variable {F : Type*} [Field F] {size m b L : ℕ}

/-- Gather flat coefficients, with zeros in absent and trailing coordinates. -/
def padded (input : Fin size → F) (block : Fin m) (lane : Fin b) : F :=
  if h : (finProdFinEquiv (block, lane)).val < size then
    input ⟨(finProdFinEquiv (block, lane)).val, h⟩ else 0

/-- The concrete row-major address, with its finite bound. -/
theorem address (block : Fin m) (lane : Fin b) :
    (finProdFinEquiv (block, lane)).val = block.val * b + lane.val := by
  change lane.val + b * block.val = block.val * b + lane.val
  ac_rfl

/-- Recover the original flat message; padded coordinates are not returned. -/
def recover (capacity : size ≤ m * b) (coefficients : Fin m → Fin b → F)
    (index : Fin size) : F :=
  let pair := finProdFinEquiv.symm
    (⟨index.val, index.isLt.trans_le capacity⟩ : Fin (m * b))
  coefficients pair.1 pair.2

theorem recover_padded (capacity : size ≤ m * b) (input : Fin size → F) :
    recover capacity (padded input) = input := by
  funext index
  unfold recover padded
  simp [finProdFinEquiv, Nat.mod_add_div]

theorem padded_injective (capacity : size ≤ m * b) :
    Function.Injective (padded : (Fin size → F) → Fin m → Fin b → F) := by
  intro input other h
  have recovered := congrArg (recover capacity) h
  simpa only [recover_padded] using recovered

theorem padded_zero (input : Fin size → F) (block : Fin m) (lane : Fin b)
    (absent : size ≤ block.val * b + lane.val) : padded input block lane = 0 := by
  unfold padded
  rw [address]
  simp [Nat.not_lt.mpr absent]

/-- Semantic row encoder before flattening the output symbols. -/
def encode (domain : Fin L → F) (input : Fin size → F) : Fin L → Fin b → F :=
  BlockEncoder.encode domain (padded (m := m) input)

/-- Symbol-major, coordinate-minor output, as in the final Rust scatter loop. -/
def flatOutput (domain : Fin L → F) (input : Fin size → F) (index : Fin (L * b)) : F :=
  let pair := finProdFinEquiv.symm index
  encode (m := m) domain input pair.1 pair.2

theorem flatOutput_at (domain : Fin L → F) (input : Fin size → F)
    (symbol : Fin L) (lane : Fin b) :
    flatOutput (m := m) domain input (finProdFinEquiv (symbol, lane)) =
      encode (m := m) domain input symbol lane := by
  simp [flatOutput]

/-- Zero padding restricts the code; it does not require a new distance assumption. -/
theorem encode_mem_code [NeZero b] (domain : Fin L ↪ F) (input : Fin size → F) :
    encode (m := m) domain input ∈ BlockCode.code domain m b :=
  BlockEncoder.encode_mem_code domain (padded input)

theorem encode_injective (domain : Fin L ↪ F) (enough : m ≤ L)
    (capacity : size ≤ m * b) :
    Function.Injective (encode (m := m) (b := b) domain :
      (Fin size → F) → Fin L → Fin b → F) := by
  exact (BlockEncoder.encode_injective domain (by simpa using enough)).comp
    (padded_injective capacity)

end FormalProof4FHE.HasteBoots.RowLayout
