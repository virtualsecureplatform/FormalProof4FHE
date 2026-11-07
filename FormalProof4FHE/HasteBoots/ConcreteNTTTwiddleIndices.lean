module
public import FormalProof4FHE.HasteBoots.ConcreteNTTBitReverse
@[expose] public section

/-! Original forward and inverse twiddle write indices, including (n-k)%n.
Their bounds and injectivity are derived from the literal 64-bit reversal. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleIndices

def opposite (size index : ℕ) : ℕ := (size-index)%size

theorem opposite_lt (size index : ℕ) (positive : 0 < size) : opposite size index < size := Nat.mod_lt _ positive

theorem opposite_involutive (size index : ℕ) (bound : index < size) :
    opposite size (opposite size index) = index := by
  by_cases zero : index = 0
  · subst index
    simp [opposite]
  · have inside : size-index < size := by omega
    have back : size-(size-index) = index := by omega
    simp only [opposite,Nat.mod_eq_of_lt inside,back,Nat.mod_eq_of_lt bound]

theorem opposite_injective (size left right : ℕ) (leftBound : left < size) (rightBound : right < size)
    (same : opposite size left = opposite size right) : left = right := by
  have again := congrArg (opposite size) same
  simpa only [opposite_involutive size left leftBound,opposite_involutive size right rightBound] using again

def forward (bits index : ℕ) : ℕ := ConcreteNTTBitReverse.word bits index

def inverse (bits index : ℕ) : ℕ := ConcreteNTTBitReverse.word bits (opposite (2^bits) index)

theorem forward_lt (bits index : ℕ) (width : bits ≤ 64) : forward bits index < 2^bits :=
  ConcreteNTTBitReverse.word_lt bits index width

theorem inverse_lt (bits index : ℕ) (width : bits ≤ 64) : inverse bits index < 2^bits :=
  ConcreteNTTBitReverse.word_lt bits _ width

theorem forward_injective (bits left right : ℕ) (width : bits ≤ 64)
    (leftBound : left < 2^bits) (rightBound : right < 2^bits)
    (same : forward bits left = forward bits right) : left = right :=
  ConcreteNTTBitReverse.word_injective bits left right width leftBound rightBound same

theorem inverse_injective (bits left right : ℕ) (width : bits ≤ 64)
    (leftBound : left < 2^bits) (rightBound : right < 2^bits)
    (same : inverse bits left = inverse bits right) : left = right := by
  have positive : 0 < 2^bits := Nat.pow_pos (by decide)
  have opposites := ConcreteNTTBitReverse.word_injective bits _ _ width
    (opposite_lt (2^bits) left positive) (opposite_lt (2^bits) right positive) same
  exact opposite_injective (2^bits) left right leftBound rightBound opposites

end FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleIndices
