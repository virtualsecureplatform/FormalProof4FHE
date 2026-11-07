module
public import FormalProof4FHE.HasteBoots.ConcreteNTTConstructedTwiddles
@[expose] public section

/-! Literal retained-state inverse and word-formula Plan constants. u128 shift
results and u64 quotient casts are retained, and their inertness is derived on
the original Goldilocks path. Actual Rust shift/division/ilog2 instructions,
allocation/compiler and physical refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTPlanConstants
open ConcreteNTTLimbArithmetic (radix Limb)
open ConcreteNTTDiv64Initialization (State Correct)
open ConcreteNTTInitializedSearch (word)

def wide (value : ℕ) : Fin (radix^2) := Fin.ofNat (radix^2) value

def inverse (state : State) (size : ℕ) : Limb :=
  ConcreteNTTInitializedPower.power state (word size) (word (state.divisor.val-2))

def shoup (state : State) (value : Limb) (bits : ℕ) : Limb :=
  word ((wide (value.val*2^bits)).val/state.divisor.val)

def bitLength (state : State) : Limb := word (Nat.log2 state.divisor.val+1)

def bigL (state : State) (bits : ℕ) : Limb := word ((bitLength state).val+(bits-1))

def barrett (state : State) (bits : ℕ) : Limb :=
  word ((wide (2^(bigL state bits).val)).val/state.divisor.val)

structure Constants where
  nInverse : Limb
  nInverseShoup : Limb
  bigQ : Limb
  pBarrett : Limb
  deriving DecidableEq, Repr

def build (state : State) (size bits : ℕ) : Constants :=
  let nInverse := inverse state size
  ⟨nInverse,shoup state nInverse bits,bitLength state,barrett state bits⟩

theorem wide_value (value : ℕ) (fits : value < radix^2) : (wide value).val = value := by
  simp only [wide,Fin.val_ofNat,Nat.mod_eq_of_lt fits]

theorem scale64_fits (value : Limb) : value.val*radix < radix^2 := by
  have bound := Nat.mul_lt_mul_of_pos_right value.isLt ConcreteNTTLimbArithmetic.radix_pos
  simpa only [Nat.pow_two] using bound

theorem shoup64_value (state : State) (value : Limb) (canonical : value.val < state.divisor.val) :
    (shoup state value 64).val = value.val*radix/state.divisor.val := by
  have positive : 0 < state.divisor.val := by omega
  have quotient : value.val*radix/state.divisor.val < radix := by
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    have bound := Nat.mul_lt_mul_of_pos_right canonical ConcreteNTTLimbArithmetic.radix_pos
    simpa only [Nat.mul_comm] using bound
  change (word ((wide (value.val*radix)).val/state.divisor.val)).val = _
  rw [wide_value _ (scale64_fits value),ConcreteNTTInitializedSearch.word_value _ quotient]

theorem inverse_value (state : State) (correct : Correct state) (size : ℕ) (fits : size < radix) :
    (inverse state size).val = size^(state.divisor.val-2)%state.divisor.val := by
  have exponentFits : state.divisor.val-2 < radix := (Nat.sub_le _ _).trans_lt state.divisor.isLt
  rw [inverse,ConcreteNTTInitializedPower.power_correct state correct,
    ConcreteNTTInitializedSearch.word_value size fits,ConcreteNTTInitializedSearch.word_value _ exponentFits]

theorem inverse_canonical (state : State) (correct : Correct state) (size : ℕ) (fits : size < radix) :
    (inverse state size).val < state.divisor.val := by
  rw [inverse_value state correct size fits]
  exact Nat.mod_lt _ (by have valid := correct.1; omega)

theorem inverse_field (state : State) (correct : Correct state) [Fact (Nat.Prime state.divisor.val)]
    (size : ℕ) (positive : 0 < size) (bound : size < state.divisor.val) :
    (size : ZMod state.divisor.val)*((inverse state size).val : ZMod state.divisor.val) = 1 := by
  have fits := bound.trans state.divisor.isLt
  have nonzero : (size : ZMod state.divisor.val) ≠ 0 := by
    intro zero
    have divisible := (ZMod.natCast_eq_zero_iff size state.divisor.val).mp zero
    have remainder : size % state.divisor.val = size := Nat.mod_eq_of_lt bound
    have zeroRem := Nat.mod_eq_zero_of_dvd divisible
    omega
  have cast : ((inverse state size).val : ZMod state.divisor.val) =
      (size : ZMod state.divisor.val)^(state.divisor.val-2) := by
    rw [inverse_value state correct size fits,ZMod.natCast_mod,Nat.cast_pow]
  have exponent : state.divisor.val-2+1 = state.divisor.val-1 := by have valid := correct.1; omega
  rw [cast,mul_comm,← pow_succ,exponent]
  exact ZMod.pow_card_sub_one_eq_one nonzero

theorem build_shoup64_value (state : State) (correct : Correct state) (size : ℕ) (fits : size < radix) :
    (build state size 64).nInverseShoup.val = (inverse state size).val*radix/state.divisor.val :=
  shoup64_value state (inverse state size) (inverse_canonical state correct size fits)

theorem goldilocks_bitLength (state : State) (modulus : state.divisor.val = NativeFields.goldilocksModulus) :
    (bitLength state).val = 64 := by
  unfold bitLength
  rw [modulus]
  decide

theorem goldilocks_bigL (state : State) (modulus : state.divisor.val = NativeFields.goldilocksModulus) :
    (bigL state 64).val = 127 := by
  unfold bigL
  rw [goldilocks_bitLength state modulus]
  decide

theorem goldilocks_barrett (state : State) (modulus : state.divisor.val = NativeFields.goldilocksModulus) :
    (barrett state 64).val = 9223372039002259455 := by
  unfold barrett
  rw [goldilocks_bigL state modulus,modulus]
  decide

theorem goldilocks_barrett_formula (state : State) (modulus : state.divisor.val = NativeFields.goldilocksModulus) :
    (barrett state 64).val = 2^127/NativeFields.goldilocksModulus := by
  rw [goldilocks_barrett state modulus]
  decide

end FormalProof4FHE.HasteBoots.ConcreteNTTPlanConstants
