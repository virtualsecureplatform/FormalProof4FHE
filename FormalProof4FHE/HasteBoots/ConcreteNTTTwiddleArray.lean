module
public import FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleIndices
@[expose] public section

/-! Literal paired writes of non-Shoup init_negacyclic_twiddles. The forward
and inverse indices, zero-index inverse branch, stored subtraction and final
modular product are retained. Bounds failure is distinguished from Plan
rejection. Allocation, machine shifts/wrapping subtraction and compiler/cost
refinement remain separate; the derived canonical word domain makes the
subtraction cast inert on the original valid root path. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleArray
open ConcreteNTTLimbArithmetic (Limb radix)
open ConcreteNTTDiv64Initialization (State Correct mulMod)
open ConcreteNTTTwiddleIndices (forward inverse)

def powerWord (state : State) (root : Limb) (index : ℕ) : Limb :=
  ConcreteNTTInitializedSearch.word (root.val^index % state.divisor.val)

def inverseValue (state : State) (index : ℕ) (wk : Limb) : Limb :=
  if index = 0 then wk else ConcreteNTTInitializedSearch.word (state.divisor.val-wk.val)

def inverseWord (state : State) (root : Limb) (index : ℕ) : Limb :=
  inverseValue state index (powerWord state root index)

theorem powerWord_value (state : State) (correct : Correct state) (root : Limb) (index : ℕ) :
    (powerWord state root index).val = root.val^index % state.divisor.val := by
  exact ConcreteNTTInitializedSearch.word_value _
    ((Nat.mod_lt _ (by have valid := correct.1; omega)).trans state.divisor.isLt)

theorem powerWord_canonical (state : State) (correct : Correct state) (root : Limb) (index : ℕ) :
    (powerWord state root index).val < state.divisor.val := by
  rw [powerWord_value state correct]
  exact Nat.mod_lt _ (by have valid := correct.1; omega)

theorem powerWord_cast (state : State) (correct : Correct state) (root : Limb) (index : ℕ) :
    ((powerWord state root index).val : ZMod state.divisor.val) = (root.val : ZMod state.divisor.val)^index := by
  rw [powerWord_value state correct,ZMod.natCast_mod,Nat.cast_pow]

theorem inverseValue_value (state : State) (index : ℕ) (wk : Limb) :
    (inverseValue state index wk).val = if index = 0 then wk.val else state.divisor.val-wk.val := by
  unfold inverseValue
  split
  · rfl
  · exact ConcreteNTTInitializedSearch.word_value _
      ((Nat.sub_le state.divisor.val wk.val).trans_lt state.divisor.isLt)

theorem inverseWord_value (state : State) (correct : Correct state) (root : Limb) (index : ℕ) :
    (inverseWord state root index).val =
      if index = 0 then root.val^index % state.divisor.val else state.divisor.val-(root.val^index % state.divisor.val) := by
  simp only [inverseWord,inverseValue_value,powerWord_value state correct]

theorem inverseWord_cast (state : State) (correct : Correct state) (root : Limb) (index : ℕ) :
    ((inverseWord state root index).val : ZMod state.divisor.val) =
      if index = 0 then 1 else -(root.val : ZMod state.divisor.val)^index := by
  by_cases zero : index = 0
  · subst index
    simp only [inverseWord,inverseValue,ite_true,powerWord_cast state correct,pow_zero]
  · rw [inverseWord_value state correct,ite_eq_right zero,ite_eq_right zero,
      Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (by have valid := correct.1; omega))),
      ZMod.natCast_self,ZMod.natCast_mod,Nat.cast_pow,zero_sub]

theorem inverseWord_canonical (state : State) (correct : Correct state)
    [Fact (Nat.Prime state.divisor.val)] (root : Limb)
    (nonzero : (root.val : ZMod state.divisor.val) ≠ 0) (index : ℕ) :
    (inverseWord state root index).val < state.divisor.val := by
  have canonical := powerWord_canonical state correct root index
  have positive : (powerWord state root index).val ≠ 0 := by
    intro zero
    have cast := powerWord_cast state correct root index
    rw [zero,Nat.cast_zero] at cast
    exact (pow_ne_zero index nonzero) cast.symm
  rw [inverseWord,inverseValue_value]
  split
  · exact canonical
  · omega

theorem powerWord_step (state : State) (correct : Correct state) (root wk : Limb) (index : ℕ)
    (previous : wk = powerWord state root index) : mulMod state wk root = powerWord state root (index+1) := by
  apply Fin.ext
  simp only [ConcreteNTTDiv64Initialization.mulMod_correct state correct,previous,
    powerWord_value state correct,Nat.pow_succ,Nat.mul_mod,Nat.mod_mod]

def fill (state : State) (root : Limb) (bits : ℕ) :
    ℕ → ℕ → Limb → Array Limb → Array Limb → Option (Array Limb × Array Limb)
  | 0,_,_,fwd,inv => some (fwd,inv)
  | remaining+1,index,wk,fwd,inv =>
    if fwdBound : forward bits index < fwd.size then
      if invBound : inverse bits index < inv.size then
        let next := mulMod state wk root
        fill state root bits remaining (index+1) next
          (fwd.set (forward bits index) wk fwdBound)
          (inv.set (inverse bits index) (inverseValue state index wk) invBound)
      else none
    else none

def Stored (state : State) (root : Limb) (bits : ℕ) (fwd inv : Array Limb) (count : ℕ) : Prop :=
  ∀ index, index < count →
    fwd[forward bits index]? = some (powerWord state root index) ∧
    inv[inverse bits index]? = some (inverseWord state root index)

theorem fill_correct (state : State) (correct : Correct state) (root : Limb) (bits : ℕ)
    (width : bits ≤ 64) (remaining index : ℕ) (wk : Limb) (fwd inv : Array Limb)
    (space : index+remaining = 2^bits) (fwdSize : fwd.size = 2^bits) (invSize : inv.size = 2^bits)
    (previous : wk = powerWord state root index) (stored : Stored state root bits fwd inv index) :
    ∃ output, fill state root bits remaining index wk fwd inv = some output ∧
      output.1.size = 2^bits ∧ output.2.size = 2^bits ∧
      Stored state root bits output.1 output.2 (2^bits) := by
  induction remaining generalizing index wk fwd inv with
  | zero =>
    refine ⟨(fwd,inv),rfl,fwdSize,invSize,?_⟩
    have same : index = 2^bits := by omega
    simpa only [same] using stored
  | succ remaining ih =>
    have indexBound : index < 2^bits := by omega
    have fwdBound : forward bits index < fwd.size := by rw [fwdSize]; exact ConcreteNTTTwiddleIndices.forward_lt bits index width
    have invBound : inverse bits index < inv.size := by rw [invSize]; exact ConcreteNTTTwiddleIndices.inverse_lt bits index width
    have updated : Stored state root bits
        (fwd.set (forward bits index) wk fwdBound)
        (inv.set (inverse bits index) (inverseValue state index wk) invBound) (index+1) := by
      intro j prior
      by_cases same : j = index
      · subst j
        simp [previous,inverseWord]
      · have earlier : j < index := by omega
        have jBound : j < 2^bits := by omega
        have fwdDifferent : forward bits index ≠ forward bits j := by
          intro collision
          exact same (ConcreteNTTTwiddleIndices.forward_injective bits index j width indexBound jBound collision).symm
        have invDifferent : inverse bits index ≠ inverse bits j := by
          intro collision
          exact same (ConcreteNTTTwiddleIndices.inverse_injective bits index j width indexBound jBound collision).symm
        simpa only [Array.getElem?_set_ne fwdBound fwdDifferent,Array.getElem?_set_ne invBound invDifferent]
          using stored j earlier
    obtain ⟨output,executed,lengthF,lengthI,contents⟩ := ih (index+1) (mulMod state wk root)
      (fwd.set (forward bits index) wk fwdBound)
      (inv.set (inverse bits index) (inverseValue state index wk) invBound)
      (by omega) (by simpa only [Array.size_set] using fwdSize) (by simpa only [Array.size_set] using invSize)
      (powerWord_step state correct root wk index previous) updated
    refine ⟨output,?_,lengthF,lengthI,contents⟩
    simpa only [fill,dite_eq_left fwdBound,dite_eq_left invBound] using executed

def build (state : State) (root : Limb) (bits : ℕ) : Option (Array Limb × Array Limb) :=
  fill state root bits (2^bits) 0 1 (Array.replicate (2^bits) 0) (Array.replicate (2^bits) 0)

theorem build_correct (state : State) (correct : Correct state) (root : Limb) (bits : ℕ) (width : bits ≤ 64) :
    ∃ output, build state root bits = some output ∧ output.1.size = 2^bits ∧ output.2.size = 2^bits ∧
      Stored state root bits output.1 output.2 (2^bits) := by
  apply fill_correct state correct root bits width (2^bits) 0 1 _ _ (by omega)
    (by simp) (by simp) ?_ ?_
  · apply Fin.ext
    rw [powerWord_value state correct]
    change 1 = root.val^0 % state.divisor.val
    simp only [Nat.pow_zero,Nat.mod_eq_of_lt correct.1]
  · intro j prior
    omega

end FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleArray
