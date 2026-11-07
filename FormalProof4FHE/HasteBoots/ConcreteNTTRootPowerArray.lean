module
public import FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
@[expose] public section

/-! Checked array-write semantics for the original root_powers initialization.
The allocated array, the two original initial writes and every subsequent
retained-state modular product are preserved. This is a component of Plan
construction; allocation/machine refinement and the remaining Plan fields are
separate obligations. None here denotes an out-of-bounds write, not a native
Plan rejection. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTRootPowerArray
open ConcreteNTTLimbArithmetic (Limb)
open ConcreteNTTDiv64Initialization (State Correct mulMod)

def fill (state : State) (root : Limb) : ℕ → ℕ → Limb → Array Limb → Option (Array Limb)
  | 0,_,_,data => some data
  | remaining+1,index,wk,data =>
    if bound : index < data.size then
      let next := mulMod state wk root
      fill state root remaining (index+1) next (data.set index next bound)
    else none

def build (state : State) (size : ℕ) (root : Limb) : Option (Array Limb) :=
  if domain : 2 ≤ size then
    let data : Array Limb := Array.replicate size 0
    let first := data.set 0 1 (by simp only [data,Array.size_replicate]; omega)
    let initialized := first.set 1 root (by simp only [first,Array.size_set,data,Array.size_replicate]; omega)
    fill state root (size-2) 2 root initialized
  else none

def Stored (state : State) (root : Limb) (data : Array Limb) (count : ℕ) : Prop :=
  ∀ (i : ℕ) (bound : i < data.size), i < count →
    (data[i]).val < state.divisor.val ∧
    ((data[i]).val : ZMod state.divisor.val) = (root.val : ZMod state.divisor.val)^i

theorem stored_value (state : State) (correct : Correct state) (root : Limb)
    (data : Array Limb) (count : ℕ) (stored : Stored state root data count)
    (i : ℕ) (bound : i < data.size) (prior : i < count) :
    (data[i]).val = root.val^i % state.divisor.val := by
  have entry := stored i bound prior
  apply (ConcreteNTTWordSearch.cast_injective state.divisor.val (data[i]).val
    (root.val^i % state.divisor.val) entry.1 (Nat.mod_lt _ (by have valid := correct.1; omega))).mp
  simpa only [ZMod.natCast_mod,Nat.cast_pow] using entry.2

theorem fill_correct (state : State) (correct : Correct state) (root : Limb)
    (remaining index : ℕ) (wk : Limb) (data : Array Limb)
    (space : index+remaining = data.size) (positive : 1 ≤ index)
    (previous : (wk.val : ZMod state.divisor.val) = (root.val : ZMod state.divisor.val)^(index-1))
    (stored : Stored state root data index) :
    ∃ output, fill state root remaining index wk data = some output ∧
      output.size = data.size ∧ Stored state root output output.size := by
  induction remaining generalizing index wk data with
  | zero =>
    refine ⟨data,rfl,rfl,?_⟩
    have same : index = data.size := by omega
    simpa only [same] using stored
  | succ remaining ih =>
    have bound : index < data.size := by omega
    let next := mulMod state wk root
    have nextEq := ConcreteNTTInitializedPower.mulMod_formula state correct wk root
    have nextBound : next.val < state.divisor.val := by
      rw [show next.val = ConcreteNTTDiv64.mulMod state.divisor.val wk.val root.val from nextEq]
      exact ConcreteNTTDiv64.mulMod_lt state.divisor.val wk.val root.val correct.1 state.divisor.isLt wk.isLt root.isLt
    have nextCast : (next.val : ZMod state.divisor.val) = (root.val : ZMod state.divisor.val)^index := by
      rw [show next.val = ConcreteNTTDiv64.mulMod state.divisor.val wk.val root.val from nextEq,
        ConcreteNTTDiv64.mulMod_cast state.divisor.val wk.val root.val correct.1 state.divisor.isLt wk.isLt root.isLt,
        previous,← pow_succ]
      congr 1
      omega
    have updated : Stored state root (data.set index next bound) (index+1) := by
      intro i fits prior
      by_cases same : i = index
      · subst i
        simpa using And.intro nextBound nextCast
      · have earlier : i < index := by omega
        have original := stored i (by simpa using fits) earlier
        simpa [Array.getElem_set,same,Ne.symm same] using original
    obtain ⟨output,executed,size,contents⟩ := ih (index+1) next (data.set index next bound)
      (by simp only [Array.size_set]; omega) (by omega)
      (by simpa only [Nat.add_sub_cancel] using nextCast) updated
    refine ⟨output,?_,?_,contents⟩
    · simpa only [fill,dite_eq_left bound] using executed
    · simpa only [Array.size_set] using size

theorem build_correct (state : State) (correct : Correct state) (size : ℕ) (root : Limb)
    (domain : 2 ≤ size) (canonical : root.val < state.divisor.val) :
    ∃ output, build state size root = some output ∧ output.size = size ∧
      Stored state root output output.size := by
  let data : Array Limb := Array.replicate size 0
  let first := data.set 0 1 (by simp only [data,Array.size_replicate]; omega)
  let initialized := first.set 1 root (by simp only [first,Array.size_set,data,Array.size_replicate]; omega)
  have length : initialized.size = size := by simp only [initialized,first,Array.size_set,data,Array.size_replicate]
  have initial : Stored state root initialized 2 := by
    intro i fits prior
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · simp only [initialized,first,Array.getElem_set]
      exact ⟨correct.1,by simp⟩
    · simp only [initialized,Array.getElem_set]
      exact ⟨canonical,by simp⟩
  obtain ⟨output,executed,sizeEq,contents⟩ := fill_correct state correct root (size-2) 2 root initialized
    (by omega) (by decide) (by simp) initial
  refine ⟨output,?_,sizeEq.trans length,contents⟩
  simpa only [build,dite_eq_left domain] using executed

end FormalProof4FHE.HasteBoots.ConcreteNTTRootPowerArray
