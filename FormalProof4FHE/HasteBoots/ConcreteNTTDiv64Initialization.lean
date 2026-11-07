module
public import FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
public import FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
@[expose] public section

/-! Literal natural-word Div64::new: retain divisor, u128 single reciprocal,
and the u256 reciprocal obtained by dividing MAX and adding one. Invalid
zero/one divisors retain the native assertion outcome. Actual machine division,
layout/instructions/compiler, plan/cache and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
open ConcreteNTTLimbArithmetic (radix Limb)
open ConcreteNTTU256Mul64 (Word value limit)
open ConcreteNTTU256Mul128 (Wide)

def maximum : Word :=
  let limb : Limb := ⟨radix-1,by have positive := ConcreteNTTLimbArithmetic.radix_pos; omega⟩
  ⟨limb,limb,limb,limb⟩

def one : Word := ⟨1,0,0,0⟩

theorem maximum_value : value maximum = limit-1 := by norm_num [maximum,value,limit,radix]
theorem one_value : value one = 1 := by norm_num [one,value]

structure State where
  doubleReciprocal : Word
  singleReciprocal : Wide
  divisor : Limb
  deriving DecidableEq, Repr

def buildState (divisor : Limb) (valid : 1 < divisor.val) : State :=
  let quotient := ConcreteNTTU256Division.divide maximum divisor (by omega)
  let doubled := (ConcreteNTTU256Add.add quotient.1 one).1
  let single := (radix^2-1)/divisor.val+1
  let fits : single < radix^2 :=
    ReciprocalRemainder.reciprocal_lt (radix^2) divisor.val (by decide) valid
  ⟨doubled,⟨single,fits⟩,divisor⟩

inductive Outcome where
  | initialized (state : State)
  | assertionFailure
  deriving DecidableEq, Repr

def new (divisor : Limb) : Outcome :=
  if valid : 1 < divisor.val then .initialized (buildState divisor valid) else .assertionFailure

def Correct (state : State) : Prop :=
  1 < state.divisor.val ∧
  value state.doubleReciprocal = ConcreteNTTDiv64.reciprocal state.divisor.val ∧
  state.singleReciprocal.val = (radix^2-1)/state.divisor.val+1

theorem initialize_double (divisor : Limb) (valid : 1 < divisor.val) :
    value (buildState divisor valid).doubleReciprocal = ConcreteNTTDiv64.reciprocal divisor.val := by
  simp only [buildState,ConcreteNTTU256Add.add_low,ConcreteNTTU256Division.divide_quotient,maximum_value,one_value]
  rfl

theorem initialize_no_overflow (divisor : Limb) (valid : 1 < divisor.val) :
    (ConcreteNTTU256Add.add (ConcreteNTTU256Division.divide maximum divisor (by omega)).1 one).2 = false := by
  have small := ReciprocalRemainder.reciprocal_lt limit divisor.val (by decide) valid
  change (limit-1)/divisor.val+1 < limit at small
  have notOverflow : ¬(ConcreteNTTU256Add.add (ConcreteNTTU256Division.divide maximum divisor (by omega)).1 one).2 = true := by
    rw [ConcreteNTTU256Add.add_overflow,ConcreteNTTU256Division.divide_quotient,maximum_value,one_value]
    omega
  cases outcome : (ConcreteNTTU256Add.add (ConcreteNTTU256Division.divide maximum divisor (by omega)).1 one).2 <;> simp_all

theorem initialize_correct (divisor : Limb) (valid : 1 < divisor.val) : Correct (buildState divisor valid) :=
  ⟨valid,initialize_double divisor valid,rfl⟩

theorem new_origin (divisor : Limb) (state : State) (executed : new divisor = .initialized state) :
    ∃ valid : 1 < divisor.val, state = buildState divisor valid := by
  unfold new at executed
  split at executed
  · rename_i valid
    exact ⟨valid,(Outcome.initialized.inj executed).symm⟩
  · contradiction

theorem new_correct (divisor : Limb) (state : State) (executed : new divisor = .initialized state) : Correct state := by
  obtain ⟨valid,rfl⟩ := new_origin divisor state executed
  exact initialize_correct divisor valid

theorem new_rejected (divisor : Limb) : new divisor = .assertionFailure ↔ divisor.val ≤ 1 := by
  unfold new
  split <;> simp_all

def remainder (state : State) (input : Wide) : Limb :=
  ConcreteNTTU256Mul128.remainder state.doubleReciprocal state.divisor input

theorem remainder_correct (state : State) (correct : Correct state) (input : Wide) :
    (remainder state input).val = input.val%state.divisor.val :=
  ConcreteNTTU256Mul128.remainder_eq state.doubleReciprocal state.divisor input correct.1 correct.2.1

theorem new_remainder (divisor : Limb) (state : State) (executed : new divisor = .initialized state) (input : Wide) :
    (remainder state input).val = input.val%divisor.val := by
  obtain ⟨valid,rfl⟩ := new_origin divisor state executed
  exact remainder_correct (buildState divisor valid) (initialize_correct divisor valid) input

def mulMod (state : State) (left right : Limb) : Limb :=
  remainder state ⟨left.val*right.val,ConcreteNTTDiv64.product_fits left.val right.val left.isLt right.isLt⟩

theorem mulMod_correct (state : State) (correct : Correct state) (left right : Limb) :
    (mulMod state left right).val = left.val*right.val%state.divisor.val := remainder_correct state correct _

theorem new_mulMod (divisor : Limb) (state : State) (executed : new divisor = .initialized state) (left right : Limb) :
    (mulMod state left right).val = left.val*right.val%divisor.val := new_remainder divisor state executed _

end FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
