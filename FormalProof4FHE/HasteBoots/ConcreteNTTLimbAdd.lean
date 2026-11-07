module
public import FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
@[expose] public section

/-! Literal two-overflow-flag adc from concrete-ntt u256_impl.rs. The Boolean
carry is their OR, not their sum. Machine/compiler/physical refinement remains
separate from this bounded-word formula. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
open ConcreteNTTLimbArithmetic (radix Limb radix_pos)

def adc (left right : Limb) (carry : Bool) : Limb × Bool :=
  let first := left.val+right.val
  let second := first%radix+(if carry then 1 else 0)
  (⟨second%radix,Nat.mod_lt _ radix_pos⟩,decide (radix ≤ first) || decide (radix ≤ second))

theorem adc_value (left right : Limb) (carry : Bool) :
    (adc left right carry).1.val+radix*(if (adc left right carry).2 then 1 else 0) =
      left.val+right.val+(if carry then 1 else 0) := by
  have l := left.isLt
  have r := right.isLt
  unfold adc
  cases carry <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero,
    Bool.or_eq_true,decide_eq_true_eq]
  all_goals
    norm_num only [radix,Nat.reducePow] at l r ⊢
    split_ifs <;> omega

end FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
