module
public import FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
@[expose] public section

/-! Literal u64 limb multiply-with-carry formula from concrete-ntt u256_impl.rs
at cdeba793e46208320b30d78be19f7be78d49016a. The u128 intermediate is proved
not to overflow, and both returned limbs are bounded. Rust instruction and
compiler/physical refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
abbrev radix : ℕ := 2^64
abbrev Limb := Fin radix

theorem radix_pos : 0 < radix := by decide

theorem multiply_add_fits (left right carry : Limb) : left.val*right.val+carry.val < radix^2 := by
  have product : left.val*right.val ≤ (radix-1)*(radix-1) :=
    Nat.mul_le_mul (by have bound := left.isLt; omega) (by have bound := right.isLt; omega)
  have bound := carry.isLt
  norm_num [radix] at product bound ⊢
  omega

def mulCarry (left right carry : Limb) : Limb × Limb :=
  let result := left.val*right.val+carry.val
  (⟨result%radix,Nat.mod_lt _ radix_pos⟩,
   ⟨result/radix,(Nat.div_lt_iff_lt_mul radix_pos).mpr (by
     simpa only [pow_two] using multiply_add_fits left right carry)⟩)

theorem mulCarry_low (left right carry : Limb) :
    (mulCarry left right carry).1.val = (left.val*right.val+carry.val)%radix := rfl

theorem mulCarry_high (left right carry : Limb) :
    (mulCarry left right carry).2.val = (left.val*right.val+carry.val)/radix := rfl

theorem mulCarry_value (left right carry : Limb) :
    (mulCarry left right carry).1.val+radix*(mulCarry left right carry).2.val = left.val*right.val+carry.val :=
  Nat.mod_add_div _ _

end FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
