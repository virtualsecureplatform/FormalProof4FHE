module
public import FormalProof4FHE.HasteBoots.BlindRotationNTT
@[expose] public section

/-! Signed monomial action for the reference blind rotation, including every
modulo-2N wrap. Its NTT meaning is proved from the explicit coefficient scatter.
This is not native public-plan evaluation or acceptance/work refinement. -/
namespace FormalProof4FHE.HasteBoots.BlindRotationMonomial
open scoped BigOperators
open NativeBlindRotation (Poly rotate)
open BlindRotationNTT (evaluate transform)
noncomputable section

theorem periodic_power {q n : ℕ} (point : ZMod q) (negative : point^n = -1) (exponent : ℕ) :
    point^(exponent%(2*n)) = point^exponent := by
  have cycle : point^(2*n) = 1 := by
    rw [show 2*n = n*2 by omega, pow_mul, negative]
    ring
  calc
    _ = point^(exponent%(2*n))*(point^(2*n))^(exponent/(2*n)) := by rw [cycle, one_pow, mul_one]
    _ = point^(exponent%(2*n)+(2*n)*(exponent/(2*n))) := by rw [pow_add, pow_mul point (2*n)]
    _ = _ := congrArg (point^·) (Nat.mod_add_div exponent (2*n))

theorem scatter {q n : ℕ} (poly : Poly q n) (point : ZMod q) (negative : point^n = -1) (exponent : ℕ) (j : Fin n) :
    (∑ index : Fin n,
      (let target := (j.val+exponent)%(2*n)
       if target < n then (if index.val = target then poly j else 0)
       else (if index.val+n = target then -poly j else 0))*point^index.val) =
      poly j*point^(j.val+exponent) := by
  classical
  let target := (j.val+exponent)%(2*n)
  change (∑ index : Fin n, (if target < n then (if index.val = target then poly j else 0)
    else (if index.val+n = target then -poly j else 0))*point^index.val) = _
  have positive : 0 < n := Nat.zero_lt_of_lt j.isLt
  have bound : target < 2*n := Nat.mod_lt _ (by omega)
  by_cases low : target < n
  · let position : Fin n := ⟨target,low⟩
    rw [Finset.sum_eq_single position]
    · simp only [ite_eq_left low, position, ite_true]
      rw [periodic_power point negative]
    · intro index _ different
      have unequal : index.val ≠ target := fun same => different (Fin.ext same)
      simp only [ite_eq_left low, ite_eq_right unequal, zero_mul]
    · simp
  · let position : Fin n := ⟨target-n,by omega⟩
    rw [Finset.sum_eq_single position]
    · have selected : position.val+n = target := by dsimp only [position]; omega
      simp only [ite_eq_right low, ite_eq_left selected]
      have power : point^(j.val+exponent) = -point^(target-n) := by
        calc
          _ = point^target := (periodic_power point negative _).symm
          _ = point^(n+(target-n)) := congrArg (point^·) (by omega)
          _ = _ := by rw [pow_add, negative, neg_one_mul]
      rw [power]
      change -poly j * point^(target-n) = poly j * -point^(target-n)
      ring
    · intro index _ different
      have unequal : index.val+n ≠ target := by
        intro same
        apply different
        apply Fin.ext
        change index.val = target-n
        omega
      simp only [ite_eq_right low, ite_eq_right unequal, zero_mul]
    · simp

theorem evaluate_rotate {q n : ℕ} (poly : Poly q n) (point : ZMod q) (negative : point^n = -1) (exponent : ℕ) :
    evaluate (rotate exponent poly) point = evaluate poly point * point^exponent := by
  classical
  unfold evaluate rotate
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [scatter poly point negative exponent j, pow_add]
  ring

section Field
variable {q : ℕ} [Fact q.Prime]

def powers (log : ℕ) (psi : ZMod q) (exponent : ℕ) : Poly q (2^log) :=
  fun index => NTTButterfly.nodes log psi index ^ exponent

theorem transform_rotate (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (poly : Poly q (2^log)) (exponent : ℕ) :
    transform log psi (rotate exponent poly) = transform log psi poly * powers log psi exponent := by
  funext index
  exact evaluate_rotate poly _ (NTTButterfly.nodes_power log psi primitive index) exponent

theorem butterfly_rotate (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (poly : Poly q (2^log)) (exponent : ℕ) :
    NTTButterfly.flatTransform log psi (psi^2) (rotate exponent poly) =
      NTTButterfly.flatTransform log psi (psi^2) poly * powers log psi exponent := by
  simp only [NTTButterfly.negacyclic_evaluation log psi primitive]
  exact transform_rotate log psi primitive poly exponent

theorem rotate_of_pointwise (log : ℕ) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (input output : Poly q (2^log)) (exponent : ℕ)
    (identity : transform log psi output = transform log psi input * powers log psi exponent) :
    output = rotate exponent input := by
  apply BlindRotationNTT.transform_injective log psi primitive
  rw [transform_rotate log psi primitive]
  exact identity
end Field
end
end FormalProof4FHE.HasteBoots.BlindRotationMonomial
