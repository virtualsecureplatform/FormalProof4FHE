module
public import FormalProof4FHE.HasteBoots.ConcreteNTTGoldPlan
@[expose] public section

/-! Original prime64::ConcreteTable::new word-formula wrapper. Goldilocks::new
copies the raw u64; canonicality is derived from Plan construction, not imposed
by a replacement field conversion. Error and panic outcomes remain distinct.
Rust representation/transmute, allocation, usize shifts, cache/concurrency,
optimized transforms and physical refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTGoldTable
open ConcreteNTTLimbArithmetic (Limb)

structure Table where
  root : Limb
  plan : ConcreteNTTGoldPlan.Plan
  deriving DecidableEq, Repr

inductive Outcome where
  | created (table : Table)
  | tableError
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def newTable (logSize : ℕ) : Outcome :=
  match ConcreteNTTGoldPlan.goldilocks logSize with
  | .rejected => .tableError
  | .assertionFailure => .assertionFailure
  | .indexFailure => .indexFailure
  | .constructed plan => .created ⟨plan.root,plan⟩

theorem origin (logSize : ℕ) (table : Table) (returned : newTable logSize = .created table) :
    ConcreteNTTGoldPlan.goldilocks logSize = .constructed table.plan ∧ table.root = table.plan.root := by
  unfold newTable at returned
  split at returned
  · cases returned
  · cases returned
  · cases returned
  · rename_i plan executed
    cases returned
    exact ⟨executed,rfl⟩

theorem plan_certified (logSize : ℕ) (table : Table) (returned : newTable logSize = .created table) :
    ConcreteNTTGoldPlan.Certified table.plan logSize :=
  ConcreteNTTGoldPlan.goldilocks_certified logSize table.plan (origin logSize table returned).1

theorem root_canonical (logSize : ℕ) (table : Table) (returned : newTable logSize = .created table) :
    table.root.val < NativeFields.goldilocksModulus := by
  have constructed := origin logSize table returned
  rw [constructed.2]
  exact ConcreteNTTGoldPlan.root_canonical logSize table.plan constructed.1

theorem root_primitive (logSize : ℕ) (table : Table) (returned : newTable logSize = .created table) :
    IsPrimitiveRoot (table.root.val : NativeFields.Goldilocks) (2^(logSize+1)) := by
  have constructed := origin logSize table returned
  rw [constructed.2]
  exact (plan_certified logSize table returned).root

theorem original_initialization (logSize : ℕ) (table : Table) (returned : newTable logSize = .created table) :
    ConcreteNTTDiv64Initialization.new table.plan.modulus = .initialized table.plan.divisor :=
  ConcreteNTTGoldPlan.original_initialization logSize table.plan (origin logSize table returned).1

theorem no_indexFailure (logSize : ℕ) : newTable logSize ≠ .indexFailure := by
  unfold newTable
  cases executed : ConcreteNTTGoldPlan.goldilocks logSize with
  | rejected => exact Outcome.noConfusion
  | assertionFailure => exact Outcome.noConfusion
  | indexFailure => exact (ConcreteNTTGoldPlan.no_indexFailure logSize executed).elim
  | constructed plan => exact Outcome.noConfusion

end FormalProof4FHE.HasteBoots.ConcreteNTTGoldTable
