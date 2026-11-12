module
import all FormalProof4FHE.HasteBoots.PrivateCoinLookupChallengeProbability
import all FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage

namespace HasteBootsOffsetWorkSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
noncomputable section

def once (key : Input) : Program Unit := .read key 99 1 (fun _ => .pure ())
def repeated (key : Input) : Program Unit := .read key 99 1 (fun _ => .read key 7 1 (fun _ => .pure ()))
def empty (key : Input) : Program Unit := .read key 99 0 (fun _ => .pure ())

/-- A far-offset partial prequery pays the complete literal key once;
a later read of a different byte offset does not pay it a second time. -/
theorem partial_prequery_paid_once (key : Input) (world : World) :
    OffsetWorkPosition.charge (repeated key) 0 world = (key.length : ENNReal)*LookupStreamWorkRate.rate ∧
    OffsetWorkPosition.charge (repeated key) 1 world = 0 := by
  constructor
  · rfl
  · apply OffsetWorkPosition.charge_seen (repeated key) 1 world key 7 1 (fun _ => .pure ()) rfl
    change CausalStreamExposure.seen [.output key 99 (InputIndexedOracle.bytes world key 99 1)] key = true
    simp [CausalStreamExposure.seen,CausalStreamExposure.touches,InputIndexedOracle.bytes_length]

/-- A zero-byte read pays no first-exposure charge. -/
theorem empty_read_not_charged (key : Input) (world : World) : OffsetWorkPosition.charge (empty key) 0 world = 0 := by
  have selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 0 (empty key) world).run = none := rfl
  simp only [OffsetWorkPosition.charge,OffsetWorkPosition.score,ScalarEquationWork.selectedBytes,selected,Nat.cast_zero,zero_mul]

/-- Summing all observation positions stops after the actual single read,
so the infinite lifetime sum does not charge completed prefixes. -/
theorem one_read_lifetime_charge (key : Input) (world : World) :
    OffsetLifetimeWork.totalCharge (once key) world = (key.length : ENNReal)*LookupStreamWorkRate.rate := by
  unfold OffsetLifetimeWork.totalCharge
  rw [tsum_eq_single 0]
  · rfl
  · intro index different
    obtain ⟨index,rfl⟩ := Nat.exists_eq_succ_of_ne_zero different
    apply OffsetWorkPosition.charge_finished (once key) (index+1) world ()
    cases index <;> rfl

end
end HasteBootsOffsetWorkSmoke
