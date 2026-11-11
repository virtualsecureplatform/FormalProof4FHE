module
import all FormalProof4FHE.HasteBoots.ProgramReceiptCollision
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ReceiptCollisionSmoke
open HasteBootsSamplerAncestrySmoke (worldZero)
open NativeReceiptPrefixView (key)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
noncomputable section

def left : InputIndexedOracle.Input := [1,2,3]
def right : InputIndexedOracle.Input := [4]
def program : Program Unit := .start (key left) (.read (key left) 7 0 (fun _ =>
  .hash (key left) (fun _ => .read (key left) 999 1 (fun _ =>
    .hash (key right) (fun _ => .read (key right) 0 64 (fun _ => .pure ()))))))

theorem prior_names : ReceiptPayloadView.payloads (runPrefix 4 program worldZero).run.2 = {left} := by
  change ReceiptPayloadView.payloads [Observation.start (key left),.output (key left) 7 [],
    .hash (key left) _,.output (key left) 999 [0]] = _
  simp [ReceiptPayloadView.payloads,List.filterMap_cons,List.filterMap_nil,ReceiptPayloadView.candidate,ReceiptPayloadView.read_key]

/-- Hash-only naming selects a fresh distinct receipt key, even though no
full digest has yet been read for either key. -/
theorem selected : ReceiptCollisionRisk.select OracleProgramMachine.step (runPrefix 4 program worldZero).run = some right := by
  change (ReceiptCollisionRisk.candidate (.hash (key right))).bind (fun raw =>
    if raw ∈ ReceiptPayloadView.payloads (runPrefix 4 program worldZero).run.2 then none else some raw) = _
  simp [ReceiptCollisionRisk.candidate,ReceiptPayloadView.read_key,prior_names,left,right]

theorem actual_hit : ReceiptCollisionRisk.event OracleProgramMachine.step (runPrefix 4 program worldZero).run worldZero := by
  simp only [ReceiptCollisionRisk.event,selected,prior_names,Finset.mem_singleton]
  exact ⟨left,rfl,rfl⟩

theorem exact_charge : ReceiptCollisionRisk.risk OracleProgramMachine.step (runPrefix 4 program worldZero).run =
    1/(2 : ENNReal)^512 := by
  simp only [ReceiptCollisionRisk.risk,selected,prior_names,Finset.card_singleton,Nat.cast_one]

/-- An actual hash naming prevents charging a later partial SHAKE read. -/
theorem repeated_none : ReceiptCollisionRisk.select OracleProgramMachine.step (runPrefix 3 program worldZero).run = none := by
  change (ReceiptCollisionRisk.candidate (.read (key left) 999 1)).bind (fun raw =>
    if raw ∈ ReceiptPayloadView.payloads [Observation.start (key left),.output (key left) 7 [],.hash (key left) _] then none else some raw) = none
  simp [ReceiptCollisionRisk.candidate,ReceiptPayloadView.payloads,ReceiptPayloadView.candidate,ReceiptPayloadView.read_key]

theorem final_collision : ReceiptDigestFixation.Collision (run program worldZero).run.2 worldZero := by
  have first : left ∈ ReceiptPayloadView.payloads (run program worldZero).run.2 := by
    apply ReceiptPayloadView.hashed left _ _
    change _ ∈ [_,_,_,_,_,_]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have second : right ∈ ReceiptPayloadView.payloads (run program worldZero).run.2 := by
    apply ReceiptPayloadView.hashed right _ _
    change _ ∈ [_,_,_,_,_,_]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  exact ⟨left,first,right,second,by decide +kernel,rfl⟩

theorem covered : ProgramReceiptCollision.Bad program worldZero :=
  ProgramReceiptCollision.covers program worldZero final_collision

end
end FormalProof4FHE.HasteBoots.ReceiptCollisionSmoke
