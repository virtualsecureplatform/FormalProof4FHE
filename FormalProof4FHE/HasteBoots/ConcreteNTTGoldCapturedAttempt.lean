module
public import FormalProof4FHE.HasteBoots.ConcreteNTTGoldCacheRCU
@[expose] public section

/-! A held snapshot value has exactly the existing private-ticket attempt
semantics. Constructor phases retain such values across permitted interleavings;
actual Arc/memory/Rust refinement is still a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTGoldCapturedAttempt
open ConcreteNTTGoldCacheRCU

def run (logSize : ℕ) (machine : Machine) (snapshot : Snapshot) : Attempt :=
  match ConcreteNTTGoldCache.publish logSize snapshot.tables with
  | .assertionFailure => .assertionFailure
  | .indexFailure => .indexFailure
  | .published proposal =>
    if snapshot.version = machine.version then
      .committed {machine with version := machine.version+1,current := {machine.current with tables := proposal}}
    else .retry proposal

theorem ticket_eq (logSize : ℕ) (machine : Machine) (ticket : Fin machine.snapshots.size) :
    run logSize machine machine.snapshots[ticket.val] = attempt logSize machine ticket := rfl

theorem member_ticket (machine : Machine) (snapshot : Snapshot) (member : snapshot ∈ machine.snapshots.toList) :
    ∃ ticket : Fin machine.snapshots.size, machine.snapshots[ticket.val] = snapshot := by
  obtain ⟨i,bound,same⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨i,by simpa only [Array.length_toList] using bound⟩,by simpa only [Array.getElem_toList] using same⟩

theorem commit_snapshots (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
    (executed : attempt logSize before ticket = .committed after) : after.snapshots = before.snapshots := by
  unfold attempt at executed
  dsimp only at executed
  split at executed
  · cases executed
  · cases executed
  · split at executed
    · cases executed
      rfl
    · cases executed

theorem root_snapshots (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
    (root : ConcreteNTTLimbArithmetic.Limb) (executed : readRootSnapshot logSize before ticket = .success root after) :
    after.snapshots = before.snapshots := by
  unfold readRootSnapshot at executed
  dsimp only at executed
  split at executed
  · cases executed
  · cases executed
  · cases executed
  · cases executed
    rfl

inductive Move : Machine → Machine → Prop where
  | capture (machine : Machine) : Move machine (ConcreteNTTGoldCacheRCU.capture machine)
  | commit (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
      (executed : attempt logSize before ticket = .committed after) : Move before after
  | root (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
      (root : ConcreteNTTLimbArithmetic.Limb) (executed : readRootSnapshot logSize before ticket = .success root after) : Move before after

theorem move_reachable (before after : Machine) (prior : Reachable before) (move : Move before after) : Reachable after := by
  cases move with
  | capture => exact .capture prior
  | commit logSize before after ticket executed => exact .commit logSize ticket prior executed
  | root logSize before after ticket root executed => exact .rootSnapshot logSize ticket root prior executed

theorem move_snapshot_member (before after : Machine) (move : Move before after) (snapshot : Snapshot)
    (member : snapshot ∈ before.snapshots.toList) : snapshot ∈ after.snapshots.toList := by
  cases move with
  | capture => simp only [ConcreteNTTGoldCacheRCU.capture,Array.toList_push,List.mem_append]; exact Or.inl member
  | commit logSize before after ticket executed => rw [commit_snapshots logSize before after ticket executed]; exact member
  | root logSize before after ticket root executed => rw [root_snapshots logSize before after ticket root executed]; exact member

theorem move_table_read (before after : Machine) (prior : Reachable before) (move : Move before after)
    (key : ℕ) (table : ConcreteNTTGoldTable.Table)
    (found : ConcreteNTTCacheLookup.lookup before.current.tables key = some table) :
    ConcreteNTTCacheLookup.lookup after.current.tables key = some table := by
  cases move with
  | capture => exact found
  | commit logSize before after ticket executed => exact committed_read_preserved logSize before after ticket prior executed key table found
  | root logSize before after ticket root executed =>
    have post := root_snapshot_post logSize before after ticket (reachable_valid before prior) root executed
    rw [post.2.1]
    exact found

end FormalProof4FHE.HasteBoots.ConcreteNTTGoldCapturedAttempt
