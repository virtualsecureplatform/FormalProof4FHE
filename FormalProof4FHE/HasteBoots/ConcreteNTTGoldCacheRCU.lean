module
public import FormalProof4FHE.HasteBoots.ConcreteNTTGoldCache
@[expose] public section

/-! Captured-snapshot and compare/publication value semantics for the original
RCU callback. Private snapshot handles arise only from capture. Stale callbacks
still construct their actual proposals; retry receipts retain rejected proposals.
Versions are logical publication identities, not an assumed Rust pointer/Arc
refinement. Mutex-body linearization, ArcSwap memory/ABA/reclamation, Rust,
allocation, complete retry scheduling and actor-separated physical work remain
mandatory separate obligations. Ghost snapshot receipts carry no work bound. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTGoldCacheRCU
open ConcreteNTTLimbArithmetic (Limb)
open ConcreteNTTGoldTable (Table newTable)
open ConcreteNTTCacheLookup (lookup)

structure Snapshot where
  version : ℕ
  tables : List (ℕ × Table)
  deriving DecidableEq, Repr

structure Machine where
  version : ℕ := 0
  current : ConcreteNTTGoldCache.State := {}
  snapshots : Array Snapshot := #[]
  deriving DecidableEq, Repr

def capture (machine : Machine) : Machine :=
  {machine with snapshots := machine.snapshots.push ⟨machine.version,machine.current.tables⟩}

def newest (machine : Machine) : Fin (capture machine).snapshots.size :=
  ⟨machine.snapshots.size,by simp [capture]⟩

theorem capture_value (machine : Machine) :
    (capture machine).snapshots[(newest machine).val] = ⟨machine.version,machine.current.tables⟩ := by
  simp [capture,newest]

inductive Attempt where
  | committed (machine : Machine)
  | retry (proposal : List (ℕ × Table))
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def attempt (logSize : ℕ) (machine : Machine) (ticket : Fin machine.snapshots.size) : Attempt :=
  let snapshot := machine.snapshots[ticket.val]
  match ConcreteNTTGoldCache.publish logSize snapshot.tables with
  | .assertionFailure => .assertionFailure
  | .indexFailure => .indexFailure
  | .published proposal =>
    if snapshot.version = machine.version then
      .committed {machine with version := machine.version+1, current := {machine.current with tables := proposal}}
    else .retry proposal

structure Valid (machine : Machine) : Prop where
  cache : ConcreteNTTGoldCache.Valid machine.current
  captured : ∀ snapshot ∈ machine.snapshots.toList,
    ConcreteNTTGoldCache.ValidTables snapshot.tables ∧ snapshot.version ≤ machine.version ∧
    (snapshot.version = machine.version → snapshot.tables = machine.current.tables) ∧
    ∃ added, machine.current.tables = snapshot.tables++added

theorem empty_valid : Valid ({} : Machine) :=
  ⟨ConcreteNTTGoldCache.empty_valid,by simp⟩

theorem capture_valid (machine : Machine) (valid : Valid machine) : Valid (capture machine) := by
  refine ⟨valid.cache,?_⟩
  intro snapshot member
  have cases : snapshot ∈ machine.snapshots.toList ∨ snapshot = ⟨machine.version,machine.current.tables⟩ := by
    simpa only [capture,Array.toList_push,List.mem_append,List.mem_singleton] using member
  rcases cases with old | rfl
  · exact valid.captured snapshot old
  · exact ⟨valid.cache.tables,le_rfl,fun _ => rfl,⟨[],by simp [capture]⟩⟩

theorem commit_post (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
    (valid : Valid before) (executed : attempt logSize before ticket = .committed after) :
    Valid after ∧ after.current.roots = before.current.roots ∧
      ∃ added, after.current.tables = before.current.tables++added := by
  have snapshotValid := valid.captured before.snapshots[ticket.val] (Array.getElem_mem_toList ticket.isLt)
  unfold attempt at executed
  cases published : ConcreteNTTGoldCache.publish logSize before.snapshots[ticket.val].tables with
  | assertionFailure => simp only [published] at executed; cases executed
  | indexFailure => simp only [published] at executed; cases executed
  | published proposal =>
    simp only [published] at executed
    split at executed
    · rename_i same
      cases executed
      have post := ConcreteNTTGoldCache.publication_post logSize _ proposal snapshotValid.1 published
      have currentEq : before.snapshots[ticket.val].tables = before.current.tables := snapshotValid.2.2.1 same
      have extension : ∃ added, proposal = before.current.tables++added := by simpa only [currentEq] using post.2.1
      refine ⟨⟨⟨post.1,valid.cache.roots⟩,?_⟩,rfl,extension⟩
      intro snapshot member
      have old := valid.captured snapshot member
      refine ⟨old.1,by change snapshot.version ≤ before.version+1; have bound := old.2.1; omega,?_,?_⟩
      · intro equalVersions
        have bound := old.2.1
        change snapshot.version = before.version+1 at equalVersions
        omega
      · obtain ⟨oldExtra,oldShape⟩ := old.2.2.2
        obtain ⟨newExtra,newShape⟩ := extension
        exact ⟨oldExtra++newExtra,by rw [newShape,oldShape,List.append_assoc]⟩
    · cases executed

theorem retry_origin (logSize : ℕ) (machine : Machine) (ticket : Fin machine.snapshots.size)
    (proposal : List (ℕ × Table)) (executed : attempt logSize machine ticket = .retry proposal) :
    ConcreteNTTGoldCache.publish logSize machine.snapshots[ticket.val].tables = .published proposal ∧
      machine.snapshots[ticket.val].version ≠ machine.version := by
  unfold attempt at executed
  cases published : ConcreteNTTGoldCache.publish logSize machine.snapshots[ticket.val].tables with
  | assertionFailure => simp only [published] at executed; cases executed
  | indexFailure => simp only [published] at executed; cases executed
  | published candidate =>
    simp only [published] at executed
    split at executed
    · cases executed
    · rename_i stale
      cases executed
      exact ⟨rfl,stale⟩

theorem root_body_valid (logSize : ℕ) (machine : Machine) (after : ConcreteNTTGoldCache.State)
    (root : Limb) (valid : Valid machine)
    (executed : ConcreteNTTGoldCache.getRoot logSize machine.current = .success root after) :
    Valid {machine with current := after} := by
  have post := ConcreteNTTGoldCache.getRoot_post logSize machine.current after valid.cache root executed
  refine ⟨post.1,?_⟩
  intro snapshot member
  have old := valid.captured snapshot member
  refine ⟨old.1,old.2.1,?_,?_⟩
  · intro same
    change snapshot.tables = after.tables
    rw [post.2.1]
    exact old.2.2.1 same
  · simpa only [post.2.1] using old.2.2.2

inductive RootRead where
  | success (root : Limb) (machine : Machine)
  | tableError
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

-- A root body uses its captured table view, while the mutex-protected roots
-- and any intervening table publications are retained from the current state.
def readRootSnapshot (logSize : ℕ) (machine : Machine) (ticket : Fin machine.snapshots.size) : RootRead :=
  let view : ConcreteNTTGoldCache.State := ⟨machine.snapshots[ticket.val].tables,machine.current.roots⟩
  match ConcreteNTTGoldCache.getRoot logSize view with
  | .tableError => .tableError
  | .assertionFailure => .assertionFailure
  | .indexFailure => .indexFailure
  | .success root after => .success root {machine with current := {machine.current with roots := after.roots}}

theorem root_snapshot_post (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
    (valid : Valid before) (root : Limb) (executed : readRootSnapshot logSize before ticket = .success root after) :
    Valid after ∧ after.current.tables = before.current.tables ∧ after.version = before.version ∧
      (∃ added, after.current.roots = before.current.roots++added) ∧
      ∃ table, newTable logSize = .created table ∧ root = table.root := by
  have snapshotValid := valid.captured before.snapshots[ticket.val] (Array.getElem_mem_toList ticket.isLt)
  let view : ConcreteNTTGoldCache.State := ⟨before.snapshots[ticket.val].tables,before.current.roots⟩
  have viewValid : ConcreteNTTGoldCache.Valid view := ⟨snapshotValid.1,valid.cache.roots⟩
  change (match ConcreteNTTGoldCache.getRoot logSize view with
    | .tableError => RootRead.tableError
    | .assertionFailure => RootRead.assertionFailure
    | .indexFailure => RootRead.indexFailure
    | .success result next => RootRead.success result {before with current := {before.current with roots := next.roots}}) =
      RootRead.success root after at executed
  cases read : ConcreteNTTGoldCache.getRoot logSize view with
  | tableError => simp only [read] at executed; cases executed
  | assertionFailure => simp only [read] at executed; cases executed
  | indexFailure => simp only [read] at executed; cases executed
  | success result next =>
    simp only [read] at executed
    cases executed
    have post := ConcreteNTTGoldCache.getRoot_post logSize view next viewValid root read
    exact ⟨⟨⟨valid.cache.tables,post.1.roots⟩,valid.captured⟩,rfl,rfl,post.2.2.1,post.2.2.2⟩

inductive Reachable : Machine → Prop where
  | empty : Reachable {}
  | capture {machine : Machine} (prior : Reachable machine) : Reachable (capture machine)
  | commit {before after : Machine} (logSize : ℕ) (ticket : Fin before.snapshots.size)
      (prior : Reachable before) (executed : attempt logSize before ticket = .committed after) : Reachable after
  | rootSnapshot {before after : Machine} (logSize : ℕ) (ticket : Fin before.snapshots.size) (root : Limb)
      (prior : Reachable before) (executed : readRootSnapshot logSize before ticket = .success root after) : Reachable after

theorem reachable_valid (machine : Machine) (reachable : Reachable machine) : Valid machine := by
  induction reachable with
  | empty => exact empty_valid
  | capture prior ih => exact capture_valid _ ih
  | commit logSize ticket prior executed ih => exact (commit_post logSize _ _ ticket ih executed).1
  | rootSnapshot logSize ticket root prior executed ih => exact (root_snapshot_post logSize _ _ ticket ih root executed).1

theorem retained_table_origin (machine : Machine) (reachable : Reachable machine) (logSize : ℕ) (table : Table)
    (found : lookup machine.current.tables logSize = some table) : newTable logSize = .created table :=
  (reachable_valid machine reachable).cache.tables logSize table (ConcreteNTTCacheLookup.member _ _ _ found)

theorem retained_root_origin (machine : Machine) (reachable : Reachable machine) (logSize : ℕ) (root : Limb)
    (found : lookup machine.current.roots logSize = some root) :
    ∃ table, newTable logSize = .created table ∧ root = table.root :=
  (reachable_valid machine reachable).cache.roots logSize root (ConcreteNTTCacheLookup.member _ _ _ found)

theorem read_root_origin (machine : Machine) (reachable : Reachable machine) (logSize : ℕ)
    (root : Limb) (after : ConcreteNTTGoldCache.State)
    (executed : ConcreteNTTGoldCache.getRoot logSize machine.current = .success root after) :
    ∃ table, newTable logSize = .created table ∧ root = table.root :=
  (ConcreteNTTGoldCache.getRoot_post logSize _ _ (reachable_valid machine reachable).cache root executed).2.2.2

theorem read_root_primitive (machine : Machine) (reachable : Reachable machine) (logSize : ℕ)
    (root : Limb) (after : ConcreteNTTGoldCache.State)
    (executed : ConcreteNTTGoldCache.getRoot logSize machine.current = .success root after) :
    IsPrimitiveRoot (root.val : NativeFields.Goldilocks) (2^(logSize+1)) := by
  obtain ⟨table,built,same⟩ := read_root_origin machine reachable logSize root after executed
  rw [same]
  exact ConcreteNTTGoldTable.root_primitive logSize table built

theorem read_root_canonical (machine : Machine) (reachable : Reachable machine) (logSize : ℕ)
    (root : Limb) (after : ConcreteNTTGoldCache.State)
    (executed : ConcreteNTTGoldCache.getRoot logSize machine.current = .success root after) :
    root.val < NativeFields.goldilocksModulus := by
  obtain ⟨table,built,same⟩ := read_root_origin machine reachable logSize root after executed
  rw [same]
  exact ConcreteNTTGoldTable.root_canonical logSize table built

theorem retained_caches_agree (machine : Machine) (reachable : Reachable machine) (logSize : ℕ)
    (table : Table) (root : Limb) (tableFound : lookup machine.current.tables logSize = some table)
    (rootFound : lookup machine.current.roots logSize = some root) : root = table.root := by
  have built := retained_table_origin machine reachable logSize table tableFound
  obtain ⟨earlier,created,same⟩ := retained_root_origin machine reachable logSize root rootFound
  have equal : table = earlier := ConcreteNTTGoldTable.Outcome.created.inj (built.symm.trans created)
  simpa only [← equal] using same

theorem snapshot_root_origin (machine after : Machine) (reachable : Reachable machine)
    (logSize : ℕ) (ticket : Fin machine.snapshots.size) (root : Limb)
    (executed : readRootSnapshot logSize machine ticket = .success root after) :
    ∃ table, newTable logSize = .created table ∧ root = table.root :=
  (root_snapshot_post logSize machine after ticket (reachable_valid machine reachable) root executed).2.2.2.2

theorem snapshot_root_primitive (machine after : Machine) (reachable : Reachable machine)
    (logSize : ℕ) (ticket : Fin machine.snapshots.size) (root : Limb)
    (executed : readRootSnapshot logSize machine ticket = .success root after) :
    IsPrimitiveRoot (root.val : NativeFields.Goldilocks) (2^(logSize+1)) := by
  obtain ⟨table,built,same⟩ := snapshot_root_origin machine after reachable logSize ticket root executed
  rw [same]
  exact ConcreteNTTGoldTable.root_primitive logSize table built

theorem snapshot_root_canonical (machine after : Machine) (reachable : Reachable machine)
    (logSize : ℕ) (ticket : Fin machine.snapshots.size) (root : Limb)
    (executed : readRootSnapshot logSize machine ticket = .success root after) :
    root.val < NativeFields.goldilocksModulus := by
  obtain ⟨table,built,same⟩ := snapshot_root_origin machine after reachable logSize ticket root executed
  rw [same]
  exact ConcreteNTTGoldTable.root_canonical logSize table built

theorem committed_read_preserved (logSize : ℕ) (before after : Machine) (ticket : Fin before.snapshots.size)
    (reachable : Reachable before) (executed : attempt logSize before ticket = .committed after)
    (key : ℕ) (table : Table) (found : lookup before.current.tables key = some table) :
    lookup after.current.tables key = some table := by
  obtain ⟨_,_,added,shape⟩ := commit_post logSize before after ticket (reachable_valid before reachable) executed
  rw [shape]
  exact ConcreteNTTCacheLookup.append_preserves _ _ key table found

end FormalProof4FHE.HasteBoots.ConcreteNTTGoldCacheRCU
