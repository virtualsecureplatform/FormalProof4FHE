module
public import FormalProof4FHE.HasteBoots.ConcreteNTTCacheLookup
@[expose] public section

/-! Word-formula bodies of the original Goldilocks cache operations. First
matches and append order are preserved. Table publication uses the literal
inner RCU callback and its unwrap; root misses may discard a temporary Plan.
These bodies do not assume a successful builder or primitive-root certificate.
ArcSwap/Mutex instruction, publication/concurrency and physical refinement
remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTGoldCache
open ConcreteNTTLimbArithmetic (Limb)
open ConcreteNTTGoldTable (Table newTable)
open ConcreteNTTCacheLookup (lookup)

structure State where
  tables : List (ℕ × Table) := []
  roots : List (ℕ × Limb) := []
  deriving DecidableEq, Repr

inductive Publication where
  | published (tables : List (ℕ × Table))
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

-- The original RCU callback clones the current vector, rechecks and appends.
def publish (logSize : ℕ) (tables : List (ℕ × Table)) : Publication :=
  match lookup tables logSize with
  | some _ => .published tables
  | none =>
    match newTable logSize with
    | .created table => .published (tables++[(logSize,table)])
    | .tableError => .assertionFailure
    | .assertionFailure => .assertionFailure
    | .indexFailure => .indexFailure

inductive Outcome (α : Type) where
  | success (value : α) (state : State)
  | tableError
  | assertionFailure
  | indexFailure
  deriving DecidableEq, Repr

def initTable (logSize : ℕ) (state : State) : Outcome Unit :=
  match lookup state.tables logSize with
  | some _ => .success () state
  | none =>
    match publish logSize state.tables with
    | .published tables => .success () {state with tables := tables}
    | .assertionFailure => .assertionFailure
    | .indexFailure => .indexFailure

def getTable (logSize : ℕ) (state : State) : Outcome Table :=
  match lookup state.tables logSize with
  | some table => .success table state
  | none =>
    match initTable logSize state with
    | .tableError => .tableError
    | .assertionFailure => .assertionFailure
    | .indexFailure => .indexFailure
    | .success _ after =>
      match lookup after.tables logSize with
      | none => .assertionFailure
      | some table => .success table after

def getRoot (logSize : ℕ) (state : State) : Outcome Limb :=
  match lookup state.roots logSize with
  | some root => .success root state
  | none =>
    match lookup state.tables logSize with
    | some table => .success table.root {state with roots := state.roots++[(logSize,table.root)]}
    | none =>
      match newTable logSize with
      | .created table => .success table.root {state with roots := state.roots++[(logSize,table.root)]}
      | .tableError => .tableError
      | .assertionFailure => .assertionFailure
      | .indexFailure => .indexFailure

theorem getTable_hit (logSize : ℕ) (state : State) (table : Table)
    (found : lookup state.tables logSize = some table) : getTable logSize state = .success table state := by
  simp only [getTable,found]

theorem getRoot_hit (logSize : ℕ) (state : State) (root : Limb)
    (found : lookup state.roots logSize = some root) : getRoot logSize state = .success root state := by
  simp only [getRoot,found]

def ValidTables (tables : List (ℕ × Table)) : Prop :=
  ∀ key table, (key,table) ∈ tables → newTable key = .created table

def ValidRoots (roots : List (ℕ × Limb)) : Prop :=
  ∀ key root, (key,root) ∈ roots → ∃ table, newTable key = .created table ∧ root = table.root

structure Valid (state : State) : Prop where
  tables : ValidTables state.tables
  roots : ValidRoots state.roots

theorem empty_valid : Valid ({} : State) := ⟨by simp [ValidTables],by simp [ValidRoots]⟩

theorem tables_append (tables : List (ℕ × Table)) (valid : ValidTables tables)
    (key : ℕ) (table : Table) (built : newTable key = .created table) :
    ValidTables (tables++[(key,table)]) := by
  intro k t member
  rcases List.mem_append.mp member with old | added
  · exact valid k t old
  · have same := List.mem_singleton.mp added
    cases same
    exact built

theorem roots_append (roots : List (ℕ × Limb)) (valid : ValidRoots roots)
    (key : ℕ) (table : Table) (built : newTable key = .created table) :
    ValidRoots (roots++[(key,table.root)]) := by
  intro k root member
  rcases List.mem_append.mp member with old | added
  · exact valid k root old
  · have same := List.mem_singleton.mp added
    cases same
    exact ⟨table,built,rfl⟩

theorem publication_post (logSize : ℕ) (before after : List (ℕ × Table)) (valid : ValidTables before)
    (executed : publish logSize before = .published after) :
    ValidTables after ∧ (∃ added, after = before++added) ∧
      ∃ table, lookup after logSize = some table ∧ newTable logSize = .created table := by
  unfold publish at executed
  cases found : lookup before logSize with
  | some table =>
    simp only [found] at executed
    cases executed
    exact ⟨valid,⟨[],by simp⟩,table,found,valid logSize table (ConcreteNTTCacheLookup.member before logSize table found)⟩
  | none =>
    simp only [found] at executed
    cases built : newTable logSize with
    | created table =>
      simp only [built] at executed
      cases executed
      exact ⟨tables_append before valid logSize table built,⟨_,rfl⟩,table,
        ConcreteNTTCacheLookup.append_new before logSize table found,rfl⟩
    | tableError => simp only [built] at executed; cases executed
    | assertionFailure => simp only [built] at executed; cases executed
    | indexFailure => simp only [built] at executed; cases executed

theorem initialize_post (logSize : ℕ) (before after : State) (valid : Valid before)
    (executed : initTable logSize before = .success () after) :
    Valid after ∧ after.roots = before.roots ∧ (∃ added, after.tables = before.tables++added) ∧
      ∃ table, lookup after.tables logSize = some table ∧ newTable logSize = .created table := by
  unfold initTable at executed
  cases found : lookup before.tables logSize with
  | some table =>
    simp only [found] at executed
    cases executed
    exact ⟨valid,rfl,⟨[],by simp⟩,table,found,valid.tables logSize table (ConcreteNTTCacheLookup.member _ _ _ found)⟩
  | none =>
    simp only [found] at executed
    cases published : publish logSize before.tables with
    | published tables =>
      simp only [published] at executed
      cases executed
      have post := publication_post logSize before.tables tables valid.tables published
      exact ⟨⟨post.1,valid.roots⟩,rfl,post.2.1,post.2.2⟩
    | assertionFailure => simp only [published] at executed; cases executed
    | indexFailure => simp only [published] at executed; cases executed

theorem getTable_post (logSize : ℕ) (before after : State) (valid : Valid before) (table : Table)
    (executed : getTable logSize before = .success table after) :
    Valid after ∧ newTable logSize = .created table := by
  unfold getTable at executed
  cases found : lookup before.tables logSize with
  | some stored =>
    simp only [found] at executed
    cases executed
    exact ⟨valid,valid.tables logSize table (ConcreteNTTCacheLookup.member _ _ _ found)⟩
  | none =>
    simp only [found] at executed
    cases initialized : initTable logSize before with
    | tableError => simp only [initialized] at executed; cases executed
    | assertionFailure => simp only [initialized] at executed; cases executed
    | indexFailure => simp only [initialized] at executed; cases executed
    | success token next =>
      cases token
      have post := initialize_post logSize before next valid initialized
      simp only [initialized] at executed
      cases readBack : lookup next.tables logSize with
      | none => simp only [readBack] at executed; cases executed
      | some stored =>
        simp only [readBack] at executed
        cases executed
        exact ⟨post.1,post.1.tables logSize table (ConcreteNTTCacheLookup.member _ _ _ readBack)⟩

theorem getRoot_post (logSize : ℕ) (before after : State) (valid : Valid before) (root : Limb)
    (executed : getRoot logSize before = .success root after) :
    Valid after ∧ after.tables = before.tables ∧ (∃ added, after.roots = before.roots++added) ∧
      ∃ table, newTable logSize = .created table ∧ root = table.root := by
  unfold getRoot at executed
  cases cached : lookup before.roots logSize with
  | some stored =>
    simp only [cached] at executed
    cases executed
    exact ⟨valid,rfl,⟨[],by simp⟩,valid.roots logSize root (ConcreteNTTCacheLookup.member _ _ _ cached)⟩
  | none =>
    simp only [cached] at executed
    cases retained : lookup before.tables logSize with
    | some table =>
      simp only [retained] at executed
      cases executed
      have built := valid.tables logSize table (ConcreteNTTCacheLookup.member _ _ _ retained)
      exact ⟨⟨valid.tables,roots_append before.roots valid.roots logSize table built⟩,rfl,⟨_,rfl⟩,table,built,rfl⟩
    | none =>
      simp only [retained] at executed
      cases built : newTable logSize with
      | created table =>
        simp only [built] at executed
        cases executed
        exact ⟨⟨valid.tables,roots_append before.roots valid.roots logSize table built⟩,rfl,⟨_,rfl⟩,table,rfl,rfl⟩
      | tableError => simp only [built] at executed; cases executed
      | assertionFailure => simp only [built] at executed; cases executed
      | indexFailure => simp only [built] at executed; cases executed

end FormalProof4FHE.HasteBoots.ConcreteNTTGoldCache
