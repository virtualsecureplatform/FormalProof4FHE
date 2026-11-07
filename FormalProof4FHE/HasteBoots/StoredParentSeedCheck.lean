module
public import FormalProof4FHE.HasteBoots.StoredShakeByteCache
@[expose] public section

/-! Concrete partial-exposure parent-seed compatibility. Unknown coordinates
remain wildcards; one disagreeing exposed coordinate rejects. All compatible
parents can therefore be retained. No functional seed or cache callback is
executed. Parsing parents/child quotes and ledger composition remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredParentSeedCheck
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)
open StoredShakeByteCache (Cache lookup lookupBound view)

def check (cache : Cache) (input : Input) (seed : Vector Byte 64) : List (Fin 64) → Run Bool
  | [] => ⟨true,1⟩
  | position::rest =>
    let found := lookup cache input position.val
    match found.value with
    | none =>
      let next := check cache input seed rest
      ⟨next.value,found.cost+next.cost+4⟩
    | some value =>
      if value = seed.get position then
        let next := check cache input seed rest
        ⟨next.value,found.cost+next.cost+4⟩
      else ⟨false,found.cost+4⟩

theorem check_value (cache : Cache) (input : Input) (seed : Vector Byte 64) (positions : List (Fin 64)) :
    (check cache input seed positions).value = positions.all (fun position =>
      match view cache (input,position.val) with | none => true | some value => decide (value = seed.get position)) := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
    simp only [check,StoredShakeByteCache.lookup_value,List.all_cons]
    cases found : view cache (input,position.val) with
    | none => simp only [ih,Bool.true_and]
    | some value => by_cases same : value = seed.get position <;>
        simp only [same,ite_true,ite_false,ih,decide_true,decide_false,Bool.true_and,Bool.false_and]

theorem check_cost (cache : Cache) (input : Input) (seed : Vector Byte 64) (positions : List (Fin 64)) :
    (check cache input seed positions).cost ≤ positions.length*(lookupBound input.length cache.length+4)+1 := by
  induction positions with
  | nil => simp [check]
  | cons position rest ih =>
    have read := StoredShakeByteCache.lookup_cost cache input position.val
    simp only [check,List.length_cons]
    split
    · dsimp only; nlinarith
    · split <;> dsimp only <;> nlinarith

def compatible (cache : Cache) (input : Input) (seed : Vector Byte 64) : Run Bool :=
  let result := check cache input seed (List.finRange 64)
  ⟨result.value,result.cost+130⟩

theorem compatible_value (cache : Cache) (input : Input) (seed : Vector Byte 64) :
    (compatible cache input seed).value = ExecutableParentInputView.compatible (view cache) input seed.get :=
  check_value _ _ _ _

theorem compatible_iff (cache : Cache) (input : Input) (seed : Vector Byte 64) :
    (compatible cache input seed).value = true ↔ NativeParentInputView.compatible (view cache) input seed.get := by
  rw [compatible_value,ExecutableParentInputView.compatible_iff]

theorem compatible_cost (cache : Cache) (input : Input) (seed : Vector Byte 64) :
    (compatible cache input seed).cost ≤ 64*((6*input.length+14)*cache.length+5)+131 := by
  have bound := check_cost cache input seed (List.finRange 64)
  simp only [List.length_finRange,lookupBound] at bound
  simp only [compatible]
  omega

/-- Visit every candidate, preserving original order and duplicate records. -/
def parents (cache : Cache) (seed : Vector Byte 64) : List NativeParentLedger.Parent → Run (List NativeParentLedger.Parent)
  | [] => ⟨[],1⟩
  | head::tail =>
    let found := compatible cache head.input seed
    let rest := parents cache seed tail
    ⟨if found.value then head::rest.value else rest.value,found.cost+rest.cost+3⟩

theorem parents_value (cache : Cache) (seed : Vector Byte 64) (candidates : List NativeParentLedger.Parent) :
    (parents cache seed candidates).value = candidates.filter (fun parent =>
      ExecutableParentInputView.compatible (view cache) parent.input seed.get) := by
  induction candidates with
  | nil => rfl
  | cons head tail ih => simp only [parents,compatible_value,List.filter_cons,ih]

def parentInputBytes : List NativeParentLedger.Parent → ℕ
  | [] => 0
  | head::tail => head.input.length+parentInputBytes tail

theorem parents_cost (cache : Cache) (seed : Vector Byte 64) (candidates : List NativeParentLedger.Parent) :
    (parents cache seed candidates).cost ≤
      64*(6*parentInputBytes candidates+14*candidates.length)*cache.length+454*candidates.length+1 := by
  induction candidates with
  | nil => simp [parents,parentInputBytes]
  | cons head tail ih =>
    have found := compatible_cost cache head.input seed
    simp only [parents,parentInputBytes,List.length_cons]
    nlinarith

theorem parents_eq_active (cache : Cache) (seed : Vector Byte 64) (state : NativeParentLedger.State)
    (child : Input) (quoted : NativeChildSeedView.quote child = some seed.get) :
    (parents cache seed state.parents).value = ExecutableParentLedger.active state (view cache) child := by
  simp only [parents_value,ExecutableParentLedger.active,quoted]
end FormalProof4FHE.HasteBoots.StoredParentSeedCheck
