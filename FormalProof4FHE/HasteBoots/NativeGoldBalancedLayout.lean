module
public import FormalProof4FHE.HasteBoots.NativeGoldParameterInitialization
@[expose] public section

/-! Goldilocks balanced_block_rs layout search. Checked usize operations reject
candidates in source order. Scores use unsigned 128-bit arithmetic, represented
by reduction modulo 2^128; they tune layout and supply no soundness budget.
This value model does not establish Rust/heap or physical-work refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBalancedLayout
open NativeUsizeMessage (Usize)

structure Request where
  numVariables : Usize
  width : Usize
  queries : Usize
  blowup : Usize
  deriving DecidableEq

structure Candidate where
  left : ℕ
  columns : ℕ
  blocks : ℕ
  rows : ℕ
  score : ℕ
  deriving DecidableEq

inductive Error where
  | dimensions | tableOverflow | unsupportedLayout
  deriving DecidableEq

def candidate (request : Request) (left : ℕ) : Option Candidate :=
  if left ≤ request.numVariables.val then
    let columns := 2^(request.numVariables.val-left)
    let padded := NativeGoldBlockCode.paddedBlocks columns request.width.val
    if padded < 2^64 then
      if padded*request.blowup.val < 2^64 then
        let blocks := max (padded*request.blowup.val) 32
        if (NativeFields.goldilocksModulus-1) % (2*blocks) = 0 then
          let rows := 2^left*request.width.val
          if rows < 2^64 then
            if rows*blocks < 2^64 ∧ rows*blocks*request.width.val < 2^64 then
              let unique := min request.queries.val blocks
              let fields := 2*request.width.val*columns+unique*rows*request.width.val
              some ⟨left,columns,blocks,rows,
                (fields*9+unique*((blocks.size-1)+1)*32) % 2^128⟩
            else none
          else none
        else none
      else none
    else none
  else none

/-- Strict comparison preserves an earlier candidate on every tie. -/
def prefer (prior : Option Candidate) (next : Candidate) : Option Candidate :=
  match prior with
  | none => some next
  | some earlier => if next.score < earlier.score then some next else some earlier

def scan : Option Candidate → List Candidate → Option Candidate
  | prior,[] => prior
  | prior,next::rest => scan (prefer prior next) rest

def candidates (request : Request) : List Candidate :=
  (List.range (request.numVariables.val+1)).filterMap (candidate request)

def select (request : Request) : Except Error Candidate :=
  if request.width.val ≠ 0 ∧ request.queries.val ≠ 0 ∧ request.numVariables.val < 64 ∧
      2 ≤ request.blowup.val ∧ request.blowup.val = 2^(NativeGoldBlockCode.nextLog request.blowup.val) then
    if 2^request.numVariables.val*request.width.val < 2^64 then
      match scan none (candidates request) with
      | none => .error .unsupportedLayout
      | some selected => .ok selected
    else .error .tableOverflow
  else .error .dimensions

/-- The source checks keep every score intermediate below u128::MAX. -/
theorem score_arithmetic_fits (width columns rows blocks queries : ℕ)
    (table : width*columns < 2^64) (encoded : rows*blocks*width < 2^64)
    (count : blocks < 2^64) :
    (2*width*columns+min queries blocks*rows*width)*9+
      min queries blocks*((blocks.size-1)+1)*32 < 2^128 := by
  have uniqueBound : min queries blocks < 2^64 := lt_of_le_of_lt (Nat.min_le_right _ _) count
  have responseBound : min queries blocks*rows*width < 2^64 := by
    have smaller := Nat.mul_le_mul_right width (Nat.mul_le_mul_right rows (Nat.min_le_right queries blocks))
    nlinarith
  have sizeBound : blocks.size ≤ 64 := Nat.size_le.mpr count
  have heightBound : (blocks.size-1)+1 ≤ 65 := by omega
  have pathBound := Nat.mul_le_mul (Nat.le_of_lt uniqueBound) heightBound
  norm_num at table responseBound pathBound ⊢
  nlinarith

theorem candidate_shape (request : Request) (left : ℕ) (selected : Candidate)
    (executed : candidate request left = some selected) :
    selected.left = left ∧ left ≤ request.numVariables.val ∧
    selected.columns = 2^(request.numVariables.val-left) ∧
    selected.blocks = NativeGoldBlockCode.domainBlocks selected.columns request.width.val request.blowup.val ∧
    selected.rows = 2^left*request.width.val ∧
    selected.rows*selected.blocks*request.width.val < 2^64 ∧
    (NativeFields.goldilocksModulus-1) % (2*selected.blocks) = 0 := by
  unfold candidate at executed
  split at executed
  · rename_i bound
    dsimp only at executed
    split at executed
    · split at executed
      · split at executed
        · rename_i compatible
          split at executed
          · split at executed
            · rename_i encoded
              cases executed
              exact ⟨rfl,bound,rfl,rfl,rfl,encoded.2,compatible⟩
            · cases executed
          · cases executed
        · cases executed
      · cases executed
    · cases executed
  · cases executed

theorem candidate_no_score_wrap (request : Request) (left : ℕ) (selected : Candidate)
    (table : 2^request.numVariables.val*request.width.val < 2^64)
    (executed : candidate request left = some selected) :
    selected.score = (2*request.width.val*selected.columns+
      min request.queries.val selected.blocks*selected.rows*request.width.val)*9+
      min request.queries.val selected.blocks*((selected.blocks.size-1)+1)*32 := by
  unfold candidate at executed
  split at executed
  · dsimp only at executed
    split at executed
    · split at executed
      · rename_i domainFits
        split at executed
        · split at executed
          · split at executed
            · rename_i encoded
              cases executed
              apply Nat.mod_eq_of_lt
              apply score_arithmetic_fits
              · have smaller := Nat.mul_le_mul_right request.width.val
                  (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.sub_le request.numVariables.val left))
                nlinarith
              · exact encoded.2
              · exact max_lt domainFits (by decide)
            · cases executed
          · cases executed
        · cases executed
      · cases executed
    · cases executed
  · cases executed

theorem prefer_tie (earlier next : Candidate) (same : next.score = earlier.score) :
    prefer (some earlier) next = some earlier := by
  simp [prefer,same]

theorem scan_origin (prior : Option Candidate) (rest : List Candidate) (selected : Candidate)
    (executed : scan prior rest = some selected) : selected ∈ prior.toList ++ rest := by
  induction rest generalizing prior with
  | nil => cases prior <;> simp_all [scan]
  | cons next rest ih =>
    have member := ih (prefer prior next) executed
    cases prior with
    | none => simpa [prefer] using member
    | some earlier =>
      simp only [prefer] at member
      split at member
      · simp only [Option.toList_some,List.singleton_append,List.mem_cons] at member ⊢
        exact Or.inr member
      · simp only [Option.toList_some,List.singleton_append,List.mem_cons] at member ⊢
        rcases member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr (Or.inr member)

theorem scan_minimum (prior : Option Candidate) (rest : List Candidate) (selected : Candidate)
    (executed : scan prior rest = some selected) :
    ∀ other ∈ prior.toList ++ rest, selected.score ≤ other.score := by
  induction rest generalizing prior with
  | nil => cases prior <;> simp_all [scan]
  | cons next rest ih =>
    have minimum := ih (prefer prior next) executed
    cases prior with
    | none => simpa [prefer] using minimum
    | some earlier =>
      simp only [prefer] at minimum
      split at minimum
      · rename_i better
        simp only [Option.toList_some,List.singleton_append,List.mem_cons] at minimum ⊢
        intro other member
        rcases member with rfl | rfl | member
        · exact (minimum _ (Or.inl rfl)).trans (Nat.le_of_lt better)
        · exact minimum _ (Or.inl rfl)
        · exact minimum other (Or.inr member)
      · rename_i noBetter
        simp only [Option.toList_some,List.singleton_append,List.mem_cons] at minimum ⊢
        intro other member
        rcases member with rfl | rfl | member
        · exact minimum _ (Or.inl rfl)
        · exact (minimum _ (Or.inl rfl)).trans (Nat.le_of_not_gt noBetter)
        · exact minimum other (Or.inr member)

theorem selected_search (request : Request) (selected : Candidate)
    (executed : select request = .ok selected) :
    scan none (candidates request) = some selected := by
  unfold select at executed
  split at executed
  · split at executed
    · split at executed
      · cases executed
      · cases executed; assumption
    · cases executed
  · cases executed

theorem selected_origin (request : Request) (selected : Candidate)
    (executed : select request = .ok selected) :
    ∃ left, left ≤ request.numVariables.val ∧ candidate request left = some selected := by
  have member := scan_origin none (candidates request) selected (selected_search request selected executed)
  simp only [Option.toList_none,List.nil_append,candidates,List.mem_filterMap,List.mem_range] at member
  obtain ⟨left,bound,built⟩ := member
  exact ⟨left,by omega,built⟩

theorem selected_minimum (request : Request) (selected : Candidate)
    (executed : select request = .ok selected) (left : ℕ) (bound : left ≤ request.numVariables.val)
    (other : Candidate) (built : candidate request left = some other) : selected.score ≤ other.score := by
  apply scan_minimum none (candidates request) selected (selected_search request selected executed) other
  simp only [Option.toList_none,List.nil_append,candidates,List.mem_filterMap,List.mem_range]
  exact ⟨left,by omega,built⟩

theorem selected_shape (request : Request) (selected : Candidate)
    (executed : select request = .ok selected) :
    selected.left ≤ request.numVariables.val ∧
    selected.columns = 2^(request.numVariables.val-selected.left) ∧
    selected.blocks = NativeGoldBlockCode.domainBlocks selected.columns request.width.val request.blowup.val ∧
    selected.rows*selected.blocks*request.width.val < 2^64 := by
  obtain ⟨left,_,built⟩ := selected_origin request selected executed
  obtain ⟨same,bound,columns,blocks,_,encoded,_⟩ := candidate_shape request left selected built
  rw [← same] at bound columns
  exact ⟨bound,columns,blocks,encoded⟩

theorem scan_preserves_minimum (earlier : Candidate) (rest : List Candidate)
    (minimal : ∀ other ∈ rest, earlier.score ≤ other.score) :
    scan (some earlier) rest = some earlier := by
  induction rest with
  | nil => rfl
  | cons next rest ih =>
    have notBetter : ¬next.score < earlier.score := Nat.not_lt.mpr (minimal next (by simp))
    simp only [scan,prefer,ite_eq_right notBetter]
    exact ih (fun other member => minimal other (by simp [member]))

theorem selected_dimensions (request : Request) (selected : Candidate)
    (executed : select request = .ok selected) :
    request.numVariables.val < 64 ∧ 2^request.numVariables.val*request.width.val < 2^64 := by
  unfold select at executed
  split at executed
  · rename_i valid
    split at executed
    · rename_i fits
      exact ⟨valid.2.2.1,fits⟩
    · cases executed
  · cases executed

theorem scan_append (prior : Option Candidate) (before after : List Candidate) :
    scan prior (before++after) = scan (scan prior before) after := by
  induction before generalizing prior with
  | nil => rfl
  | cons next rest ih => exact ih (prefer prior next)

/-- The first global minimum survives all subsequent ties. -/
theorem scan_first_minimum (before after : List Candidate) (chosen : Candidate)
    (earlier : ∀ other ∈ before, chosen.score < other.score)
    (later : ∀ other ∈ after, chosen.score ≤ other.score) :
    scan none (before++chosen::after) = some chosen := by
  rw [scan_append]
  have picked : prefer (scan none before) chosen = some chosen := by
    cases observed : scan none before with
    | none => rfl
    | some previous =>
      have member := scan_origin none before previous observed
      simp only [Option.toList_none,List.nil_append] at member
      simp only [prefer,ite_eq_left (earlier previous member)]
  change scan (prefer (scan none before) chosen) after = some chosen
  rw [picked]
  exact scan_preserves_minimum chosen after later

theorem selected_no_score_wrap (request : Request) (selected : Candidate)
    (executed : select request = .ok selected) :
    selected.score = (2*request.width.val*selected.columns+
      min request.queries.val selected.blocks*selected.rows*request.width.val)*9+
      min request.queries.val selected.blocks*((selected.blocks.size-1)+1)*32 := by
  obtain ⟨left,_,built⟩ := selected_origin request selected executed
  exact candidate_no_score_wrap request left selected (selected_dimensions request selected executed).2 built

end FormalProof4FHE.HasteBoots.NativeGoldBalancedLayout
