module
public import FormalProof4FHE.HasteBoots.TranscriptFrameStreamCost
public import FormalProof4FHE.HasteBoots.PublicSourceByteInputs
public import FormalProof4FHE.HasteBoots.StoredParentSeedCheck
public import FormalProof4FHE.HasteBoots.StoredShakeHistory
@[expose] public section

/-! Stored child-seed quotes from the original fixed frame slot. The complete
frame stream, slot traversal, label comparison and exact 64-byte seed read are
charged. No functional digest/cache callback executes. Parent/helper semantic
parsing and complete source-ledger replay remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.StoredChildSeedQuote
open InputIndexedOracle (Input Byte)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)

theorem vectorBytes {n : ℕ} (label : Fin n → Byte) :
    (Vector.ofFn label).toList = List.ofFn label := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp only [Vector.getElem_toList,Vector.getElem_ofFn,List.getElem_ofFn]

theorem digest_as_native (input : Input) :
    (PublicSourceByteInputs.digest input).value.map Vector.get = NativeExactCodec.read NativeByteCodec.digest input := by
  cases ours : (PublicSourceByteInputs.digest input).value with
  | none =>
    simp only [Option.map_none]
    cases native : NativeExactCodec.read NativeByteCodec.digest input with
    | none => rfl
    | some label =>
      have encoded := NativeExactCodec.read_sound NativeByteCodec.digest input label native
      have bytes : (Vector.ofFn label).toList = input := by
        change List.ofFn label = input at encoded
        exact (vectorBytes label).trans encoded
      have parsed := PublicSourceByteInputs.digest_encode (Vector.ofFn label)
      rw [bytes,ours] at parsed
      cases parsed
  | some value =>
    simp only [Option.map_some]
    have bytes := PublicSourceByteInputs.digest_sound input value ours
    have encoded : NativeByteCodec.digest.encode value.get = input := by
      simpa only [NativeByteCodec.digest_encode,FixedByteReadCost.ofFn_get] using bytes.symm
    exact ((NativeExactCodec.read_iff NativeByteCodec.digest input value.get).mpr encoded).symm

def frameAt : List Frame → ℕ → Run (Option Frame)
  | [],_ => ⟨none,1⟩
  | head::_,0 => ⟨some head,2⟩
  | _::tail,index+1 => let rest  := frameAt tail index; ⟨rest.value,rest.cost+2⟩

theorem at_value (frames : List Frame) (index : ℕ) : (frameAt frames index).value = frames[index]? := by
  induction frames generalizing index with
  | nil => rfl
  | cons head tail ih => cases index <;> simp only [frameAt,ih,List.getElem?_cons_zero,List.getElem?_cons_succ]

theorem at_cost (frames : List Frame) (index : ℕ) : (frameAt frames index).cost ≤ 2*index+2 := by
  induction frames generalizing index with
  | nil => simp only [frameAt]; omega
  | cons head tail ih => cases index with
    | zero => simp [frameAt]
    | succ index => have bound := ih index; simp only [frameAt]; omega

def seedLabel : Input := NativeTranscript.utf8 "parent seed"

def frameSeed (frame : Frame) : Run (Option (Vector Byte 64)) :=
  if frame.kind = 1 then
    let same := BytePrefixMatchCost.equal seedLabel frame.label
    if same.value then
      let decoded := PublicSourceByteInputs.digest frame.message
      ⟨decoded.value,same.cost+decoded.cost+5⟩
    else ⟨none,same.cost+3⟩
  else ⟨none,2⟩

theorem frameSeed_value (frame : Frame) :
    (frameSeed frame).value.map Vector.get = NativeChildSeedView.frameSeed frame := by
  by_cases kind : frame.kind = 1
  · by_cases label : frame.label = seedLabel
    · dsimp only [seedLabel] at label
      simp [frameSeed,NativeChildSeedView.frameSeed,kind,label,BytePrefixMatchCost.equal_value,
        seedLabel,digest_as_native]
    · dsimp only [seedLabel] at label
      simp [frameSeed,NativeChildSeedView.frameSeed,kind,label,BytePrefixMatchCost.equal_value,
        seedLabel,eq_comm]
  · simp [frameSeed,NativeChildSeedView.frameSeed,kind]

theorem frameSeed_cost (frame : Frame) : (frameSeed frame).cost ≤ 6*seedLabel.length+469 := by
  have compared := BytePrefixMatchCost.equal_cost seedLabel frame.label
  have size := Nat.min_le_left seedLabel.length frame.label.length
  have parsed := PublicSourceByteInputs.digest_cost frame.message
  simp only [frameSeed]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

def quote (input : Input) : Run (Option (Vector Byte 64)) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨none,frames.cost+2⟩
  | some values =>
    let selected := frameAt values 5
    match selected.value with
    | none => ⟨none,frames.cost+selected.cost+3⟩
    | some frame =>
      let result := frameSeed frame
      ⟨result.value,frames.cost+selected.cost+result.cost+5⟩

theorem quote_value (input : Input) :
    (quote input).value.map Vector.get = NativeChildSeedView.quote input := by
  simp only [quote,TranscriptFrameStreamCost.decodeAll_value,NativeChildSeedView.quote]
  cases parsed : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames =>
    simp only [Option.bind_some,at_value]
    cases selected : frames[5]? with
    | none => rfl
    | some frame => simp only [Option.bind_some,frameSeed_value]

theorem quote_cost (input : Input) : (quote input).cost ≤ 24*input.length+6*seedLabel.length+487 := by
  have frames := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [quote]
  split
  · dsimp only; omega
  · rename_i values parsed
    have selected := at_cost values 5
    split
    · dsimp only; omega
    · rename_i frame found
      have result := frameSeed_cost frame
      dsimp only
      omega

/-- All original compatible parent records, selected from the parsed child input. -/
def active (cache : StoredShakeByteCache.Cache) (state : NativeParentLedger.State) (input : Input) :=
  let seed := quote input
  match seed.value with
  | none => Run.mk [] (seed.cost+2)
  | some value =>
    let result := StoredParentSeedCheck.parents cache value state.parents
    Run.mk result.value (seed.cost+result.cost+3)

theorem active_value (cache : StoredShakeByteCache.Cache) (state : NativeParentLedger.State) (input : Input) :
    (active cache state input).value = ExecutableParentLedger.active state (StoredShakeByteCache.view cache) input := by
  have reference := quote_value input
  cases parsed : (quote input).value with
  | none =>
    rw [parsed,Option.map_none] at reference
    simp only [active,parsed,ExecutableParentLedger.active,← reference]
  | some seed =>
    rw [parsed,Option.map_some] at reference
    simp only [active,parsed,ExecutableParentLedger.active,← reference,StoredParentSeedCheck.parents_value]

theorem active_cost (cache : StoredShakeByteCache.Cache) (state : NativeParentLedger.State) (input : Input) :
    (active cache state input).cost ≤ 24*input.length+6*seedLabel.length+491+
      64*(6*StoredParentSeedCheck.parentInputBytes state.parents+14*state.parents.length)*cache.length+
      454*state.parents.length := by
  have seed := quote_cost input
  simp only [active]
  split
  · dsimp only; omega
  · rename_i value parsed
    have result := StoredParentSeedCheck.parents_cost cache value state.parents
    dsimp only
    omega

/-- Parse a raw child quote and filter supplied parents against the complete
prior SHAKE-coordinate history. Construction of the parent ledger is separate. -/
def activeFromHistory (history : List NativeTranscript.Observation)
    (state : NativeParentLedger.State) (input : Input) :=
  let cache := StoredShakeHistory.replay history
  let result := active cache.value state input
  Run.mk result.value (cache.cost+result.cost+1)

theorem activeFromHistory_value (history : List NativeTranscript.Observation)
    (state : NativeParentLedger.State) (input : Input) :
    (activeFromHistory history state input).value = ExecutableParentLedger.active state
      (CompactSourceHistory.reconstruct history).bytes input := by
  simp only [activeFromHistory,active_value,StoredShakeHistory.replay_eq_compact]

theorem activeFromHistory_cost (history : List NativeTranscript.Observation)
    (state : NativeParentLedger.State) (input : Input) :
    (activeFromHistory history state input).cost ≤
      8*StoredShakeHistory.bytes history+5*history.length+24*input.length+6*seedLabel.length+493+
      64*(6*StoredParentSeedCheck.parentInputBytes state.parents+14*state.parents.length)*StoredShakeHistory.bytes history+
      454*state.parents.length := by
  have cache := StoredShakeHistory.replay_cost history
  have result := active_cost (StoredShakeHistory.replay history).value state input
  rw [StoredShakeHistory.replay_size] at result
  simp only [activeFromHistory]
  omega
end FormalProof4FHE.HasteBoots.StoredChildSeedQuote
