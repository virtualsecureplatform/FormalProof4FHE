module
public import FormalProof4FHE.HasteBoots.OwnedNTTSoundness
public import FormalProof4FHE.HasteBoots.OwnedHadamardSoundness
@[expose] public section

/-! Cross-stage source reuse under one audited checkpoint history. Matching
parameter tags, roots and decoding geometry are required; digest equality
alone never changes a source's domain, layout or decoding radius. -/
namespace FormalProof4FHE.HasteBoots.CrossStageSourceCoherence
noncomputable section
variable {F Input Digest Cfg : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest]
  {front suffix b m height cells : ℕ}

omit [Field F] [DecidableEq F] in
/-- Successive dimension transports preserve the original cube address. -/
theorem source_trans {firstCells middleCells lastCells width : ℕ}
    (first : firstCells = middleCells) (second : middleCells = lastCells)
    (table : MatrixFold.Cube lastCells → Fin width → F) :
    QueryReindex.source first (QueryReindex.source second table) =
      QueryReindex.source (first.trans second) table := by
  cases first
  cases second
  rfl

theorem tables_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) state)
    (firstDimensions secondDimensions : cells = front+suffix)
    (firstTag secondTag : Cfg)
    (first : RecordedSourceCoherence.Snapshot Input Digest Cfg height firstTag)
    (second : RecordedSourceCoherence.Snapshot Input Digest Cfg height secondTag)
    (firstRecorded : ⟨firstTag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨secondTag,second⟩ ∈ state.checkpoints.checkpoints)
    (tags : firstTag = secondTag) (roots : first.root = second.root) :
    QueryReindex.source firstDimensions
      (RecordedSourceCoherence.source enc dummy domain capacity radius firstTag first) =
    QueryReindex.source secondDimensions
      (RecordedSourceCoherence.source enc dummy domain capacity radius secondTag second) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) state := by
  subst secondTag
  rcases RecordedSourceCoherence.source_eq_or_bad enc dummy domain capacity radius state audited
    firstTag first second firstRecorded secondRecorded roots with equal | bad
  · exact Or.inl (congrArg (QueryReindex.source firstDimensions) equal)
  · exact Or.inr bad

variable {FirstMessage Message Response Memory CommitMemory : Type}
  {c r k n count queries : ℕ}

/-- The original evaluation source of an NTT check and an original Hadamard
factor share one interpretation outside the existing whole-history bad event.
Only total dimensions are transported; cube bit order and lanes are preserved. -/
theorem ntt_hadamard_eq_or_bad
    (ntt : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hadamard : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (expected : Fin count → Digest) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited ntt.encoding dummy (RecordedSourceCoherence.Shape Cfg height) state)
    (nttOwner : ∀ side, RecordedSourceCoherence.Snapshot Input Digest Cfg height (ntt.tag side))
    (hadamardOwner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (hadamard.tag factor))
    (factor : PBSHadamard.Factor count)
    (nttRecorded : ⟨ntt.tag true,nttOwner true⟩ ∈ state.checkpoints.checkpoints)
    (hadamardRecorded : ⟨hadamard.tag factor,hadamardOwner factor⟩ ∈ state.checkpoints.checkpoints)
    (encoding : hadamard.encoding = ntt.encoding) (domain : hadamard.domain = ntt.domain)
    (tags : ntt.tag true = hadamard.tag factor)
    (roots : (nttOwner true).root = (hadamardOwner factor).root) :
    OwnedNTTSoundness.originalSources ntt dummy capacity radius nttOwner true =
      QueryReindex.source (ntt.dimensions.trans hadamard.dimensions.symm)
        (OriginalFactorExceptionUnion.originalSources (OwnedHadamardSoundness.stage expected hadamard)
          dummy capacity radius hadamardOwner factor) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) state := by
  have same := tables_eq_or_bad ntt.encoding dummy ntt.domain capacity radius state audited
    ntt.dimensions ((ntt.dimensions.trans hadamard.dimensions.symm).trans hadamard.dimensions) (ntt.tag true) (hadamard.tag factor)
    (nttOwner true) (hadamardOwner factor) nttRecorded hadamardRecorded tags roots
  rcases same with equal | bad
  · left
    change QueryReindex.source ntt.dimensions
      (RecordedSourceCoherence.source ntt.encoding dummy ntt.domain capacity radius (ntt.tag true) (nttOwner true)) = _
    change _ = QueryReindex.source (ntt.dimensions.trans hadamard.dimensions.symm) (QueryReindex.source hadamard.dimensions
      (RecordedSourceCoherence.source hadamard.encoding dummy hadamard.domain capacity radius
        (hadamard.tag factor) (hadamardOwner factor)))
    rw [encoding,domain]
    rw [source_trans]
    exact equal
  · exact Or.inr bad

/-- Every NTT/factor association shares the same whole-history exception,
including families chosen after the run. No alias-count union is introduced. -/
theorem ntt_hadamard_family_eq_or_bad {I : Type}
    (ntt : I → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hadamard : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (expected : Fin count → Digest) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (RecordedSourceCoherence.Shape Cfg height))
    (audited : ∀ index, CheckpointExecution.Audited (ntt index).encoding dummy (RecordedSourceCoherence.Shape Cfg height) state)
    (nttOwner : ∀ index side, RecordedSourceCoherence.Snapshot Input Digest Cfg height ((ntt index).tag side))
    (hadamardOwner : ∀ factor, RecordedSourceCoherence.Snapshot Input Digest Cfg height (hadamard.tag factor))
    (factors : I → PBSHadamard.Factor count)
    (nttRecorded : ∀ index, ⟨(ntt index).tag true,nttOwner index true⟩ ∈ state.checkpoints.checkpoints)
    (hadamardRecorded : ∀ index, ⟨hadamard.tag (factors index),hadamardOwner (factors index)⟩ ∈ state.checkpoints.checkpoints)
    (encoding : ∀ index, hadamard.encoding = (ntt index).encoding) (domain : ∀ index, hadamard.domain = (ntt index).domain)
    (tags : ∀ index, (ntt index).tag true = hadamard.tag (factors index))
    (roots : ∀ index, (nttOwner index true).root = (hadamardOwner (factors index)).root) :
    (∀ index, OwnedNTTSoundness.originalSources (ntt index) dummy capacity radius (nttOwner index) true =
      QueryReindex.source ((ntt index).dimensions.trans hadamard.dimensions.symm)
        (OriginalFactorExceptionUnion.originalSources (OwnedHadamardSoundness.stage expected hadamard)
          dummy capacity radius hadamardOwner (factors index))) ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) state
  · exact Or.inr bad
  · left
    intro index
    rcases ntt_hadamard_eq_or_bad (ntt index) hadamard expected dummy capacity radius state
      (audited index) (nttOwner index) hadamardOwner (factors index) (nttRecorded index)
      (hadamardRecorded index) (encoding index) (domain index) (tags index) (roots index) with equal | failed
    · exact equal
    · exact False.elim (bad failed)

end
end FormalProof4FHE.HasteBoots.CrossStageSourceCoherence
