module
import all FormalProof4FHE.HasteBoots.AllocatedLookupReadStability
import all FormalProof4FHETest.HasteBootsSourceFrontierSmoke
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.AllocatedFrontierSmoke
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open HasteBootsRealizedAncestrySmoke (modelWorld log parentValues descendantValues parent_nonempty descendant_nonempty log_eq)
open HasteBootsSourceExposureCoverageSmoke (parentInput)
open HasteBootsLifetimeLineageSmoke (descendantInput)
noncomputable section

private theorem head_first (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ []) (small : offset < 64)
    (tail : List Observation) : OracleFirstExposure.locate (.output input offset values :: tail) (OracleFirstExposure.seedCoordinates input) = some 0 := by
  have observed : (.inl (input,offset) : InputIndexedOracle.Coordinate) ∈ ObservationReplay.coordinates (.output input offset values) :=
    Finset.mem_image.mpr ⟨0,by simpa only [Finset.mem_range,List.length_pos_iff] using positive,by simp⟩
  have relevant : (.inl (input,offset) : InputIndexedOracle.Coordinate) ∈ OracleFirstExposure.seedCoordinates input :=
    Finset.mem_image.mpr ⟨⟨offset,small⟩,Finset.mem_univ _,by simp [CachedOracleResponse.shakeCoordinates]⟩
  have hit : ¬Disjoint (ObservationReplay.coordinates (.output input offset values)) (OracleFirstExposure.seedCoordinates input) :=
    Finset.not_disjoint_iff.mpr ⟨_,observed,relevant⟩
  rw [OracleFirstExposure.locate,ite_eq_right hit]

private theorem other_disjoint (left right : Input) (different : left ≠ right) (offset : ℕ) (values : Input) :
    Disjoint (ObservationReplay.coordinates (.output left offset values)) (OracleFirstExposure.seedCoordinates right) := by
  apply Finset.disjoint_left.mpr
  intro coordinate observed relevant
  obtain ⟨index,_,rfl⟩ := Finset.mem_image.mp observed
  obtain ⟨position,_,same⟩ := Finset.mem_image.mp relevant
  have inputEq : right = left ∧ position.val = offset+index := by simpa [CachedOracleResponse.shakeCoordinates] using same
  exact different inputEq.1.symm

/-- The enclosing program queries the descendant before the native segment
exposes its parent. Ancestry remains semantic, and chronology must be charged. -/
def program : OracleProgram.Program (ℕ ⊕ Unit) := .read descendantInput 7 1 (fun _ => OracleMachine.take HasteBootsRealizedAncestrySmoke.step 4 0)
def history := (OracleProgram.run program modelWorld).run.2

theorem included : log.Sublist history := by
  change log.Sublist ([.output descendantInput 7 (InputIndexedOracle.bytes modelWorld descendantInput 7 1)] ++ log)
  exact List.sublist_append_right _ _

theorem childFirst : OracleFirstExposure.locate history (OracleFirstExposure.seedCoordinates descendantInput) = some 0 :=
  head_first descendantInput 7 _ (by simp only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length]; decide) (by decide) log

theorem parentFirst : OracleFirstExposure.locate history (OracleFirstExposure.seedCoordinates parentInput) = some 1 := by
  change OracleFirstExposure.locate (.output descendantInput 7 (InputIndexedOracle.bytes modelWorld descendantInput 7 1) :: log) _ = _
  rw [OracleFirstExposure.locate,ite_eq_left (other_disjoint descendantInput parentInput HasteBootsRealizedAncestrySmoke.parent_ne_descendant.symm _ _)]
  have first : OracleFirstExposure.locate log (OracleFirstExposure.seedCoordinates parentInput) = some 0 := by
    rw [log_eq]
    exact head_first parentInput 0 parentValues parent_nonempty (by decide) _
  rw [first]
  rfl

theorem source_reindexed : NativeSeedAncestry.Realized modelWorld history descendantInput 0
    (.source (HasteBootsParentStateSmoke.context,HasteBootsParentStateSmoke.root)) := by
  obtain ⟨index,realized⟩ := HasteBootsRealizedAncestrySmoke.realized (.source (HasteBootsParentStateSmoke.context,HasteBootsParentStateSmoke.root)) (HasteBootsSourceExposureCoverageSmoke.direct_source (HasteBootsParentStateSmoke.context,HasteBootsParentStateSmoke.root) (by simp [HasteBootsSourceExposureCoverageSmoke.sources]))
  obtain ⟨position,retained⟩ := SeedAncestryEmbedding.realized_sublist included realized
  have same : position = 0 := Option.some.inj (retained.first.symm.trans childFirst)
  exact same ▸ retained

theorem helper_reindexed : NativeSeedAncestry.Realized modelWorld history descendantInput 0 (.helper HasteBootsParentStateSmoke.context) := by
  obtain ⟨index,realized⟩ := HasteBootsRealizedAncestrySmoke.realized _ HasteBootsRealizedAncestrySmoke.direct_helper
  obtain ⟨position,retained⟩ := SeedAncestryEmbedding.realized_sublist included realized
  have same : position = 0 := Option.some.inj (retained.first.symm.trans childFirst)
  exact same ▸ retained

/-- Reindexing cannot silently turn an early descendant into a chronological
parent edge: the same containing program has the existing seed-order bad event. -/
theorem early_quote_bad : SeedQuoteOrder.Bad OracleProgramMachine.step program modelWorld := by
  obtain ⟨fuel,complete⟩ := OracleProgramMachine.complete program modelWorld
  have logs := congrArg Prod.snd complete
  exact SeedQuoteOrder.early_edge_bad OracleProgramMachine.step fuel program modelWorld descendantInput parentInput 0 1
    (by rw [logs]; exact childFirst) (by rw [logs]; exact parentFirst) HasteBootsRealizedAncestrySmoke.descendant_quote_actual (by decide)

/-- The actual native roots binder preserves both original roots, without
flattening helper lanes or supplying a parsed-root membership certificate. -/
example : HasteBootsRealizedAncestrySmoke.helperRoot ∈ NativeParentLedger.roots
    (NativeLookupEquality.bindRoots HasteBootsSamplerAncestrySmoke.child
      [HasteBootsParentStateSmoke.root,HasteBootsRealizedAncestrySmoke.helperRoot] (by decide)).input :=
  LookupScalarSeedQuote.bound_root HasteBootsSamplerAncestrySmoke.header _ _ (by decide +kernel) _ (by simp)

end
end FormalProof4FHE.HasteBoots.AllocatedFrontierSmoke
