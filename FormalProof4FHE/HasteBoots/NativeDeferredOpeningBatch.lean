module

public import FormalProof4FHE.HasteBoots.NativeSourceRegistry
@[expose] public section

/-! Native non-hiding deferred claims retain their original slot, raw query
and raw values; Brakedown normalize_claim is identity. Buckets preserve claim
insertion order and use the complete original registry grouping. Packet count
is checked before sealing. Constructed allocation/index unavailability is
separate from native dimension/packet rejection. Actual source execution and
invariants must establish the reachable domains; no security/work/refinement
claim follows from this state layer alone. -/
namespace FormalProof4FHE.HasteBoots.NativeDeferredOpeningBatch
open NativePrefixCodec (Vector)
open NativeCanonicalLookupWire (Source)
open NativeSourceRegistry (Initialized)
open NativeTranscript (Transcript utf8)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeSharedLookupParent (Oracle)
open NativeUsizeMessage (Usize)
open InputIndexedOracle (Input)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Claim (sources : Vector Source) where
  slot : Fin sources.val.length
  query : Query
  values : Row

structure State where
  sources : Vector Source
  parent : Transcript
  claims : Vector (Claim sources)

def initial (metadata : Initialized) : State := ⟨metadata.sources,metadata.parent,⟨[],by change 0 < 2^64; decide⟩⟩
def claimLabel : Input := utf8 "packed deferred opening claim v1"
def sealLabel : Input := utf8 "packed deferred opening seal v1"

def claimPayload (count slot : Usize) (query : Query) (values : Row) : Input :=
  NativeUsizeMessage.encode count ++ NativeUsizeMessage.encode slot ++ NativeGoldPcsWire.queryCodec.encode query ++ NativeLookupRequestWire.rowCodec.encode values

def bindClaim (state : State) (slot : Usize) (query : Query) (values : Row) : Transcript :=
  NativeTranscript.appendBytes state.parent claimLabel (claimPayload ⟨state.claims.val.length,state.claims.property⟩ slot query values)

inductive Error where
  | unknownSource | dimensions | indexingUnavailable | allocationUnavailable
  | packetCount | noClaims
  deriving DecidableEq

/-- Native Brakedown normalization is identity: checked raw matrices and values are retained. -/
def push {C : Type} (registry : Vector (Oracle C)) (state : State) (slot : Usize) (query : Query) (values : Row) : State × Except Error Unit :=
  match registry.val[slot.val]? with
  | none => (state,.error .unknownSource)
  | some oracle => if NativeGoldPcsBinding.check oracle.parameters query values then
      if bounded : slot.val < state.sources.val.length then
        if fits : state.claims.val.length+1 < 2^64 then
          let added : Claim state.sources := ⟨⟨slot.val,bounded⟩,query,values⟩
          (⟨state.sources,bindClaim state slot query values,⟨state.claims.val++[added],by
            rw [List.length_append,List.length_singleton]; exact fits⟩⟩,.ok ())
        else (state,.error .allocationUnavailable)
      else (state,.error .indexingUnavailable)
    else (state,.error .dimensions)

/-- Original claim insertion order inside a canonical group is never changed. -/
def groupClaims (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources)) : List (Claim state.sources) :=
  state.claims.val.filter (fun claim => NativeSourceRegistry.group state.sources claim.slot == group)

def groupQueries (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources)) : Vector Query :=
  ⟨(groupClaims state group).map Claim.query,by
    rw [List.length_map]; exact lt_of_le_of_lt (List.length_filter_le _ _) state.claims.property⟩

def groupValues (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources)) : Vector Row :=
  ⟨(groupClaims state group).map Claim.values,by
    rw [List.length_map]; exact lt_of_le_of_lt (List.length_filter_le _ _) state.claims.property⟩

def usedGroups (state : State) : List (Fin (NativeSourceRegistry.groupCount state.sources)) :=
  (List.finRange (NativeSourceRegistry.groupCount state.sources)).filter (fun group => !(groupClaims state group).isEmpty)

/-- Canonical groups cannot outnumber the original finite native registry. -/
theorem groupCount_le (sources : Vector Source) : NativeSourceRegistry.groupCount sources ≤ sources.val.length := by
  have injective : Function.Injective (NativeSourceRegistry.representative sources) := by
    intro first second same
    change BatchGrouping.representative sources.val first = BatchGrouping.representative sources.val second at same
    apply Fin.ext
    apply ((BatchGrouping.representatives_nodup sources.val).getElem_inj).mp
    change (BatchGrouping.compute sources.val).1.get first = (BatchGrouping.compute sources.val).1.get second
    rw [← BatchGrouping.representative_key sources.val first,← BatchGrouping.representative_key sources.val second,same]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (NativeSourceRegistry.representative sources) injective

theorem usedGroups_fits (state : State) : (usedGroups state).length < 2^64 := by
  have filtered : (usedGroups state).length ≤ NativeSourceRegistry.groupCount state.sources := by
    unfold usedGroups
    simpa only [List.length_finRange] using List.length_filter_le
      (fun group => !(groupClaims state group).isEmpty) (List.finRange (NativeSourceRegistry.groupCount state.sources))
  exact lt_of_le_of_lt (filtered.trans (groupCount_le state.sources)) state.sources.property

/-- Packet count is checked before sealing, exactly as in CanonicalOpeningBatch::verify. -/
def sealBatch (state : State) (packets : ℕ) : State × Except Error Unit :=
  if packets = (usedGroups state).length then
    if state.claims.val = [] then (state,.error .noClaims) else
      (⟨state.sources,NativeTranscript.appendBytes state.parent sealLabel
        (NativeUsizeMessage.encode ⟨state.claims.val.length,state.claims.property⟩ ++
          NativeUsizeMessage.encode ⟨(usedGroups state).length,usedGroups_fits state⟩),state.claims⟩,.ok ())
  else (state,.error .packetCount)

theorem bindClaim_input (state : State) (slot : Usize) (query : Query) (values : Row) :
    (bindClaim state slot query values).input = state.parent.input ++ TranscriptFrame.encode
      ⟨1,claimLabel,claimPayload ⟨state.claims.val.length,state.claims.property⟩ slot query values⟩ := rfl

theorem push_spec {C : Type} (registry : Vector (Oracle C)) (state : State) (slot : Usize) (query : Query) (values : Row)
    (accepted : (push registry state slot query values).2 = .ok ()) :
    ∃ oracle bounded fits,
      registry.val[slot.val]? = some oracle ∧ NativeGoldPcsBinding.check oracle.parameters query values = true ∧
      (push registry state slot query values).1 =
        ⟨state.sources,bindClaim state slot query values,⟨state.claims.val++[⟨⟨slot.val,bounded⟩,query,values⟩],fits⟩⟩ := by
  unfold push at accepted ⊢
  split at accepted
  · contradiction
  next oracle found =>
    simp only [found]
    split at accepted
    next checked =>
      rw [ite_eq_left checked]
      split at accepted
      next bounded =>
        rw [dite_eq_left bounded]
        split at accepted
        next fits =>
          rw [dite_eq_left fits]
          exact ⟨oracle,bounded,by rw [List.length_append,List.length_singleton]; exact fits,rfl,checked,rfl⟩
        next rejected => contradiction
      next rejected => contradiction
    next rejected => contradiction

/-- The canonical source keys never change when a claim succeeds or fails. -/
theorem push_sources {C : Type} (registry : Vector (Oracle C)) (state : State) (slot : Usize) (query : Query) (values : Row) :
    (push registry state slot query values).1.sources = state.sources := by
  unfold push
  split
  · rfl
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl

theorem push_count {C : Type} (registry : Vector (Oracle C)) (state : State) (slot : Usize) (query : Query) (values : Row)
    (accepted : (push registry state slot query values).2 = .ok ()) :
    (push registry state slot query values).1.claims.val.length = state.claims.val.length+1 ∧
      (push registry state slot query values).1.parent = bindClaim state slot query values := by
  obtain ⟨oracle,bounded,fits,_,_,same⟩ := push_spec registry state slot query values accepted
  rw [same]
  exact ⟨by rw [List.length_append,List.length_singleton],rfl⟩

theorem group_counts (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources)) :
    (groupQueries state group).val.length = (groupValues state group).val.length := by
  simp only [groupQueries,groupValues,List.length_map]

theorem groupQueries_values (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources)) :
    (groupQueries state group).val = (groupClaims state group).map Claim.query ∧
      (groupValues state group).val = (groupClaims state group).map Claim.values := ⟨rfl,rfl⟩

theorem usedGroups_iff (state : State) (group : Fin (NativeSourceRegistry.groupCount state.sources)) :
    group ∈ usedGroups state ↔ groupClaims state group ≠ [] := by
  simp [usedGroups]

theorem packetCount_rejected (state : State) (packets : ℕ) (wrong : packets ≠ (usedGroups state).length) :
    sealBatch state packets = (state,.error .packetCount) := by
  simp only [sealBatch,ite_eq_right wrong]

theorem seal_spec (state : State) (packets : ℕ) (accepted : (sealBatch state packets).2 = .ok ()) :
    packets = (usedGroups state).length ∧ state.claims.val ≠ [] ∧
      ∃ fits, (sealBatch state packets).1 = ⟨state.sources,NativeTranscript.appendBytes state.parent sealLabel
        (NativeUsizeMessage.encode ⟨state.claims.val.length,state.claims.property⟩ ++
          NativeUsizeMessage.encode ⟨(usedGroups state).length,fits⟩),state.claims⟩ := by
  unfold sealBatch at accepted ⊢
  split at accepted
  next count =>
    rw [ite_eq_left count]
    split at accepted
    next empty => contradiction
    next nonempty =>
      rw [ite_eq_right nonempty]
      exact ⟨count,nonempty,usedGroups_fits state,rfl⟩
  next wrong => contradiction
end
end FormalProof4FHE.HasteBoots.NativeDeferredOpeningBatch
