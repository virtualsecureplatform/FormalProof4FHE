module

public import FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
@[expose] public section

/-! Actual source-collection invariants, including stopped prefixes. Inserted
claims retain raw slot/query/value provenance; complete keys are unique and
source slots stay ordered. Successful runs cover every used source and retain
its first used representative, with alias equality interpreted in the field.
The finite source-count bound is local and imposes no attacker lifetime cap. -/
namespace FormalProof4FHE.HasteBoots.NativeSourceClaimInvariant
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
open NativeBrakedownContext (RowDescription)
open NativeLookupRequestWire (Request Row)
open NativeGoldPcsWire (Query)
open NativeCanonicalLookupWire (Source)
open NativeSharedSourceClaims (Seen Progress Result afterContext step loop)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def claimView {sources : Vector Source} (claim : NativeDeferredOpeningBatch.Claim sources) : ℕ × Query × Row :=
  (claim.slot.val,claim.query,claim.values)
def seenView (query : Query) (seen : Seen) : ℕ × Query × Row := (seen.slot,query,seen.values)
def Recorded (query : Query) (progress : Progress) : Prop :=
  progress.state.claims.val.map claimView = progress.seen.map (seenView query)
def Unique (progress : Progress) : Prop := (progress.seen.map Seen.key).Nodup

theorem push_failure {C : Type} (registry : Vector (Oracle C)) (state : NativeDeferredOpeningBatch.State)
    (slot : NativeUsizeMessage.Usize) (query : Query) (values : Row) (reason : NativeDeferredOpeningBatch.Error)
    (failed : (NativeDeferredOpeningBatch.push registry state slot query values).2 = .error reason) :
    (NativeDeferredOpeningBatch.push registry state slot query values).1 = state := by
  unfold NativeDeferredOpeningBatch.push at failed ⊢
  split at failed
  next missing => rfl
  next oracle found =>
    split at failed
    next checked =>
      rw [ite_eq_left checked]
      split at failed
      next bounded =>
        rw [dite_eq_left bounded]
        split at failed
        next fits => simp only at failed; contradiction
        next rejected => rw [dite_eq_right rejected]
      next rejected => rw [dite_eq_right rejected]
    next rejected => rw [ite_eq_right rejected]

/-- The only state-changing branch is a successful push of a previously unseen key. -/
theorem afterContext_change {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest) :
    (afterContext registry query values slot before context).progress = before ∨
    ∃ digest row,
      context = some digest ∧ values.val[slot.val]? = some row ∧
      before.seen.find? (fun previous => decide (previous.key = (digest,(registry.val.get slot).root))) = none ∧
      (NativeDeferredOpeningBatch.push registry before.state ⟨slot.val,lt_of_lt_of_le slot.isLt registry.property.le⟩ query row).2 = .ok () ∧
      (afterContext registry query values slot before context).progress =
        ⟨(NativeDeferredOpeningBatch.push registry before.state ⟨slot.val,lt_of_lt_of_le slot.isLt registry.property.le⟩ query row).1,
          before.seen++[⟨slot.val,(digest,(registry.val.get slot).root),row⟩]⟩ := by
  cases context with
  | none => exact Or.inl rfl
  | some digest =>
    simp only [afterContext]
    split
    · exact Or.inl rfl
    next row found =>
      split
      · split <;> exact Or.inl rfl
      next absent =>
        split
        next reason failed =>
          left
          simp only [Result.progress,push_failure registry before.state _ query row reason failed]
        next passed => exact Or.inr ⟨digest,row,rfl,found,absent,passed,rfl⟩

theorem missing_key (seen : List Seen) (key : Source)
    (missing : seen.find? (fun previous => decide (previous.key = key)) = none) : key ∉ seen.map Seen.key := by
  intro member
  obtain ⟨previous,member,same⟩ := List.mem_map.mp member
  have absent := List.find?_eq_none.mp missing previous member
  exact absent (by simpa only [decide_eq_true_eq] using same)

theorem afterContext_unique {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest) (unique : Unique before) :
    Unique (afterContext registry query values slot before context).progress := by
  rcases afterContext_change registry query values slot before context with same | ⟨digest,row,_,_,absent,_,same⟩
  · rw [same]; exact unique
  · rw [same]
    have fresh := missing_key before.seen (digest,(registry.val.get slot).root) absent
    simp only [Unique,List.map_append,List.map_cons,List.map_nil]
    apply List.nodup_append.mpr
    exact ⟨unique,List.nodup_singleton _,by
      intro previous member key same
      obtain rfl := List.mem_singleton.mp same
      intro equal
      exact fresh (equal ▸ member)⟩

theorem afterContext_recorded {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before : Progress) (context : Option NativeRootMessage.Digest) (recorded : Recorded query before) :
    Recorded query (afterContext registry query values slot before context).progress := by
  rcases afterContext_change registry query values slot before context with same | ⟨digest,row,_,_,_,passed,same⟩
  · rw [same]; exact recorded
  · obtain ⟨oracle,bounded,fits,_,_,pushed⟩ := NativeDeferredOpeningBatch.push_spec registry before.state _ query row passed
    rw [same]
    unfold Recorded
    dsimp only
    rw [pushed]
    simp only [List.map_append,List.map_cons,List.map_nil,claimView,seenView]
    exact congrArg (fun views => views++[(slot.val,query,row)]) recorded

def Origin {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (values : Vector Row) (world : World) (seen : Seen) : Prop :=
  ∃ slot : Fin registry.val.length, seen.slot = slot.val ∧ NativeSharedSourceClaims.used requests slot = true ∧
    (run (NativeBrakedownContext.context description (registry.val.get slot).parameters) world).run.1 = some seen.key.1 ∧
    seen.key.2 = (registry.val.get slot).root ∧ values.val[slot.val]? = some seen.values

theorem step_invariants {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) :
    (Unique before → Unique (run (step description registry requests query values slot before) world).run.1.progress) ∧
    (Recorded query before → Recorded query (run (step description registry requests query values slot before) world).run.1.progress) := by
  unfold step
  split
  · simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    exact ⟨afterContext_unique registry query values slot before _,afterContext_recorded registry query values slot before _⟩
  · exact ⟨id,id⟩

theorem step_added {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) :
    ∃ added, (run (step description registry requests query values slot before) world).run.1.progress.seen = before.seen++added ∧
      (added.map Seen.slot).Sublist [slot.val] ∧ ∀ previous ∈ added, Origin description registry requests values world previous := by
  unfold step
  split
  next used =>
    simp only [OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
    rcases afterContext_change registry query values slot before
      (run (NativeBrakedownContext.context description (registry.val.get slot).parameters) world).run.1 with same | ⟨digest,row,computed,found,_,_,same⟩
    · exact ⟨[],by simpa only [List.append_nil] using congrArg Progress.seen same,List.nil_sublist _,by simp⟩
    · refine ⟨[⟨slot.val,(digest,(registry.val.get slot).root),row⟩],congrArg Progress.seen same,List.Sublist.refl _,?_⟩
      intro previous member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨slot,rfl,used,computed,rfl,found⟩
  · exact ⟨[],by simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,Result.progress,List.append_nil],List.nil_sublist _,by simp⟩

theorem loop_invariants {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before : Progress) (world : World)
    (unique : Unique before) (recorded : Recorded query before) :
    Unique (run (loop description registry requests query values slots before) world).run.1.progress ∧
      Recorded query (run (loop description registry requests query values slots before) world).run.1.progress := by
  induction slots generalizing before with
  | nil => exact ⟨unique,recorded⟩
  | cons slot rest ih =>
    have one := step_invariants description registry requests query values slot before world
    simp only [loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    cases current : (run (step description registry requests query values slot before) world).run.1 with
    | stopped progress reason =>
      simpa only [current,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using And.intro (one.1 unique) (one.2 recorded)
    | done after =>
      apply ih after
      · simpa only [current,Result.progress] using one.1 unique
      · simpa only [current,Result.progress] using one.2 recorded

theorem loop_added {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before : Progress) (world : World) :
    ∃ added, (run (loop description registry requests query values slots before) world).run.1.progress.seen = before.seen++added ∧
      (added.map Seen.slot).Sublist (slots.map Fin.val) ∧ ∀ previous ∈ added, Origin description registry requests values world previous := by
  induction slots generalizing before with
  | nil => exact ⟨[],by simp only [loop,OracleProgram.run,CanonicalTranscriptSampler.run_pure,Result.progress,List.append_nil],List.Sublist.refl _,by simp⟩
  | cons slot rest ih =>
    obtain ⟨first,seenFirst,slotsFirst,originFirst⟩ := step_added description registry requests query values slot before world
    simp only [loop,OracleProgram.run_bind,ObservationReplay.run_bind]
    cases current : (run (step description registry requests query values slot before) world).run.1 with
    | stopped progress reason =>
      simp only [current,Result.progress] at seenFirst
      refine ⟨first,seenFirst,?_,originFirst⟩
      exact slotsFirst.trans (List.sublist_append_left _ _)
    | done after =>
      simp only [current,Result.progress] at seenFirst
      obtain ⟨later,seenLater,slotsLater,originLater⟩ := ih after
      refine ⟨first++later,?_,?_,?_⟩
      · rw [seenLater,seenFirst,List.append_assoc]
      · simpa only [List.map_append,List.map_cons,List.cons_append,List.nil_append] using slotsFirst.append slotsLater
      · intro previous member
        rcases List.mem_append.mp member with early | late
        · exact originFirst previous early
        · exact originLater previous late

theorem program_invariants {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) (empty : state.claims.val = []) :
    let after := (run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1.progress
    Unique after ∧ Recorded query after ∧ (after.seen.map Seen.slot).Sublist ((List.finRange registry.val.length).map Fin.val) ∧
      ∀ previous ∈ after.seen, Origin description registry requests values world previous := by
  have invariant := loop_invariants description registry requests query values (List.finRange registry.val.length) ⟨state,[]⟩ world
    (by simp only [Unique,List.map_nil,List.nodup_nil]) (by simp only [Recorded,empty,List.map_nil])
  obtain ⟨added,same,slots,origins⟩ := loop_added description registry requests query values (List.finRange registry.val.length) ⟨state,[]⟩ world
  simp only [List.nil_append] at same
  dsimp only [NativeSharedSourceClaims.program]
  exact ⟨invariant.1,invariant.2,by rw [same]; exact slots,by rw [same]; exact origins⟩

theorem program_counts {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) (empty : state.claims.val = []) :
    let after := (run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1.progress
    after.state.claims.val.length = after.seen.length ∧ after.seen.length ≤ registry.val.length := by
  have invariant := program_invariants description registry requests query values state world empty
  have count := congrArg List.length invariant.2.1
  simp only [List.length_map] at count
  exact ⟨count,by simpa only [List.length_map,List.length_finRange] using invariant.2.2.1.length_le⟩

theorem program_order {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) (empty : state.claims.val = []) :
    ((run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1.progress.seen).Pairwise
      (fun left right => left.slot < right.slot) := by
  have invariant := program_invariants description registry requests query values state world empty
  have ordered : List.Pairwise (fun left right : Fin registry.val.length => left.val < right.val) (List.finRange registry.val.length) :=
    List.pairwise_lt_finRange _
  have mapped : List.Pairwise (fun left right : ℕ => left < right) ((List.finRange registry.val.length).map Fin.val) := by
    simpa only [List.pairwise_map] using ordered
  simpa only [List.pairwise_map] using List.Pairwise.sublist invariant.2.2.1 mapped

theorem afterContext_covers {C : Type} (registry : Vector (Oracle C)) (query : Query) (values : Vector Row)
    (slot : Fin registry.val.length) (before after : Progress) (context : Option NativeRootMessage.Digest)
    (accepted : afterContext registry query values slot before context = .done after) :
    ∃ digest row previous, context = some digest ∧ values.val[slot.val]? = some row ∧ previous ∈ after.seen ∧
      previous.key = (digest,(registry.val.get slot).root) ∧ NativeGoldPcsClaim.equal previous.values.val row.val = true := by
  cases context with
  | none => contradiction
  | some digest =>
    simp only [afterContext] at accepted
    split at accepted
    · contradiction
    next row found =>
      split at accepted
      next previous located =>
        split at accepted
        next equal =>
          cases accepted
          have witness := List.find?_eq_some_iff_getElem.mp located
          obtain ⟨index,bounded,same,_⟩ := witness.2
          refine ⟨digest,row,previous,rfl,found,?_,?_,equal⟩
          · rw [← same]; exact List.getElem_mem bounded
          · simpa only [decide_eq_true_eq] using witness.1
        next different => contradiction
      next absent =>
        split at accepted
        · contradiction
        next passed =>
          cases accepted
          exact ⟨digest,row,⟨slot.val,(digest,(registry.val.get slot).root),row⟩,rfl,found,
            List.mem_append_right _ (List.mem_singleton_self _),rfl,by simp only [NativeGoldPcsClaim.equal,decide_true]⟩

theorem step_covers {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before after : Progress) (world : World)
    (used : NativeSharedSourceClaims.used requests slot = true)
    (accepted : (run (step description registry requests query values slot before) world).run.1 = .done after) :
    ∃ digest row previous,
      (run (NativeBrakedownContext.context description (registry.val.get slot).parameters) world).run.1 = some digest ∧
      values.val[slot.val]? = some row ∧ previous ∈ after.seen ∧ previous.key = (digest,(registry.val.get slot).root) ∧
      NativeGoldPcsClaim.equal previous.values.val row.val = true := by
  simp only [step,used,ite_true,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at accepted
  exact afterContext_covers registry query values slot before after _ accepted

theorem step_bound {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slot : Fin registry.val.length) (before : Progress) (world : World) (bound : ℕ)
    (earlier : ∀ previous ∈ before.seen, previous.slot ≤ bound) (current : slot.val ≤ bound) :
    ∀ previous ∈ (run (step description registry requests query values slot before) world).run.1.progress.seen, previous.slot ≤ bound := by
  obtain ⟨added,same,slots,_⟩ := step_added description registry requests query values slot before world
  rw [same]
  intro previous member
  rcases List.mem_append.mp member with old | fresh
  · exact earlier previous old
  · have located : previous.slot = slot.val := List.mem_singleton.mp (slots.subset (List.mem_map.mpr ⟨previous,fresh,rfl⟩))
    exact located ▸ current

theorem loop_covers {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (slots : List (Fin registry.val.length)) (before after : Progress) (world : World)
    (ordered : slots.Pairwise (fun left right => left.val < right.val))
    (accepted : (run (loop description registry requests query values slots before) world).run.1 = .done after)
    (slot : Fin registry.val.length) (member : slot ∈ slots) (used : NativeSharedSourceClaims.used requests slot = true)
    (earlier : ∀ previous ∈ before.seen, previous.slot ≤ slot.val) :
    ∃ digest row previous,
      (run (NativeBrakedownContext.context description (registry.val.get slot).parameters) world).run.1 = some digest ∧
      values.val[slot.val]? = some row ∧ previous ∈ after.seen ∧ previous.key = (digest,(registry.val.get slot).root) ∧
      NativeGoldPcsClaim.equal previous.values.val row.val = true ∧ previous.slot ≤ slot.val := by
  induction slots generalizing before after with
  | nil => cases member
  | cons first rest ih =>
    simp only [loop,OracleProgram.run_bind,ObservationReplay.run_bind] at accepted
    cases current : (run (step description registry requests query values first before) world).run.1 with
    | stopped progress reason =>
      simp only [current,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at accepted
      contradiction
    | done progress =>
      simp only [current] at accepted
      rcases List.mem_cons.mp member with same | later
      · subst first
        obtain ⟨digest,row,previous,computed,found,seen,key,equal⟩ := step_covers description registry requests query values slot before progress world used current
        have bounded := step_bound description registry requests query values slot before world slot.val earlier (Nat.le_refl _)
        simp only [current,Result.progress] at bounded
        obtain ⟨added,seenLater,_,_⟩ := loop_added description registry requests query values rest progress world
        simp only [accepted,Result.progress] at seenLater
        refine ⟨digest,row,previous,computed,found,?_,key,equal,bounded previous seen⟩
        rw [seenLater]
        exact List.mem_append_left _ seen
      · have tailOrder := (List.pairwise_cons.mp ordered).2
        have atMost : first.val ≤ slot.val := ((List.pairwise_cons.mp ordered).1 slot later).le
        have bounded := step_bound description registry requests query values first before world slot.val earlier atMost
        simp only [current,Result.progress] at bounded
        exact ih progress after tailOrder accepted later bounded

theorem program_covers {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) (after : Progress)
    (accepted : (run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1 = .done after)
    (slot : Fin registry.val.length) (used : NativeSharedSourceClaims.used requests slot = true) :
    ∃ digest row previous,
      (run (NativeBrakedownContext.context description (registry.val.get slot).parameters) world).run.1 = some digest ∧
      values.val[slot.val]? = some row ∧ previous ∈ after.seen ∧ previous.key = (digest,(registry.val.get slot).root) ∧
      NativeGoldPcsClaim.equal previous.values.val row.val = true ∧ previous.slot ≤ slot.val := by
  exact loop_covers description registry requests query values (List.finRange registry.val.length) ⟨state,[]⟩ after world
    (List.pairwise_lt_finRange _) accepted slot (List.mem_finRange slot) used (by simp)

theorem key_injective (seen : List Seen) (unique : (seen.map Seen.key).Nodup) (left right : Seen)
    (memberLeft : left ∈ seen) (memberRight : right ∈ seen) (same : left.key = right.key) : left = right := by
  induction seen with
  | nil => cases memberLeft
  | cons first rest ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp memberLeft with firstLeft | restLeft
    · subst left
      rcases List.mem_cons.mp memberRight with firstRight | restRight
      · exact firstRight.symm
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨right,restRight,same.symm⟩))
    · rcases List.mem_cons.mp memberRight with firstRight | restRight
      · subst right
        exact False.elim (unique.1 (List.mem_map.mpr ⟨left,restLeft,same⟩))
      · exact ih unique.2 restLeft restRight

theorem program_first_used {C : Type} (description : RowDescription C) (registry : Vector (Oracle C)) (requests : Vector Request)
    (query : Query) (values : Vector Row) (state : NativeDeferredOpeningBatch.State) (world : World) (empty : state.claims.val = [])
    (after : Progress) (accepted : (run (NativeSharedSourceClaims.program description registry requests query values state) world).run.1 = .done after)
    (previous : Seen) (member : previous ∈ after.seen) (slot : Fin registry.val.length)
    (used : NativeSharedSourceClaims.used requests slot = true)
    (context : (run (NativeBrakedownContext.context description (registry.val.get slot).parameters) world).run.1 = some previous.key.1)
    (root : (registry.val.get slot).root = previous.key.2) : previous.slot ≤ slot.val := by
  have invariant := program_invariants description registry requests query values state world empty
  simp only [accepted,Result.progress] at invariant
  obtain ⟨digest,row,representative,computed,_,seen,key,_,bounded⟩ := program_covers description registry requests query values state world after accepted slot used
  have digestSame : digest = previous.key.1 := Option.some.inj (computed.symm.trans context)
  have keySame : representative.key = previous.key := by
    rw [key,digestSame]
    exact Prod.ext rfl root
  have same := key_injective after.seen invariant.1 representative previous seen member keySame
  simpa only [same] using bounded
end
end FormalProof4FHE.HasteBoots.NativeSourceClaimInvariant
