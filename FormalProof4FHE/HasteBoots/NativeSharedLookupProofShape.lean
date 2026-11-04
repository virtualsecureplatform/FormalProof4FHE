module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupPreflight
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude

@[expose] public section

/-!
# Shared proof dimensions and prepared-job getter domains

These are the native proof-size checks before value validation and child
creation. Helper opening contents are not interpreted here; their actual
vector length is the openingCount argument. Canonical values, unused-slot
zero checks, registry contexts, framing and PCS authentication remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupProofShape

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeSharedLookupStatement (Request Prepared Tagged tags)
open NativeLookupBindGeometry (Parameters)
open NativeRootMessage (Digest)
open NativeUsizeMessage (Usize)

structure Values where
  multiplicities : List (List GoldWord)
  roots : List Digest
  helpers : List Word
  sources : List (List GoldWord)

def check (registry : List Parameters) (requests : List Request) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) : Bool :=
  decide (openingCount = geometry.repetitions.val) &&
  (decide (values.multiplicities.length = requests.length) &&
   (values.multiplicities.zip requests).all (fun pair => decide (pair.1.length = pair.2.table.length)) &&
   decide (values.roots.length = geometry.repetitions.val) &&
   decide (values.helpers.length = geometry.repetitions.val) &&
   decide (values.sources.length = registry.length) &&
   values.sources.all (fun source => decide (source.length = geometry.geometry.2.val)))

structure Accepted (registry : List Parameters) (requests : List Request) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) : Prop where
  openings : openingCount = geometry.repetitions.val
  multiplicities : List.Forall₂ (fun counts request => counts.length = request.table.length) values.multiplicities requests
  roots : values.roots.length = geometry.repetitions.val
  helpers : values.helpers.length = geometry.repetitions.val
  sources : values.sources.length = registry.length
  width : ∀ source ∈ values.sources, source.length = geometry.geometry.2.val

theorem check_spec (registry : List Parameters) (requests : List Request) (geometry : NativeSharedLookupPreflight.Output)
    (openingCount : ℕ) (values : Values) (success : check registry requests geometry openingCount values = true) :
    Accepted registry requests geometry openingCount values := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc] at success
  refine ⟨success.1,?_,success.2.2.2.1,success.2.2.2.2.1,success.2.2.2.2.2.1,success.2.2.2.2.2.2⟩
  rw [List.forall₂_iff_zip]
  exact ⟨success.2.1,fun {counts} {request} member => success.2.2.1 (counts,request) member⟩

theorem tag_bound {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (tag : Tagged)
    (member : tag ∈ tags fits requests) : tag.ordinal.val < count := by
  unfold tags at member
  obtain ⟨entries,present,member⟩ := List.mem_flatten.mp member
  obtain ⟨index,same⟩ := List.mem_ofFn.mp present
  subst entries
  obtain ⟨repetition,same⟩ := List.mem_ofFn.mp member
  rw [← same]
  exact index.isLt

theorem prepared_count {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (accepted : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3)) (jobs : List Prepared)
    (prepared : NativeSharedLookupPrepared.prepare completed (tags fits requests) = some jobs) :
    jobs.length = geometry.repetitions.val := by
  have order := (NativeSharedLookupPrepared.prepare_spec completed (tags fits requests) jobs prepared).1
  have length := congrArg List.length order
  rw [List.length_map] at length
  exact length.trans (NativeSharedLookupPreflight.repetitions_tags fits requests registry helper geometry accepted).symm

/-- Every prepared request ordinal addresses the original multiplicity
vector; table lengths stay paired with the complete original request list. -/
theorem multiplicity_getters {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output) (openingCount : ℕ) (values : Values)
    (accepted : check registry (List.ofFn requests) geometry openingCount values = true)
    (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3)) (jobs : List Prepared)
    (prepared : NativeSharedLookupPrepared.prepare completed (tags fits requests) = some jobs) :
    ∀ job ∈ jobs, ∃ counts, values.multiplicities[job.tag.ordinal.val]? = some counts := by
  have shape := check_spec registry (List.ofFn requests) geometry openingCount values accepted
  have length : values.multiplicities.length = count := by simpa only [List.length_ofFn] using shape.multiplicities.length_eq
  have order := (NativeSharedLookupPrepared.prepare_spec completed (tags fits requests) jobs prepared).1
  intro job member
  have tagMember : job.tag ∈ tags fits requests := by rw [← order]; exact List.mem_map_of_mem member
  have bound : job.tag.ordinal.val < values.multiplicities.length := by rw [length]; exact tag_bound fits requests job.tag tagMember
  exact ⟨values.multiplicities[job.tag.ordinal.val],List.getElem?_eq_getElem bound⟩

theorem initialClaims_complete (multiplicities : List (List GoldWord)) (jobs : List Prepared)
    (domain : ∀ job ∈ jobs, ∃ counts, multiplicities[job.tag.ordinal.val]? = some counts) :
    ∃ sums, NativeSharedLookupStatement.initialClaims multiplicities jobs = some sums := by
  induction jobs with
  | nil => exact ⟨[],rfl⟩
  | cons job tail ih =>
    obtain ⟨counts,found⟩ := domain job List.mem_cons_self
    obtain ⟨sums,rest⟩ := ih (fun job member => domain job (List.mem_cons_of_mem _ member))
    exact ⟨NativeGoldExtensionArithmetic.tableSum job.output.inverses counts :: NativeGoldLookup.zero :: sums,
      by rw [NativeSharedLookupStatement.initialClaims,found,Option.bind_some,rest,Option.map_some]⟩

/-- Native proof dimensions discharge every multiplicity getter. The remaining
2*job count bound is the native infos/claims vector allocation domain, not a
sampler retry bound or an attacker-work cutoff. -/
theorem build_complete {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (registry : List Parameters) (geometry : NativeSharedLookupPreflight.Output) (openingCount : ℕ) (values : Values)
    (accepted : check registry (List.ofFn requests) geometry openingCount values = true)
    (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3)) (jobs : List Prepared)
    (prepared : NativeSharedLookupPrepared.prepare completed (tags fits requests) = some jobs)
    (vectorFits : 2 * jobs.length < 2^64) :
    ∃ statement, NativeSharedLookupStatement.build n (List.ofFn requests) jobs values.multiplicities = some statement := by
  obtain ⟨sums,found⟩ := initialClaims_complete values.multiplicities jobs
    (multiplicity_getters fits requests registry geometry openingCount values accepted completed jobs prepared)
  have sumFits : sums.length < 2^64 := by rw [NativeSharedLookupStatement.initialClaims_length _ _ _ found]; exact vectorFits
  have order := congrArg List.length ((NativeSharedLookupPrepared.prepare_spec completed (tags fits requests) jobs prepared).1)
  rw [List.length_map] at order
  have infoFits : (NativeSharedLookupStatement.infos n (List.ofFn requests)).length < 2^64 := by
    rw [NativeSharedLookupStatement.infos_length_tags fits requests n,← order]; exact vectorFits
  exact ⟨⟨⟨NativeSharedLookupStatement.infos n (List.ofFn requests),infoFits⟩,⟨sums,sumFits⟩⟩,
    by simp only [NativeSharedLookupStatement.build,found,Option.bind_some,dite_eq_left infoFits,dite_eq_left sumFits]⟩

/-- Proof root/helper/opening counts agree with actual prepared jobs; no
independent root/job or equality-point count certificate is supplied. -/
theorem prepared_dimensions {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values) (accepted : check registry (List.ofFn requests) geometry openingCount values = true)
    (completed : List (NativeLookupBatch.Completed goldilocksModulus Goldilocks3)) (jobs : List Prepared)
    (prepared : NativeSharedLookupPrepared.prepare completed (tags fits requests) = some jobs) :
    values.roots.length = jobs.length ∧ values.helpers.length = jobs.length ∧ openingCount = jobs.length := by
  have shape := check_spec registry (List.ofFn requests) geometry openingCount values accepted
  have count := prepared_count fits requests registry helper geometry preflight completed jobs prepared
  exact ⟨shape.roots.trans count.symm,shape.helpers.trans count.symm,shape.openings.trans count.symm⟩

theorem tag_request {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (tag : Tagged)
    (member : tag ∈ tags fits requests) :
    tag.ordinal.val < count ∧ (List.ofFn requests)[tag.ordinal.val]? = some tag.request := by
  unfold tags at member
  obtain ⟨entries,present,member⟩ := List.mem_flatten.mp member
  obtain ⟨index,same⟩ := List.mem_ofFn.mp present
  subst entries
  obtain ⟨repetition,same⟩ := List.mem_ofFn.mp member
  rw [← same]
  refine ⟨index.isLt,?_⟩
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using index.isLt),List.getElem_ofFn]

private theorem gather_of_bounds (values : List (List GoldWord)) (slots : List ℕ)
    (bounds : ∀ slot ∈ slots, slot < values.length) :
    ∃ copies, NativeSharedLookupGuard.gather values slots = some copies ∧ ∀ copy ∈ copies, copy ∈ values := by
  induction slots with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons slot tail ih =>
    have bound := bounds slot List.mem_cons_self
    obtain ⟨copies,rest,members⟩ := ih (fun slot member => bounds slot (List.mem_cons_of_mem _ member))
    refine ⟨values[slot] :: copies,?_,?_⟩
    · rw [NativeSharedLookupGuard.gather,List.getElem?_eq_getElem bound,Option.bind_some,rest,Option.map_some]
    · intro copy member
      rcases List.mem_cons.mp member with same | old
      · rw [same]; exact List.getElem_mem bound
      · exact members copy old

/-- Registry/request and proof dimensions discharge all slot lookups before
terminal arithmetic, preserving repeated slots and full native vector width. -/
theorem source_getters (registry : List Parameters) (helper : Parameters) (requests : List Request)
    (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper requests = some geometry)
    (openingCount : ℕ) (values : Values) (accepted : check registry requests geometry openingCount values = true)
    (request : Request) (member : request ∈ requests) :
    ∃ copies, NativeSharedLookupGuard.gather values.sources request.terminal.sourceSlots = some copies ∧
      copies.length = request.columns ∧
      List.Forall₂ (fun slot value => values.sources[slot]? = some value) request.terminal.sourceSlots copies ∧
      ∀ copy ∈ copies, copy.length = geometry.geometry.2.val := by
  have trusted := NativeSharedLookupPreflight.preflight_spec registry helper requests geometry preflight
  have shape := check_spec registry requests geometry openingCount values accepted
  have slots := trusted.dimensions.2.2 request member
  obtain ⟨copies,gathered,members⟩ := gather_of_bounds values.sources request.terminal.sourceSlots
    (fun slot present => by rw [shape.sources]; exact slots.2 slot present)
  have related := NativeSharedLookupGuard.gather_related values.sources request.terminal.sourceSlots copies gathered
  exact ⟨copies,gathered,related.length_eq.symm.trans slots.1,related,
    fun copy present => shape.width copy (members copy present)⟩

/-- On the actual initialized sampler and completed equality execution,
preflight/proof dimensions supply all remaining preparation/count/getter
requirements. No job-order, raw-challenge or root/job certificate is input. -/
theorem protocol_complete {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values) (accepted : check registry (List.ofFn requests) geometry openingCount values = true)
    (rootFits : values.roots.length < 2^64) (vectorFits : 2 * geometry.repetitions.val < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : NativeTranscript.Transcript) (world : InputIndexedOracle.World)
    (child : NativeTranscript.Transcript)
    (finished : (NativeLookupBatch.execute goldilocksBasis w lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1.control = .finished child)
    (complete : (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w geometry.geometry.1.val equalityFuel
      child values.roots rootFits) world).run.1.remaining = 0) :
    ∃ ready, (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready := by
  let batch := (NativeLookupBatch.execute goldilocksBasis w lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1
  obtain ⟨jobs,prepared,_⟩ := NativeSharedLookupPrepared.executed_prepare fits requests w lookupFuel transcript world child finished
  change NativeSharedLookupPrepared.prepare batch.completed (tags fits requests) = some jobs at prepared
  have length := prepared_count fits requests registry helper geometry preflight batch.completed jobs prepared
  have dimensions := prepared_dimensions fits requests registry helper geometry preflight openingCount values accepted batch.completed jobs prepared
  obtain ⟨statement,built⟩ := build_complete fits requests geometry.geometry.1 registry geometry openingCount values accepted batch.completed jobs prepared
    (by rw [length]; exact vectorFits)
  obtain ⟨equality,exported,_,_,_,_⟩ := NativeGoldLookupEquality.request_finished w geometry.geometry.1.val equalityFuel child values.roots rootFits world complete
  let machine := (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w geometry.geometry.1.val equalityFuel
    child values.roots rootFits) world).run.1
  let ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val := ⟨jobs,machine,equality,statement⟩
  have packed : NativeSharedLookupPrelude.pack geometry.geometry.1 (List.ofFn requests) jobs values.multiplicities machine = some ready := by
    rw [NativeSharedLookupPrelude.pack,exported,Option.bind_some,built,Option.map_some]
  have control : batch.control = .finished child := finished
  refine ⟨ready,?_⟩
  rw [NativeSharedLookupPrelude.run_protocol]
  change (OracleProgram.run (NativeSharedLookupPrelude.compile fits requests geometry.geometry.1 values.multiplicities
    values.roots rootFits w equalityFuel batch) world).run.1 = some ready
  simpa only [NativeSharedLookupPrelude.compile,control,prepared,dimensions.1,ite_true,OracleProgram.run_bind,
    ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] using packed

end FormalProof4FHE.HasteBoots.NativeSharedLookupProofShape
