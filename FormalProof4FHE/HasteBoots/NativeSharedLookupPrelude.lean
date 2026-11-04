module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupEquality
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPrepared
public import FormalProof4FHE.HasteBoots.NativeSharedLookupGeometryLink

@[expose] public section

/-!
# Composed actual lookup sampling, equality draws and shared statement

The same completed lookup machine supplies the raw producer jobs and the
child transcript used for root binding and equality draws. The resulting
statement and guard inputs retain those exact jobs and points. Fuel bounds
only an analysis prefix; suspension returns no ready statement. Native
preflight and child creation/final binding are still separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeSharedLookupStatement (Request Prepared tags)
open NativeTranscript (Transcript Observation)
open NativeRootMessage (Digest)
open NativeUsizeMessage (Usize)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

noncomputable section

structure Ready (dimension : ℕ) where
  jobs : List Prepared
  machine : NativeLookupEquality.Machine dimension Goldilocks3
  equality : NativeGoldLookupEquality.Output
  statement : NativeScalarBatchWire.Statement

def pack (n : Usize) (requests : List Request) (jobs : List Prepared) (multiplicities : List (List GoldWord))
    (machine : NativeLookupEquality.Machine n.val Goldilocks3) : Option (Ready n.val) :=
  (NativeGoldLookupEquality.finish machine).bind (fun equality =>
    (NativeSharedLookupStatement.build n requests jobs multiplicities).map
      (fun statement => ⟨jobs,machine,equality,statement⟩))

/-- Native dimension checks precede this window. The explicit root/job test
exposes that reachable-domain requirement without assuming a proof trace. -/
def compile {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w fuel : ℕ) (batch : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) : Program (Option (Ready n.val)) :=
  match batch.control with
  | .finished transcript =>
      match NativeSharedLookupPrepared.prepare batch.completed (tags fits requests) with
      | none => .pure none
      | some jobs =>
          if roots.length = jobs.length then
            bind (NativeLookupEquality.request goldilocksBasis w n.val fuel transcript roots rootFits)
              (fun machine => .pure (pack n (List.ofFn requests) jobs multiplicities machine))
          else .pure none
  | _ => .pure none

/-- The lookup sampler's full retained execution is the prefix of the same
oracle program. No lookup/equality transcript is supplied independently. -/
def protocol {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) : Program (Option (Ready n.val)) :=
  bind (NativeLookupBatch.steps goldilocksBasis w lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript))
    (compile fits requests n multiplicities roots rootFits w equalityFuel)

theorem pack_spec (n : Usize) (requests : List Request) (jobs : List Prepared) (multiplicities : List (List GoldWord))
    (machine : NativeLookupEquality.Machine n.val Goldilocks3) (ready : Ready n.val)
    (success : pack n requests jobs multiplicities machine = some ready) :
    ready.jobs = jobs ∧ ready.machine = machine ∧ NativeGoldLookupEquality.finish machine = some ready.equality ∧
      NativeSharedLookupStatement.build n requests jobs multiplicities = some ready.statement := by
  rcases Option.bind_eq_some_iff.mp success with ⟨equality, finished, rest⟩
  cases built : NativeSharedLookupStatement.build n requests jobs multiplicities with
  | none => simp only [built, Option.map_none] at rest; contradiction
  | some statement =>
    have same : Ready.mk jobs machine equality statement = ready := Option.some.inj
      (by simpa only [built, Option.map_some] using rest)
    rw [← same]
    exact ⟨rfl,rfl,finished,rfl⟩

structure Contract {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w fuel : ℕ) (batch : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World) (ready : Ready n.val) : Prop where
  lookup : ∃ transcript, batch.control = .finished transcript ∧
    ready.machine = (run (NativeLookupEquality.request goldilocksBasis w n.val fuel transcript roots rootFits) world).run.1 ∧
    (run (compile fits requests n multiplicities roots rootFits w fuel batch) world).run.2 =
      (run (NativeLookupEquality.request goldilocksBasis w n.val fuel transcript roots rootFits) world).run.2
  prepared : NativeSharedLookupPrepared.prepare batch.completed (tags fits requests) = some ready.jobs
  rootCount : roots.length = ready.jobs.length
  complete : ready.machine.remaining = 0
  settled : ready.machine.active = none
  draws : List.Forall₂ NativeGoldLookupEquality.DrawEvidence ready.machine.draws ready.equality.points
  child : ready.equality.transcript = ready.machine.transcript
  built : NativeSharedLookupStatement.build n (List.ofFn requests) ready.jobs multiplicities = some ready.statement
  dimensions : ready.statement.infos.val.length = ready.statement.claims.val.length ∧
    ready.statement.claims.val.length = 2 * ready.jobs.length
  pointCount : ready.equality.points.length = ready.jobs.length

/-- A successful composed run supplies original job ordering, root count,
every equality coefficient reader and the final transcript/statement itself. -/
theorem compile_contract {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w fuel : ℕ) (batch : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World) (ready : Ready n.val)
    (success : (run (compile fits requests n multiplicities roots rootFits w fuel batch) world).run.1 = some ready) :
    Contract fits requests n multiplicities roots rootFits w fuel batch world ready := by
  cases control : batch.control with
  | ready todo transcript => simp only [compile, control, OracleProgram.run, CanonicalTranscriptSampler.run_pure] at success; contradiction
  | sampling job todo selection => simp only [compile, control, OracleProgram.run, CanonicalTranscriptSampler.run_pure] at success; contradiction
  | finished transcript =>
    cases prepared : NativeSharedLookupPrepared.prepare batch.completed (tags fits requests) with
    | none => simp only [compile, control, prepared, OracleProgram.run, CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some jobs =>
      by_cases dimensions : roots.length = jobs.length
      · simp only [compile, control, prepared, dimensions, ite_true, OracleProgram.run_bind, ObservationReplay.run_bind,
          OracleProgram.run, CanonicalTranscriptSampler.run_pure] at success
        let machine := (run (NativeLookupEquality.request goldilocksBasis w n.val fuel transcript roots rootFits) world).run.1
        have packed := pack_spec n (List.ofFn requests) jobs multiplicities machine ready success
        have valid := NativeLookupEquality.request_valid goldilocksBasis w n.val fuel transcript roots rootFits world
        have exported := NativeGoldLookupEquality.finish_spec machine valid ready.equality packed.2.2.1
        have completed := NativeLookupEquality.request_complete goldilocksBasis w n.val fuel transcript roots rootFits world exported.1
        refine ⟨⟨transcript,control,packed.2.1,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · simp only [compile, control, prepared, dimensions, ite_true, OracleProgram.run_bind, ObservationReplay.run_bind,
            OracleProgram.run, CanonicalTranscriptSampler.run_pure, List.append_nil]
        · rw [packed.1]; exact prepared
        · rw [packed.1]; exact dimensions
        · rw [packed.2.1]; exact exported.1
        · rw [packed.2.1]; exact completed.2
        · rw [packed.2.1]; exact exported.2.2
        · rw [packed.2.1]; exact exported.2.1
        · rw [packed.1]; exact packed.2.2.2
        · exact NativeSharedLookupPrepared.build_dimensions fits requests n batch.completed ready.jobs
            (by rw [packed.1]; exact prepared) multiplicities ready.statement (by rw [packed.1]; exact packed.2.2.2)
        · exact exported.2.2.length_eq.symm.trans (completed.1.trans (dimensions.trans (congrArg List.length packed.1.symm)))
      · simp only [compile, control, prepared, dimensions, ite_false, OracleProgram.run, CanonicalTranscriptSampler.run_pure] at success
        contradiction

/-- The observations of the lookup prefix are retained in order before
those of the actual equality phase. Pure compilation emits no oracle work. -/
theorem run_protocol {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) :
    (run (protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript) world).run =
      let earlier := NativeLookupBatch.execute goldilocksBasis w lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world
      let later := (run (compile fits requests n multiplicities roots rootFits w equalityFuel earlier.1) world).run
      (later.1,earlier.2 ++ later.2) := by
  simp only [protocol, OracleProgram.run_bind, ObservationReplay.run_bind, NativeLookupBatch.run_steps]

theorem protocol_contract {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) (ready : Ready n.val)
    (success : (run (protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready) :
    Contract fits requests n multiplicities roots rootFits w equalityFuel
      (NativeLookupBatch.execute goldilocksBasis w lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) transcript) world).1 world ready := by
  rw [run_protocol] at success
  exact compile_contract fits requests n multiplicities roots rootFits w equalityFuel _ world ready success

/-- The strict terminal consumes the exact original request descriptors,
produced jobs and equality points of the composed prelude. -/
def guardInputs {count dimension : ℕ} (requests : Fin count → Request) (ready : Ready dimension)
    (sourceValues : List (List GoldWord)) (helperValues : List Word) : NativeSharedLookupGuard.Inputs :=
  ⟨(List.ofFn requests).map Request.terminal, NativeSharedLookupPrepared.guardJobs ready.jobs,
    ready.equality.points,sourceValues,helperValues⟩

theorem guard_equality {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w fuel : ℕ) (batch : NativeLookupBatch.Machine goldilocksModulus Goldilocks3) (world : World) (ready : Ready n.val)
    (contract : Contract fits requests n multiplicities roots rootFits w fuel batch world ready)
    (sourceValues : List (List GoldWord)) (helperValues : List Word)
    (claims : List NativeScalarBatchVerifier.SubClaim) (sourceVars width : ℕ) (result : NativeSharedLookupGuard.Result)
    (success : NativeSharedLookupGuard.guard (guardInputs requests ready sourceValues helperValues) claims sourceVars width = some result)
    (checked : NativeSharedLookupGuard.Checked) (member : checked ∈ result.checked) :
    ∃ draw, ready.machine.draws[checked.ordinal]? = some draw ∧ NativeGoldLookupEquality.DrawEvidence draw checked.equalityPoint := by
  have accepted := NativeSharedLookupGuard.guard_spec (guardInputs requests ready sourceValues helperValues) claims sourceVars width result success
  have found := (accepted.checked checked member).equalityPoint
  change ready.equality.points[checked.ordinal]? = some checked.equalityPoint at found
  obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp found
  have drawBound : checked.ordinal < ready.machine.draws.length := by rw [contract.draws.length_eq]; exact bound
  refine ⟨ready.machine.draws[checked.ordinal],List.getElem?_eq_getElem drawBound,?_⟩
  have evidence := contract.draws.get drawBound bound
  simpa only [List.get_eq_getElem, same] using evidence

/-- The actual prelude and initialized scalar verifier jointly supply both
families of challenge records consumed by every strict terminal check. -/
theorem protocol_scalar_link {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) (ready : Ready n.val)
    (prepared : (run (protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (sourceValues : List (List GoldWord)) (helperValues : List Word)
    (proof : NativeScalarBatchPreflight.Proof) (first : NativeScalarBatchWire.Info) (resultTranscript : Transcript)
    (accepted : NativeScalarBatchPreflight.beginVerify ready.equality.transcript ready.statement proof = .ok resultTranscript)
    (head : ready.statement.infos.val.head? = some first) (fuel : ℕ) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute ready.statement proof fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1.control = .finished claims)
    (sourceVars width : ℕ) (result : NativeSharedLookupGuard.Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready sourceValues helperValues) claims sourceVars width = some result) :
    NativeSharedLookupBatchLink.Linked (guardInputs requests ready sourceValues helperValues) ready.statement proof first
      (NativeScalarBatchVerifier.execute ready.statement proof fuel
        (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1 claims sourceVars width result ∧
      result.point.length = n.val ∧
      ∀ checked ∈ result.checked, ∃ draw, ready.machine.draws[checked.ordinal]? = some draw ∧
        NativeGoldLookupEquality.DrawEvidence draw checked.equalityPoint := by
  have contract := protocol_contract fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript world ready prepared
  have linked := NativeSharedLookupBatchLink.initialized_link (guardInputs requests ready sourceValues helperValues)
    ready.equality.transcript resultTranscript ready.statement proof first accepted head fuel world claims finished sourceVars width result passed
  refine ⟨linked,?_,?_⟩
  · exact linked.length.trans (congrArg Fin.val
      (NativeSharedLookupGeometryLink.statement_head n (List.ofFn requests) ready.jobs multiplicities ready.statement contract.built first head))
  · intro checked member
    exact guard_equality fits requests n multiplicities roots rootFits w equalityFuel _ world ready contract sourceValues helperValues
      claims sourceVars width result passed checked member

end

end FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude
