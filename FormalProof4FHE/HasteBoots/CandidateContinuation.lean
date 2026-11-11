module
public import FormalProof4FHE.HasteBoots.ProgramContinuationPrefix
public import FormalProof4FHE.HasteBoots.ScalarLifetimeComposition
@[expose] public section

/-! Native attained candidates persist when the original program is extended.
Their data, first-read ordinal and original factor receipts are retained. -/
namespace FormalProof4FHE.HasteBoots.CandidateContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind run runPrefix)
open ProgramContinuationPrefix (active_bind log_prefix)
noncomputable section

variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

def parent (original : OriginalParentFamily.Family program position world) (next : A → Program B)
    (same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2) :
    OriginalParentFamily.Family (bind program next) position world where
  registry := original.registry
  helper := original.helper
  requests := original.requests
  input := original.input
  parent := original.parent
  bindings := original.bindings
  known := by rw [same]; exact original.known
  parsed := original.parsed
  bindingParsed := original.bindingParsed
  computed := original.computed
  requests_eq := original.requests_eq
  related := original.related
  nonempty := original.nonempty
  helperFull := original.helperFull.trans (log_prefix program next world).sublist
  registryFull := fun slot => (original.registryFull slot).trans (log_prefix program next world).sublist

def family (original : OriginalScalarFamily.Family program position world) (next : A → Program B)
    (same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2) :
    OriginalScalarFamily.Family (bind program next) position world :=
  ⟨parent original.parent next same,original.input,original.roots,original.parsed,original.quote⟩

def selection (original : AllocatedJobFamily.Selection program position world) (next : A → Program B)
    (same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2) :
    AllocatedJobFamily.Selection (bind program next) position world :=
  ⟨original.ctx,original.body,original.allocation,original.origin,original.index,original.job,original.geometry,
    family original.family next same,original.registry,original.helper,original.requests,original.roots⟩

theorem observed (sample : LookupFactorFixation.Sample) (next : A → Program B)
    (original : ProgramFactorFixation.Observed program sample) : ProgramFactorFixation.Observed (bind program next) sample :=
  (log_prefix program next sample.view.reader.world).sublist.subset original

def candidate (original : JobReferenceCandidate.Candidate program position world) (next : A → Program B) :
    JobReferenceCandidate.Candidate (bind program next) position world := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  exact {
    selection := selection original.selection next same
    first := ProgramContinuationPrefix.first original.first next
    first_position := original.first_position
    compression := ⟨original.compression.value,original.compression.world_eq,original.compression.input_eq,
      original.compression.position_eq,observed _ next original.compression.observed⟩
    offset := ⟨original.offset.value,original.offset.world_eq,original.offset.input_eq,
      original.offset.position_eq,observed _ next original.offset.observed⟩
    point := ⟨original.point.value,original.point.world_eq,original.point.input_eq,
      original.point.position_eq,observed _ next original.point.observed⟩
    roots_fit := original.roots_fit
    reader_statement := original.reader_statement
    reader_transcript := original.reader_transcript
    compression_native := original.compression_native
    offset_native := original.offset_native
    point_native := original.point_native }

theorem test (original : JobReferenceCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) (radius : ℕ) (message : NativeScalarBatchWire.Message) :
    CandidateIdentityTest.test (candidate original next) dummy radius message = CandidateIdentityTest.test original dummy radius message := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  change (if (CandidateScalarTest.info original).maxMultiplicands.val = 3 then _ else _) = _
  unfold CandidateIdentityTest.test CandidateScalarTest.fullTest CandidateScalarTest.partialTest
    CandidateIdentityTables.fullTables CandidateIdentityTables.partialTables
    AllocatedJobFamily.Selection.sources AllocatedJobFamily.Selection.helpers
  simp only [same]
  rfl

def packet {input : Input} {ordinal : ℕ} (original : AttainableIdentityEvent.Packet program position input ordinal world)
    (next : A → Program B) : AttainableIdentityEvent.Packet (bind program next) position input ordinal world :=
  ⟨⟨candidate original.classed.val next,original.classed.property⟩,original.message,original.messageAt,
    original.configuration,original.found⟩

theorem event {input : Input} {ordinal : ℕ} (next : A → Program B)
    (dummy : NativeRootMessage.Digest) (radius : ℕ)
    (original : AttainableIdentityEvent.Event program position input ordinal dummy radius world) :
    AttainableIdentityEvent.Event (bind program next) position input ordinal dummy radius world := by
  obtain ⟨witness,occurred⟩ := original
  refine ⟨packet witness next,?_⟩
  change ScalarRecoveredUnboundedLaw.event _ _ _ (CandidateIdentityTest.test (candidate witness.classed.val next) dummy radius witness.message) world
  rw [test]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest) (radius : ℕ)
    (original : ScalarLifetimeComposition.Event program dummy radius world) :
    ScalarLifetimeComposition.Event (bind program next) dummy radius world := by
  obtain ⟨position,input,ordinal,occurred⟩ := original
  exact ⟨position,input,ordinal,event next dummy radius occurred⟩

end
end FormalProof4FHE.HasteBoots.CandidateContinuation
