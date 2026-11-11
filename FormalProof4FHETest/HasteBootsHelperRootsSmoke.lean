module
import all FormalProof4FHE.HasteBoots.AllocatedScalarFamily
import all FormalProof4FHETest.HasteBootsScalarCompletedSmoke

namespace FormalProof4FHE.HasteBoots.HelperRootsSmoke
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativePrefixCodec (Vector)
open OracleProgram (run)
open ScalarReplaySmoke (statement proof)
open HasteBootsSamplerAncestrySmoke (worldZero worldReject)
noncomputable section

def digest (value : InputIndexedOracle.Byte) : Digest := fun _ => value
def roots : Vector Digest := ⟨[digest 1,digest 2,digest 1],by decide⟩
def decoy : Vector Digest := ⟨[digest 9],by decide⟩
def parent := NativeTranscript.new [] (digest 0)
def earlier := NativeLookupEquality.bindRoots parent decoy.val decoy.property
def before := (TranscriptFrame.decodeAll earlier.input).getD []
theorem decoded : TranscriptFrame.decodeAll earlier.input = some before := by decide +kernel
theorem framed : (∀ frame ∈ before, TranscriptFrame.Valid frame) ∧ earlier.input = TranscriptFrame.encodeMany before :=
  TranscriptFrame.decodeAll_sound _ _ decoded

def bound := NativeLookupEquality.bindRoots earlier roots.val roots.property

theorem actual_parsed : HelperRootsView.parse bound.input = some roots :=
  HelperRootsView.parse_bound earlier before framed.2 framed.1 roots (by decide +kernel)

theorem original_order : roots.val[0]? = roots.val[2]? ∧ roots.val[0]?.map (fun digest => digest ⟨0,by decide⟩) = some 1 ∧
    roots.val[1]?.map (fun digest => digest ⟨0,by decide⟩) = some 2 := ⟨rfl,rfl,rfl⟩

/-- The earlier well-formed decoy cannot replace the actual binder. -/
theorem decoy_rejected : HelperRootsView.parse bound.input ≠ some decoy := by
  intro accepted
  have same := Option.some.inj (actual_parsed.symm.trans accepted)
  have count : (3 : ℕ) = 1 := congrArg (fun roots => roots.val.length) same
  contradiction

/-- A malformed latest roots frame is rejected without falling back. -/
theorem malformed_rejected : HelperRootsView.readFrames
    [⟨1,NativeLookupEquality.rootsLabel,[]⟩,HelperRootsView.rootFrame roots] = none := rfl

/-- Receipt-kind frames bearing the same label cannot replace a binder. -/
theorem receipt_ignored : HelperRootsView.readFrames
    [⟨5,NativeLookupEquality.rootsLabel,[]⟩,HelperRootsView.rootFrame roots] = some roots := by
  rw [HelperRootsView.readFrames,ite_eq_right (by intro tagged; cases tagged.1)]
  exact HelperRootsView.read_native roots []

/-- Equality sampling retains the complete vector at every analysis budget,
including suspension and candidate rejection. -/
theorem equality_preserves (fuel : ℕ) (world : World) :
    HelperRootsView.parse (run (NativeLookupEquality.request NativeExtensionFields.goldilocksBasis 7 2 fuel earlier roots.val roots.property) world).run.1.transcript.input = some roots := by
  have extension := RootSafeEquality.equality_request NativeExtensionFields.goldilocksBasis 7 2 fuel earlier roots.val roots.property world (by decide +kernel)
  obtain ⟨frames,decoded,_⟩ := Option.bind_eq_some_iff.mp actual_parsed
  rw [extension.1.parse frames decoded]
  exact actual_parsed

def scalar (fuel : ℕ) (world : World) := NativeScalarBatchVerifier.execute statement proof fuel
  (NativeScalarBatchVerifier.initial bound statement proof) world

/-- Every actual completed scalar record recovers the same literal roots,
with no separate membership, order or equality-search certificate. -/
theorem scalar_preserves (fuel : ℕ) (world : World) (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (scalar fuel world).1.completed) :
    HelperRootsView.parse entry.coefficients.phase.pending.input = some roots := by
  have extension := RootSafeScalar.execute bound statement proof fuel _ world ScalarExecutionRecoverySmoke.domain
    (RootSafeScalar.initial bound statement proof (by decide +kernel))
  obtain ⟨frames,decoded,_⟩ := Option.bind_eq_some_iff.mp actual_parsed
  rw [((extension.2.2 entry member).1).parse frames decoded]
  exact actual_parsed

theorem actual_completions : (scalar 9 worldZero).1.completed.length = 2 := by decide +kernel

def first := (scalar 9 worldZero).1.completed[0]'(by rw [actual_completions]; decide)
def second := (scalar 9 worldZero).1.completed[1]'(by rw [actual_completions]; decide)

theorem second_parsed : HelperRootsView.parse second.coefficients.phase.pending.input = some roots :=
  scalar_preserves 9 worldZero second (List.getElem_mem _)

/-- Matching original ordinal 2 retains the repeated root at that position. -/
theorem ordinal_two : roots.val.get ⟨2,by decide⟩ = roots.val.get ⟨2,by decide⟩ :=
  OriginalHelperRoots.ordinal second.coefficients.phase.pending.input second.coefficients.phase.pending.input roots roots
    second_parsed second_parsed rfl ⟨2,by decide⟩ ⟨2,by decide⟩ rfl

/-- Rejection-only sampling has no completed record and does not replace the
original bound vector with an earlier decoy. -/
theorem rejection_retains : (scalar 10 worldReject).1.completed = [] ∧
    HelperRootsView.parse (scalar 10 worldReject).1.state.transcript.input = some roots := by
  constructor
  · decide +kernel
  · have extension := RootSafeScalar.execute bound statement proof 10 _ worldReject ScalarExecutionRecoverySmoke.domain
      (RootSafeScalar.initial bound statement proof (by decide +kernel))
    obtain ⟨frames,decoded,_⟩ := Option.bind_eq_some_iff.mp actual_parsed
    unfold scalar
    rw [extension.1.parse frames decoded]
    exact actual_parsed

end
end FormalProof4FHE.HasteBoots.HelperRootsSmoke
