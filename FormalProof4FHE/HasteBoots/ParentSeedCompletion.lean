module
public import FormalProof4FHE.HasteBoots.ParentSeedCandidates
public import FormalProof4FHE.HasteBoots.ReceiptCandidateCompletion
@[expose] public section

/-! Complete the full seed blocks of every recognized parent input in a raw
prefix. The old packet remains explicit. This removes partial-seed ambiguity
on the refined fiber without selecting one compatible parent prematurely. -/
namespace FormalProof4FHE.HasteBoots.ParentSeedCompletion
open InputIndexedOracle (Input World)
open NativeTranscript (Execution Observation)
open OracleProgram (Program run bind)
open scoped Classical
noncomputable section

def program : List Input → Program Unit
  | [] => .pure ()
  | input :: rest => bind (NativeTranscriptProgram.query input 64) (fun _ => program rest)

def observations (inputs : List Input) (world : World) : List Observation :=
  inputs.flatMap (fun input => [.start input,.output input 0 (InputIndexedOracle.bytes world input 0 64)])

theorem run_program (inputs : List Input) (world : World) :
    (run (program inputs) world).run = ((),observations inputs world) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind,NativeTranscriptProgram.run_query,
      NativeTranscript.query,WriterT.run_mk,ih,observations,List.flatMap_cons]

def extend {A : Type} (past : World → Execution A) :=
  OracleProgramHistory.extend past (fun packet => program (ParentSeedCandidates.inputs packet.2).toList)

theorem replay {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past) :
    ObservationReplay.Replayable (extend past) := OracleProgramHistory.replay old _

theorem old_packet {A : Type} (past : World → Execution A) (world other : World)
    (same : (extend past other).run = (extend past world).run) : (past other).run = (past world).run :=
  congrArg (fun packet => packet.1.1) same

theorem named_output {A : Type} (past : World → Execution A) (world : World) (input : Input)
    (named : input ∈ ParentSeedCandidates.inputs (past world).run.2) :
    Observation.output input 0 (InputIndexedOracle.bytes world input 0 64) ∈ (extend past world).run.2 := by
  change _ ∈ (past world).run.2 ++ (run (program _) world).run.2
  rw [run_program]
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨input,Finset.mem_toList.mpr named,by simp⟩

theorem seed_on_fiber {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (world other : World) (input : Input) (named : input ∈ ParentSeedCandidates.inputs (past world).run.2)
    (same : (extend past other).run = (extend past world).run) :
    InputIndexedOracle.block other input 0 64 = InputIndexedOracle.block world input 0 64 := by
  have truthful := (replay old).truthful other
  rw [same] at truthful
  have equal := ObservationReplay.same_of_agrees world other _ ((replay old).truthful world) truthful
  funext position
  apply equal
  have output := named_output past world input named
  apply Finset.mem_biUnion.mpr
  refine ⟨_,List.mem_toFinset.mpr output,?_⟩
  apply (NativeShakeProjection.output_coordinate _ _ _ _).mpr
  exact ⟨rfl,by omega,by simpa only [InputIndexedOracle.bytes_length,Nat.zero_add] using position.isLt⟩

/-- Exact seed matches among recognized prefix parents. This set may contain
several inputs; no uniqueness premise is smuggled into replay. -/
def matching (history : List Observation) (world : World) (seed : NativeRootMessage.Digest) : Finset Input :=
  (ParentSeedCandidates.inputs history).filter (fun input => InputIndexedOracle.block world input 0 64 = seed)

theorem matching_on_fiber {A : Type} {past : World → Execution A} (old : ObservationReplay.Replayable past)
    (world other : World) (seed : NativeRootMessage.Digest)
    (same : (extend past other).run = (extend past world).run) :
    matching (past other).run.2 other seed = matching (past world).run.2 world seed := by
  have earlier := old_packet past world other same
  simp only [matching,earlier]
  ext input
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨named,equal⟩
    exact ⟨named,(seed_on_fiber old world other input named same).symm.trans equal⟩
  · rintro ⟨named,equal⟩
    exact ⟨named,(seed_on_fiber old world other input named same).trans equal⟩

theorem unseen {A : Type} (past : World → Execution A) (world : World) (input : Input)
    (fresh : CausalStreamExposure.seen (past world).run.2 input = false)
    (rejected : NativeParentInputView.parseParent input = none) :
    CausalStreamExposure.seen (extend past world).run.2 input = false := by
  change CausalStreamExposure.seen ((past world).run.2 ++ (run (program _) world).run.2) input = false
  rw [run_program]
  simp only [CausalStreamExposure.seen,List.any_append]
  rw [show (past world).run.2.any (CausalStreamExposure.touches input) = false from fresh]
  apply List.any_eq_false.mpr
  intro entry member
  obtain ⟨parent,named,present⟩ := List.mem_flatMap.mp member
  have different : parent ≠ input := by
    intro same
    obtain ⟨frames,parsed⟩ := ParentSeedCandidates.parsed _ parent (Finset.mem_toList.mp named)
    rw [same,rejected] at parsed
    contradiction
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl
  · simp only [CausalStreamExposure.touches,Bool.false_eq_true,not_false_eq_true]
  · simp only [CausalStreamExposure.touches,different,false_and,decide_false,Bool.false_eq_true,not_false_eq_true]

end
end FormalProof4FHE.HasteBoots.ParentSeedCompletion
