module
public import FormalProof4FHE.HasteBoots.HadamardNTTEnforcement
public import FormalProof4FHE.HasteBoots.NTTConditionalSoundness
@[expose] public section

/-! Average original NTT risk over actual reached Hadamard prefixes. The
conditional arithmetic/PCS rate is uniform, while the enclosing short-circuit
program pays the shared collision charge exactly once. -/
namespace FormalProof4FHE.HasteBoots.HadamardNTTProbability
open OracleSpec OracleComp
noncomputable section
variable {F K Input Digest Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  {b c r k n count front suffix m queries height : ℕ}
  [SampleableType Digest] [SampleableType F] [SampleableType (Fin r → F)]
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

abbrev Outcome :=
  HadamardNTTSourceAssociation.FirstOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (n := n)
      (count := count) (front := front) (queries := queries) (height := height) ×
    Option (HadamardNTTSourceAssociation.SecondOutcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r)
      (k := k) (front := front) (queries := queries) (height := height))

/-- One row-detection/compression loss and the two original PCS batch errors. -/
def rate
    (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (radius : ℕ) : ENNReal :=
  ((((r : ENNReal)/Fintype.card F)^k) +
    (c : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) +
  (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) ns.domain radius +
    JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) ns.domain radius)

/-- The reached NTT keeps its actual incoming history. The conditional safe
bound is averaged only over supported Hadamard outcomes; skipped paths add zero. -/
theorem safe_risk_bound [NeZero m] [NeZero b]
    (coefficient : Digest) (expected : Fin count → Digest)
    (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ns.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (encoding : hs.encoding = ns.encoding) :
    Pr{let outcome ← (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy initial)}[
      ∃ second, outcome.2 = some second ∧
        OwnedNTTSoundness.OriginalRisk
          (CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns)
          dummy capacity radius second ∧
        ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2] ≤ rate (K := K) ns radius := by
  let h := CallerBoundStageRoots.hadamard expected publicRoots hs
  let t := CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns
  unfold HadamardNTTComposition.witness ShortCircuitStageHistory.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro first firstSupported
  by_cases go : AuthenticatedZeroCheck.accepted first.2.1 = true
  · have projected : ((first.1.1,first.2.1),first.2.2) ∈ support
        ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
          (RecordedSourceCoherence.Shape Cfg height)) (AuthenticatedZeroCheck.program h)).run initial) := by
      unfold AuthenticatedZeroCheck.program
      rw [←MultiCommitmentPrefix.project_witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests h.tag h.factors) h.commit (AuthenticatedZeroCheck.continuation h) initial,
        support_map]
      exact Set.mem_image_of_mem _ firstSupported
    have incoming := CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (RecordedSourceCoherence.Shape Cfg height) (AuthenticatedZeroCheck.program h) initial audited _ projected
    rw [encoding] at incoming
    have conditional := NTTConditionalSoundness.original_safe_bound t basis dummy enough capacity radius small first.2.2 incoming
    simp only [go,ite_true,prEvent_norm]
    rw [encoding]
    convert conditional using 1
    · apply prEvent_congr
      intro outcome
      rcases outcome with ⟨⟨⟨roots,privateMemory⟩,before⟩,⟨packet,results⟩,after⟩
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨second,equal,risk,safe⟩
        subst second
        exact ⟨risk,safe⟩
      · rintro ⟨risk,safe⟩
        exact ⟨_,rfl,risk,safe⟩
    · rfl
  · simp [go,prEvent_norm]

/-- A supported caller-event reduction to reached original NTT risk or the
shared collision event pays the averaged NTT rate and ONE caller hash charge. -/
theorem covered_bound [NeZero m] [NeZero b] [Fintype Digest]
    (coefficient : Digest) (expected : Fin count → Digest)
    (publicRoots : PBSHadamard.Factor count → Digest) (factor : PBSHadamard.Factor count)
    (ns : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme F (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ns.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (encoding : hs.encoding = ns.encoding)
    (event : Outcome (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n)
      (count := count) (front := front) (queries := queries) (height := height) → Prop)
    (coverage : ∀ outcome ∈ support (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy
        (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))), event outcome →
      (∃ second, outcome.2 = some second ∧ OwnedNTTSoundness.OriginalRisk
        (CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns)
        dummy capacity radius second) ∨
      (match outcome.2 with
        | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
        | some second => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2)) :
    Pr{let outcome ← (HadamardNTTComposition.witness coefficient expected publicRoots factor ns hs dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[event outcome] ≤ rate (K := K) ns radius +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (HadamardNTTComposition.program coefficient expected publicRoots factor ns hs)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have arithmetic := safe_risk_bound coefficient expected publicRoots factor ns hs basis dummy enough capacity radius small
    _ ⟨initial.1,fun _ => initial.2.2⟩ encoding
  have hash := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (RecordedSourceCoherence.Shape Cfg height) (HadamardNTTComposition.program coefficient expected publicRoots factor ns hs)
  rw [←HadamardNTTComposition.project_witness coefficient expected publicRoots factor ns hs dummy
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at hash
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    (∃ second, outcome.2 = some second ∧ OwnedNTTSoundness.OriginalRisk
      (CallerBoundStageRoots.ntt coefficient (OwnedHadamardSoundness.roots expected publicRoots factor) ns)
      dummy capacity radius second ∧ ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2) ∨
    (match outcome.2 with
      | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
      | some second => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2)) ?_)
  · apply (prEvent_or_le _ _ _).trans
    apply add_le_add arithmetic
    convert hash using 1
    apply prEvent_congr
    intro outcome
    cases outcome.2 <;> rfl
  · intro outcome supported failed
    rcases coverage outcome supported failed with risk | bad
    · rcases outcome with ⟨first,optional⟩
      obtain ⟨second,reached,risk⟩ := risk
      change optional = some second at reached
      subst optional
      by_cases bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2
      · exact Or.inr bad
      · exact Or.inl ⟨second,rfl,risk,bad⟩
    · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.HadamardNTTProbability
