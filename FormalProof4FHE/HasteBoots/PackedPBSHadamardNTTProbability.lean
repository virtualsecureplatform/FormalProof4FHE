module
public import FormalProof4FHE.HasteBoots.PackedPBSHadamardNTT
@[expose] public section

/-! Quantitative original NTT risks after the actual original-root Hadamard
prefix. Local safe errors average over supported prefix outcomes, and the
complete short-circuit prefix pays the shared collision charge once. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHadamardNTTProbability
open OracleSpec OracleComp
open NativeRootMessage (Digest)
noncomputable section
variable {q log count b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {K Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- The full original-slot loop keeps the real Hadamard-returned memory and
state. Its safe-rate sum is averaged only over supported Hadamard outcomes. -/
theorem safe_ntt_risk_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial)}[
      ∃ later, outcome.2 = some later ∧ NTTSequenceSoundness.AnySafeRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1] ≤
      ((List.finRange (count+1)).map epsilon).sum := by
  let h := PackedPBSHadamardNTT.hadamard family hs
  let factory := PackedPBSNTTLoop.factory length psi primitive family base
  unfold PackedPBSHadamardNTT.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro first firstSupported
  by_cases passes : AuthenticatedZeroCheck.accepted first.2.1 = true
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
    have conditional := NTTLoopProbability.native_safe_union_bound factory hs.encoding dummy
      (List.finRange (count+1)) basis enough capacity radius epsilon
      (fun slot _ state => encoding slot state) (fun slot _ state => small slot state)
      (fun slot _ state => calibrated slot state) first.2.1.2.memory first.2.2 incoming
    simp only [passes,ite_true,prEvent_norm]
    convert conditional using 1
    apply prEvent_congr
    intro later
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨selected,equal,event⟩
      subst selected
      exact event
    · intro event
      exact ⟨later,rfl,event⟩
  · simp [passes,prEvent_norm]

/-- All reached original NTT risks share ONE collision charge on the entire
Hadamard-plus-loop program, including the original prefix's hash work. -/
theorem ntt_risk_bound [Fintype Digest] [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (family : PackedPBSOriginalReferences.Family count)
    (base : Fin (count+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      b c r k front suffix m queries height)
    (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor count) (PBSHadamard.Term count)
      FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b)
    (radius : Fin (count+1) → ℕ) (epsilon : Fin (count+1) → ENNReal)
    (encoding : ∀ slot incoming, (base slot incoming).encoding = hs.encoding)
    (small : ∀ slot incoming, ((radius slot : ℕ) : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (base slot incoming).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ slot incoming,
      HadamardNTTProbability.rate (K := K) (base slot incoming) (radius slot) ≤ epsilon slot) :
    Pr{let outcome ← (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ∃ later, outcome.2 = some later ∧ NTTLoopProbability.AnyRisk
        (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1] ≤
      ((List.finRange (count+1)).map epsilon).sum +
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
      (PackedPBSHadamardNTT.program length psi primitive family base hs)
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have arithmetic := safe_ntt_risk_bound length psi primitive family base hs basis dummy enough capacity radius epsilon
    encoding small calibrated _ ⟨initial.1,fun _ => initial.2.2⟩
  have hash := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (RecordedSourceCoherence.Shape Cfg height) (PackedPBSHadamardNTT.program length psi primitive family base hs)
  rw [←PackedPBSHadamardNTT.project_witness length psi primitive family base hs dummy
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at hash
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    (∃ later, outcome.2 = some later ∧ NTTSequenceSoundness.AnySafeRisk
      (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius later.1) ∨
    (match outcome.2 with
      | none => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.1.2.2
      | some later => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) later.2)) ?_)
  · apply (prEvent_or_le _ _ _).trans
    apply add_le_add arithmetic
    convert hash using 1
    apply prEvent_congr
    intro outcome
    cases outcome.2 <;> rfl
  · intro outcome supported event
    rcases outcome with ⟨first,optional⟩
    obtain ⟨later,reached,entry,member,risk⟩ := event
    change optional = some later at reached
    subst optional
    by_cases bad : CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) entry.2.2.2.2
    · have reachedLoop := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy _ first later supported
      exact Or.inr (NTTSequenceSoundness.child_bad_persistent (PackedPBSNTTLoop.factory length psi primitive family base)
        hs.encoding dummy (List.finRange (count+1)) first.2.1.2.memory first.2.2 later reachedLoop.2.2 entry member bad)
    · exact Or.inl ⟨later,rfl,entry,member,risk,bad⟩

end
end FormalProof4FHE.HasteBoots.PackedPBSHadamardNTTProbability
