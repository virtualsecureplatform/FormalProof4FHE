module
public import FormalProof4FHE.HasteBoots.PackedPBSReconstructionCoherence
@[expose] public section

/-! Reconstruction risk is averaged over actual accepted NTT-loop returns.
The enclosing verifier keeps ownership of the single final collision charge. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSFirstReconstructionProbability
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (reconstruction)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- The newly reached reconstruction uses its actual inherited audit and
private memory, paying the conditional original-registry rate exactly once. -/
theorem safe_linear_risk_bound [NeZero m] [NeZero b]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ) (epsilon : ENNReal)
    (encoding : ∀ memory, (linearBase memory).encoding = hs.encoding)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (linearBase memory).domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries)
        (linearBase memory).domain radius ≤ epsilon)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy initial)}[
      ∃ later child, outcome.1.2 = some later ∧ outcome.2 = some child ∧
        OwnedLinearSoundness.OriginalRisk (reconstruction family inputs nodesEnough radix linearBase false later.1.memory)
          dummy capacity radius child ∧
        ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) child.2.2] ≤ epsilon := by
  unfold PackedPBSFirstReconstruction.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have projected : (PackedPBSFirstReconstruction.eraseBefore before,PackedPBSFirstReconstruction.beforeState before) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (RecordedSourceCoherence.Shape Cfg height)) (PackedPBSHadamardNTT.program length psi primitive family base hs)).run initial) := by
    rw [←PackedPBSFirstReconstruction.project_before length psi primitive family base hs dummy initial,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (RecordedSourceCoherence.Shape Cfg height) (PackedPBSHadamardNTT.program length psi primitive family base hs) initial audited _ projected
  cases equal : before.2 with
  | none => simp [equal,prEvent_norm]
  | some later =>
    by_cases passed : later.1.accepted = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) later.2 := by
        simpa only [PackedPBSFirstReconstruction.beforeState,equal] using incoming
      let l := reconstruction family inputs nodesEnough radix linearBase false later.1.memory
      have linearAudit : CheckpointExecution.Audited (linearBase later.1.memory).encoding dummy
          (RecordedSourceCoherence.Shape Cfg height) later.2 := by
        rw [encoding]
        exact stateAudit
      have conditional := DecompositionConditionalSoundness.native_original_safe_bound q nodesEnough
        (inputs.roots false) (fun level => family.coefficients (PackedPBSDecompositionReferences.digitSlot false level))
        radix (linearBase later.1.memory) basis dummy enough capacity radius (small later.1.memory) later.2 linearAudit
      change Pr{let child ← (MultiCommitmentPrefix.witness l.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
        (CommittedJointMatrixOpening.requests l.tag (AuthenticatedLinear.factors (2*d+2))) l.commit
        (AuthenticatedLinear.continuation l) later.2)}[
          OwnedLinearSoundness.OriginalRisk l dummy capacity radius child ∧
          ¬CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) child.2.2] ≤ _ at conditional
      have enc : l.encoding = hs.encoding := encoding later.1.memory
      rw [enc] at conditional
      have bound := conditional.trans (calibrated later.1.memory)
      simp only [equal,passed,ite_true,prEvent_norm]
      convert bound using 1
      apply prEvent_congr
      intro result
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨chosen,selected,sameChosen,sameSelected,risk,safe⟩
        subst chosen
        subst selected
        exact ⟨risk,safe⟩
      · rintro ⟨risk,safe⟩
        exact ⟨later,result,rfl,rfl,risk,safe⟩
    · simp [equal,passed,prEvent_norm]

end
end FormalProof4FHE.HasteBoots.PackedPBSFirstReconstructionProbability
