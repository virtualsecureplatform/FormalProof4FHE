module
public import FormalProof4FHE.HasteBoots.CanonicalSafeIdentityKernel
@[expose] public section

/-! Canonical independent-radius healing pays the same actual input-bound
original equation-count score as the preceding scalar analysis. -/
namespace FormalProof4FHE.HasteBoots.CanonicalScalarPositionKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
open ScalarPositionKernel (key score charge packet_key ordinal_lt charge_measurable)
noncomputable section


def Event {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ input ordinal, CanonicalSafeIdentityKernel.Event program position input ordinal dummy world

theorem jobs_conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (count : ℕ)
    (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | ∃ i : Fin count, CanonicalSafeIdentityKernel.Event program position input i.val dummy other} ≤
        (count : ENNReal) * ((4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)) := by
  have union : {other | ∃ i : Fin count, CanonicalSafeIdentityKernel.Event program position input i.val dummy other} =
      ⋃ i : Fin count, {other | CanonicalSafeIdentityKernel.Event program position input i.val dummy other} := by ext other; simp
  rw [union]
  have bounded := (measure_iUnion_le (fun i : Fin count => {other | CanonicalSafeIdentityKernel.Event program position input i.val dummy other})
    (μ := law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])).trans
    (ENNReal.tsum_le_tsum (fun i => CanonicalSafeIdentityKernel.conditional program position input i.val world dummy))
  simpa [tsum_fintype,nsmul_eq_mul] using bounded

theorem conditional {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position dummy other} ≤
        charge program position world := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  change _ ≤ match key program position world with
    | none => (0 : ENNReal)
    | some input => match ScalarRecoveredReplay.recover input with
      | none => (0 : ENNReal)
      | some configuration => (configuration.view.history.statement.infos.val.length : ENNReal) * ((4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ))
  cases selected : key program position world with
  | none =>
    have included := FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy) (fun _ => False) (by
      intro other fiber occurred
      obtain ⟨input,ordinal,⟨⟨packet,_⟩,_⟩⟩ := occurred
      have read := packet_key packet fiber
      rw [selected] at read
      cases read)
    simpa using included
  | some input =>
    simp only []
    cases found : ScalarRecoveredReplay.recover input with
    | none =>
      have included := FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy) (fun _ => False) (by
        intro other fiber occurred
        obtain ⟨otherInput,ordinal,⟨⟨packet,_⟩,_⟩⟩ := occurred
        have inputEq := Option.some.inj ((packet_key packet fiber).symm.trans selected)
        subst otherInput
        have recovered := packet.found
        rw [packet.classed.property.1,found] at recovered
        cases recovered)
      simpa using included
    | some configuration =>
      apply (FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy)
        (fun other => ∃ i : Fin configuration.view.history.statement.infos.val.length,
          CanonicalSafeIdentityKernel.Event program position input i.val dummy other) (by
          intro other fiber occurred
          obtain ⟨otherInput,ordinal,⟨⟨packet,healing⟩,safe⟩⟩ := occurred
          have inputEq := Option.some.inj ((packet_key packet fiber).symm.trans selected)
          subst otherInput
          have recovered := packet.found
          rw [packet.classed.property.1] at recovered
          have configurationEq := Option.some.inj (recovered.symm.trans found)
          have inside := ordinal_lt packet
          rw [configurationEq] at inside
          exact ⟨⟨ordinal,inside⟩,⟨packet,healing⟩,safe⟩)).trans
      exact jobs_conditional program position input configuration.view.history.statement.infos.val.length world dummy

theorem bound {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    law {world | Event program position dummy world} ≤ ∫⁻ world, charge program position world ∂law := by
  apply OracleFiberOuterBound.score_bound (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))
    {world | Event program position dummy world} (fun packet => score packet.1.1.1.1)
  intro world
  exact conditional program position world dummy


end
end FormalProof4FHE.HasteBoots.CanonicalScalarPositionKernel
