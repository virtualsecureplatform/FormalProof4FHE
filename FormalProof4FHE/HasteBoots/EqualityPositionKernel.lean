module
public import FormalProof4FHE.HasteBoots.EqualityInputJobCount
@[expose] public section

/-! One original first read pays for every eligible original equality job.
Input bytes conservatively cover the ordered root/job vector; the shared
reference bad event is excluded once before taking finite class unions. -/
namespace FormalProof4FHE.HasteBoots.EqualityPositionKernel
open InputIndexedOracle (Input World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
open ScalarPositionKernel (key)
noncomputable section

def rate : ENNReal := (63 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)

def score {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : ENNReal :=
  match CausalStreamExposure.firstRead OracleProgramMachine.step packet with
  | none => 0
  | some input => (input.length : ENNReal)*rate

def charge {A : Type} (program : Program A) (position : ℕ) (world : World) : ENNReal := score (runPrefix position program world).run

def Event {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) : Prop :=
  ∃ input ordinal, SafeEqualityClassKernel.Event program position input ordinal dummy world

theorem packet_key {A : Type} {program : Program A} {position ordinal : ℕ} {input : Input} {world other : World}
    (packet : EqualityClassKernel.Class program position input ordinal other)
    (same : (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run) : key program position world = some input := by
  have selected := packet.val.family.first.selected
  rw [packet.val.family.first_position,packet.property.1] at selected
  have previous := ParentFactorFiber.old_packet (runPrefix position program) world other same
  rw [previous] at selected
  exact selected

theorem ordinal_lt {A : Type} {program : Program A} {position ordinal : ℕ} {input : Input} {world : World}
    (packet : EqualityClassKernel.Class program position input ordinal world) : ordinal < input.length := by
  have inside := EqualityInputJobCount.ordinal_lt packet.val
  rwa [packet.property.1,packet.property.2] at inside

theorem jobs_conditional {A : Type} (program : Program A) (position : ℕ) (input : Input) (count : ℕ)
    (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])
      {other | ∃ i : Fin count, SafeEqualityClassKernel.Event program position input i.val dummy other} ≤
        (count : ENNReal)*rate := by
  have union : {other | ∃ i : Fin count, SafeEqualityClassKernel.Event program position input i.val dummy other} =
      ⋃ i : Fin count, {other | SafeEqualityClassKernel.Event program position input i.val dummy other} := by ext other; simp
  rw [union]
  have bounded := (measure_iUnion_le (fun i : Fin count => {other | SafeEqualityClassKernel.Event program position input i.val dummy other})
    (μ := law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}])).trans
    (ENNReal.tsum_le_tsum (fun i => SafeEqualityClassKernel.conditional program position input i.val world dummy))
  simpa [tsum_fintype,nsmul_eq_mul,rate] using bounded

theorem conditional {A : Type} (program : Program A) (position : ℕ) (world : World) (dummy : Digest) :
    (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Event program position dummy other} ≤
        charge program position world := by
  let replay := ParentFactorFiber.replay (OracleProgram.prefix_replay position program)
  change _ ≤ match key program position world with
    | none => (0 : ENNReal)
    | some input => (input.length : ENNReal)*rate
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
    apply (FactorPosteriorMismatch.conditional_mono replay world (Event program position dummy)
      (fun other => ∃ i : Fin input.length, SafeEqualityClassKernel.Event program position input i.val dummy other) (by
        intro other fiber occurred
        obtain ⟨otherInput,ordinal,⟨⟨packet,failed⟩,safe⟩⟩ := occurred
        have inputEq := Option.some.inj ((packet_key packet fiber).symm.trans selected)
        subst otherInput
        exact ⟨⟨ordinal,ordinal_lt packet⟩,⟨packet,failed⟩,safe⟩)).trans
    exact jobs_conditional program position input input.length world dummy

theorem charge_measurable {A : Type} (program : Program A) (position : ℕ) : Measurable (charge program position) :=
  OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program) score

theorem bound {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    law {world | Event program position dummy world} ≤ ∫⁻ world, charge program position world ∂law := by
  apply OracleFiberOuterBound.score_bound (ParentFactorFiber.replay (OracleProgram.prefix_replay position program))
    {world | Event program position dummy world} (fun packet => score packet.1.1.1.1)
  intro world
  exact conditional program position world dummy

end
end FormalProof4FHE.HasteBoots.EqualityPositionKernel
