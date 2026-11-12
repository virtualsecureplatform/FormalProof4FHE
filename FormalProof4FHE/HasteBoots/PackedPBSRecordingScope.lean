module
public import FormalProof4FHE.HasteBoots.LinearRecordingScope
public import FormalProof4FHE.HasteBoots.NTTRecordingScope
public import FormalProof4FHE.HasteBoots.ZeroCheckRecordingScope
public import FormalProof4FHE.HasteBoots.PackedPBSFirstReconstruction
@[expose] public section

/-! Derive scope for the assembled pre-comparison PBS program from its actual
callback scopes and trusted tags. Public root/transform overrides are retained. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSRecordingScope
open OracleSpec OracleComp CheckpointRecordScope CheckpointProgramScope
open NativeRootMessage (Digest)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

/-- Fixed original digit/key roots do not grant extra callback recording sites. -/
theorem hadamard_callbacks (scope : Cfg → Prop) (restricted : ZeroCheckRecordingScope.Callbacks scope hs) :
    ZeroCheckRecordingScope.Callbacks scope (PackedPBSHadamardNTT.hadamard family hs) := by
  constructor
  · apply bind_scoped scope _ _
    · exact bind_scoped scope _ _ restricted.commit (fun _ => pure_scoped scope _)
    · intro _
      exact pure_scoped scope _
  · exact restricted.firstRespond
  · exact restricted.afterFirst
  · exact restricted.send
  · exact restricted.afterChallenge
  · exact restricted.receiveValues
  · exact restricted.bindValues
  · exact restricted.openings

/-- The original NTT roots and proved transform change no callback privilege. -/
theorem ntt_callbacks (scope : Cfg → Prop) (slot : Fin (2*d+1)) (memory : Memory)
    (restricted : NTTRecordingScope.Callbacks scope (base slot memory)) :
    NTTRecordingScope.Callbacks scope (PackedPBSNTTLoop.factory length psi primitive family base slot memory) := by
  constructor
  · exact bind_scoped scope _ _ restricted.commit (fun _ => pure_scoped scope _)
  · exact restricted.receive
  · exact restricted.bindRows
  · exact restricted.afterQuery
  · exact restricted.openings

/-- Reconstruction retains caller-selected roots and native interpolation. -/
theorem reconstruction_callbacks (scope : Cfg → Prop) (memory : Memory)
    (restricted : LinearRecordingScope.Callbacks scope (linearBase memory)) :
    LinearRecordingScope.Callbacks scope
      (PackedPBSFirstReconstruction.reconstruction family inputs nodesEnough radix linearBase false memory) :=
  LinearRecordingScope.native_callbacks scope q nodesEnough _
    (LinearRecordingScope.owned_callbacks scope _ _ radix (linearBase memory) restricted)

variable [DecidableEq Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]

/-- The ordered NTT loop accounts for all root-recording callbacks at the
actual private memory handed to each child, including early rejection. -/
theorem ntt_program (scope : Cfg → Prop)
    (restricted : ∀ slot memory, NTTRecordingScope.Callbacks scope (base slot memory))
    (tags : ∀ slot memory side, scope ((base slot memory).tag side)) (memory : Memory) :
    Scoped scope (PackedPBSNTTLoop.program length psi primitive family base memory) := by
  unfold PackedPBSNTTLoop.program NTTSequence.program
  apply shortCircuit_scoped scope _ _ _ memory
  intro slot _ incoming
  unfold NTTSequence.step
  apply bind_scoped scope _ _
    (NTTRecordingScope.program scope _
      (ntt_callbacks length psi primitive family base scope slot incoming (restricted slot incoming))
      (tags slot incoming))
  intro _
  exact pure_scoped scope _

variable [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]

/-- The complete Hadamard-before-NTT ordering retains the callbacks' scope. -/
theorem hadamard_ntt_program (scope : Cfg → Prop)
    (had : ZeroCheckRecordingScope.Callbacks scope hs)
    (ntt : ∀ slot memory, NTTRecordingScope.Callbacks scope (base slot memory))
    (hadTags : ∀ factor, scope (hs.tag factor))
    (nttTags : ∀ slot memory side, scope ((base slot memory).tag side)) :
    Scoped scope (PackedPBSHadamardNTT.program length psi primitive family base hs) := by
  unfold PackedPBSHadamardNTT.program
  apply bind_scoped scope _ _
    (ZeroCheckRecordingScope.program scope _ (hadamard_callbacks family hs scope had) (fun factor _ => hadTags factor))
  intro first
  split
  · exact bind_scoped scope _ _
      (ntt_program length psi primitive family base scope ntt nttTags first.2.2.memory)
      (fun _ => pure_scoped scope _)
  · exact pure_scoped scope _

/-- Structural scope for the actual whole pre-comparison program is derived
from callback scope and trusted context tags; it is not an incoming certificate. -/
theorem program (scope : Cfg → Prop)
    (had : ZeroCheckRecordingScope.Callbacks scope hs)
    (ntt : ∀ slot memory, NTTRecordingScope.Callbacks scope (base slot memory))
    (linear : ∀ memory, LinearRecordingScope.Callbacks scope (linearBase memory))
    (hadTags : ∀ factor, scope (hs.tag factor))
    (nttTags : ∀ slot memory side, scope ((base slot memory).tag side))
    (linearTags : ∀ memory factor, scope ((linearBase memory).tag factor)) :
    Scoped scope (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase) := by
  unfold PackedPBSFirstReconstruction.program
  apply bind_scoped scope _ _
    (hadamard_ntt_program length psi primitive family base hs scope had ntt hadTags nttTags)
  intro before
  cases before.2 with
  | none =>
    dsimp only
    exact pure_scoped scope _
  | some later =>
    dsimp only
    split
    · exact bind_scoped scope _ _
        (LinearRecordingScope.program scope _
          (reconstruction_callbacks family inputs nodesEnough radix linearBase scope later.memory (linear later.memory))
          (linearTags later.memory)) (fun _ => pure_scoped scope _)
    · exact pure_scoped scope _

end
end FormalProof4FHE.HasteBoots.PackedPBSRecordingScope
