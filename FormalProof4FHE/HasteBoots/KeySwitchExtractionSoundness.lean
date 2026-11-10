module
public import FormalProof4FHE.HasteBoots.KeySwitchExtraction
public import FormalProof4FHE.HasteBoots.PackedZeroSharedSoundness
@[expose] public section

/-! Arithmetic error of the native extraction ZeroCheck on one shared run.
Public mask and target are fixed from the original endpoint/output; only the
increment is private. TruthfulResult is deliberately not replaced by native
acceptance: its single private opening still needs authentication. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchExtractionSoundness
open OracleSpec OracleComp BinaryTree
noncomputable section

abbrev FirstMessage (q k : ℕ) := Fin k → Fin ((2*k-1)*2+1) → ZMod q
abbrev Message (q k : ℕ) := Fin ((2*k-1)*3+1) → ZMod q

def error (q c k : ℕ) : ENNReal :=
  ((c : ENNReal)/q)^k + (((((2*k-1)*2+1 : ℕ) : ENNReal)/q)^k) +
    (c : ENNReal)*(((((2*k-1)*3 : ℕ) : ENNReal)/q)^k)

structure Prover (q c k : ℕ) (Cfg Input Digest Memory : Type) where
  initial : Memory
  firstRespond : PackedZeroReduction.Points (ZMod q) c k → Memory →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (FirstMessage q k × Memory)
  afterFirst : PackedZeroReduction.Points (ZMod q) c k → FirstMessage q k × Memory → PackedZeroReduction.Coins (ZMod q) k →
    OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory
  send : ℕ → Memory → (Fin k → ZMod q) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Message q k × Memory)
  afterChallenge : Memory → (Fin k → ZMod q) → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory

variable {q c lanes dimension : ℕ} [Fact q.Prime]
  {Cfg Input Digest Memory Payload : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (Fin c → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]

def program (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (enough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1) (prover : Prover q c (2^lanes) Cfg Input Digest Memory) :=
  PackedZeroOracle.program (NativePackedInterpolation.nodes q (enough.trans firstSmall))
    (fun message point => NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive q firstSmall) (message point))
    (NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive q roundSmall))
    prover.firstRespond prover.afterFirst prover.send prover.afterChallenge prover.initial

/-- The complete three-term arithmetic error, with actual adversarial shared
callbacks, stopping behavior and returned cache. No opening error is omitted
from an acceptance claim: this event is a truthful ZeroCheck subclaim only. -/
theorem miss_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (hashShape : Cfg → Skeleton)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (enough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1) (prover : Prover q c (2^lanes) Cfg Input Digest Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) hashShape)
    (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc increment : NativeBlindRotation.Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (wrong : ¬CanonicalKeySwitch.Extraction shape acc increment output) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy hashShape)
      (program firstSmall roundSmall enough prover)).run state}[
      PackedZeroOracle.TruthfulResult (NativePackedInterpolation.nodes q (enough.trans firstSmall))
        PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
        (KeySwitchExtraction.tables (c := c) (lanes := lanes) positive acc increment output) outcome.1] ≤
      error q c (2^lanes) := by
  have bound := PackedZeroSharedSoundness.native_soundness_bound enc dummy hashShape q 2 firstSmall roundSmall enough
    PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices PBSHadamard.degree_bound
    (KeySwitchExtraction.tables (c := c) (lanes := lanes) positive acc increment output)
    prover.firstRespond prover.afterFirst prover.send prover.afterChallenge prover.initial state
    (KeySwitchExtraction.false_zero_relation shape positive acc increment output wrong)
  simpa only [program,error,ZMod.card] using bound

theorem wrong_output_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (hashShape : Cfg → Skeleton)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (enough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1) (prover : Prover q c (2^lanes) Cfg Input Digest Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) hashShape)
    (bits : ℕ) {levels : ℕ} (key : NativeKeySwitch.Key q (2^(c+lanes)) levels)
    (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc increment : NativeBlindRotation.Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (product : increment = CanonicalKeySwitch.increment bits key (acc false))
    (wrong : output ≠ NativeKeySwitch.extract shape (CanonicalKeySwitch.switch bits key acc)) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy hashShape)
      (program firstSmall roundSmall enough prover)).run state}[
      PackedZeroOracle.TruthfulResult (NativePackedInterpolation.nodes q (enough.trans firstSmall))
        PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices
        (KeySwitchExtraction.tables (c := c) (lanes := lanes) positive acc increment output) outcome.1] ≤
      error q c (2^lanes) := by
  apply miss_bound enc dummy hashShape firstSmall roundSmall enough prover state shape positive acc increment output
  intro checked
  have extracted := CanonicalKeySwitch.extract_of_constraints shape acc increment output checked
  rw [product] at extracted
  exact wrong extracted

end
end FormalProof4FHE.HasteBoots.KeySwitchExtractionSoundness
