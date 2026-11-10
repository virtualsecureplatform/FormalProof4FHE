module
public import FormalProof4FHE.HasteBoots.NativePBS
public import FormalProof4FHE.HasteBoots.CanonicalKeySwitch
public import FormalProof4FHE.HasteBoots.PackedBlindRotationTrace
@[expose] public section

/-! Corrected coefficient-domain PBS reference. Public preprocessing, original
blind-rotation rows and q/8 bias are reused; the final stage decomposes the
canonical negative mask, as the actual native implementation does. The frozen
NativePBS evaluator uses a different key-switch reference and is not the target
of this corrected arithmetic relation. Verifier acceptance remains separate. -/
namespace FormalProof4FHE.HasteBoots.CanonicalPBS
open NativeBlindRotation
variable {q n dimension brLevels ksLevels : ℕ} [NeZero n]

def evaluate (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension) :
    NativePublic.Ciphertext q dimension :=
  let front := NativePublic.frontend (n := n) stride input.1 input.2
  let acc := run brBits (NativePBS.controls key front) (NativePBS.initial front)
  NativeKeySwitch.extract shape (CanonicalKeySwitch.switch ksBits key.switching (NativePBS.bias acc))

structure Trace (q n : ℕ) where
  blind : List (StepTrace q n)
  accumulator : Cipher q n
  finalStage : CanonicalKeySwitch.Trace q n

def Relation (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (output : NativePublic.Ciphertext q dimension) (trace : Trace q n) : Prop :=
  let front := NativePublic.frontend (n := n) stride input.1 input.2
  ValidTrace brBits (NativePBS.controls key front) (NativePBS.initial front) trace.blind trace.accumulator ∧
  CanonicalKeySwitch.Valid ksBits key.switching shape (NativePBS.bias trace.accumulator) trace.finalStage output

theorem relation_output (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (output : NativePublic.Ciphertext q dimension) (trace : Trace q n)
    (valid : Relation brBits ksBits stride shape key input output trace) :
    output = evaluate brBits ksBits stride shape key input := by
  obtain ⟨blind,switched⟩ := valid
  have accumulator := validTrace_output brBits _ _ _ _ blind
  have result := CanonicalKeySwitch.valid_output ksBits key.switching shape _ _ output switched
  rw [accumulator] at result
  exact result

def makeTrace (brBits ksBits stride : ℕ)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension) : Trace q n :=
  let front := NativePublic.frontend (n := n) stride input.1 input.2
  let acc := run brBits (NativePBS.controls key front) (NativePBS.initial front)
  ⟨NativeBlindRotation.makeTrace brBits (NativePBS.controls key front) (NativePBS.initial front),acc,
    CanonicalKeySwitch.makeTrace ksBits key.switching (NativePBS.bias acc)⟩

theorem makeTrace_valid (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension) :
    Relation brBits ksBits stride shape key input (evaluate brBits ksBits stride shape key input) (makeTrace brBits ksBits stride key input) :=
  ⟨NativeBlindRotation.makeTrace_valid _ _ _,CanonicalKeySwitch.makeTrace_valid _ _ _ _⟩

/-- A false corrected PBS output violates the complete blind trace or the
canonical negative-mask final stage; no acceptance premise is hidden here. -/
theorem wrong_output_coverage (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : NativePBS.PublicKey q n dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (output : NativePublic.Ciphertext q dimension) (trace : Trace q n)
    (wrong : output ≠ evaluate brBits ksBits stride shape key input) :
    (let front := NativePublic.frontend (n := n) stride input.1 input.2;
      ¬ValidTrace brBits (NativePBS.controls key front) (NativePBS.initial front) trace.blind trace.accumulator) ∨
    ¬CanonicalKeySwitch.Valid ksBits key.switching shape (NativePBS.bias trace.accumulator) trace.finalStage output := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (relation_output brBits ksBits stride shape key input output trace ⟨not_not.mp absent.1,absent.2⟩)

def rounds {r : ℕ} (positive : 0 < dimension) (fits : dimension ≤ 2^r) : PackedAccumulatorTrace.Rounds r :=
  ⟨dimension,positive,fits⟩

/-- The packed blind trace uses exactly the original public frontend rotations
and key rows; the corrected final-stage relation completes the PBS witness. -/
theorem relation_of_packed {c lanes r mc mw ec ew : ℕ} {F : Type} [Field F] [Fact q.Prime]
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1))) (embed : ZMod q →+* F)
    (brBits ksBits stride : ℕ) (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension) (fits : dimension ≤ 2^r)
    (key : NativePBS.PublicKey q (2^(c+lanes)) dimension brLevels ksLevels) (input : NativePBS.Inputs q dimension)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (stages : Fin dimension → PackedBlindRotationTrace.Stages q (c+lanes) brLevels mc mw ec ew)
    (arithmetic : AccumulatorEndpointSoundness.FullHolds (PackedAccumulatorTrace.sources embed (rounds positive fits) tables
      (NativePBS.initial (NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2)) final decompositionA decompositionB))
    (multiplication : PackedBlindRotationTrace.AllHolds psi brBits (rounds positive fits) tables
      (fun i => (key.blind i,(NativePublic.frontend (n := 2^(c+lanes)) stride input.1 input.2).rotations i)) stages)
    (finalStage : CanonicalKeySwitch.Trace q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (switched : CanonicalKeySwitch.Valid ksBits key.switching shape (NativePBS.bias final) finalStage output) :
    Relation brBits ksBits stride shape key input output
      ⟨List.ofFn (AccumulatorTrace.traceAt (rounds positive fits).shape tables),final,finalStage⟩ := by
  constructor
  · exact PackedBlindRotationTrace.validTrace psi primitive embed (rounds positive fits) tables _ final
      decompositionA decompositionB arithmetic brBits _ stages multiplication
  · exact switched

end FormalProof4FHE.HasteBoots.CanonicalPBS
