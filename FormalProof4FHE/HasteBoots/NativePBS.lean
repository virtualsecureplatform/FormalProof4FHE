module

public import FormalProof4FHE.HasteBoots.NativeKeySwitch
public import FormalProof4FHE.HasteBoots.ApplicationKnowledge

@[expose] public section

/-!
# Independent reference NAND/PBS computation and trace relation

Public preprocessing, coefficient-domain binary blind rotation, the q/8 body
bias, one-block key switching and partial extraction are composed here.
This relation contains no cryptographic verifier or acceptance predicate.
NTT/key-layout equivalence and enforcement by the actual proof-system stages
remain open. Knowledge below concerns this reference relation only.
-/

namespace FormalProof4FHE.HasteBoots.NativePBS

open NativeBlindRotation

variable {q n dimension brLevels ksLevels : ℕ} [NeZero n]

structure PublicKey (q n dimension brLevels ksLevels : ℕ) where
  blind : Fin dimension → Control q n brLevels
  switching : NativeKeySwitch.Key q n ksLevels

abbrev Inputs (q dimension : ℕ) := NativePublic.Ciphertext q dimension ×
  NativePublic.Ciphertext q dimension

def controls (key : PublicKey q n dimension brLevels ksLevels)
    (front : NativePublic.Frontend q dimension n) : Controls q n brLevels :=
  List.ofFn (fun i => (key.blind i, front.rotations i))

/-- Reinterpret the public flat initial accumulator as nonce/body coefficient arrays. -/
def initial (front : NativePublic.Frontend q dimension n) : Cipher q n :=
  fun half i => front.initial ⟨(if half then n else 0) + i.val, by
    have := i.isLt
    cases half <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

def bias (acc : Cipher q n) : Cipher q n :=
  fun half i => if half && (i.val == 0) then acc half i + (q / 8 : ℕ) else acc half i

/-- Deterministic coefficient-domain evaluator using only public evaluation rows. -/
def evaluate (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension) :
    NativePublic.Ciphertext q dimension :=
  let front := NativePublic.frontend (n := n) stride input.1 input.2
  let acc := run brBits (controls key front) (initial front)
  NativeKeySwitch.extract shape (NativeKeySwitch.switch ksBits key.switching (bias acc))

structure Trace (q n : ℕ) where
  blind : List (StepTrace q n)
  accumulator : Cipher q n
  finalStage : NativeKeySwitch.Trace q n

/-- Complete reference arithmetic trace constraints, independent of proof acceptance. -/
def Relation (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension)
    (output : NativePublic.Ciphertext q dimension) (trace : Trace q n) : Prop :=
  let front := NativePublic.frontend (n := n) stride input.1 input.2
  ValidTrace brBits (controls key front) (initial front) trace.blind trace.accumulator ∧
  NativeKeySwitch.Valid ksBits key.switching shape (bias trace.accumulator) trace.finalStage output

/-- A satisfying trace determines the same unique output as public reference evaluation. -/
theorem relation_output (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension)
    (output : NativePublic.Ciphertext q dimension) (trace : Trace q n)
    (valid : Relation brBits ksBits stride shape key input output trace) :
    output = evaluate brBits ksBits stride shape key input := by
  obtain ⟨hb, hk⟩ := valid
  have ha := validTrace_output brBits _ _ _ _ hb
  have ho := NativeKeySwitch.valid_output ksBits key.switching shape _ _ output hk
  rw [ha] at ho
  exact ho

def makeTrace (brBits ksBits stride : ℕ)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension) : Trace q n :=
  let front := NativePublic.frontend (n := n) stride input.1 input.2
  let acc := run brBits (controls key front) (initial front)
  ⟨NativeBlindRotation.makeTrace brBits (controls key front) (initial front), acc,
    NativeKeySwitch.makeTrace ksBits key.switching (bias acc)⟩

theorem makeTrace_valid (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension) :
    Relation brBits ksBits stride shape key input
      (evaluate brBits ksBits stride shape key input) (makeTrace brBits ksBits stride key input) :=
  ⟨NativeBlindRotation.makeTrace_valid _ _ _, NativeKeySwitch.makeTrace_valid _ _ _ _⟩

/-- Existence of an application witness is exactly correctness of the reference output. -/
theorem exists_trace_iff (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension)
    (output : NativePublic.Ciphertext q dimension) :
    (∃ trace, Relation brBits ksBits stride shape key input output trace) ↔
      output = evaluate brBits ksBits stride shape key input := by
  constructor
  · rintro ⟨trace, valid⟩
    exact relation_output _ _ _ _ _ _ _ _ valid
  · intro h
    subst output
    exact ⟨_, makeTrace_valid _ _ _ _ _ _⟩

/-- Public reference evaluation with its independently checked arithmetic witness. -/
def publicEvaluator (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension) :
    NativePublic.Ciphertext q dimension × Trace q n :=
  ⟨evaluate brBits ksBits stride shape key input, makeTrace brBits ksBits stride key input⟩

/-- Actual instantiation of the generic public-evaluator extraction bridge. -/
def extract (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension)
    (claimed : NativePublic.Ciphertext q dimension) : Option (Trace q n) :=
  ApplicationKnowledge.extract (publicEvaluator brBits ksBits stride shape) key input claimed

theorem extraction_succeeds_iff (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (input : Inputs q dimension)
    (claimed : NativePublic.Ciphertext q dimension) :
    (∃ trace, extract brBits ksBits stride shape key input claimed = some trace ∧
      Relation brBits ksBits stride shape key input claimed trace) ↔
      evaluate brBits ksBits stride shape key input = claimed :=
  ApplicationKnowledge.succeeds_iff (publicEvaluator brBits ksBits stride shape)
    (Relation brBits ksBits stride shape) key input claimed (makeTrace_valid _ _ _ _ _ _)

/-- Any eventual false-output bound transfers to this reference application extractor
with no additional knowledge-error loss, for the same joint adaptive execution law. -/
theorem extractionFailure_measure_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (brBits ksBits stride : ℕ) (shape : dimension ≤ n)
    (key : PublicKey q n dimension brLevels ksLevels) (inputs : Ω → Inputs q dimension)
    (claims : Ω → NativePublic.Ciphertext q dimension) (accept : Ω → Prop) :
    μ {ω | accept ω ∧ ¬ ∃ trace,
      extract brBits ksBits stride shape key (inputs ω) (claims ω) = some trace ∧
      Relation brBits ksBits stride shape key (inputs ω) (claims ω) trace} =
    μ {ω | accept ω ∧ evaluate brBits ksBits stride shape key (inputs ω) ≠ claims ω} :=
  ApplicationKnowledge.failure_measure_eq_falseOutput μ
    (publicEvaluator brBits ksBits stride shape) (Relation brBits ksBits stride shape)
    key inputs claims accept (fun input => makeTrace_valid _ _ _ _ _ input)

end FormalProof4FHE.HasteBoots.NativePBS
