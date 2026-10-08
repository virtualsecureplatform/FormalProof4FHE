/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWBootstrapParameters
import Batteries.Data.Vector.Lemmas

/-!
# Stored evaluation of shared NAND circuits under one GSW key

A program appends gates to an indexed wire table. Every gate refers to two existing
wires; references can be reused arbitrarily, so shared subcircuits are not expanded
into trees. The evaluator computes a gate once and stores its ciphertext before any
later gate reads it. Its public inputs are the program, stored input ciphertexts, and
the same stored controls used throughout. It never receives the secret or wire bits.

The concrete correctness theorem instantiates the checked polynomial-modulus GSW
family. Every wire has the same noise invariant regardless of circuit depth, and an
arbitrary selected output decrypts to the Boolean program result. The output has the
fixed ciphertext type determined by the secret dimension, independent of program size.
The counted evaluator records exactly one gate-operation invocation per gate; it does
not assert a machine-level bit-operation cost for the GSW gate operation itself.
Security of the complete same-key control view remains an ordinary-LWE proof obligation.
-/

namespace FormalProof4FHE.LWE.GSWCircuit

open GSWGadget GSWBootstrap GSWAccumulator

/-- A topologically ordered NAND DAG, with checked references to earlier wires. -/
inductive Program (inputs : ℕ) : ℕ → Type
  | start : Program inputs inputs
  | nand {wires : ℕ} (priorProgram : Program inputs wires) (first second : Fin wires) :
      Program inputs (wires + 1)

/-- Number of actual gates, counting every shared gate once. -/
def gateCount {inputs : ℕ} : {wires : ℕ} → Program inputs wires → ℕ
  | _, .start => 0
  | _, .nand priorProgram _ _ => gateCount priorProgram + 1

theorem wireCount_eq {inputs wires : ℕ} (program : Program inputs wires) :
    wires = inputs + gateCount program := by
  induction program with
  | start => simp [gateCount]
  | nand priorProgram first second ih => simp only [gateCount]; omega

/-- Execute each gate once and append its concrete data to the wire table. -/
def runStored {Data : Type} {inputs : ℕ} (operation : Data → Data → Data)
    (initial : Vector Data inputs) : {wires : ℕ} → Program inputs wires → Vector Data wires
  | _, .start => initial
  | _, .nand priorProgram first second =>
      let previous := runStored operation initial priorProgram
      let output := operation (previous.get first) (previous.get second)
      previous.push output

/-- Plaintext Boolean semantics of the same indexed program. -/
def runBits {inputs wires : ℕ} (initial : Vector Bool inputs) (program : Program inputs wires) :
    Vector Bool wires :=
  runStored (fun first second ↦ !(first && second)) initial program

/-- Explicit accounting of public gate calls, with the same stored-data recursion. -/
def runCounted {Data : Type} {inputs : ℕ} (operation : Data → Data → Data)
    (initial : Vector Data inputs) : {wires : ℕ} → Program inputs wires → Vector Data wires × ℕ
  | _, .start => (initial, 0)
  | _, .nand priorProgram first second =>
      let previous := runCounted operation initial priorProgram
      let output := operation (previous.1.get first) (previous.1.get second)
      (previous.1.push output, previous.2 + 1)

/-- Counting does not change the result, and counts exactly one operation per DAG gate. -/
theorem runCounted_eq {Data : Type} {inputs wires : ℕ} (operation : Data → Data → Data)
    (initial : Vector Data inputs) (program : Program inputs wires) :
    runCounted operation initial program = (runStored operation initial program, gateCount program) := by
  induction program with
  | start => rfl
  | nand priorProgram first second ih => simp only [runCounted, ih, runStored, gateCount]

/-- Transfer any gate-preserved relation to every shared wire in the actual stored evaluator. -/
theorem runStored_rel {Data : Type} {inputs wires : ℕ} (operation : Data → Data → Data)
    (relation : Data → Bool → Prop) (initial : Vector Data inputs) (messages : Vector Bool inputs)
    (program : Program inputs wires)
    (hoperation : ∀ first second firstBit secondBit,
      relation first firstBit → relation second secondBit →
        relation (operation first second) (!(firstBit && secondBit)))
    (hinputs : ∀ index, relation (initial.get index) (messages.get index)) :
    ∀ index, relation ((runStored operation initial program).get index)
      ((runBits messages program).get index) := by
  unfold runBits
  induction program with
  | start => exact hinputs
  | nand priorProgram first second ih =>
    intro index
    refine Fin.lastCases ?_ (fun earlier ↦ ?_) index
    · simpa only [runStored, Vector.get_push_last] using
        hoperation _ _ _ _ (ih first) (ih second)
    · simpa only [runStored, Vector.get_push_castSucc] using ih earlier

/-- Concrete stored NAND/refresh operation with caller-supplied public parameters. -/
def refreshedNand {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (level : Fin params.levels) (oneCode : ZMod p)
    (controls : Vector (StoredCiphertext params (dimension + 1)) dimension)
    (first second : StoredCiphertext params (dimension + 1)) : StoredCiphertext params (dimension + 1) :=
  bootstrapStored params (fun index ↦ ciphertextView params (controls.get index))
    (nand params (ciphertextView params first) (ciphertextView params second)) level oneCode

/-- Complete public circuit evaluation, retaining previously computed wire data. -/
def evaluateWires {factor p dimension inputs wires : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (level : Fin params.levels) (oneCode : ZMod p)
    (controls : Vector (StoredCiphertext params (dimension + 1)) dimension)
    (initial : Vector (StoredCiphertext params (dimension + 1)) inputs)
    (program : Program inputs wires) :
    Vector (StoredCiphertext params (dimension + 1)) wires :=
  runStored (refreshedNand params level oneCode controls) initial program

/-- A selected output is a fixed-size stored ciphertext, independently of program depth or size. -/
def evaluate {factor p dimension inputs wires : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (level : Fin params.levels) (oneCode : ZMod p)
    (controls : Vector (StoredCiphertext params (dimension + 1)) dimension)
    (initial : Vector (StoredCiphertext params (dimension + 1)) inputs)
    (program : Program inputs wires) (output : Fin wires) :
    StoredCiphertext params (dimension + 1) :=
  (evaluateWires params level oneCode controls initial program).get output

/-- The same bounded-noise invariant holds on every wire, including reused intermediate wires. -/
theorem noiseBound_evaluateWires {dimension inputs wires : ℕ} (bits : Fin dimension → Bool)
    (controls : Vector (StoredCiphertext (GSWBootstrapParameters.params dimension) (dimension + 1))
      dimension)
    (initial : Vector (StoredCiphertext (GSWBootstrapParameters.params dimension) (dimension + 1)) inputs)
    (messages : Vector Bool inputs) (program : Program inputs wires)
    (hcontrols : ∀ index, NoiseBound (GSWBootstrapParameters.params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension) (controls.get index))
      (bitMessage (bits index)) (GSWBootstrapParameters.keyBound dimension))
    (hinputs : ∀ index, NoiseBound (GSWBootstrapParameters.params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension) (initial.get index))
      (bitMessage (messages.get index)) (GSWBootstrapParameters.outputBound dimension)) :
    ∀ index, NoiseBound (GSWBootstrapParameters.params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension)
        ((evaluateWires (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
          (GSWBootstrapParameters.oneCode dimension) controls initial program).get index))
      (bitMessage ((runBits messages program).get index)) (GSWBootstrapParameters.outputBound dimension) := by
  apply runStored_rel (refreshedNand (GSWBootstrapParameters.params dimension)
    (GSWBootstrapParameters.level dimension) (GSWBootstrapParameters.oneCode dimension) controls)
    (fun ciphertext bit ↦ NoiseBound (GSWBootstrapParameters.params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension) ciphertext)
      (bitMessage bit) (GSWBootstrapParameters.outputBound dimension)) initial messages program _ hinputs
  intro first second firstBit secondBit hfirst hsecond
  exact GSWBootstrapParameters.noiseBound_refreshedNand bits
    (fun index ↦ ciphertextView (GSWBootstrapParameters.params dimension) (controls.get index))
    _ _ firstBit secondBit hcontrols hfirst hsecond

/-- Arbitrary-depth shared-circuit correctness under the original one-key secret. -/
theorem decrypt_evaluate {dimension inputs wires : ℕ} (bits : Fin dimension → Bool)
    (controls : Vector (StoredCiphertext (GSWBootstrapParameters.params dimension) (dimension + 1))
      dimension)
    (initial : Vector (StoredCiphertext (GSWBootstrapParameters.params dimension) (dimension + 1)) inputs)
    (messages : Vector Bool inputs) (program : Program inputs wires) (output : Fin wires)
    (hcontrols : ∀ index, NoiseBound (GSWBootstrapParameters.params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension) (controls.get index))
      (bitMessage (bits index)) (GSWBootstrapParameters.keyBound dimension))
    (hinputs : ∀ index, NoiseBound (GSWBootstrapParameters.params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension) (initial.get index))
      (bitMessage (messages.get index)) (GSWBootstrapParameters.outputBound dimension)) :
    decrypt (GSWBootstrapParameters.params dimension) (GSWSelfKey.binaryEmbed bits)
      (ciphertextView (GSWBootstrapParameters.params dimension)
        (evaluate (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
          (GSWBootstrapParameters.oneCode dimension) controls initial program output))
      (GSWBootstrapParameters.level dimension) = (runBits messages program).get output :=
  decrypt_eq_bit (GSWBootstrapParameters.params dimension) (GSWSelfKey.binaryEmbed bits) _ _ _
    (GSWBootstrapParameters.level dimension)
    (noiseBound_evaluateWires bits controls initial messages program hcontrols hinputs output)
    (GSWBootstrapParameters.output_margin dimension)

end FormalProof4FHE.LWE.GSWCircuit
