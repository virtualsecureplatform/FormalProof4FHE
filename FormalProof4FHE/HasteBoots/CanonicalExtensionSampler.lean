module

public import FormalProof4FHE.HasteBoots.CanonicalCoefficientWork
public import Mathlib.LinearAlgebra.Basis.Defs
public import FormalProof4FHE.HasteBoots.SharedContinuation

@[expose] public section

/-!
# Extension assembly after sequential canonical coefficient sampling

The core fills flat coordinates in increasing order, then applies a pure
indexed constructor. Indexing is element*degree+coordinate. The constructor
cannot resample coefficients or alter their retained raw-byte traces.

This models the core after native profile/degree/size validation. A proved
basis supplies the mathematical coordinate map; matching the concrete Rust
field constructor and descriptors, XOF/transcript execution and hash work
remain separate refinement obligations. Byte counts exclude phase framing,
including zero-element identity phases.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.CanonicalExtensionSampler

noncomputable section

variable {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]

def assemble (basis : Module.Basis (Fin degree) (ZMod p) K) {count : ℕ}
    (flat : Fin (count * degree) → ZMod p) : Fin count → K :=
  fun element => basis.equivFun.symm (fun coordinate => flat (finProdFinEquiv (element, coordinate)))

/-- The trusted getter uses the same flat offset as the nested native loops. -/
theorem offset {count : ℕ} (element : Fin count) (coordinate : Fin degree) :
    (finProdFinEquiv (element, coordinate)).val = coordinate.val + degree * element.val := rfl

/-- Fixed indexed coefficients, independent of the constructor's read order. -/
theorem assemble_coordinate (basis : Module.Basis (Fin degree) (ZMod p) K) {count : ℕ}
    (flat : Fin (count * degree) → ZMod p) (element : Fin count) (coordinate : Fin degree) :
    basis.equivFun (assemble basis flat element) coordinate = flat (finProdFinEquiv (element, coordinate)) := by
  simp only [assemble, LinearEquiv.apply_symm_apply]

/-- Actual coefficient and field-vector spaces are in bijection; no assumed
independence or guessed extension cardinality enters the uniformity proof. -/
def assemblyEquiv (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) :
    (Fin (count * degree) → ZMod p) ≃ (Fin count → K) where
  toFun := assemble basis
  invFun values index :=
    basis.equivFun (values ((finProdFinEquiv (m := count) (n := degree)).symm index).1)
      ((finProdFinEquiv (m := count) (n := degree)).symm index).2
  left_inv flat := by
    funext index
    simp only [assemble_coordinate]
    exact congrArg flat ((finProdFinEquiv (m := count) (n := degree)).apply_symm_apply index)
  right_inv values := by
    funext element
    apply basis.equivFun.injective
    funext coordinate
    simp only [assemble, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]

def program (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ) :
    ProbComp (Option (Fin count → K) × CanonicalCoefficientVector.Result p (count * degree)) :=
  (fun coefficients => (coefficients.values.map (assemble basis), coefficients)) <$>
    CanonicalCoefficientVector.program p fuel (count * degree)

/-- Erasing the pure assembled value preserves the whole actual coefficient
program, its partial accepted values and all previously issued byte queries. -/
theorem raw_erasure (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ) :
    Prod.snd <$> program basis fuel count = CanonicalCoefficientVector.program p fuel (count * degree) := by
  rw [program, Functor.map_map]
  exact id_map _

theorem observation (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ) (event : (Fin count → K) → Prop) :
    Pr{let result ← program basis fuel count}[result.1.elim False event] =
      Pr{let result ← CanonicalCoefficientVector.program p fuel (count * degree)}[
        result.values.elim False (fun flat => event (assemble basis flat))] := by
  rw [program, prEvent_map]
  exact prEvent_congr _ _ _ (fun result => by cases result.values <;> rfl)

variable [NeZero p] [SampleableType K]

theorem uniform_assembly (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) (event : (Fin count → K) → Prop) :
    Pr{let flat ← $ᵗ (Fin (count * degree) → ZMod p)}[event (assemble basis flat)] =
      Pr{let values ← $ᵗ (Fin count → K)}[event values] :=
  SampleableType.prEvent_uniformSample_equiv (assemblyEquiv basis count) event

/-- Finite-prefix field-vector law, retaining the exact chance that every
required canonical coefficient has actually completed. -/
theorem probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ)
    (event : (Fin count → K) → Prop) :
    Pr{let result ← program basis fuel count}[result.1.elim False event] =
      CanonicalCoefficientVector.completion p fuel ^ (count * degree) *
        Pr{let values ← $ᵗ (Fin count → K)}[event values] := by
  rw [observation, CanonicalCoefficientVector.probability p valid, uniform_assembly]

def eventProbability (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) (event : (Fin count → K) → Prop) : ENNReal :=
  ⨆ fuel, Pr{let result ← program basis fuel count}[result.1.elim False event]

/-- Unbounded field vectors have their derived uniform joint law. Actual
scalar filling order and all rejected raw chunks remain in the execution. -/
theorem uniform_values (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ)
    (event : (Fin count → K) → Prop) :
    eventProbability basis count event = Pr{let values ← $ᵗ (Fin count → K)}[event values] := by
  unfold eventProbability
  simp_rw [observation]
  exact (CanonicalCoefficientVector.uniform_values p valid (count * degree) _).trans (uniform_assembly basis count event)

omit [NeZero p] [SampleableType K] in
/-- Pure assembly adds no byte reads; the expected cost still observes every
raw chunk on success and on suspension. -/
theorem expectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result => (CanonicalCoefficientWork.consumedBytes p result.2 : ENNReal)) <$>
      program basis fuel count]) = CanonicalCoefficientWork.expectedBytes p fuel (count * degree) := by
  rw [program, Functor.map_map]
  rfl

omit [SampleableType K] in
/-- Full raw-byte cost is the number of requested elements times their actual
extension degree times the canonical base-coefficient cost. -/
theorem totalExpectedBytes (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) :
    (⨆ fuel, ∫⁻ value, value ∂𝒟[(fun result => (CanonicalCoefficientWork.consumedBytes p result.2 : ENNReal)) <$>
      program basis fuel count]) = ((count * degree : ℕ) : ENNReal) * CanonicalByteSampler.totalExpectedBytes p := by
  simp_rw [expectedBytes]
  exact CanonicalCoefficientWork.totalExpectedBytes_eq p valid (count * degree)

section SharedRuntime

variable {Cfg Input Digest Payload Later : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

omit [NeZero p] [SampleableType K] in
/-- Every finite byte/assembly prefix preserves the incoming hash/cache and
checkpoint state while retaining its complete raw coefficient observation. -/
theorem private_state (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (PrivateSampling.embed Cfg Input Digest (program basis fuel count))).run state =
      (fun result => (result, state)) <$> program basis fuel count :=
  PrivateSampling.run_probComp enc dummy shape _ state

/-- Later adaptive work receives the full byte trace and partial coefficient
memory, not only an erased accepted value. Its actual shared queries remain
in the complete execution, and cannot amplify the earlier value event. -/
theorem retained_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (next : (Option (Fin count → K) × CanonicalCoefficientVector.Result p (count * degree)) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (event : (Fin count → K) → Prop) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PrivateSampling.embed Cfg Input Digest (program basis fuel count)) next)).run state}[
        result.1.1.1.elim False event] ≤
      CanonicalCoefficientVector.completion p fuel ^ (count * degree) * Pr{let values ← $ᵗ (Fin count → K)}[event values] := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (program basis fuel count)) next state (fun earlier => earlier.1.elim False event)
  have sampled := probability valid basis fuel count event
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_map] using sampled.le)

end SharedRuntime

end

end FormalProof4FHE.HasteBoots.CanonicalExtensionSampler
